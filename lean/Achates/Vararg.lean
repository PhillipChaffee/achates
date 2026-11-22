import Achates.Memory
/-!
Variadic arguments (C11 7.16) on x86-64: the `...` arguments of a call,
`va_list` values, and `va_start`, `va_arg`, `va_copy` and `va_end`.

On this ABI a `va_list` is an array of one 24-byte structure, so a function
that is passed a `va_list` receives a pointer to its caller's object. The
model keeps the list's state beside the memory (`Mem.vaLists`); the bytes of
the object say which list it holds (`MByte.va`), and reading them as an
integer is `unsupported`.

Undefined, and reported as undefined behaviour:
- `va_arg` past the last argument, or with a type not compatible with the
  argument's promoted type (7.16.1.1p2), except for the two cases C defines:
  a signed integer type read as the corresponding unsigned type or back,
  when the value fits both; a pointer to `void` read as a pointer to a
  character type or back;
- any use of a `va_list` object that `va_start` or `va_copy` did not
  initialise, or that `va_end` ended;
- `va_start` or `va_copy` into a list that was not ended first (7.16.1.2,
  7.16.1.4);
- a return from a function that started or copied a list without ending it,
  and `va_end` in another function than the one that started or copied the
  list (7.16.1);
- any use but `va_end` of a list after passing it to a function that read
  from it (7.16p3);
- `va_arg` on a list after the variadic function whose arguments it walks
  has returned.

Pointer types whose compatibility the spelling does not decide (arrays,
functions, enums, and pointers that differ only in qualifiers, where C11
and C23 disagree) are `unsupported`.
-/
namespace Achates

namespace VArg

def ty : VArg → VTy
  | @sint w r _ => .int true w r
  | @uint w r _ => .int false w r
  | f64 _ => .double
  | ptr t _ => .ptr t
  | agg t _ => .agg t

def bytes : VArg → Array MByte
  | sint _ v => CVal.encode v
  | uint _ v => CVal.encode v
  | f64 v => CVal.encode v
  | ptr _ p => CVal.encode p
  | agg _ a => a.bytes

end VArg

namespace VTy

/-- The type as C spells it, for messages. -/
def spell : VTy → String
  | int s _ r => if s then r else s!"unsigned {r}"
  | double => "double"
  | ptr t => s!"{t} *"
  | agg t => t

end VTy

namespace VaList

/-- `sizeof (va_list)` and its alignment on x86-64; the emitter checks both
with clang. -/
def size : Nat := 24
def align : Nat := 8

/-- Entry to a variadic function: its `...` arguments, by number. -/
def enter (args : List VArg) : M Nat := do
  let n := (← get).vaArgs.size
  modify fun m => { m with vaArgs := m.vaArgs.push { args := (args.map fun a => (a.ty, a.bytes)).toArray } }
  pure n

/-- Return from a variadic function: its arguments are gone. -/
def leave (n : Nat) : M Unit :=
  modify fun m => { m with vaArgs := m.vaArgs.modify n fun a => { a with live := false } }

/-- Entry to a function that uses `va_start`, `va_copy` or `va_end`: the
number of this call, which owns the lists it starts and copies. -/
def call : M Nat := do
  let n := (← get).vaCalls
  modify fun m => { m with vaCalls := n + 1 }
  pure n

/-- Return from such a function: every list it started or copied must be ended. -/
def checkEnded (c : Nat) : M Unit := do
  if (← get).vaLists.any fun l => l.owner == c && !l.ended then
    ub "return from a function that did not va_end a va_list it started or copied"

/-- The list the object at `p` holds, if its bytes are those of one. Does
not fail: an object that holds no list gives `none`. -/
def peek (m : Mem) (p : Ptr) : Option Nat :=
  match p with
  | .obj b off =>
    match m.blocks[b]? with
    | some blk =>
      if !blk.live || off < 0 then none
      else
        let bs := blk.data.extract off.toNat (off.toNat + size)
        match (bs[0]? : Option MByte) with
        | some (.va n 0) =>
          if bs.size = size ∧ (List.range size).all fun i => bs[i]? == some (.va n i) then some n
          else none
        | _ => none
    | none => none
  | _ => none

/-- The open list the `va_list` object at `p` holds. -/
def held (what : String) (p : Ptr) : M (Nat × VaState) := do
  -- An access check first, so that a bad pointer is reported as such.
  discard <| Mem.loadBytes p size align
  let m ← get
  let some n := peek m p
    | ub s!"{what} on an object that holds no va_list (not initialised by va_start or va_copy, or ended by va_end)"
  let some l := m.vaLists[n]? | ub s!"{what} on an object that holds no va_list"
  if l.ended then ub s!"{what} on a va_list after va_end"
  pure (n, l)

/-- A new list `l`, stored in the object at `p`, which must not hold a list
that is still open. -/
def fresh (what : String) (p : Ptr) (l : VaState) : M Unit := do
  let m ← get
  if let some n := peek m p then
    if (m.vaLists[n]?.map (!·.ended)).getD false then
      ub s!"{what} into a va_list that was not ended with va_end"
  let n := m.vaLists.size
  modify fun m => { m with vaLists := m.vaLists.push l }
  Mem.storeBytes p (Array.ofFn (n := size) fun i => .va n i.val) align

/-- `va_start(ap, last)`, in the call `c` of a variadic function whose
arguments are number `args`. -/
def start (p : Ptr) (args c : Nat) : M Unit := fresh "va_start" p { args, owner := c }

/-- `va_copy(dst, src)` in the call `c`. -/
def copy (dst src : Ptr) (c : Nat) : M Unit := do
  let (_, l) ← held "va_copy" src
  if l.spent then
    ub "va_copy from a va_list passed to a function that read from it (its value is indeterminate)"
  fresh "va_copy" dst { args := l.args, pos := l.pos, owner := c }

/-- `va_end(ap)` in the call `c`; the object becomes indeterminate. -/
def «end» (p : Ptr) (c : Nat) : M Unit := do
  let (n, l) ← held "va_end" p
  if l.owner != c then
    ub "va_end in a function other than the one that started or copied the va_list"
  modify fun m => { m with vaLists := m.vaLists.modify n fun l => { l with ended := true } }
  Mem.undefine p size

/-- `va_arg`: the next argument, with its promoted type and its bytes. -/
def next (p : Ptr) : M (VTy × Array MByte) := do
  let (n, l) ← held "va_arg" p
  if l.spent then
    ub "va_arg on a va_list passed to a function that read from it (its value is indeterminate)"
  let some a := (← get).vaArgs[l.args]? | ub "va_arg on a va_list of no call"
  if !a.live then ub "va_arg on a va_list after the variadic function it walks returned"
  let some arg := a.args[l.pos]?
    | ub s!"va_arg past the last variadic argument (there are {a.args.size})"
  modify fun m => { m with vaLists := m.vaLists.modify n fun l => { l with pos := l.pos + 1 } }
  pure arg

/-- A call `x` that is passed the `va_list` at `p` by value. If the callee
read from the list, its value in the caller is indeterminate afterwards:
only `va_end` may follow (C11 7.16p3). -/
def passing {α : Type} (p : Ptr) (x : M α) : M α := do
  let m ← get
  let before := (peek m p).bind fun n => m.vaLists[n]?.map fun l => (n, l.pos)
  let r ← x
  if let some (n, pos) := before then
    if ((← get).vaLists[n]?.map (·.pos != pos)).getD false then
      modify fun m => { m with vaLists := m.vaLists.modify n fun l => { l with spent := true } }
  pure r

def mismatch {α : Type} (want : String) (t : VTy) : M α :=
  ub s!"va_arg of type {want} for an argument of type {t.spell}"

/-- `va_arg(ap, T)` for a signed integer type `T` of rank `rank`. -/
def argS (p : Ptr) (w : Nat) (rank : String) : M (SInt w) := do
  let (t, bs) ← next p
  match t with
  | .int s b r =>
    if b ≠ w ∨ r ≠ rank then mismatch rank t
    else if s then CVal.decode bs
    else
      let v : UInt w ← CVal.decode bs
      if v.toNat < 2 ^ (w - 1) then pure (SInt.ofInt w v.toNat)
      else ub s!"va_arg of type {rank} for an unsigned {rank} argument {v.toNat} that {rank} cannot represent"
  | _ => mismatch rank t

/-- `va_arg(ap, T)` for an unsigned integer type `T` of rank `rank`. -/
def argU (p : Ptr) (w : Nat) (rank : String) : M (UInt w) := do
  let (t, bs) ← next p
  match t with
  | .int s b r =>
    if b ≠ w ∨ r ≠ rank then mismatch s!"unsigned {rank}" t
    else if !s then CVal.decode bs
    else
      let v : SInt w ← CVal.decode bs
      if v.toInt ≥ 0 then pure (UInt.ofNat w v.toInt.toNat)
      else ub s!"va_arg of type unsigned {rank} for a {rank} argument {v.toInt} that it cannot represent"
  | _ => mismatch s!"unsigned {rank}" t

/-- `va_arg(ap, double)`. -/
def argF64 (p : Ptr) : M Float := do
  let (t, bs) ← next p
  match t with
  | .double => CVal.decode bs
  | _ => mismatch "double" t

def isChar (s : String) : Bool := s == "char" || s == "signed char" || s == "unsigned char"

def stripQuals (s : String) : String :=
  ((s.replace "const " "").replace "volatile " "").replace "restrict " ""

/-- `va_arg(ap, T *)`, `T` spelt `pointee`. -/
def argPtr (p : Ptr) (pointee : String) : M Ptr := do
  let (t, bs) ← next p
  match t with
  | .ptr q =>
    if q = pointee ∨ (q = "void" ∧ isChar pointee) ∨ (pointee = "void" ∧ isChar q) then
      CVal.decode bs
    else if [q, pointee].any (fun s => s.any (fun c => c == '[' || c == '(') || (s.splitOn "enum ").length > 1)
        || stripQuals q = stripQuals pointee then
      unsupported s!"va_arg of type {pointee} * for an argument of type {q} *: whether the two are compatible is not decided"
    else mismatch s!"{pointee} *" t
  | _ => mismatch s!"{pointee} *" t

end VaList

end Achates
