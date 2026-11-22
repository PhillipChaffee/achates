import Achates
/-!
What a generated check driver needs: reading one test input from tokens,
building the objects it describes in memory, and printing what a call left
behind in a form the C harness prints the same way.

A pointer is never printed as a number. It is printed by where it points:
`null`, `in<k>+<off>` for an offset into the `k`-th object the input
created, or by the bytes it points to when the call made or found the
object elsewhere.
-/
namespace AchatesCheck

open Achates

structure St where
  toks : Array String
  pos : Nat := 0
  /-- Block number of each object the input created, in creation order. -/
  inputs : Array Nat := #[]
  /-- Which of them are byte buffers whose final contents are reported. -/
  dumped : Array Nat := #[]
  /-- Which of them are buffers the C side allocates with talloc. -/
  tallocBufs : Array Nat := #[]

abbrev H := StateT St M

def bad {α : Type} (msg : String) : H α := throw (.unsupported s!"check harness: {msg}")

def tok : H String := do
  let s ← get
  match s.toks[s.pos]? with
  | some t =>
    set { s with pos := s.pos + 1 }
    pure t
  | none => bad "input line is too short"

def natTok : H Nat := do
  let t ← tok
  match t.toNat? with
  | some n => pure n
  | none => bad s!"`{t}` is not a number"

def intTok : H Int := do
  let t ← tok
  match t.toInt? with
  | some n => pure n
  | none => bad s!"`{t}` is not an integer"

def uint (w : Nat) : H (UInt w) := do pure (UInt.ofNat w (← natTok))
def sint (w : Nat) : H (SInt w) := do pure (SInt.ofInt w (← intTok))
def bool : H Bool := do pure ((← natTok) != 0)

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else none

def hexBytes : List Char → List UInt8 → Option (List UInt8)
  | [], acc => some acc.reverse
  | a :: b :: rest, acc =>
    match hexVal a, hexVal b with
    | some x, some y => hexBytes rest (UInt8.ofNat (x * 16 + y) :: acc)
    | _, _ => none
  | _, _ => none

def hexNat (s : String) : Option Nat :=
  s.toList.foldlM (fun acc c => (hexVal c).map (acc * 16 + ·)) 0

def f64 : H Float := do
  let t ← tok
  match hexNat t with
  | some n => pure (Float.ofBits (UInt64.ofNat n))
  | none => bad s!"`{t}` is not a hexadecimal bit pattern"

def f32 : H Float32 := do
  let t ← tok
  match hexNat t with
  | some n => pure (Float32.ofBits (UInt32.ofNat n))
  | none => bad s!"`{t}` is not a hexadecimal bit pattern"

/-- Makes an input object and remembers it, so that pointers into it can be
printed relative to it. -/
def newInput (kind : BlockKind) (bytes : Array MByte) (align : Nat) (buffer : Bool) : H Ptr := do
  let p ← (Mem.alloc kind bytes.size align .undef : M Ptr)
  (Mem.storeBytes p bytes : M Unit)
  let .obj b _ := p | bad "allocation did not return an object"
  modify fun s => { s with
    inputs := s.inputs.push b
    dumped := if buffer ∧ kind != .talloc then s.dumped.push b else s.dumped
    tallocBufs := if buffer ∧ kind == .talloc then s.tallocBufs.push b else s.tallocBufs }
  pure p

/-- A byte buffer: `N` is the null pointer, `H<hex>` an object holding those
bytes, with a terminating zero added when `nul`; `H<hex>:<k>` adds `k`
indeterminate bytes of room to a talloc buffer. A talloc buffer is one the
C side allocates with talloc, so the function may resize or free it; its
final contents are reported through whatever still points to it. -/
def buffer (talloc nul : Bool) : H (Ptr × Nat) := do
  let t ← tok
  if t == "N" then return (.null, 0)
  match t.toList with
  | 'H' :: body =>
    let (hex, room) := match List.splitOn ':' body with
      | [h, k] => (h, (String.ofList k).toNat?.getD 0)
      | _ => (body, 0)
    let some bs := hexBytes hex [] | bad s!"`{t}` is not a hexadecimal buffer"
    let bs := if nul then bs ++ [0] else bs
    let room := if talloc then Array.replicate room MByte.undef else #[]
    let p ← newInput (if talloc then .talloc else .malloc) (bs.toArray.map .byte ++ room)
      (if talloc then 16 else 1) true
    pure (p, if nul then bs.length - 1 else bs.length)
  | _ => bad s!"`{t}` is not a buffer"

def cstr : H Ptr := do pure (← buffer false true).1

namespace Agg'

def zero (size : Nat) : Agg := ⟨Array.replicate size (.byte 0)⟩

def putBytes (a : Agg) (off : Nat) (bs : Array MByte) : Agg :=
  ⟨(List.range bs.size).foldl (init := a.bytes) fun d i =>
    d.setIfInBounds (off + i) (bs[i]?.getD .undef)⟩

def put {α : Type} [CVal α] (a : Agg) (off : Nat) (v : α) : Agg := putBytes a off (CVal.encode v)

def putAgg (a : Agg) (off : Nat) (v : Agg) : Agg := putBytes a off v.bytes

end Agg'

/-- mpv's `struct bstr`: a pointer at offset 0 and a length at offset 8. -/
def bstrOf (p : Ptr) (len : Nat) : Agg :=
  Agg'.put (Agg'.put (Agg'.zero 16) 0 p) 8 (UInt.ofNat 64 len)

def bstr (talloc : Bool) : H Agg := do
  let (p, n) ← buffer talloc false
  pure (bstrOf p n)

/-- A talloc context: `N` for none, `C` for a fresh empty one. -/
def tallocCtx : H Ptr := do
  let t ← tok
  if t == "N" then pure .null
  else
    let p ← (Talloc.ta_new_context .null : M Ptr)
    let .obj b _ := p | bad "allocation did not return an object"
    modify fun s => { s with inputs := s.inputs.push b }
    pure p

/-- The pointee of an in/out parameter: `N` for a null pointer, `P` followed
by the pointee's own tokens. -/
def pointee (size align : Nat) (read : H (Array MByte)) : H Ptr := do
  let t ← tok
  if t == "N" then pure .null
  else
    let bs ← read
    if bs.size != size then bad s!"pointee of {bs.size} bytes, expected {size}"
    newInput .malloc bs (max align 16) false

def hexByte (b : UInt8) : String :=
  let d (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

/-- Bytes as hexadecimal. An indeterminate byte is `??`: C may hold anything
there, so the comparison accepts any byte. -/
def hexOf (bs : Array MByte) : Except Err String :=
  bs.foldlM (init := "") fun acc b =>
    match b with
    | .byte v => pure (acc ++ hexByte v)
    | .undef => pure (acc ++ "??")
    | .frag _ _ => throw (.unsupported "a stored pointer where bytes are reported")

def renderErr (e : Err) : String :=
  let one (s : String) : String := s.map fun c => if c == '\n' then ' ' else c
  match e with
  | .ub m => one s!"ub {m}"
  | .assertFail ex _ _ _ => one s!"assert {ex}"
  | .abort => "abort"
  | .unsupported m => one s!"unsupported {m}"
  | .outOfFuel => "fuel"

/-- Runs an observation; one that fails is reported in place, so that the
rest of the result is still compared. -/
def observe (x : H String) : H String :=
  fun s m => match x s m with
    | .ok r => .ok r
    | .error e => .ok ((s!"!unobservable({renderErr e})", s), m)

/-- Where a pointer points, relative to the input objects; `none` when it
points to an object the input did not create.

The start of a talloc input buffer also gives `none`. A real `realloc` may
grow such a buffer in place or move it, and the model always moves it, so
"still the input" and "a new object" cannot be told apart there by anything
C guarantees. -/
def locate (p : Ptr) : H (Option String) := do
  match p with
  | .null => pure (some "null")
  | .obj b off =>
    let s ← get
    match s.inputs.idxOf? b with
    | some k => if off == 0 ∧ s.tallocBufs.contains b then pure none else pure (some s!"in{k}+{off}")
    | none => pure none
  | .fn name => pure (some s!"fn:{name}")
  | .addr a => pure (some s!"addr:{a}")

/-- A pointer whose target's type the check does not look into. -/
def obsPtr (p : Ptr) : H String := observe do
  match ← locate p with
  | some s => pure s
  | none => pure "other"

/-- A `char *`: by position in an input, or by the string it points to. -/
def obsCStr (p : Ptr) : H String := observe do
  match ← locate p with
  | some s => pure s
  | none =>
    let bs ← (Libc.cstr p : M (List UInt8))
    pure s!"str:{String.join (bs.map hexByte)}"

/-- A `struct bstr`: by position in an input, or by its bytes. A view into
a talloc input also reports its bytes, since that buffer is not reported on
its own. -/
def obsBstr (a : Agg) : H String := observe do
  let p ← (liftM (Agg.get Ptr a 0) : M Ptr)
  let len := (← (liftM (Agg.get U64 a 8) : M U64)).toNat
  let bytes : H String := do
    if len = 0 then pure ""
    else
      let bs ← (Mem.loadBytes p len : M (Array MByte))
      (liftM (hexOf bs) : M String)
  match p, ← locate p with
  | .obj b _, some s =>
    if (← get).tallocBufs.contains b then pure s!"bstr({s},{len},{← bytes})"
    else pure s!"bstr({s},{len})"
  | _, some s => pure s!"bstr({s},{len})"
  | _, none => pure s!"bstr(new,{len},{← bytes})"
where
  liftM {α : Type} (x : Except Err α) : M α := liftExcept x

/-- The final contents of every reported input buffer. -/
def obsInputs : H String := do
  let s ← get
  let mut out := ""
  for b in s.dumped do
    let k := (s.inputs.idxOf? b).getD 0
    let r ← observe do
      let m ← getThe Mem
      match m.blocks[b]? with
      | some blk =>
        if blk.live then (liftExcept (hexOf blk.data) : M String)
        else pure "freed"
      | none => pure "freed"
    out := out ++ s!" in{k}={r}"
  pure out

/-- Runs the function under test and keeps how it ended, so that a failure
of the function is told apart from a failure of the harness around it. -/
def call {α : Type} (x : M α) : H (Except Err α) :=
  fun s m => match x.run m with
    | .ok (v, m') => .ok ((.ok v, s), m')
    | .error e => .ok ((.error e, s), m)

/-- One test input, from the memory after static initialisation. -/
def runCase (m0 : Mem) (toks : Array String) (body : H String) : String :=
  match (body.run { toks }).run m0 with
  | .ok ((s, _), _) => s
  | .error e => s!"harness {renderErr e}"

/-- A `double` by its bits; `D` and `S` occur in no other part of a result,
so the comparison can find floats and apply its two exceptions to them. -/
def obsFloat (x : Float) : String := s!"D{x.toBits.toNat}"
def obsFloat32 (x : Float32) : String := s!"S{x.toBits.toNat}"

end AchatesCheck
