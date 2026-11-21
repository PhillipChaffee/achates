import Achates.Memory
/-!
Models of the C library functions whose behaviour the C standard fixes.
Each takes and returns the Lean types the emitter maps the C prototype to.

Where the standard leaves the result open the model says so: `memcmp`,
`strcmp` and `strncmp` promise only the sign of their result, and the model
returns the difference of the first differing bytes, which is what glibc
does on x86-64. The emitter records that as an assumption of every function
that calls them.
-/
namespace Achates.Libc

open Achates

/-- C11 7.24.1p2: pointer arguments must be valid even when the count is zero. -/
def checkRange (what : String) (p : Ptr) (n : Nat) : M Unit := do
  if p == .null then ub s!"{what} with a null pointer"
  discard <| Mem.loadBytes p n

def memcpy (dst src : Ptr) (n : U64) : M Ptr := do
  let n := n.toNat
  checkRange "memcpy" dst n
  let bs ← Mem.loadBytes src n
  match dst, src with
  | .obj b o, .obj b' o' =>
    if b = b' ∧ n > 0 ∧ o < o' + n ∧ o' < o + n then ub "memcpy between overlapping objects"
  | _, _ => pure ()
  Mem.storeBytes dst bs
  pure dst

def memmove (dst src : Ptr) (n : U64) : M Ptr := do
  let n := n.toNat
  checkRange "memmove" dst n
  let bs ← Mem.loadBytes src n
  Mem.storeBytes dst bs
  pure dst

def memset (dst : Ptr) (c : I32) (n : U64) : M Ptr := do
  if dst == .null then ub "memset with a null pointer"
  Mem.fill dst n.toNat (.byte (UInt8.ofNat (SInt.toU 8 c).toNat))
  pure dst

def bytesAt (p : Ptr) (n : Nat) : M (List UInt8) :=
  (List.range n).mapM fun (i : Nat) => do Mem.loadByte (← p.add 1 i)

def firstDiff : List UInt8 → List UInt8 → I32
  | a :: as, b :: bs => if a = b then firstDiff as bs else SInt.ofInt 32 ((a.toNat : Int) - b.toNat)
  | _, _ => 0

def memcmp (a b : Ptr) (n : U64) : M I32 := do
  let n := n.toNat
  checkRange "memcmp" a n
  checkRange "memcmp" b n
  pure (firstDiff (← bytesAt a n) (← bytesAt b n))

/-- C11 7.24.5.1: behaves as if it read the bytes in order and stopped at the
first match, so the object may be shorter than `n` when a match exists. -/
def memchr (s : Ptr) (c : I32) (n : U64) : M Ptr := do
  if s == .null then ub "memchr with a null pointer"
  let c := UInt8.ofNat (SInt.toU 8 c).toNat
  let rec go : Nat → Nat → M Ptr
    | 0, _ => pure .null
    | k + 1, i => do
      let p ← s.add 1 i
      if (← Mem.loadByte p) = c then pure p else go k (i + 1)
  go n.toNat 0

/-- The bytes of the string at `s`, without the terminator. Reading past the
end of the object before a terminator is found is undefined. -/
def cstr (s : Ptr) : M (List UInt8) := do
  let some (_, off, size) ← s.live | ub "string function applied to a pointer to no object"
  let rec go : Nat → Nat → List UInt8 → M (List UInt8)
    | 0, _, _ => ub "string without a terminator inside its object"
    | k + 1, i, acc => do
      let c ← Mem.loadByte (← s.add 1 i)
      if c = 0 then pure acc.reverse else go k (i + 1) (c :: acc)
  go (size - off.toNat + 1) 0 []

def strlen (s : Ptr) : M U64 := do
  pure (UInt.ofNat 64 (← cstr s).length)

def strcmp (a b : Ptr) : M I32 := do
  -- The terminators are compared too, so a proper prefix compares less.
  pure (firstDiff ((← cstr a) ++ [0]) ((← cstr b) ++ [0]))

def strncmp (a b : Ptr) (n : U64) : M I32 := do
  let rec go : Nat → Nat → M I32
    | 0, _ => pure 0
    | k + 1, i => do
      let x ← Mem.loadByte (← a.add 1 i)
      let y ← Mem.loadByte (← b.add 1 i)
      if x != y then pure (SInt.ofInt 32 ((x.toNat : Int) - y.toNat))
      else if x = 0 then pure 0
      else go k (i + 1)
  if n.toNat > 0 ∧ (a == .null ∨ b == .null) then ub "strncmp with a null pointer"
  go n.toNat 0

/-- The terminator is part of the string, so `strchr(s, 0)` finds it. -/
def strchr (s : Ptr) (c : I32) : M Ptr := do
  let c := UInt8.ofNat (SInt.toU 8 c).toNat
  let bs ← cstr s
  match (bs ++ [0]).findIdx? (· = c) with
  | some i => s.add 1 i
  | none => pure .null

def showCStr (s : Ptr) : M String := do
  pure (String.ofList ((← cstr s).map fun b => Char.ofNat b.toNat))

def «__assert_fail» (expr file : Ptr) (line : U32) (func : Ptr) : M Unit := do
  throw (.assertFail (← showCStr expr) (← showCStr file) line.toNat (← showCStr func))

def abort : M Unit := throw .abort

def malloc (n : U64) : M Ptr := Mem.alloc .malloc n.toNat 16 .undef

def calloc (n size : U64) : M Ptr :=
  if n.toNat * size.toNat ≥ 2 ^ 64 then unsupported "calloc whose size overflows"
  else Mem.alloc .malloc (n.toNat * size.toNat) 16 (.byte 0)

def free (p : Ptr) : M Unit := do
  match p with
  | .null => pure ()
  | .obj b 0 =>
    let some blk := (← get).blocks[b]? | ub "free of a pointer to no object"
    if !blk.live then ub "free of an object that was already freed"
    if blk.kind != .malloc then ub "free of an object that malloc did not return"
    Mem.popFrame [p]
  | _ => ub "free of a pointer that malloc did not return"

end Achates.Libc
