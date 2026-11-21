import Achates.Basic
/-!
C integers on a two's-complement target. The width is in the type, and so is
the signedness, so Lean rejects an emitted operation applied at the wrong C
type.

Unsigned arithmetic wraps and cannot fail. Signed arithmetic fails with
undefined behaviour when the exact result does not fit.
-/
namespace Achates

structure UInt (w : Nat) where
  bv : BitVec w
  deriving DecidableEq, Inhabited

structure SInt (w : Nat) where
  bv : BitVec w
  deriving DecidableEq, Inhabited

abbrev U8 := UInt 8
abbrev U16 := UInt 16
abbrev U32 := UInt 32
abbrev U64 := UInt 64
abbrev U128 := UInt 128
abbrev I8 := SInt 8
abbrev I16 := SInt 16
abbrev I32 := SInt 32
abbrev I64 := SInt 64
abbrev I128 := SInt 128

namespace UInt
variable {w : Nat}

def toNat (a : UInt w) : Nat := a.bv.toNat
def toInt (a : UInt w) : Int := a.bv.toNat
def ofNat (w n : Nat) : UInt w := ⟨BitVec.ofNat w n⟩
def ofInt (w : Nat) (i : Int) : UInt w := ⟨BitVec.ofInt w i⟩
def ofBool (w : Nat) (b : Bool) : UInt w := ofNat w (if b then 1 else 0)

instance {n : Nat} : OfNat (UInt w) n := ⟨ofNat w n⟩
instance : Repr (UInt w) := ⟨fun a _ => repr a.toNat⟩
instance : ToString (UInt w) := ⟨fun a => toString a.toNat⟩
instance : Add (UInt w) := ⟨fun a b => ⟨a.bv + b.bv⟩⟩
instance : Sub (UInt w) := ⟨fun a b => ⟨a.bv - b.bv⟩⟩
instance : Mul (UInt w) := ⟨fun a b => ⟨a.bv * b.bv⟩⟩
instance : LT (UInt w) := ⟨fun a b => a.toNat < b.toNat⟩
instance : LE (UInt w) := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance (a b : UInt w) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))
instance (a b : UInt w) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

def neg (a : UInt w) : UInt w := ⟨-a.bv⟩
def band (a b : UInt w) : UInt w := ⟨a.bv &&& b.bv⟩
def bor (a b : UInt w) : UInt w := ⟨a.bv ||| b.bv⟩
def bxor (a b : UInt w) : UInt w := ⟨a.bv ^^^ b.bv⟩
def bnot (a : UInt w) : UInt w := ⟨~~~a.bv⟩

def div (a b : UInt w) : Except Err (UInt w) :=
  if b.toNat = 0 then throw (.ub "division by zero") else pure (ofNat w (a.toNat / b.toNat))

def rem (a b : UInt w) : Except Err (UInt w) :=
  if b.toNat = 0 then throw (.ub "remainder by zero") else pure (ofNat w (a.toNat % b.toNat))

/-- The count is the right operand's own value: C does not convert it to the
type of the left operand. -/
def shl (a : UInt w) (n : Int) : Except Err (UInt w) :=
  if n < 0 ∨ n ≥ w then throw (.ub s!"shift by {n} of a {w}-bit value")
  else pure ⟨a.bv <<< n.toNat⟩

def shr (a : UInt w) (n : Int) : Except Err (UInt w) :=
  if n < 0 ∨ n ≥ w then throw (.ub s!"shift by {n} of a {w}-bit value")
  else pure ⟨a.bv >>> n.toNat⟩

/-- Conversion to an unsigned type: reduction modulo `2^v`. -/
def toU (v : Nat) (a : UInt w) : UInt v := ⟨a.bv.setWidth v⟩
/-- Conversion to a signed type. Out-of-range values are implementation-defined
in C; gcc and clang reduce modulo `2^v`. -/
def toS (v : Nat) (a : UInt w) : SInt v := ⟨a.bv.setWidth v⟩

end UInt

namespace SInt
variable {w : Nat}

def toInt (a : SInt w) : Int := a.bv.toInt
def ofInt (w : Nat) (i : Int) : SInt w := ⟨BitVec.ofInt w i⟩
def ofBool (w : Nat) (b : Bool) : SInt w := ofInt w (if b then 1 else 0)

instance {n : Nat} : OfNat (SInt w) n := ⟨ofInt w n⟩
instance : Repr (SInt w) := ⟨fun a _ => repr a.toInt⟩
instance : ToString (SInt w) := ⟨fun a => toString a.toInt⟩
instance : LT (SInt w) := ⟨fun a b => a.toInt < b.toInt⟩
instance : LE (SInt w) := ⟨fun a b => a.toInt ≤ b.toInt⟩
instance (a b : SInt w) : Decidable (a < b) := inferInstanceAs (Decidable (a.toInt < b.toInt))
instance (a b : SInt w) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toInt ≤ b.toInt))

/-- The value `i` if the type can represent it, undefined behaviour otherwise. -/
def checked (w : Nat) (i : Int) (what : String) : Except Err (SInt w) :=
  if -(2 ^ (w - 1) : Int) ≤ i ∧ i < (2 ^ (w - 1) : Int) then pure (ofInt w i)
  else throw (.ub s!"signed overflow in {what}: {i} does not fit in {w} bits")

def add (a b : SInt w) : Except Err (SInt w) := checked w (a.toInt + b.toInt) "addition"
def sub (a b : SInt w) : Except Err (SInt w) := checked w (a.toInt - b.toInt) "subtraction"
def mul (a b : SInt w) : Except Err (SInt w) := checked w (a.toInt * b.toInt) "multiplication"
def neg (a : SInt w) : Except Err (SInt w) := checked w (-a.toInt) "negation"

/-- Truncates toward zero. `MIN / -1` does not fit and is caught by the range check. -/
def div (a b : SInt w) : Except Err (SInt w) :=
  if b.toInt = 0 then throw (.ub "division by zero")
  else checked w (Int.tdiv a.toInt b.toInt) "division"

def rem (a b : SInt w) : Except Err (SInt w) :=
  if b.toInt = 0 then throw (.ub "remainder by zero")
  -- C11 6.5.5p6: if `a / b` is not representable, `a % b` is undefined too.
  else if a.toInt = -(2 ^ (w - 1) : Int) ∧ b.toInt = -1 then
    throw (.ub "signed overflow in remainder: MIN % -1")
  else pure (ofInt w (Int.tmod a.toInt b.toInt))

def band (a b : SInt w) : SInt w := ⟨a.bv &&& b.bv⟩
def bor (a b : SInt w) : SInt w := ⟨a.bv ||| b.bv⟩
def bxor (a b : SInt w) : SInt w := ⟨a.bv ^^^ b.bv⟩
def bnot (a : SInt w) : SInt w := ⟨~~~a.bv⟩

/-- C11 6.5.7p4: defined only for a nonnegative left operand whose product
with `2^n` fits. -/
def shl (a : SInt w) (n : Int) : Except Err (SInt w) :=
  if n < 0 ∨ n ≥ w then throw (.ub s!"shift by {n} of a {w}-bit value")
  else if a.toInt < 0 then throw (.ub "left shift of a negative value")
  else checked w (a.toInt * 2 ^ n.toNat) "left shift"

/-- Right shift of a negative value is implementation-defined; gcc and clang
shift arithmetically. -/
def shr (a : SInt w) (n : Int) : Except Err (SInt w) :=
  if n < 0 ∨ n ≥ w then throw (.ub s!"shift by {n} of a {w}-bit value")
  else pure ⟨a.bv.sshiftRight n.toNat⟩

def toS (v : Nat) (a : SInt w) : SInt v := ofInt v a.toInt
def toU (v : Nat) (a : SInt w) : UInt v := UInt.ofInt v a.toInt

end SInt

end Achates
