import Achates.Int
/-!
`double` is Lean's `Float` and `float` is `Float32`: IEEE 754 binary64 and
binary32, computed by the host with round-to-nearest-even, which is what
x86-64 SSE code does unless the program changes the rounding mode.

Lean proves nothing about `Float` arithmetic, so these definitions execute
but give later proofs no facts to use.
-/
namespace Achates

abbrev F64 := Float
abbrev F32 := Float32

namespace F64

/-- Rounds toward zero; exact, since the result is a `Float`. -/
def trunc (x : Float) : Float := if x < 0 then x.ceil else x.floor

/-- C11 6.3.1.4p1: the fractional part is discarded, and the conversion is
undefined when the integral part does not fit, which includes NaN and the
infinities. -/
def toS (w : Nat) (x : Float) : Except Err (SInt w) :=
  let t := trunc x
  if w > 64 then throw (.unsupported "floating conversion to an integer wider than 64 bits")
  else if x.isNaN ∨ ¬(t ≥ -(Float.ofScientific 1 false 0).scaleB (w - 1)
      ∧ t < (Float.ofScientific 1 false 0).scaleB (w - 1)) then
    throw (.ub s!"floating value does not fit in a signed {w}-bit integer")
  else pure (SInt.ofInt w t.toInt64.toInt)

def toU (w : Nat) (x : Float) : Except Err (UInt w) :=
  let t := trunc x
  if w > 64 then throw (.unsupported "floating conversion to an integer wider than 64 bits")
  else if x.isNaN ∨ ¬(t ≥ 0 ∧ t < (Float.ofScientific 1 false 0).scaleB w) then
    throw (.ub s!"floating value does not fit in an unsigned {w}-bit integer")
  else pure (UInt.ofNat w t.toUInt64.toNat)

def ofS {w : Nat} (a : SInt w) : Except Err Float :=
  if w > 64 then throw (.unsupported "conversion of an integer wider than 64 bits to floating")
  else pure (Int64.ofInt a.toInt).toFloat

def ofU {w : Nat} (a : UInt w) : Except Err Float :=
  if w > 64 then throw (.unsupported "conversion of an integer wider than 64 bits to floating")
  else pure (UInt64.ofNat a.toNat).toFloat

end F64

namespace F32

def toS (w : Nat) (x : Float32) : Except Err (SInt w) := F64.toS w x.toFloat
def toU (w : Nat) (x : Float32) : Except Err (UInt w) := F64.toU w x.toFloat

def ofS {w : Nat} (a : SInt w) : Except Err Float32 :=
  if w > 64 then throw (.unsupported "conversion of an integer wider than 64 bits to floating")
  else pure (Int64.ofInt a.toInt).toFloat32

def ofU {w : Nat} (a : UInt w) : Except Err Float32 :=
  if w > 64 then throw (.unsupported "conversion of an integer wider than 64 bits to floating")
  else pure (UInt64.ofNat a.toNat).toFloat32

end F32

end Achates
