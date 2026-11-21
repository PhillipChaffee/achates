import Achates
import Misc.Statics
import Misc.Externals

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Ctype_h

/-- C function `mp_isspace`, ../.mpv/misc/ctype.h:8.
-/
def mp_isspace (fuel : Nat) (c : I8) : M I32 := do
  let mut c_v : I8 := c
  return (SInt.ofBool 32 (((((((SInt.toS 32 c_v) == (32 : I32)) || ((SInt.toS 32 c_v) == (12 : I32))) || ((SInt.toS 32 c_v) == (10 : I32))) || ((SInt.toS 32 c_v) == (13 : I32))) || ((SInt.toS 32 c_v) == (9 : I32))) || ((SInt.toS 32 c_v) == (11 : I32))))

/-- C function `mp_isupper`, ../.mpv/misc/ctype.h:10.
-/
def mp_isupper (fuel : Nat) (c : I8) : M I32 := do
  let mut c_v : I8 := c
  return (SInt.ofBool 32 ((decide ((SInt.toS 32 c_v) ≥ (65 : I32))) && (decide ((SInt.toS 32 c_v) ≤ (90 : I32)))))

/-- C function `mp_tolower`, ../.mpv/misc/ctype.h:16.
-/
def mp_tolower (fuel : Nat) (c : I8) : M I8 := do
  let mut c_v : I8 := c
  let t1 : I32 ← Misc.Ctype_h.mp_isupper fuel c_v
  let mut t4 : I32 := default
  if (t1 != 0) then
    let t2 : I32 ← SInt.sub (SInt.toS 32 c_v) (65 : I32)
    let t3 : I32 ← SInt.add t2 (97 : I32)
    t4 := t3
  else
    t4 := (SInt.toS 32 c_v)
  return (SInt.toS 8 t4)

/-- C function `mp_islower`, ../.mpv/misc/ctype.h:11.
-/
def mp_islower (fuel : Nat) (c : I8) : M I32 := do
  let mut c_v : I8 := c
  return (SInt.ofBool 32 ((decide ((SInt.toS 32 c_v) ≥ (97 : I32))) && (decide ((SInt.toS 32 c_v) ≤ (122 : I32)))))

/-- C function `mp_isalpha`, ../.mpv/misc/ctype.h:13.
-/
def mp_isalpha (fuel : Nat) (c : I8) : M I32 := do
  let mut c_v : I8 := c
  let t1 : I32 ← Misc.Ctype_h.mp_isupper fuel c_v
  let mut t3 : Bool := true
  if !(t1 != 0) then
    let t2 : I32 ← Misc.Ctype_h.mp_islower fuel c_v
    t3 := (t2 != 0)
  return (SInt.ofBool 32 t3)

/-- C function `mp_isdigit`, ../.mpv/misc/ctype.h:12.
-/
def mp_isdigit (fuel : Nat) (c : I8) : M I32 := do
  let mut c_v : I8 := c
  return (SInt.ofBool 32 ((decide ((SInt.toS 32 c_v) ≥ (48 : I32))) && (decide ((SInt.toS 32 c_v) ≤ (57 : I32)))))

/-- C function `mp_isalnum`, ../.mpv/misc/ctype.h:14.
-/
def mp_isalnum (fuel : Nat) (c : I8) : M I32 := do
  let mut c_v : I8 := c
  let t1 : I32 ← Misc.Ctype_h.mp_isalpha fuel c_v
  let mut t3 : Bool := true
  if !(t1 != 0) then
    let t2 : I32 ← Misc.Ctype_h.mp_isdigit fuel c_v
    t3 := (t2 != 0)
  return (SInt.ofBool 32 t3)

end Misc.Misc.Ctype_h
