import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_c.Part2
import Misc.Misc.Bstr_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Bstr_h

/-- C function `bstr_eatstart0`, ../.mpv/misc/bstr.h:290.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_eatstart0 (fuel : Nat) (s : Ptr) (v_prefix : Ptr) : M Bool := do
  let mut s_v : Ptr := s
  let mut v_prefix_v : Ptr := v_prefix
  let t1 : Agg ← Misc.Bstr_h.bstr0 fuel v_prefix_v
  let t2 : Bool ← Misc.Bstr_c.bstr_eatstart fuel s_v t1
  return t2

/-- C function `bstr_find0`, ../.mpv/misc/bstr.h:285.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_find0 (fuel : Nat) (haystack : Agg) (needle : Ptr) : M I32 := do
  let haystack_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg haystack_p haystack 8
    let mut needle_v : Ptr := needle
    let t1 : Agg ← Mem.loadAgg haystack_p 16 8
    let t2 : Agg ← Misc.Bstr_h.bstr0 fuel needle_v
    let t3 : I32 ← Misc.Bstr_c.bstr_find fuel t1 t2
    return t3
    : M I32)
  Mem.popFrame [haystack_p]
  pure result

end Misc.Misc.Bstr_h
