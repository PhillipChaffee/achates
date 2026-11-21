import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_c
import Misc.Misc.Bstr_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Bstr_h

/-- C function `bstrcasecmp0`, ../.mpv/misc/bstr.h:280.
-/
def bstrcasecmp0 [Ext.strncasecmp] (fuel : Nat) (str1 : Agg) (str2 : Ptr) : M I32 := do
  let str1_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg str1_p str1 8
    let mut str2_v : Ptr := str2
    let t1 : Agg ← Mem.loadAgg str1_p 16 8
    let t2 : Agg ← Misc.Bstr_h.bstr0 fuel str2_v
    let t3 : I32 ← Misc.Bstr_c.bstrcasecmp fuel t1 t2
    return t3
    : M I32)
  Mem.popFrame [str1_p]
  pure result

/-- C function `bstrcmp0`, ../.mpv/misc/bstr.h:262.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstrcmp0 (fuel : Nat) (str1 : Agg) (str2 : Ptr) : M I32 := do
  let str1_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg str1_p str1 8
    let mut str2_v : Ptr := str2
    let t1 : Agg ← Mem.loadAgg str1_p 16 8
    let t2 : Agg ← Misc.Bstr_h.bstr0 fuel str2_v
    let t3 : I32 ← Misc.Bstr_c.bstrcmp fuel t1 t2
    return t3
    : M I32)
  Mem.popFrame [str1_p]
  pure result

/-- C function `bstr_equals`, ../.mpv/misc/bstr.h:267.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_equals (fuel : Nat) (str1 : Agg) (str2 : Agg) : M Bool := do
  let str1_p ← Mem.alloca 16 8
  let str2_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg str1_p str1 8
    Mem.storeAgg str2_p str2 8
    let t1 : Ptr ← Ptr.add str1_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    let t3 : Ptr ← Ptr.add str2_p 1 8
    let t4 : U64 ← Mem.load U64 t3
    if (t2 != t4) then
      return ((0 : I32) != 0)
    let t5 : Ptr ← Mem.load Ptr str1_p
    let t6 : Ptr ← Mem.load Ptr str2_p
    let t7 : Bool ← Ptr.eq t5 t6
    let mut t11 : Bool := true
    if !t7 then
      let t8 : Agg ← Mem.loadAgg str1_p 16 8
      let t9 : Agg ← Mem.loadAgg str2_p 16 8
      let t10 : I32 ← Misc.Bstr_c.bstrcmp fuel t8 t9
      t11 := (t10 == (0 : I32))
    return ((SInt.ofBool 32 t11) != 0)
    : M Bool)
  Mem.popFrame [str1_p, str2_p]
  pure result

/-- C function `bstr_equals0`, ../.mpv/misc/bstr.h:275.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_equals0 (fuel : Nat) (str1 : Agg) (str2 : Ptr) : M Bool := do
  let str1_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg str1_p str1 8
    let mut str2_v : Ptr := str2
    let t1 : Agg ← Mem.loadAgg str1_p 16 8
    let t2 : Agg ← Misc.Bstr_h.bstr0 fuel str2_v
    let t3 : Bool ← Misc.Bstr_h.bstr_equals fuel t1 t2
    return t3
    : M Bool)
  Mem.popFrame [str1_p]
  pure result

end Misc.Misc.Bstr_h
