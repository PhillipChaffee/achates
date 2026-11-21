import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_h.Part2

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Bstr_c

/-- C function `bstr_find_in_list0`, ../.mpv/misc/bstr.c:464.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_find_in_list0 [Ext.strncasecmp] (fuel : Nat) (str : Agg) (list : Ptr) (case_sensitive : Bool) : M I32 := do
  let str_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg str_p str 8
    let mut list_v : Ptr := list
    let mut case_sensitive_v : Bool := case_sensitive
    let mut n_1 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      let mut t3 : Bool := false
      if (list_v != Ptr.null) then
        let t1 : Ptr ← Ptr.add list_v 8 (SInt.toInt n_1)
        let t2 : Ptr ← Mem.load Ptr t1
        t3 := (t2 != Ptr.null)
      if !t3 then break
      for _ in Once.mk do
        let mut t12 : I32 := default
        if ((SInt.ofBool 32 case_sensitive_v) != 0) then
          let t4 : Agg ← Mem.loadAgg str_p 16 8
          let t5 : Ptr ← Ptr.add list_v 8 (SInt.toInt n_1)
          let t6 : Ptr ← Mem.load Ptr t5
          let t7 : I32 ← Misc.Bstr_h.bstrcmp0 fuel t4 t6
          t12 := (SInt.ofBool 32 (!(t7 != 0)))
        else
          let t8 : Agg ← Mem.loadAgg str_p 16 8
          let t9 : Ptr ← Ptr.add list_v 8 (SInt.toInt n_1)
          let t10 : Ptr ← Mem.load Ptr t9
          let t11 : I32 ← Misc.Bstr_h.bstrcasecmp0 fuel t8 t10
          t12 := (SInt.ofBool 32 (!(t11 != 0)))
        if (t12 != 0) then
          return n_1
      let t13 : I32 := n_1
      let t14 : I32 ← SInt.add t13 1
      n_1 := t14
    return (SInt.ofInt 32 (-1))
    : M I32)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_in_list0`, ../.mpv/misc/bstr.c:473.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_in_list0 [Ext.strncasecmp] (fuel : Nat) (str : Agg) (list : Ptr) : M Bool := do
  let str_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg str_p str 8
    let mut list_v : Ptr := list
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : I32 ← Misc.Bstr_c.bstr_find_in_list0 fuel t1 list_v ((0 : I32) != 0)
    return ((SInt.ofBool 32 (t2 != (SInt.ofInt 32 (-1)))) != 0)
    : M Bool)
  Mem.popFrame [str_p]
  pure result

end Misc.Misc.Bstr_c
