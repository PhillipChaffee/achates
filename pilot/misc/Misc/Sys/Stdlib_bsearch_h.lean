import Achates
import Misc.Statics
import Misc.Externals

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Sys.Stdlib_bsearch_h

/-- C function `bsearch`, /usr/include/x86_64-linux-gnu/bits/stdlib-bsearch.h:20.
-/
def bsearch [Ext.Misc_Language_c_lang_compare] (fuel : Nat) (v___key : Ptr) (v___base : Ptr) (v___nmemb : U64) (v___size : U64) (v___compar : Ptr) : M Ptr := do
  let v___l_1 ← Mem.alloca 8 8
  let v___u_2 ← Mem.alloca 8 8
  let v___idx_3 ← Mem.alloca 8 8
  let v___p_4 ← Mem.alloca 8 8
  let v___comparison_5 ← Mem.alloca 4 4
  let result : Ptr ← (do
    let mut v___key_v : Ptr := v___key
    let mut v___base_v : Ptr := v___base
    let mut v___nmemb_v : U64 := v___nmemb
    let mut v___size_v : U64 := v___size
    let mut v___compar_v : Ptr := v___compar
    Mem.undefine v___l_1 8
    Mem.undefine v___u_2 8
    Mem.undefine v___idx_3 8
    Mem.undefine v___p_4 8
    Mem.undefine v___comparison_5 4
    let t1 : U64 := (SInt.toU 64 (0 : I32))
    Mem.store v___l_1 t1
    Mem.store v___u_2 v___nmemb_v
    for _ in Fuel.mk fuel do
      let t2 : U64 ← Mem.load U64 v___l_1
      let t3 : U64 ← Mem.load U64 v___u_2
      if !(decide (t2 < t3)) then break
      let t4 : U64 ← Mem.load U64 v___l_1
      let t5 : U64 ← Mem.load U64 v___u_2
      let t6 : U64 ← UInt.div (t4 + t5) (SInt.toU 64 (2 : I32))
      Mem.store v___idx_3 t6
      let t7 : U64 ← Mem.load U64 v___idx_3
      let t8 : Ptr ← Ptr.add v___base_v 1 (UInt.toInt (t7 * v___size_v))
      Mem.store v___p_4 t8
      let t9 : Ptr ← Mem.load Ptr v___p_4
      let t10 : I32 ← (match v___compar_v with
        | Ptr.fn "Misc.Language_c.lang_compare" => Ext.Misc_Language_c_lang_compare.call v___key_v t9
        | Ptr.null => ub "call through a null pointer"
        | _ => unsupported "call through a pointer to a function the selection does not know with this type")
      Mem.store v___comparison_5 t10
      let t11 : I32 ← Mem.load I32 v___comparison_5
      if (decide (t11 < (0 : I32))) then
        let t12 : U64 ← Mem.load U64 v___idx_3
        Mem.store v___u_2 t12
      else
        let t13 : I32 ← Mem.load I32 v___comparison_5
        if (decide (t13 > (0 : I32))) then
          let t14 : U64 ← Mem.load U64 v___idx_3
          let t15 : U64 := (t14 + (SInt.toU 64 (1 : I32)))
          Mem.store v___l_1 t15
        else
          let t16 : Ptr ← Mem.load Ptr v___p_4
          return t16
    return Ptr.null
    : M Ptr)
  Mem.popFrame [v___l_1, v___u_2, v___idx_3, v___p_4, v___comparison_5]
  pure result

end Misc.Sys.Stdlib_bsearch_h
