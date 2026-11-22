import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_c

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Hash_c

/-- C function `mp_hash_to_bstr`, ../.mpv/misc/hash.c:25.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_hash_to_bstr [Ext.av_hash_alloc] [Ext.av_hash_final] [Ext.av_hash_freep] [Ext.av_hash_get_size] [Ext.av_hash_init] [Ext.av_hash_update] [Ext.vsnprintf] (fuel : Nat) (talloc_ctx : Ptr) (data : Ptr) (len : U64) (algorithm : Ptr) : M Agg := do
  let ctx_1 ← Mem.alloca 8 8
  let hash_3 ← Mem.alloca 64 1
  let ret_4 ← Mem.alloca 16 8
  let result : Agg ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    let mut data_v : Ptr := data
    let mut len_v : U64 := len
    let mut algorithm_v : Ptr := algorithm
    Mem.store ctx_1 Ptr.null
    let t1 : I32 ← Ext.av_hash_alloc.call ctx_1 algorithm_v
    let mut t2 : Unit := default
    if (t1 == (0 : I32)) then
      t2 := ()
    else
      Libc.«__assert_fail» Statics.str_70 Statics.str_71 (SInt.toU 32 (28 : I32)) Statics.str_72
      t2 := ()
    let t3 : Ptr ← Mem.load Ptr ctx_1
    let t4 : I32 ← Ext.av_hash_get_size.call t3
    let mut size_2 : I32 := t4
    Mem.storeList hash_3 [(SInt.toU 8 (0 : I32))]
    let t5 : Ptr ← Ptr.add hash_3 1 1
    Mem.zero t5 63
    let t6 : Ptr ← Mem.load Ptr ctx_1
    Ext.av_hash_init.call t6
    let t7 : Ptr ← Mem.load Ptr ctx_1
    Ext.av_hash_update.call t7 data_v len_v
    let t8 : Ptr ← Mem.load Ptr ctx_1
    Ext.av_hash_final.call t8 hash_3
    Ext.av_hash_freep.call ctx_1
    Mem.store ret_4 Ptr.null
    let t9 : Ptr ← Ptr.add ret_4 1 8
    Mem.zero t9 8
    let mut n_5 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      if !(decide (n_5 < size_2)) then break
      for _ in Once.mk do
        let t10 : Ptr ← Ptr.add hash_3 1 (SInt.toInt n_5)
        let t11 : U8 ← Mem.load U8 t10
        let t12 : I32 ← Misc.Bstr_c.bstr_xappend_asprintf fuel talloc_ctx_v ret_4 Statics.str_73 [(VArg.sint "int" (UInt.toS 32 t11))]
        pure ()
      let t13 : I32 := n_5
      let t14 : I32 ← SInt.add t13 1
      n_5 := t14
    let t15 : Agg ← Mem.loadAgg ret_4 16 8
    return t15
    : M Agg)
  Mem.popFrame [ctx_1, hash_3, ret_4]
  pure result

end Misc.Misc.Hash_c
