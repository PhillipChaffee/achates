import Achates
import Misc.Statics
import Misc.Externals

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Bstr_h

/-- C function `bstr0`, ../.mpv/misc/bstr.h:61.
-/
def bstr0 (fuel : Nat) (s : Ptr) : M Agg := do
  let cl1 ← Mem.alloca 16 8
  let result : Agg ← (do
    let mut s_v : Ptr := s
    Mem.undefine cl1 16
    Mem.store cl1 s_v
    let mut t3 : U64 := default
    if (s_v != Ptr.null) then
      let t2 : U64 ← Libc.strlen s_v
      t3 := t2
    else
      t3 := (SInt.toU 64 (0 : I32))
    let t4 : Ptr ← Ptr.add cl1 1 8
    Mem.store t4 t3
    let t5 : Agg ← Mem.loadAgg cl1 16 8
    return t5
    : M Agg)
  Mem.popFrame [cl1]
  pure result

/-- C function `bstr_cut`, ../.mpv/misc/bstr.h:226.
-/
def bstr_cut (fuel : Nat) (str : Agg) (n : I32) : M Agg := do
  let str_p ← Mem.alloca 16 8
  let cl10 ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg str_p str 8
    let mut n_v : I32 := n
    if (decide (n_v < (0 : I32))) then
      let t1 : Ptr ← Ptr.add str_p 1 8
      let t2 : U64 ← Mem.load U64 t1
      let t3 : I32 := (UInt.toS 32 ((SInt.toU 64 n_v) + t2))
      n_v := t3
      if (decide (n_v < (0 : I32))) then
        let t4 : I32 := (0 : I32)
        n_v := t4
    let t5 : Ptr ← Ptr.add str_p 1 8
    let t6 : U64 ← Mem.load U64 t5
    if (decide ((SInt.toU 64 n_v) > t6)) then
      let t7 : Ptr ← Ptr.add str_p 1 8
      let t8 : U64 ← Mem.load U64 t7
      let t9 : I32 := (UInt.toS 32 t8)
      n_v := t9
    Mem.undefine cl10 16
    let t11 : Ptr ← Mem.load Ptr str_p
    let t12 : Ptr ← Ptr.add t11 1 (SInt.toInt n_v)
    Mem.store cl10 t12
    let t13 : Ptr ← Ptr.add str_p 1 8
    let t14 : U64 ← Mem.load U64 t13
    let t15 : Ptr ← Ptr.add cl10 1 8
    Mem.store t15 (t14 - (SInt.toU 64 n_v))
    let t16 : Agg ← Mem.loadAgg cl10 16 8
    return t16
    : M Agg)
  Mem.popFrame [str_p, cl10]
  pure result

/-- C function `bstr_endswith`, ../.mpv/misc/bstr.h:250.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_endswith (fuel : Nat) (str : Agg) (suffix : Agg) : M Bool := do
  let str_p ← Mem.alloca 16 8
  let suffix_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg str_p str 8
    Mem.storeAgg suffix_p suffix 8
    let t1 : Ptr ← Ptr.add str_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    let t3 : Ptr ← Ptr.add suffix_p 1 8
    let t4 : U64 ← Mem.load U64 t3
    if (decide (t2 < t4)) then
      return ((0 : I32) != 0)
    let t5 : Ptr ← Mem.load Ptr str_p
    let t6 : Ptr ← Ptr.add str_p 1 8
    let t7 : U64 ← Mem.load U64 t6
    let t8 : Ptr ← Ptr.add t5 1 (UInt.toInt t7)
    let t9 : Ptr ← Ptr.add suffix_p 1 8
    let t10 : U64 ← Mem.load U64 t9
    let t11 : Ptr ← Ptr.sub t8 1 (UInt.toInt t10)
    let t12 : Ptr ← Mem.load Ptr suffix_p
    let t13 : Ptr ← Ptr.add suffix_p 1 8
    let t14 : U64 ← Mem.load U64 t13
    let t15 : I32 ← Libc.memcmp t11 t12 t14
    return ((SInt.ofBool 32 (!(t15 != 0))) != 0)
    : M Bool)
  Mem.popFrame [str_p, suffix_p]
  pure result

/-- C function `bstr_endswith0`, ../.mpv/misc/bstr.h:257.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_endswith0 (fuel : Nat) (str : Agg) (suffix : Ptr) : M Bool := do
  let str_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg str_p str 8
    let mut suffix_v : Ptr := suffix
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : Agg ← Misc.Bstr_h.bstr0 fuel suffix_v
    let t3 : Bool ← Misc.Bstr_h.bstr_endswith fuel t1 t2
    return t3
    : M Bool)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_startswith`, ../.mpv/misc/bstr.h:238.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_startswith (fuel : Nat) (str : Agg) (v_prefix : Agg) : M Bool := do
  let str_p ← Mem.alloca 16 8
  let v_prefix_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg str_p str 8
    Mem.storeAgg v_prefix_p v_prefix 8
    let t1 : Ptr ← Ptr.add str_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    let t3 : Ptr ← Ptr.add v_prefix_p 1 8
    let t4 : U64 ← Mem.load U64 t3
    if (decide (t2 < t4)) then
      return ((0 : I32) != 0)
    let t5 : Ptr ← Mem.load Ptr str_p
    let t6 : Ptr ← Mem.load Ptr v_prefix_p
    let t7 : Ptr ← Ptr.add v_prefix_p 1 8
    let t8 : U64 ← Mem.load U64 t7
    let t9 : I32 ← Libc.memcmp t5 t6 t8
    return ((SInt.ofBool 32 (!(t9 != 0))) != 0)
    : M Bool)
  Mem.popFrame [str_p, v_prefix_p]
  pure result

/-- C function `bstrdup0`, ../.mpv/misc/bstr.h:39.
-/
def bstrdup0 [Ext.ta_xstrndup] (fuel : Nat) (talloc_ctx : Ptr) (str : Agg) : M Ptr := do
  let str_p ← Mem.alloca 16 8
  let result : Ptr ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    Mem.storeAgg str_p str 8
    let t1 : Ptr ← Mem.load Ptr str_p
    let t2 : Ptr ← Ptr.add str_p 1 8
    let t3 : U64 ← Mem.load U64 t2
    let t4 : Ptr ← Ext.ta_xstrndup.call talloc_ctx_v t1 t3
    return t4
    : M Ptr)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_startswith0`, ../.mpv/misc/bstr.h:245.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_startswith0 (fuel : Nat) (str : Agg) (v_prefix : Ptr) : M Bool := do
  let str_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg str_p str 8
    let mut v_prefix_v : Ptr := v_prefix
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : Agg ← Misc.Bstr_h.bstr0 fuel v_prefix_v
    let t3 : Bool ← Misc.Bstr_h.bstr_startswith fuel t1 t2
    return t3
    : M Bool)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstrto0`, ../.mpv/misc/bstr.h:45.
-/
def bstrto0 [Ext.ta_xstrdup] [Ext.ta_xstrndup] (fuel : Nat) (talloc_ctx : Ptr) (str : Agg) : M Ptr := do
  let str_p ← Mem.alloca 16 8
  let result : Ptr ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    Mem.storeAgg str_p str 8
    let t1 : Ptr ← Mem.load Ptr str_p
    let mut t5 : Ptr := default
    if (t1 != Ptr.null) then
      let t2 : Agg ← Mem.loadAgg str_p 16 8
      let t3 : Ptr ← Misc.Bstr_h.bstrdup0 fuel talloc_ctx_v t2
      t5 := t3
    else
      let t4 : Ptr ← Ext.ta_xstrdup.call talloc_ctx_v Statics.str_97
      t5 := t4
    return t5
    : M Ptr)
  Mem.popFrame [str_p]
  pure result

end Misc.Misc.Bstr_h
