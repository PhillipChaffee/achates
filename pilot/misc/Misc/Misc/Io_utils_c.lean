import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Random_c
import Misc.Ta.Ta_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Io_utils_c

/-- C function `mp_mkostemps`, ../.mpv/misc/io_utils.c:34.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def mp_mkostemps [Ext.«__errno_location»] [Ext.av_random_bytes] [Ext.mp_raw_time_ns] [Ext.mp_tprintf_buf] [Ext.«open»] (fuel : Nat) (template : Ptr) (suffixlen : I32) (flags : I32) : M I32 := do
  let s_3 ← Mem.alloca 32 8
  let crap_6 ← Mem.alloca 7 1
  let result : I32 ← (do
    let mut template_v : Ptr := template
    let mut suffixlen_v : I32 := suffixlen
    let mut flags_v : I32 := flags
    let t1 : U64 ← Libc.strlen template_v
    let mut len_1 : U64 := t1
    let t2 : I32 ← SInt.add (6 : I32) suffixlen_v
    let mut t5 : Ptr := default
    if (decide (len_1 ≥ (SInt.toU 64 t2))) then
      let t3 : I32 ← SInt.add (6 : I32) suffixlen_v
      let t4 : Ptr ← Ptr.add template_v 1 (UInt.toInt (len_1 - (SInt.toU 64 t3)))
      t5 := t4
    else
      t5 := Ptr.null
    let mut t_2 : Ptr := t5
    let mut t7 : Bool := true
    if !(!(t_2 != Ptr.null)) then
      let t6 : I32 ← Libc.strncmp t_2 Statics.str_74 (SInt.toU 64 (6 : I32))
      t7 := (t6 != (0 : I32))
    if t7 then
      let t8 : Ptr ← Ext.«__errno_location».call
      let t9 : I32 := (22 : I32)
      Mem.store t8 t9
      return (SInt.ofInt 32 (-1))
    let t10 : Agg ← Misc.Random_c.mp_rand_seed fuel (SInt.toU 64 (0 : I32))
    Mem.storeAgg s_3 t10 8
    let mut fuckshit_4 : U64 := (SInt.toU 64 (0 : I32))
    for _ in Fuel.mk fuel do
      if !(decide (fuckshit_4 < (UInt.toU 64 (4294967295 : U32)))) then break
      for _ in Once.mk do
        let t11 : U64 ← Misc.Random_c.mp_rand_next fuel s_3
        let mut fuckmess_5 : U64 := t11
        Mem.zero crap_6 7
        let t12 : Ptr ← Ext.mp_tprintf_buf.call crap_6 (7 : U64) Statics.str_75 [(VArg.uint fuckmess_5)]
        let t13 : Ptr ← Libc.memcpy t_2 crap_6 (SInt.toU 64 (6 : I32))
        let t14 : I32 ← Ext.«open».call template_v (SInt.bor (SInt.bor (SInt.bor (2 : I32) (64 : I32)) (128 : I32)) flags_v) [(VArg.sint (384 : I32))]
        let mut res_7 : I32 := t14
        let mut t17 : Bool := true
        if !(decide (res_7 ≥ (0 : I32))) then
          let t15 : Ptr ← Ext.«__errno_location».call
          let t16 : I32 ← Mem.load I32 t15
          t17 := (t16 != (17 : I32))
        if t17 then
          return res_7
      let t18 : U64 := fuckshit_4
      let t19 : U64 := (t18 + 1)
      fuckshit_4 := t19
    let t20 : Ptr ← Ext.«__errno_location».call
    let t21 : I32 := (17 : I32)
    Mem.store t20 t21
    return (SInt.ofInt 32 (-1))
    : M I32)
  Mem.popFrame [s_3, crap_6]
  pure result

/-- C function `mp_save_to_file`, ../.mpv/misc/io_utils.c:61.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_save_to_file [Ext.«__errno_location»] [Ext.av_random_bytes] [Ext.close] [Ext.fclose] [Ext.fdopen] [Ext.fwrite] [Ext.mp_raw_time_ns] [Ext.mp_tprintf_buf] [Ext.«open»] [Ext.rename] [Ext.ta_asprintf] [Ext.unlink] (fuel : Nat) (filepath : Ptr) (data : Ptr) (size : U64) : M Bool := do
  let v_result_1 ← Mem.alloca 1 1
  let tmp_2 ← Mem.alloca 8 8
  let fd_3 ← Mem.alloca 4 4
  let fs_4 ← Mem.alloca 8 8
  let written_5 ← Mem.alloca 8 8
  let ret_6 ← Mem.alloca 4 4
  let result : Bool ← (do
    let mut filepath_v : Ptr := filepath
    let mut data_v : Ptr := data
    let mut size_v : U64 := size
    for _ in Once.mk do
      let mut t1 : Unit := default
      if (filepath_v != Ptr.null) then
        t1 := ()
      else
        Libc.«__assert_fail» Statics.str_76 Statics.str_77 (SInt.toU 32 (63 : I32)) Statics.str_78
        t1 := ()
      Mem.store v_result_1 ((0 : I32) != 0)
      let t2 : Ptr ← Ext.ta_asprintf.call Ptr.null Statics.str_79 [(VArg.ptr filepath_v)]
      let t3 : Ptr ← Ta.Ta_h.ta_oom_s fuel t2
      Mem.store tmp_2 t3
      let t4 : Ptr ← Mem.load Ptr tmp_2
      let t5 : I32 ← Misc.Io_utils_c.mp_mkostemps fuel t4 (0 : I32) (524288 : I32)
      Mem.store fd_3 t5
      let t6 : I32 ← Mem.load I32 fd_3
      if (decide (t6 < (0 : I32))) then
        break
      let t7 : I32 ← Mem.load I32 fd_3
      let t8 : Ptr ← Ext.fdopen.call t7 Statics.str_80
      Mem.store fs_4 t8
      let t9 : Ptr ← Mem.load Ptr fs_4
      if (!(t9 != Ptr.null)) then
        let t10 : I32 ← Mem.load I32 fd_3
        let t11 : I32 ← Ext.close.call t10
        let t12 : Ptr ← Mem.load Ptr tmp_2
        let t13 : I32 ← Ext.unlink.call t12
        break
      let mut t16 : U64 := default
      if ((data_v != Ptr.null) && (size_v != 0)) then
        let t14 : Ptr ← Mem.load Ptr fs_4
        let t15 : U64 ← Ext.fwrite.call data_v size_v (SInt.toU 64 (1 : I32)) t14
        t16 := t15
      else
        t16 := (SInt.toU 64 (1 : I32))
      Mem.store written_5 t16
      let t17 : Ptr ← Mem.load Ptr fs_4
      let t18 : I32 ← Ext.fclose.call t17
      Mem.store ret_6 t18
      let t19 : U64 ← Mem.load U64 written_5
      let mut t21 : Bool := false
      if (decide (t19 > (SInt.toU 64 (0 : I32)))) then
        let t20 : I32 ← Mem.load I32 ret_6
        t21 := (!(t20 != 0))
      if t21 then
        let t22 : Ptr ← Mem.load Ptr tmp_2
        let t23 : I32 ← Ext.rename.call t22 filepath_v
        Mem.store ret_6 t23
        let t24 : I32 ← Mem.load I32 ret_6
        let t25 : Bool := ((SInt.ofBool 32 (!(t24 != 0))) != 0)
        Mem.store v_result_1 t25
      else
        let t26 : Ptr ← Mem.load Ptr tmp_2
        let t27 : I32 ← Ext.unlink.call t26
        pure ()
    let t28 : Ptr ← Mem.load Ptr tmp_2
    Talloc.ta_free t28
    let t29 : Bool ← Mem.load Bool v_result_1
    return t29
    : M Bool)
  Mem.popFrame [v_result_1, tmp_2, fd_3, fs_4, written_5, ret_6]
  pure result

end Misc.Misc.Io_utils_c
