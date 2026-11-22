import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_c
import Misc.Misc.Bstr_c.Part2
import Misc.Misc.Bstr_h
import Misc.Misc.Bstr_h.Part3
import Misc.Misc.Ctype_h
import Misc.Ta.Ta_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Path_utils_c

/-- C function `mp_basename_bstr`, ../.mpv/misc/path_utils.c:42.
-/
def mp_basename_bstr [Ext.memrchr] (fuel : Nat) (path : Agg) : M Agg := do
  let path_p ← Mem.alloca 16 8
  let separator_pos_1 ← Mem.alloca 4 4
  let result : Agg ← (do
    Mem.storeAgg path_p path 8
    Mem.undefine separator_pos_1 4
    let t1 : Agg ← Mem.loadAgg path_p 16 8
    let t2 : I32 ← Misc.Bstr_c.bstrrchr fuel t1 (47 : I32)
    Mem.store separator_pos_1 t2
    let t3 : I32 ← Mem.load I32 separator_pos_1
    if (decide (t3 < (0 : I32))) then
      let t4 : Agg ← Mem.loadAgg path_p 16 8
      return t4
    let t5 : Agg ← Mem.loadAgg path_p 16 8
    let t6 : I32 ← Mem.load I32 separator_pos_1
    let t7 : I32 ← SInt.add t6 (1 : I32)
    let t8 : Ptr ← Ptr.add path_p 1 8
    let t9 : U64 ← Mem.load U64 t8
    let t10 : Agg ← Misc.Bstr_c.bstr_splice fuel t5 t7 (UInt.toS 32 t9)
    return t10
    : M Agg)
  Mem.popFrame [path_p, separator_pos_1]
  pure result

/-- C function `mp_basename`, ../.mpv/misc/path_utils.c:62.
-/
def mp_basename [Ext.memrchr] (fuel : Nat) (path : Ptr) : M Ptr := do
  let mut path_v : Ptr := path
  let t1 : Agg ← Misc.Bstr_h.bstr0 fuel path_v
  let t2 : Agg ← Misc.Path_utils_c.mp_basename_bstr fuel t1
  let t3 : Ptr ← Agg.get Ptr t2 0
  return t3

/-- C function `mp_dirname`, ../.mpv/misc/path_utils.c:67.
-/
def mp_dirname [Ext.memrchr] (fuel : Nat) (path : Ptr) : M Agg := do
  let ret_1 ← Mem.alloca 16 8
  let result : Agg ← (do
    let mut path_v : Ptr := path
    Mem.store ret_1 path_v
    let t1 : Ptr ← Misc.Path_utils_c.mp_basename fuel path_v
    let t2 : I64 ← Ptr.diff t1 path_v 1
    let t3 : Ptr ← Ptr.add ret_1 1 8
    Mem.store t3 (SInt.toU 64 t2)
    let t4 : Ptr ← Ptr.add ret_1 1 8
    let t5 : U64 ← Mem.load U64 t4
    if (t5 == (SInt.toU 64 (0 : I32))) then
      let t6 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_136
      return t6
    let t7 : Agg ← Mem.loadAgg ret_1 16 8
    return t7
    : M Agg)
  Mem.popFrame [ret_1]
  pure result

/-- C function `mp_path_strip_trailing_separator`, ../.mpv/misc/path_utils.c:85.
-/
def mp_path_strip_trailing_separator (fuel : Nat) (path : Ptr) : M Unit := do
  let mut path_v : Ptr := path
  let t1 : U64 ← Libc.strlen path_v
  let mut len_1 : U64 := t1
  let mut t5 : Bool := false
  if (decide (len_1 > (SInt.toU 64 (0 : I32)))) then
    let t2 : Ptr ← Ptr.add path_v 1 (UInt.toInt (len_1 - (SInt.toU 64 (1 : I32))))
    let t3 : I8 ← Mem.load I8 t2
    let t4 : Ptr ← Libc.strchr Statics.g_Misc_Path_utils_c_mp_path_separators (SInt.toS 32 t3)
    t5 := (t4 != Ptr.null)
  if t5 then
    let t6 : Ptr ← Ptr.add path_v 1 (UInt.toInt (len_1 - (SInt.toU 64 (1 : I32))))
    let t7 : I8 := (SInt.toS 8 (0 : I32))
    Mem.store t6 t7
  pure ()

/-- C function `split_ext`, ../.mpv/misc/path_utils.c:96.
-/
def split_ext [Ext.memrchr] (fuel : Nat) (path : Agg) (root : Ptr) : M Agg := do
  let path_p ← Mem.alloca 16 8
  let basename_1 ← Mem.alloca 16 8
  let ext_3 ← Mem.alloca 16 8
  let cl14 ← Mem.alloca 16 8
  let cl22 ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg path_p path 8
    let mut root_v : Ptr := root
    let t1 : Agg ← Mem.loadAgg path_p 16 8
    let t2 : Agg ← Misc.Path_utils_c.mp_basename_bstr fuel t1
    Mem.storeAgg basename_1 t2 8
    let t3 : Agg ← Mem.loadAgg basename_1 16 8
    let t4 : Agg ← Mem.loadAgg basename_1 16 8
    let t5 : I32 ← Misc.Bstr_c.bstrspn fuel t4 Statics.str_136
    let t6 : Ptr ← Ptr.add basename_1 1 8
    let t7 : U64 ← Mem.load U64 t6
    let t8 : Agg ← Misc.Bstr_c.bstr_splice fuel t3 t5 (UInt.toS 32 t7)
    Mem.storeAgg basename_1 t8 8
    let t9 : Agg ← Mem.loadAgg basename_1 16 8
    let t10 : I32 ← Misc.Bstr_c.bstrrchr fuel t9 (46 : I32)
    let mut dot_pos_2 : I32 := t10
    let mut t13 : Bool := true
    if !(decide (dot_pos_2 < (0 : I32))) then
      let t11 : Ptr ← Ptr.add basename_1 1 8
      let t12 : U64 ← Mem.load U64 t11
      t13 := ((SInt.toU 64 dot_pos_2) == (t12 - (SInt.toU 64 (1 : I32))))
    if t13 then
      Mem.undefine cl14 16
      Mem.store cl14 Ptr.null
      let t15 : Ptr ← Ptr.add cl14 1 8
      Mem.zero t15 8
      let t16 : Agg ← Mem.loadAgg cl14 16 8
      return t16
    let t17 : Agg ← Mem.loadAgg basename_1 16 8
    let t18 : I32 ← SInt.add dot_pos_2 (1 : I32)
    let t19 : Ptr ← Ptr.add basename_1 1 8
    let t20 : U64 ← Mem.load U64 t19
    let t21 : Agg ← Misc.Bstr_c.bstr_splice fuel t17 t18 (UInt.toS 32 t20)
    Mem.storeAgg ext_3 t21 8
    if (root_v != Ptr.null) then
      Mem.undefine cl22 16
      let t23 : Ptr ← Mem.load Ptr path_p
      Mem.store cl22 t23
      let t24 : Ptr ← Mem.load Ptr ext_3
      let t25 : Ptr ← Ptr.sub t24 1 (SInt.toInt (1 : I32))
      let t26 : Ptr ← Mem.load Ptr path_p
      let t27 : I64 ← Ptr.diff t25 t26 1
      let t28 : Ptr ← Ptr.add cl22 1 8
      Mem.store t28 (SInt.toU 64 t27)
      let t29 : Agg ← Mem.loadAgg cl22 16 8
      Mem.storeAgg root_v t29 8
    let t30 : Agg ← Mem.loadAgg ext_3 16 8
    return t30
    : M Agg)
  Mem.popFrame [path_p, basename_1, ext_3, cl14, cl22]
  pure result

/-- C function `mp_strip_ext`, ../.mpv/misc/path_utils.c:113.
-/
def mp_strip_ext [Ext.memrchr] (fuel : Nat) (path : Agg) : M Agg := do
  let path_p ← Mem.alloca 16 8
  let root_1 ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg path_p path 8
    Mem.store root_1 Ptr.null
    let t1 : Ptr ← Ptr.add root_1 1 8
    Mem.zero t1 8
    let t2 : Agg ← Mem.loadAgg path_p 16 8
    let t3 : Agg ← Misc.Path_utils_c.split_ext fuel t2 root_1
    let t4 : Ptr ← Ptr.add root_1 1 8
    let t5 : U64 ← Mem.load U64 t4
    let mut t8 : Agg := default
    if (t5 != 0) then
      let t6 : Agg ← Mem.loadAgg root_1 16 8
      t8 := t6
    else
      let t7 : Agg ← Mem.loadAgg path_p 16 8
      t8 := t7
    return t8
    : M Agg)
  Mem.popFrame [path_p, root_1]
  pure result

/-- C function `mp_get_ext`, ../.mpv/misc/path_utils.c:120.
-/
def mp_get_ext [Ext.memrchr] (fuel : Nat) (path : Agg) : M Agg := do
  let path_p ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg path_p path 8
    let t1 : Agg ← Mem.loadAgg path_p 16 8
    let t2 : Agg ← Misc.Path_utils_c.split_ext fuel t1 Ptr.null
    return t2
    : M Agg)
  Mem.popFrame [path_p]
  pure result

/-- C function `mp_path_is_absolute`, ../.mpv/misc/path_utils.c:125.
-/
def mp_path_is_absolute (fuel : Nat) (path : Agg) : M Bool := do
  let path_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg path_p path 8
    let t1 : Ptr ← Ptr.add path_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    let mut t7 : Bool := false
    if (t2 != 0) then
      let t3 : Ptr ← Mem.load Ptr path_p
      let t4 : Ptr ← Ptr.add t3 1 (SInt.toInt (0 : I32))
      let t5 : U8 ← Mem.load U8 t4
      let t6 : Ptr ← Libc.strchr Statics.g_Misc_Path_utils_c_mp_path_separators (UInt.toS 32 t5)
      t7 := (t6 != Ptr.null)
    if t7 then
      return ((1 : I32) != 0)
    return ((0 : I32) != 0)
    : M Bool)
  Mem.popFrame [path_p]
  pure result

/-- C function `mp_path_join_bstr`, ../.mpv/misc/path_utils.c:142.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_path_join_bstr [Ext.ta_asprintf] (fuel : Nat) (talloc_ctx : Ptr) (p1 : Agg) (p2 : Agg) : M Ptr := do
  let p1_p ← Mem.alloca 16 8
  let p2_p ← Mem.alloca 16 8
  let result : Ptr ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    Mem.storeAgg p1_p p1 8
    Mem.storeAgg p2_p p2 8
    let t1 : Ptr ← Ptr.add p1_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    if (t2 == (SInt.toU 64 (0 : I32))) then
      let t3 : Agg ← Mem.loadAgg p2_p 16 8
      let t4 : Ptr ← Misc.Bstr_h.bstrdup0 fuel talloc_ctx_v t3
      return t4
    let t5 : Ptr ← Ptr.add p2_p 1 8
    let t6 : U64 ← Mem.load U64 t5
    if (t6 == (SInt.toU 64 (0 : I32))) then
      let t7 : Agg ← Mem.loadAgg p1_p 16 8
      let t8 : Ptr ← Misc.Bstr_h.bstrdup0 fuel talloc_ctx_v t7
      return t8
    let t9 : Agg ← Mem.loadAgg p2_p 16 8
    let t10 : Bool ← Misc.Path_utils_c.mp_path_is_absolute fuel t9
    if t10 then
      let t11 : Agg ← Mem.loadAgg p2_p 16 8
      let t12 : Ptr ← Misc.Bstr_h.bstrdup0 fuel talloc_ctx_v t11
      return t12
    let t13 : Ptr ← Mem.load Ptr p1_p
    let t14 : Ptr ← Ptr.add p1_p 1 8
    let t15 : U64 ← Mem.load U64 t14
    let t16 : Ptr ← Ptr.add t13 1 (UInt.toInt (t15 - (SInt.toU 64 (1 : I32))))
    let t17 : U8 ← Mem.load U8 t16
    let t18 : Ptr ← Libc.strchr Statics.g_Misc_Path_utils_c_mp_path_separators (UInt.toS 32 t17)
    let mut have_separator_1 : Bool := (t18 != Ptr.null)
    let t19 : Ptr ← Ptr.add p1_p 1 8
    let t20 : U64 ← Mem.load U64 t19
    let t21 : Ptr ← Mem.load Ptr p1_p
    let mut t23 : Ptr := default
    if (t21 != Ptr.null) then
      let t22 : Ptr ← Mem.load Ptr p1_p
      t23 := t22
    else
      t23 := Statics.str_97
    let t24 : Ptr ← Ptr.add p2_p 1 8
    let t25 : U64 ← Mem.load U64 t24
    let t26 : Ptr ← Mem.load Ptr p2_p
    let mut t28 : Ptr := default
    if (t26 != Ptr.null) then
      let t27 : Ptr ← Mem.load Ptr p2_p
      t28 := t27
    else
      t28 := Statics.str_97
    let t29 : Ptr ← Ext.ta_asprintf.call talloc_ctx_v Statics.str_137 [(VArg.sint "int" (UInt.toS 32 t20)), (VArg.ptr "char" t23), (VArg.ptr "char" (if ((SInt.ofBool 32 have_separator_1) != 0) then Statics.str_97 else Statics.str_138)), (VArg.sint "int" (UInt.toS 32 t25)), (VArg.ptr "char" t28)]
    let t30 : Ptr ← Ta.Ta_h.ta_oom_s fuel t29
    return t30
    : M Ptr)
  Mem.popFrame [p1_p, p2_p]
  pure result

/-- C function `mp_path_join`, ../.mpv/misc/path_utils.c:163.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_path_join [Ext.ta_asprintf] (fuel : Nat) (talloc_ctx : Ptr) (p1 : Ptr) (p2 : Ptr) : M Ptr := do
  let mut talloc_ctx_v : Ptr := talloc_ctx
  let mut p1_v : Ptr := p1
  let mut p2_v : Ptr := p2
  let t1 : Agg ← Misc.Bstr_h.bstr0 fuel p1_v
  let t2 : Agg ← Misc.Bstr_h.bstr0 fuel p2_v
  let t3 : Ptr ← Misc.Path_utils_c.mp_path_join_bstr fuel talloc_ctx_v t1 t2
  return t3

/-- C function `mp_getcwd`, ../.mpv/misc/path_utils.c:168.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_getcwd [Ext.«__errno_location»] [Ext.getcwd] [Ext.getenv] [Ext.stat] (fuel : Nat) (talloc_ctx : Ptr) : M Ptr := do
  let pwd_st_2 ← Mem.alloca 144 8
  let dot_st_3 ← Mem.alloca 144 8
  let result : Ptr ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    let t1 : Ptr ← Ext.getenv.call Statics.str_139
    let mut e_wd_1 : Ptr := t1
    Mem.undefine pwd_st_2 144
    Mem.undefine dot_st_3 144
    let mut t4 : Bool := false
    if (e_wd_1 != Ptr.null) then
      let t2 : Agg ← Misc.Bstr_h.bstr0 fuel e_wd_1
      let t3 : Bool ← Misc.Path_utils_c.mp_path_is_absolute fuel t2
      t4 := ((SInt.ofBool 32 t3) != 0)
    let mut t6 : Bool := false
    if t4 then
      let t5 : I32 ← Ext.stat.call e_wd_1 pwd_st_2
      t6 := (t5 == (0 : I32))
    let mut t8 : Bool := false
    if t6 then
      let t7 : I32 ← Ext.stat.call Statics.str_136 dot_st_3
      t8 := (t7 == (0 : I32))
    let mut t11 : Bool := false
    if t8 then
      let t9 : U64 ← Mem.load U64 pwd_st_2
      let t10 : U64 ← Mem.load U64 dot_st_3
      t11 := (t9 == t10)
    let mut t16 : Bool := false
    if t11 then
      let t12 : Ptr ← Ptr.add pwd_st_2 1 8
      let t13 : U64 ← Mem.load U64 t12
      let t14 : Ptr ← Ptr.add dot_st_3 1 8
      let t15 : U64 ← Mem.load U64 t14
      t16 := (t13 == t15)
    if t16 then
      let t17 : Ptr ← Talloc.ta_xstrdup talloc_ctx_v e_wd_1
      return t17
    let t18 : U64 ← Talloc.ta_calc_array_size (1 : U64) (SInt.toU 64 (20 : I32))
    let t19 : Ptr ← Talloc.ta_alloc_size talloc_ctx_v t18
    let t20 : Ptr ← Talloc.ta_dbg_set_loc t19 Statics.str_140
    let t21 : Ptr ← Ta.Ta_h.ta_oom_p fuel t20
    let mut wd_4 : Ptr := t21
    for _ in Fuel.mk fuel do
      let t22 : U64 ← Talloc.ta_get_size wd_4
      let t23 : Ptr ← Ext.getcwd.call wd_4 t22
      let t24 : Bool ← Ptr.eq t23 Ptr.null
      if !t24 then break
      let t25 : Ptr ← Ext.«__errno_location».call
      let t26 : I32 ← Mem.load I32 t25
      if (t26 != (34 : I32)) then
        Talloc.ta_free wd_4
        return Ptr.null
      let t27 : U64 ← Talloc.ta_get_size wd_4
      let t28 : U64 ← Talloc.ta_calc_array_size (1 : U64) (t27 * (SInt.toU 64 (2 : I32)))
      let t29 : Ptr ← Talloc.ta_xrealloc_size talloc_ctx_v wd_4 t28
      let t30 : Ptr ← Talloc.ta_dbg_set_loc t29 Statics.str_141
      wd_4 := t30
    return wd_4
    : M Ptr)
  Mem.popFrame [pwd_st_2, dot_st_3]
  pure result

/-- C function `mp_is_url`, ../.mpv/misc/path_utils.c:289.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def mp_is_url (fuel : Nat) (path : Agg) : M Bool := do
  let path_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg path_p path 8
    let t1 : Agg ← Mem.loadAgg path_p 16 8
    let t2 : I32 ← Misc.Bstr_h.bstr_find0 fuel t1 Statics.str_142
    let mut proto_1 : I32 := t2
    if (decide (proto_1 < (1 : I32))) then
      return ((0 : I32) != 0)
    let mut i_2 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      if !(decide (i_2 < proto_1)) then break
      for _ in Once.mk do
        let t3 : Ptr ← Mem.load Ptr path_p
        let t4 : Ptr ← Ptr.add t3 1 (SInt.toInt i_2)
        let t5 : U8 ← Mem.load U8 t4
        let mut c_3 : U8 := t5
        let mut t7 : Bool := false
        if (i_2 == (0 : I32)) then
          let t6 : I32 ← Misc.Ctype_h.mp_isalpha fuel (UInt.toS 8 c_3)
          t7 := (!(t6 != 0))
        let mut t9 : Bool := true
        if !t7 then
          let t8 : I32 ← Misc.Ctype_h.mp_isalnum fuel (UInt.toS 8 c_3)
          t9 := ((((!(t8 != 0)) && ((UInt.toS 32 c_3) != (46 : I32))) && ((UInt.toS 32 c_3) != (45 : I32))) && ((UInt.toS 32 c_3) != (43 : I32)))
        if t9 then
          return ((0 : I32) != 0)
      let t10 : I32 := i_2
      let t11 : I32 ← SInt.add t10 1
      i_2 := t11
    return ((1 : I32) != 0)
    : M Bool)
  Mem.popFrame [path_p]
  pure result

/-- C function `mp_normalize_path`, ../.mpv/misc/path_utils.c:190.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_normalize_path [Ext.«__errno_location»] [Ext.getcwd] [Ext.getenv] [Ext.realpath] [Ext.stat] [Ext.ta_asprintf] [Ext.ta_talloc_strdup_append_buffer] [Ext.ta_talloc_strndup_append_buffer] (fuel : Nat) (talloc_ctx : Ptr) (path : Ptr) : M Ptr := do
  let tmp_1 ← Mem.alloca 8 8
  let v_result_2 ← Mem.alloca 8 8
  let next_4 ← Mem.alloca 8 8
  let v_end_5 ← Mem.alloca 8 8
  let result : Ptr ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    let mut path_v : Ptr := path
    for _ in Once.mk do
      if (!(path_v != Ptr.null)) then
        return Ptr.null
      let t1 : Ptr ← Ptr.add path_v 1 (SInt.toInt (0 : I32))
      let t2 : I8 ← Mem.load I8 t1
      let mut t5 : Bool := true
      if !(!(t2 != 0)) then
        let t3 : Agg ← Misc.Bstr_h.bstr0 fuel path_v
        let t4 : Bool ← Misc.Path_utils_c.mp_is_url fuel t3
        t5 := ((SInt.ofBool 32 t4) != 0)
      let mut t7 : Bool := true
      if !t5 then
        let t6 : I32 ← Libc.strcmp path_v Statics.str_105
        t7 := (!(t6 != 0))
      if t7 then
        let t8 : Ptr ← Talloc.ta_xstrdup talloc_ctx_v path_v
        return t8
      let t9 : Ptr ← Talloc.ta_new_context Ptr.null
      let t10 : Ptr ← Ta.Ta_h.ta_oom_p fuel t9
      Mem.store tmp_1 t10
      Mem.undefine v_result_2 8
      let t11 : Agg ← Misc.Bstr_h.bstr0 fuel path_v
      let t12 : Bool ← Misc.Path_utils_c.mp_path_is_absolute fuel t11
      if (!t12) then
        let t13 : Ptr ← Mem.load Ptr tmp_1
        let t14 : Ptr ← Misc.Path_utils_c.mp_getcwd fuel t13
        let mut cwd_3 : Ptr := t14
        if (!(cwd_3 != Ptr.null)) then
          let t15 : Ptr ← Talloc.ta_xstrdup talloc_ctx_v path_v
          Mem.store v_result_2 t15
          break
        let t16 : Ptr ← Mem.load Ptr tmp_1
        let t17 : Ptr ← Misc.Path_utils_c.mp_path_join fuel t16 cwd_3 path_v
        path_v := t17
      let t18 : Ptr ← Mem.load Ptr tmp_1
      let t19 : Ptr ← Talloc.ta_xstrdup t18 Statics.str_97
      Mem.store v_result_2 t19
      Mem.undefine next_4 8
      let t20 : U64 ← Libc.strlen path_v
      let t21 : Ptr ← Ptr.add path_v 1 (UInt.toInt t20)
      Mem.store v_end_5 t21
      let mut ptr_6 : Ptr := path_v
      let mut j45 := false
      for _ in Fuel.mk fuel do
        let t22 : Ptr ← Mem.load Ptr v_end_5
        let t23 : Bool ← Ptr.lt ptr_6 t22
        if !t23 then break
        for _ in Once.mk do
          let t24 : Ptr ← Mem.load Ptr v_end_5
          let t25 : I64 ← Ptr.diff t24 ptr_6 1
          let t26 : Ptr ← Libc.memchr ptr_6 (47 : I32) (SInt.toU 64 t25)
          Mem.store next_4 t26
          let t27 : Ptr ← Mem.load Ptr next_4
          let t28 : Bool ← Ptr.eq t27 Ptr.null
          if t28 then
            let t29 : Ptr ← Mem.load Ptr v_end_5
            Mem.store next_4 t29
          let t30 : Ptr ← Mem.load Ptr next_4
          let t31 : I64 ← Ptr.diff t30 ptr_6 1
          let t32 := t31
          let t33 : Nat := if t32 == (SInt.toS 64 (0 : I32)) then 0 else if t32 == (SInt.toS 64 (1 : I32)) then 1 else if t32 == (SInt.toS 64 (2 : I32)) then 2 else 3
          let mut j34 := false
          let mut j37 := false
          for _ in Once.mk do
            if t33 ≤ 0 then
              j34 := true
              break
            if t33 ≤ 1 then
              let t35 : Ptr ← Ptr.add ptr_6 1 (SInt.toInt (0 : I32))
              let t36 : I8 ← Mem.load I8 t35
              if ((SInt.toS 32 t36) == (46 : I32)) then
                j37 := true
                break
              break
            if t33 ≤ 2 then
              let t38 : Ptr ← Ptr.add ptr_6 1 (SInt.toInt (0 : I32))
              let t39 : I8 ← Mem.load I8 t38
              let mut t42 : Bool := false
              if ((SInt.toS 32 t39) == (46 : I32)) then
                let t40 : Ptr ← Ptr.add ptr_6 1 (SInt.toInt (1 : I32))
                let t41 : I8 ← Mem.load I8 t40
                t42 := ((SInt.toS 32 t41) == (46 : I32))
              if t42 then
                let t43 : Ptr ← Ext.realpath.call path_v Ptr.null
                let mut tmp_result_7 : Ptr := t43
                let t44 : Ptr ← Talloc.ta_xstrdup talloc_ctx_v (if (tmp_result_7 != Ptr.null) then tmp_result_7 else path_v)
                Mem.store v_result_2 t44
                Libc.free tmp_result_7
                j45 := true
                break
          if j34 then break
          if j37 then break
          if j45 then break
          let t46 : Ptr ← Mem.load Ptr v_result_2
          let t47 : Ptr ← Ext.ta_talloc_strdup_append_buffer.call t46 Statics.str_138
          Mem.store v_result_2 t47
          let t48 : Ptr ← Mem.load Ptr v_result_2
          let t49 : Ptr ← Mem.load Ptr next_4
          let t50 : I64 ← Ptr.diff t49 ptr_6 1
          let t51 : Ptr ← Ext.ta_talloc_strndup_append_buffer.call t48 ptr_6 (SInt.toU 64 t50)
          Mem.store v_result_2 t51
        if j45 then break
        let t52 : Ptr ← Mem.load Ptr next_4
        let t53 : Ptr ← Ptr.add t52 1 (SInt.toInt (1 : I32))
        ptr_6 := t53
      if j45 then break
      let t54 : Ptr ← Mem.load Ptr v_result_2
      let t55 : Ptr ← Ptr.add t54 1 (SInt.toInt (0 : I32))
      let t56 : I8 ← Mem.load I8 t55
      if (!(t56 != 0)) then
        let t57 : Ptr ← Mem.load Ptr v_result_2
        let t58 : Ptr ← Ext.ta_talloc_strdup_append_buffer.call t57 Statics.str_138
        Mem.store v_result_2 t58
      let t59 : Ptr ← Mem.load Ptr v_result_2
      let t60 : Ptr ← Talloc.ta_steal_ talloc_ctx_v t59
      Mem.store v_result_2 t60
    let t61 : Ptr ← Mem.load Ptr tmp_1
    Talloc.ta_free t61
    let t62 : Ptr ← Mem.load Ptr v_result_2
    return t62
    : M Ptr)
  Mem.popFrame [tmp_1, v_result_2, next_4, v_end_5]
  pure result

/-- C function `mp_path_exists`, ../.mpv/misc/path_utils.c:276.
-/
def mp_path_exists [Ext.stat] (fuel : Nat) (path : Ptr) : M Bool := do
  let st_1 ← Mem.alloca 144 8
  let result : Bool ← (do
    let mut path_v : Ptr := path
    Mem.undefine st_1 144
    let mut t2 : Bool := false
    if (path_v != Ptr.null) then
      let t1 : I32 ← Ext.stat.call path_v st_1
      t2 := (t1 == (0 : I32))
    return ((SInt.ofBool 32 t2) != 0)
    : M Bool)
  Mem.popFrame [st_1]
  pure result

/-- C function `mp_path_isdir`, ../.mpv/misc/path_utils.c:282.
-/
def mp_path_isdir [Ext.stat] (fuel : Nat) (path : Ptr) : M Bool := do
  let st_1 ← Mem.alloca 144 8
  let result : Bool ← (do
    let mut path_v : Ptr := path
    Mem.undefine st_1 144
    let t1 : I32 ← Ext.stat.call path_v st_1
    let mut t4 : Bool := false
    if (t1 == (0 : I32)) then
      let t2 : Ptr ← Ptr.add st_1 1 24
      let t3 : U32 ← Mem.load U32 t2
      t4 := ((UInt.band t3 (SInt.toU 32 (61440 : I32))) == (SInt.toU 32 (16384 : I32)))
    return ((SInt.ofBool 32 t4) != 0)
    : M Bool)
  Mem.popFrame [st_1]
  pure result

/-- C function `mp_split_proto`, ../.mpv/misc/path_utils.c:309.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def mp_split_proto (fuel : Nat) (path : Agg) (out_url : Ptr) : M Agg := do
  let path_p ← Mem.alloca 16 8
  let r_1 ← Mem.alloca 16 8
  let cl3 ← Mem.alloca 16 8
  let cl7 ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg path_p path 8
    let mut out_url_v : Ptr := out_url
    let t1 : Agg ← Mem.loadAgg path_p 16 8
    let t2 : Bool ← Misc.Path_utils_c.mp_is_url fuel t1
    if (!t2) then
      Mem.undefine cl3 16
      Mem.store cl3 Ptr.null
      let t4 : Ptr ← Ptr.add cl3 1 8
      Mem.zero t4 8
      let t5 : Agg ← Mem.loadAgg cl3 16 8
      return t5
    Mem.undefine r_1 16
    let t6 : Agg ← Mem.loadAgg path_p 16 8
    let mut t9 : Ptr := default
    if (out_url_v != Ptr.null) then
      t9 := out_url_v
    else
      Mem.undefine cl7 16
      Mem.store cl7 Ptr.null
      let t8 : Ptr ← Ptr.add cl7 1 8
      Mem.zero t8 8
      t9 := cl7
    let t10 : Bool ← Misc.Bstr_c.bstr_split_tok fuel t6 Statics.str_142 r_1 t9
    let t11 : Agg ← Mem.loadAgg r_1 16 8
    return t11
    : M Agg)
  Mem.popFrame [path_p, r_1, cl3, cl7]
  pure result

/-- C function `mp_mkdirp`, ../.mpv/misc/path_utils.c:318.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_mkdirp [Ext.mkdir] [Ext.stat] (fuel : Nat) (dir : Ptr) : M Unit := do
  let mut dir_v : Ptr := dir
  let t1 : Bool ← Misc.Path_utils_c.mp_path_exists fuel dir_v
  if t1 then
    return ()
  let t2 : Ptr ← Talloc.ta_xstrdup Ptr.null dir_v
  let mut path_1 : Ptr := t2
  let t3 : Ptr ← Ptr.add path_1 1 (SInt.toInt (1 : I32))
  let mut cdir_2 : Ptr := t3
  for _ in Fuel.mk fuel do
    if !(cdir_2 != Ptr.null) then break
    let t4 : Ptr ← Libc.strchr cdir_2 (47 : I32)
    cdir_2 := t4
    if (cdir_2 != Ptr.null) then
      let t5 : I8 := (SInt.toS 8 (0 : I32))
      Mem.store cdir_2 t5
    let t6 : I32 ← Ext.mkdir.call path_1 (SInt.toU 32 (511 : I32))
    if (cdir_2 != Ptr.null) then
      let t7 : Ptr := cdir_2
      let t8 : Ptr ← Ptr.add t7 1 1
      cdir_2 := t8
      let t9 : I8 := (SInt.toS 8 (47 : I32))
      Mem.store t7 t9
  Talloc.ta_free path_1
  pure ()

end Misc.Misc.Path_utils_c
