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

namespace Misc.Misc.Charset_conv_c

/-- C function `mp_charset_is_utf8`, ../.mpv/misc/charset_conv.c:41.
-/
def mp_charset_is_utf8 [Ext.strcasecmp] (fuel : Nat) (user_cp : Ptr) : M Bool := do
  let mut user_cp_v : Ptr := user_cp
  let mut t4 : Bool := false
  if (user_cp_v != Ptr.null) then
    let t1 : I32 ← Ext.strcasecmp.call user_cp_v Statics.str_26
    let mut t3 : Bool := true
    if !(t1 == (0 : I32)) then
      let t2 : I32 ← Ext.strcasecmp.call user_cp_v Statics.str_5
      t3 := (t2 == (0 : I32))
    t4 := t3
  return ((SInt.ofBool 32 t4) != 0)

/-- C function `mp_charset_is_utf16`, ../.mpv/misc/charset_conv.c:47.
-/
def mp_charset_is_utf16 [Ext.strncasecmp] (fuel : Nat) (user_cp : Ptr) : M Bool := do
  let s_1 ← Mem.alloca 16 8
  let result : Bool ← (do
    let mut user_cp_v : Ptr := user_cp
    let t1 : Agg ← Misc.Bstr_h.bstr0 fuel user_cp_v
    Mem.storeAgg s_1 t1 8
    let t2 : Agg ← Mem.loadAgg s_1 16 8
    let t3 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_27
    let t4 : Bool ← Misc.Bstr_c.bstr_case_startswith fuel t2 t3
    let mut t8 : Bool := true
    if !((SInt.ofBool 32 t4) != 0) then
      let t5 : Agg ← Mem.loadAgg s_1 16 8
      let t6 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_28
      let t7 : Bool ← Misc.Bstr_c.bstr_case_startswith fuel t5 t6
      t8 := ((SInt.ofBool 32 t7) != 0)
    return ((SInt.ofBool 32 t8) != 0)
    : M Bool)
  Mem.popFrame [s_1]
  pure result

/-- C function `ms_bom_guess`, ../.mpv/misc/charset_conv.c:57.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def ms_bom_guess (fuel : Nat) (buf : Agg) : M Ptr := do
  let buf_p ← Mem.alloca 16 8
  let result : Ptr ← (do
    Mem.storeAgg buf_p buf 8
    let mut n_1 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      if !(decide (n_1 < (3 : I32))) then break
      for _ in Once.mk do
        let t1 : Agg ← Mem.loadAgg buf_p 16 8
        let t2 : Ptr ← Ptr.add Statics.g_Misc_Charset_conv_c_utf_bom 8 (SInt.toInt n_1)
        let t3 : Ptr ← Mem.load Ptr t2
        let t4 : Bool ← Misc.Bstr_h.bstr_startswith0 fuel t1 t3
        if t4 then
          let t5 : Ptr ← Ptr.add Statics.g_Misc_Charset_conv_c_utf_enc 8 (SInt.toInt n_1)
          let t6 : Ptr ← Mem.load Ptr t5
          return t6
      let t7 : I32 := n_1
      let t8 : I32 ← SInt.add t7 1
      n_1 := t8
    return Ptr.null
    : M Ptr)
  Mem.popFrame [buf_p]
  pure result

/-- C function `mp_charset_guess`, ../.mpv/misc/charset_conv.c:101.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def mp_charset_guess [Ext.mp_log2] [Ext.mp_msg] [Ext.strcasecmp] (fuel : Nat) (talloc_ctx : Ptr) (log : Ptr) (buf : Agg) (user_cp : Ptr) (flags : I32) : M Ptr := do
  let buf_p ← Mem.alloca 16 8
  let result : Ptr ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    let mut log_v : Ptr := log
    Mem.storeAgg buf_p buf 8
    let mut user_cp_v : Ptr := user_cp
    let mut flags_v : I32 := flags
    let t1 : Ptr ← Ptr.add user_cp_v 1 (SInt.toInt (0 : I32))
    let t2 : I8 ← Mem.load I8 t1
    if ((SInt.toS 32 t2) == (43 : I32)) then
      let t3 : Ptr ← Ptr.add user_cp_v 1 (SInt.toInt (1 : I32))
      Ext.mp_msg.call log_v (5 : I32) Statics.str_29 [(VArg.ptr t3)]
      let t4 : Ptr ← Ptr.add user_cp_v 1 (SInt.toInt (1 : I32))
      return t4
    let t5 : Agg ← Mem.loadAgg buf_p 16 8
    let t6 : Ptr ← Misc.Charset_conv_c.ms_bom_guess fuel t5
    let mut bom_cp_1 : Ptr := t6
    if (bom_cp_1 != Ptr.null) then
      Ext.mp_msg.call log_v (5 : I32) Statics.str_30 [(VArg.ptr bom_cp_1)]
      return bom_cp_1
    let t7 : Agg ← Mem.loadAgg buf_p 16 8
    let t8 : I32 ← Misc.Bstr_c.bstr_validate_utf8 fuel t7
    let mut r_2 : I32 := t8
    if ((decide (r_2 ≥ (0 : I32))) || ((decide (r_2 > (SInt.ofInt 32 (-8)))) && ((SInt.band flags_v (2 : I32)) != 0))) then
      let t9 : I32 ← Libc.strcmp user_cp_v Statics.str_31
      let mut t11 : Bool := false
      if (t9 != (0 : I32)) then
        let t10 : Bool ← Misc.Charset_conv_c.mp_charset_is_utf8 fuel user_cp_v
        t11 := (!t10)
      if t11 then
        Ext.mp_msg.call log_v (5 : I32) Statics.str_32 []
      return Statics.str_5
    let mut res_3 : Ptr := Ptr.null
    let t12 : I32 ← Ext.strcasecmp.call user_cp_v Statics.str_31
    if (t12 == (0 : I32)) then
      if (!(res_3 != Ptr.null)) then
        Ext.mp_msg.call log_v (5 : I32) Statics.str_33 []
        let t13 : Ptr := Statics.str_34
        res_3 := t13
    else
      res_3 := user_cp_v
    Ext.mp_msg.call log_v (5 : I32) Statics.str_35 [(VArg.ptr res_3)]
    return res_3
    : M Ptr)
  Mem.popFrame [buf_p]
  pure result

/-- C function `mp_iconv_to_utf8`, ../.mpv/misc/charset_conv.c:150.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_iconv_to_utf8 [Ext.mp_append_utf8_bstr] [Ext.mp_log2] (fuel : Nat) (log : Ptr) (buf : Agg) (cp : Ptr) (flags : I32) : M Agg := do
  let buf_p ← Mem.alloca 16 8
  let result : Agg ← (do
    let mut log_v : Ptr := log
    Mem.storeAgg buf_p buf 8
    let mut cp_v : Ptr := cp
    let mut flags_v : I32 := flags
    if ((SInt.band flags_v (8 : I32)) != 0) then
      let t1 : Agg ← Mem.loadAgg buf_p 16 8
      return t1
    else
      let t2 : Agg ← Mem.loadAgg buf_p 16 8
      let t3 : Agg ← Misc.Bstr_c.bstr_sanitize_utf8_latin1 fuel Ptr.null t2
      return t3
    : M Agg)
  Mem.popFrame [buf_p]
  pure result

end Misc.Misc.Charset_conv_c
