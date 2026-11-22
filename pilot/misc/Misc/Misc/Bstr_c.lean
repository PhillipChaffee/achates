import Achates
import Misc.Statics
import Misc.Externals

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Bstr_c

/-- C function `bstrcmp`, ../.mpv/misc/bstr.c:30.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstrcmp (fuel : Nat) (str1 : Agg) (str2 : Agg) : M I32 := do
  let str1_p ← Mem.alloca 16 8
  let str2_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg str1_p str1 8
    Mem.storeAgg str2_p str2 8
    let mut ret_1 : I32 := (0 : I32)
    let t1 : Ptr ← Ptr.add str1_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    let mut t5 : Bool := false
    if (t2 != 0) then
      let t3 : Ptr ← Ptr.add str2_p 1 8
      let t4 : U64 ← Mem.load U64 t3
      t5 := (t4 != 0)
    if t5 then
      let t6 : Ptr ← Mem.load Ptr str1_p
      let t7 : Ptr ← Mem.load Ptr str2_p
      let t8 : Ptr ← Ptr.add str1_p 1 8
      let t9 : U64 ← Mem.load U64 t8
      let t10 : Ptr ← Ptr.add str2_p 1 8
      let t11 : U64 ← Mem.load U64 t10
      let mut t16 : U64 := default
      if (decide (t9 > t11)) then
        let t12 : Ptr ← Ptr.add str2_p 1 8
        let t13 : U64 ← Mem.load U64 t12
        t16 := t13
      else
        let t14 : Ptr ← Ptr.add str1_p 1 8
        let t15 : U64 ← Mem.load U64 t14
        t16 := t15
      let t17 : I32 ← Libc.memcmp t6 t7 t16
      ret_1 := t17
    if (!(ret_1 != 0)) then
      let t18 : Ptr ← Ptr.add str1_p 1 8
      let t19 : U64 ← Mem.load U64 t18
      let t20 : Ptr ← Ptr.add str2_p 1 8
      let t21 : U64 ← Mem.load U64 t20
      if (t19 == t21) then
        return (0 : I32)
      else
        let t22 : Ptr ← Ptr.add str1_p 1 8
        let t23 : U64 ← Mem.load U64 t22
        let t24 : Ptr ← Ptr.add str2_p 1 8
        let t25 : U64 ← Mem.load U64 t24
        if (decide (t23 > t25)) then
          return (1 : I32)
        else
          return (SInt.ofInt 32 (-1))
    return ret_1
    : M I32)
  Mem.popFrame [str1_p, str2_p]
  pure result

/-- C function `bstrcasecmp`, ../.mpv/misc/bstr.c:47.
-/
def bstrcasecmp [Ext.strncasecmp] (fuel : Nat) (str1 : Agg) (str2 : Agg) : M I32 := do
  let str1_p ← Mem.alloca 16 8
  let str2_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg str1_p str1 8
    Mem.storeAgg str2_p str2 8
    let mut ret_1 : I32 := (0 : I32)
    let t1 : Ptr ← Ptr.add str1_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    let mut t5 : Bool := false
    if (t2 != 0) then
      let t3 : Ptr ← Ptr.add str2_p 1 8
      let t4 : U64 ← Mem.load U64 t3
      t5 := (t4 != 0)
    if t5 then
      let t6 : Ptr ← Mem.load Ptr str1_p
      let t7 : Ptr ← Mem.load Ptr str2_p
      let t8 : Ptr ← Ptr.add str1_p 1 8
      let t9 : U64 ← Mem.load U64 t8
      let t10 : Ptr ← Ptr.add str2_p 1 8
      let t11 : U64 ← Mem.load U64 t10
      let mut t16 : U64 := default
      if (decide (t9 > t11)) then
        let t12 : Ptr ← Ptr.add str2_p 1 8
        let t13 : U64 ← Mem.load U64 t12
        t16 := t13
      else
        let t14 : Ptr ← Ptr.add str1_p 1 8
        let t15 : U64 ← Mem.load U64 t14
        t16 := t15
      let t17 : I32 ← Ext.strncasecmp.call t6 t7 t16
      ret_1 := t17
    if (!(ret_1 != 0)) then
      let t18 : Ptr ← Ptr.add str1_p 1 8
      let t19 : U64 ← Mem.load U64 t18
      let t20 : Ptr ← Ptr.add str2_p 1 8
      let t21 : U64 ← Mem.load U64 t20
      if (t19 == t21) then
        return (0 : I32)
      else
        let t22 : Ptr ← Ptr.add str1_p 1 8
        let t23 : U64 ← Mem.load U64 t22
        let t24 : Ptr ← Ptr.add str2_p 1 8
        let t25 : U64 ← Mem.load U64 t24
        if (decide (t23 > t25)) then
          return (1 : I32)
        else
          return (SInt.ofInt 32 (-1))
    return ret_1
    : M I32)
  Mem.popFrame [str1_p, str2_p]
  pure result

/-- C function `bstrchr`, ../.mpv/misc/bstr.c:64.
-/
def bstrchr (fuel : Nat) (str : Agg) (c : I32) : M I32 := do
  let str_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg str_p str 8
    let mut c_v : I32 := c
    let t1 : Ptr ← Ptr.add str_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    if (!(t2 != 0)) then
      return (SInt.ofInt 32 (-1))
    let t3 : Ptr ← Mem.load Ptr str_p
    let t4 : Ptr ← Ptr.add str_p 1 8
    let t5 : U64 ← Mem.load U64 t4
    let t6 : Ptr ← Libc.memchr t3 c_v t5
    let mut pos_1 : Ptr := t6
    let mut t9 : I64 := default
    if (pos_1 != Ptr.null) then
      let t7 : Ptr ← Mem.load Ptr str_p
      let t8 : I64 ← Ptr.diff pos_1 t7 1
      t9 := t8
    else
      t9 := (SInt.toS 64 (SInt.ofInt 32 (-1)))
    return (SInt.toS 32 t9)
    : M I32)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstrrchr`, ../.mpv/misc/bstr.c:72.
-/
def bstrrchr [Ext.memrchr] (fuel : Nat) (str : Agg) (c : I32) : M I32 := do
  let str_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg str_p str 8
    let mut c_v : I32 := c
    let t1 : Ptr ← Ptr.add str_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    if (!(t2 != 0)) then
      return (SInt.ofInt 32 (-1))
    let t3 : Ptr ← Mem.load Ptr str_p
    let t4 : Ptr ← Ptr.add str_p 1 8
    let t5 : U64 ← Mem.load U64 t4
    let t6 : Ptr ← Ext.memrchr.call t3 c_v t5
    let mut pos_1 : Ptr := t6
    let mut t9 : I64 := default
    if (pos_1 != Ptr.null) then
      let t7 : Ptr ← Mem.load Ptr str_p
      let t8 : I64 ← Ptr.diff pos_1 t7 1
      t9 := t8
    else
      t9 := (SInt.toS 64 (SInt.ofInt 32 (-1)))
    return (SInt.toS 32 t9)
    : M I32)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstrcspn`, ../.mpv/misc/bstr.c:87.
-/
def bstrcspn (fuel : Nat) (str : Agg) (reject : Ptr) : M I32 := do
  let str_p ← Mem.alloca 16 8
  let i_1 ← Mem.alloca 4 4
  let result : I32 ← (do
    Mem.storeAgg str_p str 8
    let mut reject_v : Ptr := reject
    Mem.undefine i_1 4
    let t1 : I32 := (0 : I32)
    Mem.store i_1 t1
    for _ in Fuel.mk fuel do
      let t2 : I32 ← Mem.load I32 i_1
      let t3 : Ptr ← Ptr.add str_p 1 8
      let t4 : U64 ← Mem.load U64 t3
      if !(decide ((SInt.toU 64 t2) < t4)) then break
      let mut j10 := false
      for _ in Once.mk do
        let t5 : Ptr ← Mem.load Ptr str_p
        let t6 : I32 ← Mem.load I32 i_1
        let t7 : Ptr ← Ptr.add t5 1 (SInt.toInt t6)
        let t8 : U8 ← Mem.load U8 t7
        let t9 : Ptr ← Libc.strchr reject_v (UInt.toS 32 t8)
        if (t9 != Ptr.null) then
          j10 := true
          break
      if j10 then break
      let t11 : I32 ← Mem.load I32 i_1
      let t12 : I32 ← SInt.add t11 1
      Mem.store i_1 t12
    let t13 : I32 ← Mem.load I32 i_1
    return t13
    : M I32)
  Mem.popFrame [str_p, i_1]
  pure result

/-- C function `bstrspn`, ../.mpv/misc/bstr.c:96.
-/
def bstrspn (fuel : Nat) (str : Agg) (accept : Ptr) : M I32 := do
  let str_p ← Mem.alloca 16 8
  let i_1 ← Mem.alloca 4 4
  let result : I32 ← (do
    Mem.storeAgg str_p str 8
    let mut accept_v : Ptr := accept
    Mem.undefine i_1 4
    let t1 : I32 := (0 : I32)
    Mem.store i_1 t1
    for _ in Fuel.mk fuel do
      let t2 : I32 ← Mem.load I32 i_1
      let t3 : Ptr ← Ptr.add str_p 1 8
      let t4 : U64 ← Mem.load U64 t3
      if !(decide ((SInt.toU 64 t2) < t4)) then break
      let mut j10 := false
      for _ in Once.mk do
        let t5 : Ptr ← Mem.load Ptr str_p
        let t6 : I32 ← Mem.load I32 i_1
        let t7 : Ptr ← Ptr.add t5 1 (SInt.toInt t6)
        let t8 : U8 ← Mem.load U8 t7
        let t9 : Ptr ← Libc.strchr accept_v (UInt.toS 32 t8)
        if (!(t9 != Ptr.null)) then
          j10 := true
          break
      if j10 then break
      let t11 : I32 ← Mem.load I32 i_1
      let t12 : I32 ← SInt.add t11 1
      Mem.store i_1 t12
    let t13 : I32 ← Mem.load I32 i_1
    return t13
    : M I32)
  Mem.popFrame [str_p, i_1]
  pure result

/-- C function `bstr_splice`, ../.mpv/misc/bstr.c:158.
-/
def bstr_splice (fuel : Nat) (str : Agg) (start : I32) (v_end : I32) : M Agg := do
  let str_p ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg str_p str 8
    let mut start_v : I32 := start
    let mut v_end_v : I32 := v_end
    let t1 : Ptr ← Ptr.add str_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    if (!(t2 != 0)) then
      let t3 : Agg ← Mem.loadAgg str_p 16 8
      return t3
    if (decide (start_v < (0 : I32))) then
      let t4 : Ptr ← Ptr.add str_p 1 8
      let t5 : U64 ← Mem.load U64 t4
      let t6 : I32 := (UInt.toS 32 ((SInt.toU 64 start_v) + t5))
      start_v := t6
    if (decide (v_end_v < (0 : I32))) then
      let t7 : Ptr ← Ptr.add str_p 1 8
      let t8 : U64 ← Mem.load U64 t7
      let t9 : I32 := (UInt.toS 32 ((SInt.toU 64 v_end_v) + t8))
      v_end_v := t9
    let t10 : Ptr ← Ptr.add str_p 1 8
    let t11 : U64 ← Mem.load U64 t10
    let mut t14 : U64 := default
    if (decide ((SInt.toU 64 v_end_v) > t11)) then
      let t12 : Ptr ← Ptr.add str_p 1 8
      let t13 : U64 ← Mem.load U64 t12
      t14 := t13
    else
      t14 := (SInt.toU 64 v_end_v)
    let t15 : I32 := (UInt.toS 32 t14)
    v_end_v := t15
    let t16 : I32 := (if (decide (start_v > (0 : I32))) then start_v else (0 : I32))
    start_v := t16
    let t17 : I32 := (if (decide (v_end_v > start_v)) then v_end_v else start_v)
    v_end_v := t17
    let t18 : Ptr ← Mem.load Ptr str_p
    let t19 : Ptr ← Ptr.add t18 1 (SInt.toInt start_v)
    Mem.store str_p t19
    let t20 : Ptr ← Ptr.add str_p 1 8
    let t21 : I32 ← SInt.sub v_end_v start_v
    let t22 : U64 := (SInt.toU 64 t21)
    Mem.store t20 t22
    let t23 : Agg ← Mem.loadAgg str_p 16 8
    return t23
    : M Agg)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_parse_utf8_code_length`, ../.mpv/misc/bstr.c:256.
-/
def bstr_parse_utf8_code_length [Ext.mp_log2] (fuel : Nat) (b : U8) : M I32 := do
  let mut b_v : U8 := b
  if (decide ((UInt.toS 32 b_v) < (128 : I32))) then
    return (1 : I32)
  let t1 : U32 ← Ext.mp_log2.call (SInt.toU 32 (SInt.bxor (UInt.toS 32 b_v) (255 : I32)))
  let mut bytes_1 : I32 := (UInt.toS 32 ((SInt.toU 32 (7 : I32)) - t1))
  return (if ((decide (bytes_1 ≥ (2 : I32))) && (decide (bytes_1 ≤ (4 : I32)))) then bytes_1 else (SInt.ofInt 32 (-1)))

/-- C function `bstr_decode_partial_utf8`, ../.mpv/misc/bstr.c:264.
-/
def bstr_decode_partial_utf8 [Ext.mp_log2] (fuel : Nat) (s : Ptr) : M I32 := do
  let mut s_v : Ptr := s
  let t1 : Ptr ← Ptr.add s_v 1 8
  let t2 : U64 ← Mem.load U64 t1
  if (t2 == (SInt.toU 64 (0 : I32))) then
    return (SInt.ofInt 32 (-1))
  let t3 : Ptr ← Mem.load Ptr s_v
  let t4 : Ptr ← Ptr.add t3 1 (SInt.toInt (0 : I32))
  let t5 : U8 ← Mem.load U8 t4
  let mut codepoint_1 : U32 := (UInt.toU 32 t5)
  let t6 : Ptr ← Mem.load Ptr s_v
  let t7 : Ptr ← Ptr.add t6 1 1
  Mem.store s_v t7
  let t8 : Ptr ← Ptr.add s_v 1 8
  let t9 : U64 ← Mem.load U64 t8
  let t10 : U64 := (t9 - 1)
  Mem.store t8 t10
  if (decide (codepoint_1 ≥ (SInt.toU 32 (128 : I32)))) then
    let t11 : I32 ← Misc.Bstr_c.bstr_parse_utf8_code_length fuel (UInt.toU 8 codepoint_1)
    let mut bytes_2 : I32 := t11
    if (decide (bytes_2 < (1 : I32))) then
      return (SInt.ofInt 32 (-1))
    let t12 : I32 ← SInt.shr (127 : I32) (SInt.toInt bytes_2)
    let t13 : U32 := (UInt.band codepoint_1 (SInt.toU 32 t12))
    codepoint_1 := t13
    let mut n_3 : I32 := (1 : I32)
    for _ in Fuel.mk fuel do
      if !(decide (n_3 < bytes_2)) then break
      for _ in Once.mk do
        let t14 : Ptr ← Ptr.add s_v 1 8
        let t15 : U64 ← Mem.load U64 t14
        if (!(t15 != 0)) then
          return (SInt.ofInt 32 (-2))
        let t16 : Ptr ← Mem.load Ptr s_v
        let t17 : Ptr ← Ptr.add t16 1 (SInt.toInt (0 : I32))
        let t18 : U8 ← Mem.load U8 t17
        let mut tmp_4 : I32 := (UInt.toS 32 t18)
        if ((SInt.band tmp_4 (192 : I32)) != (128 : I32)) then
          return (SInt.ofInt 32 (-2))
        let t19 : U32 ← UInt.shl codepoint_1 (SInt.toInt (6 : I32))
        let t20 : U32 := (UInt.bor t19 (SInt.toU 32 (SInt.band tmp_4 (SInt.bnot (192 : I32)))))
        codepoint_1 := t20
        let t21 : Ptr ← Mem.load Ptr s_v
        let t22 : Ptr ← Ptr.add t21 1 1
        Mem.store s_v t22
        let t23 : Ptr ← Ptr.add s_v 1 8
        let t24 : U64 ← Mem.load U64 t23
        let t25 : U64 := (t24 - 1)
        Mem.store t23 t25
      let t26 : I32 := n_3
      let t27 : I32 ← SInt.add t26 1
      n_3 := t27
    if ((decide (codepoint_1 > (SInt.toU 32 (1114111 : I32)))) || ((decide (codepoint_1 ≥ (SInt.toU 32 (55296 : I32)))) && (decide (codepoint_1 ≤ (SInt.toU 32 (57343 : I32)))))) then
      return (SInt.ofInt 32 (-1))
    let mut t31 : I32 := default
    if (bytes_2 == (2 : I32)) then
      t31 := (128 : I32)
    else
      let t28 : I32 ← SInt.mul (5 : I32) bytes_2
      let t29 : I32 ← SInt.sub t28 (4 : I32)
      let t30 : I32 ← SInt.shl (1 : I32) (SInt.toInt t29)
      t31 := t30
    let mut min_5 : U32 := (SInt.toU 32 t31)
    if (decide (codepoint_1 < min_5)) then
      return (SInt.ofInt 32 (-3))
  return (UInt.toS 32 codepoint_1)

/-- C function `bstr_decode_utf8`, ../.mpv/misc/bstr.c:295.
-/
def bstr_decode_utf8 [Ext.mp_log2] (fuel : Nat) (s : Agg) (out_next : Ptr) : M I32 := do
  let s_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg s_p s 8
    let mut out_next_v : Ptr := out_next
    let t1 : I32 ← Misc.Bstr_c.bstr_decode_partial_utf8 fuel s_p
    let mut res_1 : I32 := t1
    if ((decide (res_1 ≥ (0 : I32))) && (out_next_v != Ptr.null)) then
      let t2 : Agg ← Mem.loadAgg s_p 16 8
      Mem.storeAgg out_next_v t2 8
    return res_1
    : M I32)
  Mem.popFrame [s_p]
  pure result

/-- C function `bstr_split_utf8`, ../.mpv/misc/bstr.c:303.
-/
def bstr_split_utf8 [Ext.mp_log2] (fuel : Nat) (str : Agg) (out_next : Ptr) : M Agg := do
  let str_p ← Mem.alloca 16 8
  let rest_1 ← Mem.alloca 16 8
  let cl3 ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg str_p str 8
    let mut out_next_v : Ptr := out_next
    Mem.undefine rest_1 16
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : I32 ← Misc.Bstr_c.bstr_decode_utf8 fuel t1 rest_1
    let mut code_2 : I32 := t2
    if (decide (code_2 < (0 : I32))) then
      Mem.undefine cl3 16
      Mem.store cl3 Ptr.null
      let t4 : Ptr ← Ptr.add cl3 1 8
      Mem.zero t4 8
      let t5 : Agg ← Mem.loadAgg cl3 16 8
      return t5
    if (out_next_v != Ptr.null) then
      let t6 : Agg ← Mem.loadAgg rest_1 16 8
      Mem.storeAgg out_next_v t6 8
    let t7 : Agg ← Mem.loadAgg str_p 16 8
    let t8 : Ptr ← Ptr.add str_p 1 8
    let t9 : U64 ← Mem.load U64 t8
    let t10 : Ptr ← Ptr.add rest_1 1 8
    let t11 : U64 ← Mem.load U64 t10
    let t12 : Agg ← Misc.Bstr_c.bstr_splice fuel t7 (0 : I32) (UInt.toS 32 (t9 - t11))
    return t12
    : M Agg)
  Mem.popFrame [str_p, rest_1, cl3]
  pure result

/-- C function `bstr_validate_utf8`, ../.mpv/misc/bstr.c:314.
-/
def bstr_validate_utf8 [Ext.mp_log2] (fuel : Nat) (s : Agg) : M I32 := do
  let s_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg s_p s 8
    for _ in Fuel.mk fuel do
      let t1 : Ptr ← Ptr.add s_p 1 8
      let t2 : U64 ← Mem.load U64 t1
      if !(t2 != 0) then break
      let t3 : Agg ← Mem.loadAgg s_p 16 8
      let t4 : I32 ← Misc.Bstr_c.bstr_decode_utf8 fuel t3 s_p
      if (decide (t4 < (0 : I32))) then
        let t5 : Ptr ← Mem.load Ptr s_p
        let t6 : Ptr ← Ptr.add t5 1 (SInt.toInt (0 : I32))
        let t7 : U8 ← Mem.load U8 t6
        let mut codepoint_1 : U32 := (UInt.toU 32 t7)
        let t8 : I32 ← Misc.Bstr_c.bstr_parse_utf8_code_length fuel (UInt.toU 8 codepoint_1)
        let mut bytes_2 : I32 := t8
        let mut t11 : Bool := false
        if (decide (bytes_2 > (1 : I32))) then
          let t9 : Ptr ← Ptr.add s_p 1 8
          let t10 : U64 ← Mem.load U64 t9
          t11 := (decide (t10 < (SInt.toU 64 (6 : I32))))
        if t11 then
          let mut n_3 : I32 := (1 : I32)
          for _ in Fuel.mk fuel do
            if !(decide (n_3 < bytes_2)) then break
            let mut j19 := false
            for _ in Once.mk do
              let t12 : Ptr ← Ptr.add s_p 1 8
              let t13 : U64 ← Mem.load U64 t12
              if (decide ((SInt.toU 64 n_3) ≥ t13)) then
                let t14 : Ptr ← Ptr.add s_p 1 8
                let t15 : U64 ← Mem.load U64 t14
                return (UInt.toS 32 (UInt.neg ((SInt.toU 64 bytes_2) - t15)))
              let t16 : Ptr ← Mem.load Ptr s_p
              let t17 : Ptr ← Ptr.add t16 1 (SInt.toInt n_3)
              let t18 : U8 ← Mem.load U8 t17
              let mut tmp_4 : I32 := (UInt.toS 32 t18)
              if ((SInt.band tmp_4 (192 : I32)) != (128 : I32)) then
                j19 := true
                break
            if j19 then break
            let t20 : I32 := n_3
            let t21 : I32 ← SInt.add t20 1
            n_3 := t21
        return (SInt.ofInt 32 (-8))
    return (0 : I32)
    : M I32)
  Mem.popFrame [s_p]
  pure result

/-- C function `resize_append`, ../.mpv/misc/bstr.c:361.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def resize_append (fuel : Nat) (talloc_ctx : Ptr) (s : Ptr) (append_min : U64) : M Unit := do
  let mut talloc_ctx_v : Ptr := talloc_ctx
  let mut s_v : Ptr := s
  let mut append_min_v : U64 := append_min
  let t1 : Ptr ← Mem.load Ptr s_v
  let t2 : U64 ← Talloc.ta_get_size t1
  let mut size_1 : U64 := t2
  let t3 : Ptr ← Ptr.add s_v 1 8
  let t4 : U64 ← Mem.load U64 t3
  let mut t5 : Unit := default
  if (decide (t4 ≤ size_1)) then
    t5 := ()
  else
    Libc.«__assert_fail» Statics.str_21 Statics.str_22 (SInt.toU 32 (364 : I32)) Statics.str_23
    t5 := ()
  let t6 : Ptr ← Ptr.add s_v 1 8
  let t7 : U64 ← Mem.load U64 t6
  if (decide (append_min_v > (size_1 - t7))) then
    if (decide (append_min_v < size_1)) then
      append_min_v := size_1
    let t8 : U64 ← UInt.div (18446744073709551615 : U64) (SInt.toU 64 (2 : I32))
    let mut t10 : Bool := true
    if !(decide (size_1 ≥ t8)) then
      let t9 : U64 ← UInt.div (18446744073709551615 : U64) (SInt.toU 64 (2 : I32))
      t10 := (decide (append_min_v ≥ t9))
    if t10 then
      Libc.abort
    let t11 : Ptr ← Mem.load Ptr s_v
    let t12 : Ptr ← Talloc.ta_xrealloc_size talloc_ctx_v t11 (size_1 + append_min_v)
    let t13 : Ptr ← Talloc.ta_dbg_set_loc t12 Statics.str_24
    Mem.store s_v t13
  pure ()

/-- C function `bstr_xappend`, ../.mpv/misc/bstr.c:374.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def bstr_xappend (fuel : Nat) (talloc_ctx : Ptr) (s : Ptr) (append : Agg) : M Unit := do
  let append_p ← Mem.alloca 16 8
  let result : Unit ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    let mut s_v : Ptr := s
    Mem.storeAgg append_p append 8
    let t1 : Ptr ← Ptr.add append_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    if (!(t2 != 0)) then
      return ()
    let t3 : Ptr ← Ptr.add append_p 1 8
    let t4 : U64 ← Mem.load U64 t3
    Misc.Bstr_c.resize_append fuel talloc_ctx_v s_v (t4 + (SInt.toU 64 (1 : I32)))
    let t5 : Ptr ← Mem.load Ptr s_v
    let t6 : Ptr ← Ptr.add s_v 1 8
    let t7 : U64 ← Mem.load U64 t6
    let t8 : Ptr ← Ptr.add t5 1 (UInt.toInt t7)
    let t9 : Ptr ← Mem.load Ptr append_p
    let t10 : Ptr ← Ptr.add append_p 1 8
    let t11 : U64 ← Mem.load U64 t10
    let t12 : Ptr ← Libc.memmove t8 t9 t11
    let t13 : Ptr ← Ptr.add s_v 1 8
    let t14 : U64 ← Mem.load U64 t13
    let t15 : Ptr ← Ptr.add append_p 1 8
    let t16 : U64 ← Mem.load U64 t15
    let t17 : U64 := (t14 + t16)
    Mem.store t13 t17
    let t18 : Ptr ← Mem.load Ptr s_v
    let t19 : Ptr ← Ptr.add s_v 1 8
    let t20 : U64 ← Mem.load U64 t19
    let t21 : Ptr ← Ptr.add t18 1 (UInt.toInt t20)
    let t22 : U8 := (SInt.toU 8 (0 : I32))
    Mem.store t21 t22
    pure ()
    : M Unit)
  Mem.popFrame [append_p]
  pure result

/-- C function `bstr_sanitize_utf8_latin1`, ../.mpv/misc/bstr.c:339.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def bstr_sanitize_utf8_latin1 [Ext.mp_append_utf8_bstr] [Ext.mp_log2] (fuel : Nat) (talloc_ctx : Ptr) (s : Agg) : M Agg := do
  let s_p ← Mem.alloca 16 8
  let new_1 ← Mem.alloca 16 8
  let left_2 ← Mem.alloca 16 8
  let cl8 ← Mem.alloca 16 8
  let cl26 ← Mem.alloca 16 8
  let result : Agg ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    Mem.storeAgg s_p s 8
    Mem.store new_1 Ptr.null
    let t1 : Ptr ← Ptr.add new_1 1 8
    Mem.zero t1 8
    let t2 : Agg ← Mem.loadAgg s_p 16 8
    Mem.storeAgg left_2 t2 8
    let t3 : Ptr ← Mem.load Ptr s_p
    let mut first_ok_3 : Ptr := t3
    for _ in Fuel.mk fuel do
      let t4 : Ptr ← Ptr.add left_2 1 8
      let t5 : U64 ← Mem.load U64 t4
      if !(t5 != 0) then break
      let t6 : Agg ← Mem.loadAgg left_2 16 8
      let t7 : I32 ← Misc.Bstr_c.bstr_decode_utf8 fuel t6 left_2
      let mut r_4 : I32 := t7
      if (decide (r_4 < (0 : I32))) then
        Mem.undefine cl8 16
        Mem.store cl8 first_ok_3
        let t9 : Ptr ← Mem.load Ptr left_2
        let t10 : I64 ← Ptr.diff t9 first_ok_3 1
        let t11 : Ptr ← Ptr.add cl8 1 8
        Mem.store t11 (SInt.toU 64 t10)
        let t12 : Agg ← Mem.loadAgg cl8 16 8
        Misc.Bstr_c.bstr_xappend fuel talloc_ctx_v new_1 t12
        let t13 : Ptr ← Mem.load Ptr left_2
        let t14 : Ptr ← Ptr.add t13 1 (SInt.toInt (0 : I32))
        let t15 : U8 ← Mem.load U8 t14
        Ext.mp_append_utf8_bstr.call talloc_ctx_v new_1 (UInt.toU 32 t15)
        let t16 : Ptr ← Mem.load Ptr left_2
        let t17 : Ptr ← Ptr.add t16 1 (SInt.toInt (1 : I32))
        Mem.store left_2 t17
        let t18 : Ptr ← Ptr.add left_2 1 8
        let t19 : U64 ← Mem.load U64 t18
        let t20 : U64 := (t19 - (SInt.toU 64 (1 : I32)))
        Mem.store t18 t20
        let t21 : Ptr ← Mem.load Ptr left_2
        first_ok_3 := t21
    let t22 : Ptr ← Mem.load Ptr new_1
    if (!(t22 != Ptr.null)) then
      let t23 : Agg ← Mem.loadAgg s_p 16 8
      return t23
    let t24 : Ptr ← Mem.load Ptr left_2
    let t25 : Bool ← Ptr.ne first_ok_3 t24
    if t25 then
      Mem.undefine cl26 16
      Mem.store cl26 first_ok_3
      let t27 : Ptr ← Mem.load Ptr left_2
      let t28 : I64 ← Ptr.diff t27 first_ok_3 1
      let t29 : Ptr ← Ptr.add cl26 1 8
      Mem.store t29 (SInt.toU 64 t28)
      let t30 : Agg ← Mem.loadAgg cl26 16 8
      Misc.Bstr_c.bstr_xappend fuel talloc_ctx_v new_1 t30
    let t31 : Agg ← Mem.loadAgg new_1 16 8
    return t31
    : M Agg)
  Mem.popFrame [s_p, new_1, left_2, cl8, cl26]
  pure result

/-- C function `bstr_case_startswith`, ../.mpv/misc/bstr.c:415.
-/
def bstr_case_startswith [Ext.strncasecmp] (fuel : Nat) (s : Agg) (v_prefix : Agg) : M Bool := do
  let s_p ← Mem.alloca 16 8
  let v_prefix_p ← Mem.alloca 16 8
  let start_1 ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg s_p s 8
    Mem.storeAgg v_prefix_p v_prefix 8
    let t1 : Agg ← Mem.loadAgg s_p 16 8
    let t2 : Ptr ← Ptr.add v_prefix_p 1 8
    let t3 : U64 ← Mem.load U64 t2
    let t4 : Agg ← Misc.Bstr_c.bstr_splice fuel t1 (0 : I32) (UInt.toS 32 t3)
    Mem.storeAgg start_1 t4 8
    let t5 : Ptr ← Ptr.add start_1 1 8
    let t6 : U64 ← Mem.load U64 t5
    let t7 : Ptr ← Ptr.add v_prefix_p 1 8
    let t8 : U64 ← Mem.load U64 t7
    let mut t12 : Bool := false
    if (t6 == t8) then
      let t9 : Agg ← Mem.loadAgg start_1 16 8
      let t10 : Agg ← Mem.loadAgg v_prefix_p 16 8
      let t11 : I32 ← Misc.Bstr_c.bstrcasecmp fuel t9 t10
      t12 := (t11 == (0 : I32))
    return ((SInt.ofBool 32 t12) != 0)
    : M Bool)
  Mem.popFrame [s_p, v_prefix_p, start_1]
  pure result

/-- C function `h_to_i`, ../.mpv/misc/bstr.c:427.
-/
def h_to_i (fuel : Nat) (c : U8) : M I32 := do
  let mut c_v : U8 := c
  if ((decide ((UInt.toS 32 c_v) ≥ (48 : I32))) && (decide ((UInt.toS 32 c_v) ≤ (57 : I32)))) then
    let t1 : I32 ← SInt.sub (UInt.toS 32 c_v) (48 : I32)
    return t1
  if ((decide ((UInt.toS 32 c_v) ≥ (97 : I32))) && (decide ((UInt.toS 32 c_v) ≤ (102 : I32)))) then
    let t2 : I32 ← SInt.sub (UInt.toS 32 c_v) (97 : I32)
    let t3 : I32 ← SInt.add t2 (10 : I32)
    return t3
  if ((decide ((UInt.toS 32 c_v) ≥ (65 : I32))) && (decide ((UInt.toS 32 c_v) ≤ (70 : I32)))) then
    let t4 : I32 ← SInt.sub (UInt.toS 32 c_v) (65 : I32)
    let t5 : I32 ← SInt.add t4 (10 : I32)
    return t5
  return (SInt.ofInt 32 (-1))

end Misc.Misc.Bstr_c
