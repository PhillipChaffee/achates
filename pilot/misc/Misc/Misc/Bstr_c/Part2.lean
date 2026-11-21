import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_c
import Misc.Misc.Bstr_h
import Misc.Misc.Ctype_h
import Misc.Ta.Ta_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Bstr_c

/-- C function `bstr_find`, ../.mpv/misc/bstr.c:105.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_find (fuel : Nat) (haystack : Agg) (needle : Agg) : M I32 := do
  let haystack_p ← Mem.alloca 16 8
  let needle_p ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg haystack_p haystack 8
    Mem.storeAgg needle_p needle 8
    let mut i_1 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      let t1 : Ptr ← Ptr.add haystack_p 1 8
      let t2 : U64 ← Mem.load U64 t1
      if !(decide ((SInt.toU 64 i_1) < t2)) then break
      for _ in Once.mk do
        let t3 : Agg ← Mem.loadAgg haystack_p 16 8
        let t4 : Ptr ← Ptr.add haystack_p 1 8
        let t5 : U64 ← Mem.load U64 t4
        let t6 : Agg ← Misc.Bstr_c.bstr_splice fuel t3 i_1 (UInt.toS 32 t5)
        let t7 : Agg ← Mem.loadAgg needle_p 16 8
        let t8 : Bool ← Misc.Bstr_h.bstr_startswith fuel t6 t7
        if t8 then
          return i_1
      let t9 : I32 := i_1
      let t10 : I32 ← SInt.add t9 1
      i_1 := t10
    return (SInt.ofInt 32 (-1))
    : M I32)
  Mem.popFrame [haystack_p, needle_p]
  pure result

/-- C function `bstr_lstrip`, ../.mpv/misc/bstr.c:113.
-/
def bstr_lstrip (fuel : Nat) (str : Agg) : M Agg := do
  let str_p ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg str_p str 8
    for _ in Fuel.mk fuel do
      let t1 : Ptr ← Ptr.add str_p 1 8
      let t2 : U64 ← Mem.load U64 t1
      let mut t6 : Bool := false
      if (t2 != 0) then
        let t3 : Ptr ← Mem.load Ptr str_p
        let t4 : U8 ← Mem.load U8 t3
        let t5 : I32 ← Misc.Ctype_h.mp_isspace fuel (UInt.toS 8 t4)
        t6 := (t5 != 0)
      if !t6 then break
      let t7 : Ptr ← Mem.load Ptr str_p
      let t8 : Ptr ← Ptr.add t7 1 1
      Mem.store str_p t8
      let t9 : Ptr ← Ptr.add str_p 1 8
      let t10 : U64 ← Mem.load U64 t9
      let t11 : U64 := (t10 - 1)
      Mem.store t9 t11
    let t12 : Agg ← Mem.loadAgg str_p 16 8
    return t12
    : M Agg)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_strip`, ../.mpv/misc/bstr.c:122.
-/
def bstr_strip (fuel : Nat) (str : Agg) : M Agg := do
  let str_p ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg str_p str 8
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : Agg ← Misc.Bstr_c.bstr_lstrip fuel t1
    Mem.storeAgg str_p t2 8
    for _ in Fuel.mk fuel do
      let t3 : Ptr ← Ptr.add str_p 1 8
      let t4 : U64 ← Mem.load U64 t3
      let mut t11 : Bool := false
      if (t4 != 0) then
        let t5 : Ptr ← Mem.load Ptr str_p
        let t6 : Ptr ← Ptr.add str_p 1 8
        let t7 : U64 ← Mem.load U64 t6
        let t8 : Ptr ← Ptr.add t5 1 (UInt.toInt (t7 - (SInt.toU 64 (1 : I32))))
        let t9 : U8 ← Mem.load U8 t8
        let t10 : I32 ← Misc.Ctype_h.mp_isspace fuel (UInt.toS 8 t9)
        t11 := (t10 != 0)
      if !t11 then break
      let t12 : Ptr ← Ptr.add str_p 1 8
      let t13 : U64 ← Mem.load U64 t12
      let t14 : U64 := (t13 - 1)
      Mem.store t12 t14
    let t15 : Agg ← Mem.loadAgg str_p 16 8
    return t15
    : M Agg)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_split`, ../.mpv/misc/bstr.c:130.
-/
def bstr_split (fuel : Nat) (str : Agg) (sep : Ptr) (rest : Ptr) : M Agg := do
  let str_p ← Mem.alloca 16 8
  let start_1 ← Mem.alloca 4 4
  let result : Agg ← (do
    Mem.storeAgg str_p str 8
    let mut sep_v : Ptr := sep
    let mut rest_v : Ptr := rest
    Mem.undefine start_1 4
    let t1 : I32 := (0 : I32)
    Mem.store start_1 t1
    for _ in Fuel.mk fuel do
      let t2 : I32 ← Mem.load I32 start_1
      let t3 : Ptr ← Ptr.add str_p 1 8
      let t4 : U64 ← Mem.load U64 t3
      if !(decide ((SInt.toU 64 t2) < t4)) then break
      let mut j10 := false
      for _ in Once.mk do
        let t5 : Ptr ← Mem.load Ptr str_p
        let t6 : I32 ← Mem.load I32 start_1
        let t7 : Ptr ← Ptr.add t5 1 (SInt.toInt t6)
        let t8 : U8 ← Mem.load U8 t7
        let t9 : Ptr ← Libc.strchr sep_v (UInt.toS 32 t8)
        if (!(t9 != Ptr.null)) then
          j10 := true
          break
      if j10 then break
      let t11 : I32 ← Mem.load I32 start_1
      let t12 : I32 ← SInt.add t11 1
      Mem.store start_1 t12
    let t13 : Agg ← Mem.loadAgg str_p 16 8
    let t14 : I32 ← Mem.load I32 start_1
    let t15 : Agg ← Misc.Bstr_h.bstr_cut fuel t13 t14
    Mem.storeAgg str_p t15 8
    let t16 : Agg ← Mem.loadAgg str_p 16 8
    let t17 : I32 ← Misc.Bstr_c.bstrcspn fuel t16 sep_v
    let mut v_end_2 : I32 := t17
    if (rest_v != Ptr.null) then
      let t18 : Agg ← Mem.loadAgg str_p 16 8
      let t19 : Agg ← Misc.Bstr_h.bstr_cut fuel t18 v_end_2
      Mem.storeAgg rest_v t19 8
    let t20 : Agg ← Mem.loadAgg str_p 16 8
    let t21 : Agg ← Misc.Bstr_c.bstr_splice fuel t20 (0 : I32) v_end_2
    return t21
    : M Agg)
  Mem.popFrame [str_p, start_1]
  pure result

/-- C function `bstr_split_tok`, ../.mpv/misc/bstr.c:147.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_split_tok (fuel : Nat) (str : Agg) (tok : Ptr) (out_left : Ptr) (out_right : Ptr) : M Bool := do
  let str_p ← Mem.alloca 16 8
  let bsep_1 ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg str_p str 8
    let mut tok_v : Ptr := tok
    let mut out_left_v : Ptr := out_left
    let mut out_right_v : Ptr := out_right
    let t1 : Agg ← Misc.Bstr_h.bstr0 fuel tok_v
    Mem.storeAgg bsep_1 t1 8
    let t2 : Agg ← Mem.loadAgg str_p 16 8
    let t3 : Agg ← Mem.loadAgg bsep_1 16 8
    let t4 : I32 ← Misc.Bstr_c.bstr_find fuel t2 t3
    let mut pos_2 : I32 := t4
    if (decide (pos_2 < (0 : I32))) then
      let t5 : Ptr ← Ptr.add str_p 1 8
      let t6 : U64 ← Mem.load U64 t5
      let t7 : I32 := (UInt.toS 32 t6)
      pos_2 := t7
    let t8 : Agg ← Mem.loadAgg str_p 16 8
    let t9 : Agg ← Misc.Bstr_c.bstr_splice fuel t8 (0 : I32) pos_2
    Mem.storeAgg out_left_v t9 8
    let t10 : Agg ← Mem.loadAgg str_p 16 8
    let t11 : Ptr ← Ptr.add bsep_1 1 8
    let t12 : U64 ← Mem.load U64 t11
    let t13 : Agg ← Misc.Bstr_h.bstr_cut fuel t10 (UInt.toS 32 ((SInt.toU 64 pos_2) + t12))
    Mem.storeAgg out_right_v t13 8
    let t14 : Ptr ← Ptr.add str_p 1 8
    let t15 : U64 ← Mem.load U64 t14
    return ((SInt.ofBool 32 ((SInt.toU 64 pos_2) != t15)) != 0)
    : M Bool)
  Mem.popFrame [str_p, bsep_1]
  pure result

/-- C function `bstrtoll`, ../.mpv/misc/bstr.c:175.
-/
def bstrtoll [Ext.strtoll] (fuel : Nat) (str : Agg) (rest : Ptr) (base : I32) : M I64 := do
  let str_p ← Mem.alloca 16 8
  let buf_1 ← Mem.alloca 51 1
  let endptr_3 ← Mem.alloca 8 8
  let result : I64 ← (do
    Mem.storeAgg str_p str 8
    let mut rest_v : Ptr := rest
    let mut base_v : I32 := base
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : Agg ← Misc.Bstr_c.bstr_lstrip fuel t1
    Mem.storeAgg str_p t2 8
    Mem.undefine buf_1 51
    let t3 : Ptr ← Ptr.add str_p 1 8
    let t4 : U64 ← Mem.load U64 t3
    let mut t7 : U64 := default
    if (decide (t4 > (SInt.toU 64 (50 : I32)))) then
      t7 := (SInt.toU 64 (50 : I32))
    else
      let t5 : Ptr ← Ptr.add str_p 1 8
      let t6 : U64 ← Mem.load U64 t5
      t7 := t6
    let mut len_2 : I32 := (UInt.toS 32 t7)
    let t8 : Ptr ← Mem.load Ptr str_p
    let t9 : Ptr ← Libc.memcpy buf_1 t8 (SInt.toU 64 len_2)
    let t10 : Ptr ← Ptr.add buf_1 1 (SInt.toInt len_2)
    let t11 : I8 := (SInt.toS 8 (0 : I32))
    Mem.store t10 t11
    Mem.undefine endptr_3 8
    let t12 : I64 ← Ext.strtoll.call buf_1 endptr_3 base_v
    let mut r_4 : I64 := t12
    if (rest_v != Ptr.null) then
      let t13 : Agg ← Mem.loadAgg str_p 16 8
      let t14 : Ptr ← Mem.load Ptr endptr_3
      let t15 : I64 ← Ptr.diff t14 buf_1 1
      let t16 : Agg ← Misc.Bstr_h.bstr_cut fuel t13 (SInt.toS 32 t15)
      Mem.storeAgg rest_v t16 8
    return r_4
    : M I64)
  Mem.popFrame [str_p, buf_1, endptr_3]
  pure result

/-- C function `bstrtod`, ../.mpv/misc/bstr.c:189.
-/
def bstrtod [Ext.strtod] (fuel : Nat) (str : Agg) (rest : Ptr) : M F64 := do
  let str_p ← Mem.alloca 16 8
  let buf_1 ← Mem.alloca 101 1
  let endptr_3 ← Mem.alloca 8 8
  let result : F64 ← (do
    Mem.storeAgg str_p str 8
    let mut rest_v : Ptr := rest
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : Agg ← Misc.Bstr_c.bstr_lstrip fuel t1
    Mem.storeAgg str_p t2 8
    Mem.undefine buf_1 101
    let t3 : Ptr ← Ptr.add str_p 1 8
    let t4 : U64 ← Mem.load U64 t3
    let mut t7 : U64 := default
    if (decide (t4 > (SInt.toU 64 (100 : I32)))) then
      t7 := (SInt.toU 64 (100 : I32))
    else
      let t5 : Ptr ← Ptr.add str_p 1 8
      let t6 : U64 ← Mem.load U64 t5
      t7 := t6
    let mut len_2 : I32 := (UInt.toS 32 t7)
    let t8 : Ptr ← Mem.load Ptr str_p
    let t9 : Ptr ← Libc.memcpy buf_1 t8 (SInt.toU 64 len_2)
    let t10 : Ptr ← Ptr.add buf_1 1 (SInt.toInt len_2)
    let t11 : I8 := (SInt.toS 8 (0 : I32))
    Mem.store t10 t11
    Mem.undefine endptr_3 8
    let t12 : F64 ← Ext.strtod.call buf_1 endptr_3
    let mut r_4 : F64 := t12
    if (rest_v != Ptr.null) then
      let t13 : Agg ← Mem.loadAgg str_p 16 8
      let t14 : Ptr ← Mem.load Ptr endptr_3
      let t15 : I64 ← Ptr.diff t14 buf_1 1
      let t16 : Agg ← Misc.Bstr_h.bstr_cut fuel t13 (SInt.toS 32 t15)
      Mem.storeAgg rest_v t16 8
    return r_4
    : M F64)
  Mem.popFrame [str_p, buf_1, endptr_3]
  pure result

/-- C function `bstr_splitchar`, ../.mpv/misc/bstr.c:203.
-/
def bstr_splitchar (fuel : Nat) (str : Agg) (rest : Ptr) (c : I8) : M Agg := do
  let str_p ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg str_p str 8
    let mut rest_v : Ptr := rest
    let mut c_v : I8 := c
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : I32 ← Misc.Bstr_c.bstrchr fuel t1 (SInt.toS 32 c_v)
    let mut pos_1 : I32 := t2
    if (decide (pos_1 < (0 : I32))) then
      let t3 : Ptr ← Ptr.add str_p 1 8
      let t4 : U64 ← Mem.load U64 t3
      let t5 : I32 := (UInt.toS 32 t4)
      pos_1 := t5
    if (rest_v != Ptr.null) then
      let t6 : Agg ← Mem.loadAgg str_p 16 8
      let t7 : I32 ← SInt.add pos_1 (1 : I32)
      let t8 : Agg ← Misc.Bstr_h.bstr_cut fuel t6 t7
      Mem.storeAgg rest_v t8 8
    let t9 : Agg ← Mem.loadAgg str_p 16 8
    let t10 : I32 ← SInt.add pos_1 (1 : I32)
    let t11 : Agg ← Misc.Bstr_c.bstr_splice fuel t9 (0 : I32) t10
    return t11
    : M Agg)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_strip_linebreaks`, ../.mpv/misc/bstr.c:213.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_strip_linebreaks (fuel : Nat) (str : Agg) : M Agg := do
  let str_p ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg str_p str 8
    let t1 : Agg ← Mem.loadAgg str_p 16 8
    let t2 : Bool ← Misc.Bstr_h.bstr_endswith0 fuel t1 Statics.str_19
    if t2 then
      let t3 : Agg ← Mem.loadAgg str_p 16 8
      let t4 : Ptr ← Ptr.add str_p 1 8
      let t5 : U64 ← Mem.load U64 t4
      let t6 : Agg ← Misc.Bstr_c.bstr_splice fuel t3 (0 : I32) (UInt.toS 32 (t5 - (SInt.toU 64 (2 : I32))))
      Mem.storeAgg str_p t6 8
    else
      let t7 : Agg ← Mem.loadAgg str_p 16 8
      let t8 : Bool ← Misc.Bstr_h.bstr_endswith0 fuel t7 Statics.str_20
      if t8 then
        let t9 : Agg ← Mem.loadAgg str_p 16 8
        let t10 : Ptr ← Ptr.add str_p 1 8
        let t11 : U64 ← Mem.load U64 t10
        let t12 : Agg ← Misc.Bstr_c.bstr_splice fuel t9 (0 : I32) (UInt.toS 32 (t11 - (SInt.toU 64 (1 : I32))))
        Mem.storeAgg str_p t12 8
    let t13 : Agg ← Mem.loadAgg str_p 16 8
    return t13
    : M Agg)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_eatstart`, ../.mpv/misc/bstr.c:223.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_eatstart (fuel : Nat) (s : Ptr) (v_prefix : Agg) : M Bool := do
  let v_prefix_p ← Mem.alloca 16 8
  let result : Bool ← (do
    let mut s_v : Ptr := s
    Mem.storeAgg v_prefix_p v_prefix 8
    let t1 : Agg ← Mem.loadAgg s_v 16 8
    let t2 : Agg ← Mem.loadAgg v_prefix_p 16 8
    let t3 : Bool ← Misc.Bstr_h.bstr_startswith fuel t1 t2
    if (!t3) then
      return ((0 : I32) != 0)
    let t4 : Agg ← Mem.loadAgg s_v 16 8
    let t5 : Ptr ← Ptr.add v_prefix_p 1 8
    let t6 : U64 ← Mem.load U64 t5
    let t7 : Agg ← Misc.Bstr_h.bstr_cut fuel t4 (UInt.toS 32 t6)
    Mem.storeAgg s_v t7 8
    return ((1 : I32) != 0)
    : M Bool)
  Mem.popFrame [v_prefix_p]
  pure result

/-- C function `bstr_eatend`, ../.mpv/misc/bstr.c:231.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def bstr_eatend (fuel : Nat) (s : Ptr) (v_prefix : Agg) : M Bool := do
  let v_prefix_p ← Mem.alloca 16 8
  let result : Bool ← (do
    let mut s_v : Ptr := s
    Mem.storeAgg v_prefix_p v_prefix 8
    let t1 : Agg ← Mem.loadAgg s_v 16 8
    let t2 : Agg ← Mem.loadAgg v_prefix_p 16 8
    let t3 : Bool ← Misc.Bstr_h.bstr_endswith fuel t1 t2
    if (!t3) then
      return ((0 : I32) != 0)
    let t4 : Ptr ← Ptr.add s_v 1 8
    let t5 : U64 ← Mem.load U64 t4
    let t6 : Ptr ← Ptr.add v_prefix_p 1 8
    let t7 : U64 ← Mem.load U64 t6
    let t8 : U64 := (t5 - t7)
    Mem.store t4 t8
    return ((1 : I32) != 0)
    : M Bool)
  Mem.popFrame [v_prefix_p]
  pure result

/-- C function `bstr_lower`, ../.mpv/misc/bstr.c:239.
-/
def bstr_lower (fuel : Nat) (str : Agg) : M Unit := do
  let str_p ← Mem.alloca 16 8
  let result : Unit ← (do
    Mem.storeAgg str_p str 8
    let mut i_1 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      let t1 : Ptr ← Ptr.add str_p 1 8
      let t2 : U64 ← Mem.load U64 t1
      if !(decide ((SInt.toU 64 i_1) < t2)) then break
      for _ in Once.mk do
        let t3 : Ptr ← Mem.load Ptr str_p
        let t4 : Ptr ← Ptr.add t3 1 (SInt.toInt i_1)
        let t5 : Ptr ← Mem.load Ptr str_p
        let t6 : Ptr ← Ptr.add t5 1 (SInt.toInt i_1)
        let t7 : U8 ← Mem.load U8 t6
        let t8 : I8 ← Misc.Ctype_h.mp_tolower fuel (UInt.toS 8 t7)
        let t9 : U8 := (SInt.toU 8 t8)
        Mem.store t4 t9
      let t10 : I32 := i_1
      let t11 : I32 ← SInt.add t10 1
      i_1 := t11
    pure ()
    : M Unit)
  Mem.popFrame [str_p]
  pure result

/-- C function `bstr_case_endswith`, ../.mpv/misc/bstr.c:421.
-/
def bstr_case_endswith [Ext.strncasecmp] (fuel : Nat) (s : Agg) (suffix : Agg) : M Bool := do
  let s_p ← Mem.alloca 16 8
  let suffix_p ← Mem.alloca 16 8
  let v_end_1 ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg s_p s 8
    Mem.storeAgg suffix_p suffix 8
    let t1 : Agg ← Mem.loadAgg s_p 16 8
    let t2 : Ptr ← Ptr.add suffix_p 1 8
    let t3 : U64 ← Mem.load U64 t2
    let t4 : Agg ← Misc.Bstr_h.bstr_cut fuel t1 (UInt.toS 32 (UInt.neg t3))
    Mem.storeAgg v_end_1 t4 8
    let t5 : Ptr ← Ptr.add v_end_1 1 8
    let t6 : U64 ← Mem.load U64 t5
    let t7 : Ptr ← Ptr.add suffix_p 1 8
    let t8 : U64 ← Mem.load U64 t7
    let mut t12 : Bool := false
    if (t6 == t8) then
      let t9 : Agg ← Mem.loadAgg v_end_1 16 8
      let t10 : Agg ← Mem.loadAgg suffix_p 16 8
      let t11 : I32 ← Misc.Bstr_c.bstrcasecmp fuel t9 t10
      t12 := (t11 == (0 : I32))
    return ((SInt.ofBool 32 t12) != 0)
    : M Bool)
  Mem.popFrame [s_p, suffix_p, v_end_1]
  pure result

/-- C function `bstr_decode_hex`, ../.mpv/misc/bstr.c:439.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def bstr_decode_hex (fuel : Nat) (talloc_ctx : Ptr) (hex : Agg) (out : Ptr) : M Bool := do
  let hex_p ← Mem.alloca 16 8
  let cl27 ← Mem.alloca 16 8
  let result : Bool ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    Mem.storeAgg hex_p hex 8
    let mut out_v : Ptr := out
    if (!(out_v != Ptr.null)) then
      return ((0 : I32) != 0)
    let t1 : Ptr ← Ptr.add hex_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    let t3 : U64 ← UInt.div t2 (SInt.toU 64 (2 : I32))
    let t4 : U64 ← Talloc.ta_calc_array_size (1 : U64) t3
    let t5 : Ptr ← Talloc.ta_alloc_size talloc_ctx_v t4
    let t6 : Ptr ← Talloc.ta_dbg_set_loc t5 Statics.str_25
    let t7 : Ptr ← Ta.Ta_h.ta_oom_p fuel t6
    let mut arr_1 : Ptr := t7
    let mut len_2 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      let t8 : Ptr ← Ptr.add hex_p 1 8
      let t9 : U64 ← Mem.load U64 t8
      if !(decide (t9 ≥ (SInt.toU 64 (2 : I32)))) then break
      let t10 : Ptr ← Mem.load Ptr hex_p
      let t11 : Ptr ← Ptr.add t10 1 (SInt.toInt (0 : I32))
      let t12 : U8 ← Mem.load U8 t11
      let t13 : I32 ← Misc.Bstr_c.h_to_i fuel t12
      let mut a_3 : I32 := t13
      let t14 : Ptr ← Mem.load Ptr hex_p
      let t15 : Ptr ← Ptr.add t14 1 (SInt.toInt (1 : I32))
      let t16 : U8 ← Mem.load U8 t15
      let t17 : I32 ← Misc.Bstr_c.h_to_i fuel t16
      let mut b_4 : I32 := t17
      let t18 : Agg ← Mem.loadAgg hex_p 16 8
      let t19 : Ptr ← Ptr.add hex_p 1 8
      let t20 : U64 ← Mem.load U64 t19
      let t21 : Agg ← Misc.Bstr_c.bstr_splice fuel t18 (2 : I32) (UInt.toS 32 t20)
      Mem.storeAgg hex_p t21 8
      if ((decide (a_3 < (0 : I32))) || (decide (b_4 < (0 : I32)))) then
        Talloc.ta_free arr_1
        return ((0 : I32) != 0)
      let t22 : I32 := len_2
      let t23 : I32 ← SInt.add t22 1
      len_2 := t23
      let t24 : Ptr ← Ptr.add arr_1 1 (SInt.toInt t22)
      let t25 : I32 ← SInt.shl a_3 (SInt.toInt (4 : I32))
      let t26 : I8 := (SInt.toS 8 (SInt.bor t25 b_4))
      Mem.store t24 t26
    Mem.undefine cl27 16
    Mem.store cl27 arr_1
    let t28 : Ptr ← Ptr.add cl27 1 8
    Mem.store t28 (SInt.toU 64 len_2)
    let t29 : Agg ← Mem.loadAgg cl27 16 8
    Mem.storeAgg out_v t29 8
    return ((1 : I32) != 0)
    : M Bool)
  Mem.popFrame [hex_p, cl27]
  pure result

end Misc.Misc.Bstr_c
