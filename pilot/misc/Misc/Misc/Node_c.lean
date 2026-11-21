import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_h
import Misc.Misc.Bstr_h.Part2
import Misc.Ta.Ta_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Node_c

/-- C function `node_init`, ../.mpv/misc/node.c:12.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def node_init (fuel : Nat) (dst : Ptr) (format : I32) (parent : Ptr) : M Unit := do
  let cl9 ← Mem.alloca 16 8
  let result : Unit ← (do
    let mut dst_v : Ptr := dst
    let mut format_v : I32 := format
    let mut parent_v : Ptr := parent
    let mut t1 : Unit := default
    if (((((((format_v == (8 : I32)) || (format_v == (7 : I32))) || (format_v == (3 : I32))) || (format_v == (4 : I32))) || (format_v == (5 : I32))) || (format_v == (9 : I32))) || (format_v == (0 : I32))) then
      t1 := ()
    else
      Libc.«__assert_fail» Statics.str_113 Statics.str_114 (SInt.toU 32 (18 : I32)) Statics.str_115
      t1 := ()
    let mut ta_parent_1 : Ptr := Ptr.null
    if (parent_v != Ptr.null) then
      let t2 : Ptr ← Ptr.add parent_v 1 8
      let t3 : U32 ← Mem.load U32 t2
      let mut t6 : Bool := true
      if !(t3 == (SInt.toU 32 (8 : I32))) then
        let t4 : Ptr ← Ptr.add parent_v 1 8
        let t5 : U32 ← Mem.load U32 t4
        t6 := (t5 == (SInt.toU 32 (7 : I32)))
      let mut t7 : Unit := default
      if t6 then
        t7 := ()
      else
        Libc.«__assert_fail» Statics.str_116 Statics.str_114 (SInt.toU 32 (23 : I32)) Statics.str_115
        t7 := ()
      let t8 : Ptr ← Mem.load Ptr parent_v
      ta_parent_1 := t8
    Mem.undefine cl9 16
    Mem.zero cl9 8
    let t10 : Ptr ← Ptr.add cl9 1 8
    Mem.store t10 (SInt.toU 32 format_v)
    let t11 : Agg ← Mem.loadAgg cl9 16 8
    Mem.storeAgg dst_v t11 8
    if ((format_v == (8 : I32)) || (format_v == (7 : I32))) then
      let t12 : Ptr ← Talloc.ta_zalloc_size ta_parent_1 (24 : U64)
      let t13 : Ptr ← Talloc.ta_dbg_set_loc t12 Statics.str_117
      let t14 : Ptr ← Ta.Ta_h.ta_oom_p fuel t13
      Mem.store dst_v t14
    if (format_v == (9 : I32)) then
      let t15 : Ptr ← Talloc.ta_zalloc_size ta_parent_1 (16 : U64)
      let t16 : Ptr ← Talloc.ta_dbg_set_loc t15 Statics.str_118
      let t17 : Ptr ← Ta.Ta_h.ta_oom_p fuel t16
      Mem.store dst_v t17
    pure ()
    : M Unit)
  Mem.popFrame [cl9]
  pure result

/-- C function `node_map_add`, ../.mpv/misc/node.c:48.
-/
def node_map_add [Ext.node_map_badd] (fuel : Nat) (dst : Ptr) (key : Ptr) (format : I32) : M Ptr := do
  let mut dst_v : Ptr := dst
  let mut key_v : Ptr := key
  let mut format_v : I32 := format
  let mut t1 : Unit := default
  if (key_v != Ptr.null) then
    t1 := ()
  else
    Libc.«__assert_fail» Statics.str_122 Statics.str_114 (SInt.toU 32 (50 : I32)) Statics.str_123
    t1 := ()
  let t2 : Agg ← Misc.Bstr_h.bstr0 fuel key_v
  let t3 : Ptr ← Ext.node_map_badd.call dst_v t2 format_v
  return t3

/-- C function `node_map_add_string`, ../.mpv/misc/node.c:70.
-/
def node_map_add_string [Ext.node_map_badd] [Ext.ta_xstrdup] (fuel : Nat) (dst : Ptr) (key : Ptr) (val : Ptr) : M Unit := do
  let mut dst_v : Ptr := dst
  let mut key_v : Ptr := key
  let mut val_v : Ptr := val
  let mut t1 : Unit := default
  if (val_v != Ptr.null) then
    t1 := ()
  else
    Libc.«__assert_fail» Statics.str_129 Statics.str_114 (SInt.toU 32 (72 : I32)) Statics.str_130
    t1 := ()
  let t2 : Ptr ← Misc.Node_c.node_map_add fuel dst_v key_v (0 : I32)
  let mut entry_1 : Ptr := t2
  let t3 : Ptr ← Ptr.add entry_1 1 8
  let t4 : U32 := (SInt.toU 32 (1 : I32))
  Mem.store t3 t4
  let t5 : Ptr ← Mem.load Ptr dst_v
  let t6 : Ptr ← Ext.ta_xstrdup.call t5 val_v
  Mem.store entry_1 t6
  pure ()

/-- C function `node_map_add_bstr`, ../.mpv/misc/node.c:79.
-/
def node_map_add_bstr [Ext.node_map_badd] [Ext.ta_xstrdup] [Ext.ta_xstrndup] (fuel : Nat) (dst : Ptr) (key : Ptr) (val : Agg) : M Unit := do
  let val_p ← Mem.alloca 16 8
  let result : Unit ← (do
    let mut dst_v : Ptr := dst
    let mut key_v : Ptr := key
    Mem.storeAgg val_p val 8
    let t1 : Ptr ← Mem.load Ptr val_p
    let mut t2 : Unit := default
    if (t1 != Ptr.null) then
      t2 := ()
    else
      Libc.«__assert_fail» Statics.str_131 Statics.str_114 (SInt.toU 32 (81 : I32)) Statics.str_132
      t2 := ()
    let t3 : Ptr ← Misc.Node_c.node_map_add fuel dst_v key_v (0 : I32)
    let mut entry_1 : Ptr := t3
    let t4 : Ptr ← Ptr.add entry_1 1 8
    let t5 : U32 := (SInt.toU 32 (1 : I32))
    Mem.store t4 t5
    let t6 : Ptr ← Mem.load Ptr dst_v
    let t7 : Agg ← Mem.loadAgg val_p 16 8
    let t8 : Ptr ← Misc.Bstr_h.bstrto0 fuel t6 t7
    Mem.store entry_1 t8
    pure ()
    : M Unit)
  Mem.popFrame [val_p]
  pure result

/-- C function `node_map_add_int64`, ../.mpv/misc/node.c:88.
-/
def node_map_add_int64 [Ext.node_map_badd] (fuel : Nat) (dst : Ptr) (key : Ptr) (v : I64) : M Unit := do
  let mut dst_v : Ptr := dst
  let mut key_v : Ptr := key
  let mut v_v : I64 := v
  let t1 : Ptr ← Misc.Node_c.node_map_add fuel dst_v key_v (4 : I32)
  Mem.store t1 v_v
  pure ()

/-- C function `node_map_add_double`, ../.mpv/misc/node.c:93.
-/
def node_map_add_double [Ext.node_map_badd] (fuel : Nat) (dst : Ptr) (key : Ptr) (v : F64) : M Unit := do
  let mut dst_v : Ptr := dst
  let mut key_v : Ptr := key
  let mut v_v : F64 := v
  let t1 : Ptr ← Misc.Node_c.node_map_add fuel dst_v key_v (5 : I32)
  Mem.store t1 v_v
  pure ()

/-- C function `node_map_add_flag`, ../.mpv/misc/node.c:98.
-/
def node_map_add_flag [Ext.node_map_badd] (fuel : Nat) (dst : Ptr) (key : Ptr) (v : Bool) : M Unit := do
  let mut dst_v : Ptr := dst
  let mut key_v : Ptr := key
  let mut v_v : Bool := v
  let t1 : Ptr ← Misc.Node_c.node_map_add fuel dst_v key_v (3 : I32)
  let t2 : I32 := (SInt.ofBool 32 v_v)
  Mem.store t1 t2
  pure ()

/-- C function `node_map_bget`, ../.mpv/misc/node.c:108.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def node_map_bget (fuel : Nat) (src : Ptr) (key : Agg) : M Ptr := do
  let key_p ← Mem.alloca 16 8
  let result : Ptr ← (do
    let mut src_v : Ptr := src
    Mem.storeAgg key_p key 8
    let t1 : Ptr ← Ptr.add src_v 1 8
    let t2 : U32 ← Mem.load U32 t1
    if (t2 != (SInt.toU 32 (8 : I32))) then
      return Ptr.null
    let mut i_1 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      let t3 : Ptr ← Mem.load Ptr src_v
      let t4 : I32 ← Mem.load I32 t3
      if !(decide (i_1 < t4)) then break
      for _ in Once.mk do
        let t5 : Agg ← Mem.loadAgg key_p 16 8
        let t6 : Ptr ← Mem.load Ptr src_v
        let t7 : Ptr ← Ptr.add t6 1 16
        let t8 : Ptr ← Mem.load Ptr t7
        let t9 : Ptr ← Ptr.add t8 8 (SInt.toInt i_1)
        let t10 : Ptr ← Mem.load Ptr t9
        let t11 : Bool ← Misc.Bstr_h.bstr_equals0 fuel t5 t10
        if t11 then
          let t12 : Ptr ← Mem.load Ptr src_v
          let t13 : Ptr ← Ptr.add t12 1 8
          let t14 : Ptr ← Mem.load Ptr t13
          let t15 : Ptr ← Ptr.add t14 16 (SInt.toInt i_1)
          return t15
      let t16 : I32 := i_1
      let t17 : I32 ← SInt.add t16 1
      i_1 := t17
    return Ptr.null
    : M Ptr)
  Mem.popFrame [key_p]
  pure result

/-- C function `node_map_get`, ../.mpv/misc/node.c:103.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def node_map_get (fuel : Nat) (src : Ptr) (key : Ptr) : M Ptr := do
  let mut src_v : Ptr := src
  let mut key_v : Ptr := key
  let t1 : Agg ← Misc.Bstr_h.bstr0 fuel key_v
  let t2 : Ptr ← Misc.Node_c.node_map_bget fuel src_v t1
  return t2

mutual

/-- C function `equal_mpv_value`, ../.mpv/misc/node.c:123.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def equal_mpv_value (fuel : Nat) (a : Ptr) (b : Ptr) (format : I32) : M Bool :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let mut a_v : Ptr := a
    let mut b_v : Ptr := b
    let mut format_v : I32 := format
    let t1 := format_v
    let t2 : Nat := if t1 == (0 : I32) then 0 else if t1 == (1 : I32) || t1 == (2 : I32) then 1 else if t1 == (3 : I32) then 2 else if t1 == (4 : I32) then 3 else if t1 == (5 : I32) then 4 else if t1 == (6 : I32) then 5 else if t1 == (9 : I32) then 6 else if t1 == (7 : I32) || t1 == (8 : I32) then 7 else 8
    for _ in Once.mk do
      if t2 ≤ 0 then
        return ((1 : I32) != 0)
      if t2 ≤ 1 then
        let t3 : Ptr ← Mem.load Ptr a_v
        let t4 : Ptr ← Mem.load Ptr b_v
        let t5 : I32 ← Libc.strcmp t3 t4
        return ((SInt.ofBool 32 (t5 == (0 : I32))) != 0)
      if t2 ≤ 2 then
        let t6 : I32 ← Mem.load I32 a_v
        let t7 : I32 ← Mem.load I32 b_v
        return ((SInt.ofBool 32 (t6 == t7)) != 0)
      if t2 ≤ 3 then
        let t8 : I64 ← Mem.load I64 a_v
        let t9 : I64 ← Mem.load I64 b_v
        return ((SInt.ofBool 32 (t8 == t9)) != 0)
      if t2 ≤ 4 then
        let t10 : F64 ← Mem.load F64 a_v
        let t11 : F64 ← Mem.load F64 b_v
        return ((SInt.ofBool 32 (t10 == t11)) != 0)
      if t2 ≤ 5 then
        let t12 : Bool ← Misc.Node_c.equal_mpv_node fuel a_v b_v
        return t12
      if t2 ≤ 6 then
        let mut a_r_1 : Ptr := a_v
        let mut b_r_2 : Ptr := b_v
        let t13 : Ptr ← Ptr.add a_r_1 1 8
        let t14 : U64 ← Mem.load U64 t13
        let t15 : Ptr ← Ptr.add b_r_2 1 8
        let t16 : U64 ← Mem.load U64 t15
        if (t14 != t16) then
          return ((0 : I32) != 0)
        let t17 : Ptr ← Mem.load Ptr a_r_1
        let t18 : Ptr ← Mem.load Ptr b_r_2
        let t19 : Ptr ← Ptr.add a_r_1 1 8
        let t20 : U64 ← Mem.load U64 t19
        let t21 : I32 ← Libc.memcmp t17 t18 t20
        return ((SInt.ofBool 32 (t21 == (0 : I32))) != 0)
      if t2 ≤ 7 then
        let t22 : Ptr ← Mem.load Ptr a_v
        let mut l_a_3 : Ptr := t22
        let t23 : Ptr ← Mem.load Ptr b_v
        let mut l_b_4 : Ptr := t23
        let t24 : I32 ← Mem.load I32 l_a_3
        let t25 : I32 ← Mem.load I32 l_b_4
        if (t24 != t25) then
          return ((0 : I32) != 0)
        let mut n_5 : I32 := (0 : I32)
        for _ in Fuel.mk fuel do
          let t26 : I32 ← Mem.load I32 l_a_3
          if !(decide (n_5 < t26)) then break
          for _ in Once.mk do
            if (format_v == (8 : I32)) then
              let t27 : Ptr ← Ptr.add l_a_3 1 16
              let t28 : Ptr ← Mem.load Ptr t27
              let t29 : Ptr ← Ptr.add t28 8 (SInt.toInt n_5)
              let t30 : Ptr ← Mem.load Ptr t29
              let t31 : Ptr ← Ptr.add l_b_4 1 16
              let t32 : Ptr ← Mem.load Ptr t31
              let t33 : Ptr ← Ptr.add t32 8 (SInt.toInt n_5)
              let t34 : Ptr ← Mem.load Ptr t33
              let t35 : I32 ← Libc.strcmp t30 t34
              if (t35 != (0 : I32)) then
                return ((0 : I32) != 0)
            let t36 : Ptr ← Ptr.add l_a_3 1 8
            let t37 : Ptr ← Mem.load Ptr t36
            let t38 : Ptr ← Ptr.add t37 16 (SInt.toInt n_5)
            let t39 : Ptr ← Ptr.add l_b_4 1 8
            let t40 : Ptr ← Mem.load Ptr t39
            let t41 : Ptr ← Ptr.add t40 16 (SInt.toInt n_5)
            let t42 : Bool ← Misc.Node_c.equal_mpv_node fuel t38 t41
            if (!t42) then
              return ((0 : I32) != 0)
          let t43 : I32 := n_5
          let t44 : I32 ← SInt.add t43 1
          n_5 := t44
        return ((1 : I32) != 0)
    let mut t45 : Unit := default
    if (!(Statics.str_133 != Ptr.null)) then
      t45 := ()
    else
      Libc.«__assert_fail» Statics.str_134 Statics.str_114 (SInt.toU 32 (162 : I32)) Statics.str_135
      t45 := ()
    Libc.abort
    ub "control reached the end of a function that returns a value"
termination_by structural fuel

/-- C function `equal_mpv_node`, ../.mpv/misc/node.c:166.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def equal_mpv_node (fuel : Nat) (a : Ptr) (b : Ptr) : M Bool :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let mut a_v : Ptr := a
    let mut b_v : Ptr := b
    let t1 : Ptr ← Ptr.add a_v 1 8
    let t2 : U32 ← Mem.load U32 t1
    let t3 : Ptr ← Ptr.add b_v 1 8
    let t4 : U32 ← Mem.load U32 t3
    if (t2 != t4) then
      return ((0 : I32) != 0)
    let t5 : Ptr ← Ptr.add a_v 1 8
    let t6 : U32 ← Mem.load U32 t5
    let t7 : Bool ← Misc.Node_c.equal_mpv_value fuel a_v b_v (UInt.toS 32 t6)
    return t7
termination_by structural fuel

end

end Misc.Misc.Node_c
