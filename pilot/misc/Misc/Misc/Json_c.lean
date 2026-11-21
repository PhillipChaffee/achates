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

namespace Misc.Misc.Json_c

/-- C function `eat_c`, ../.mpv/misc/json.c:59.
-/
def eat_c (fuel : Nat) (s : Ptr) (c : I8) : M Bool := do
  let mut s_v : Ptr := s
  let mut c_v : I8 := c
  let t1 : Ptr ← Mem.load Ptr s_v
  let t2 : I8 ← Mem.load I8 t1
  if ((SInt.toS 32 t2) == (SInt.toS 32 c_v)) then
    let t3 : Ptr ← Mem.load Ptr s_v
    let t4 : Ptr ← Ptr.add t3 1 (SInt.toInt (1 : I32))
    Mem.store s_v t4
    return ((1 : I32) != 0)
  return ((0 : I32) != 0)

/-- C function `eat_ws`, ../.mpv/misc/json.c:68.
-/
def eat_ws (fuel : Nat) (src : Ptr) : M Unit := do
  let mut src_v : Ptr := src
  for _ in Fuel.mk fuel do
    if !((1 : I32) != 0) then break
    let t1 : Ptr ← Mem.load Ptr src_v
    let t2 : I8 ← Mem.load I8 t1
    let mut c_1 : I8 := t2
    if (((((SInt.toS 32 c_1) != (32 : I32)) && ((SInt.toS 32 c_1) != (9 : I32))) && ((SInt.toS 32 c_1) != (10 : I32))) && ((SInt.toS 32 c_1) != (13 : I32))) then
      return ()
    let t3 : Ptr ← Mem.load Ptr src_v
    let t4 : Ptr ← Ptr.add t3 1 (SInt.toInt (1 : I32))
    Mem.store src_v t4
  pure ()

/-- C function `json_skip_whitespace`, ../.mpv/misc/json.c:78.
-/
def json_skip_whitespace (fuel : Nat) (src : Ptr) : M Unit := do
  let mut src_v : Ptr := src
  Misc.Json_c.eat_ws fuel src_v
  pure ()

/-- C function `read_id`, ../.mpv/misc/json.c:83.
-/
def read_id [Ext.ta_xstrndup] (fuel : Nat) (ta_parent : Ptr) (dst : Ptr) (src : Ptr) : M I32 := do
  let mut ta_parent_v : Ptr := ta_parent
  let mut dst_v : Ptr := dst
  let mut src_v : Ptr := src
  let t1 : Ptr ← Mem.load Ptr src_v
  let mut start_1 : Ptr := t1
  let t2 : Ptr ← Mem.load Ptr src_v
  let t3 : I8 ← Mem.load I8 t2
  let t4 : I32 ← Misc.Ctype_h.mp_isalpha fuel t3
  let mut t7 : Bool := false
  if (!(t4 != 0)) then
    let t5 : Ptr ← Mem.load Ptr src_v
    let t6 : I8 ← Mem.load I8 t5
    t7 := ((SInt.toS 32 t6) != (95 : I32))
  if t7 then
    return (SInt.ofInt 32 (-1))
  for _ in Fuel.mk fuel do
    let t8 : Ptr ← Mem.load Ptr src_v
    let t9 : I8 ← Mem.load I8 t8
    let t10 : I32 ← Misc.Ctype_h.mp_isalnum fuel t9
    let mut t13 : Bool := true
    if !(t10 != 0) then
      let t11 : Ptr ← Mem.load Ptr src_v
      let t12 : I8 ← Mem.load I8 t11
      t13 := ((SInt.toS 32 t12) == (95 : I32))
    if !t13 then break
    let t14 : Ptr ← Mem.load Ptr src_v
    let t15 : Ptr ← Ptr.add t14 1 (SInt.toInt (1 : I32))
    Mem.store src_v t15
  let t16 : Ptr ← Mem.load Ptr src_v
  let t17 : I8 ← Mem.load I8 t16
  if ((SInt.toS 32 t17) == (32 : I32)) then
    let t18 : Ptr ← Mem.load Ptr src_v
    let t19 : I8 := (SInt.toS 8 (0 : I32))
    Mem.store t18 t19
    let t20 : Ptr ← Mem.load Ptr src_v
    let t21 : Ptr ← Ptr.add t20 1 (SInt.toInt (1 : I32))
    Mem.store src_v t21
  else
    let t22 : Ptr ← Mem.load Ptr src_v
    let t23 : I64 ← Ptr.diff t22 start_1 1
    let t24 : Ptr ← Ext.ta_xstrndup.call ta_parent_v start_1 (SInt.toU 64 t23)
    start_1 := t24
  let t25 : Ptr ← Ptr.add dst_v 1 8
  let t26 : U32 := (SInt.toU 32 (1 : I32))
  Mem.store t25 t26
  Mem.store dst_v start_1
  return (0 : I32)

/-- C function `read_str`, ../.mpv/misc/json.c:101.
-/
def read_str [Ext.mp_append_escaped_string] (fuel : Nat) (ta_parent : Ptr) (dst : Ptr) (src : Ptr) : M I32 := do
  let unescaped_4 ← Mem.alloca 16 8
  let r_5 ← Mem.alloca 16 8
  let result : I32 ← (do
    let mut ta_parent_v : Ptr := ta_parent
    let mut dst_v : Ptr := dst
    let mut src_v : Ptr := src
    let t1 : Bool ← Misc.Json_c.eat_c fuel src_v (SInt.toS 8 (34 : I32))
    if (!t1) then
      return (SInt.ofInt 32 (-1))
    let t2 : Ptr ← Mem.load Ptr src_v
    let mut str_1 : Ptr := t2
    let mut cur_2 : Ptr := str_1
    let mut has_escapes_3 : Bool := ((0 : I32) != 0)
    for _ in Fuel.mk fuel do
      let t3 : Ptr ← Ptr.add cur_2 1 (SInt.toInt (0 : I32))
      let t4 : I8 ← Mem.load I8 t3
      let mut t7 : Bool := false
      if ((SInt.toS 32 t4) != 0) then
        let t5 : Ptr ← Ptr.add cur_2 1 (SInt.toInt (0 : I32))
        let t6 : I8 ← Mem.load I8 t5
        t7 := ((SInt.toS 32 t6) != (34 : I32))
      if !t7 then break
      let t8 : Ptr ← Ptr.add cur_2 1 (SInt.toInt (0 : I32))
      let t9 : I8 ← Mem.load I8 t8
      if ((SInt.toS 32 t9) == (92 : I32)) then
        let t10 : Bool := ((1 : I32) != 0)
        has_escapes_3 := t10
        let t11 : Ptr ← Ptr.add cur_2 1 (SInt.toInt (1 : I32))
        let t12 : I8 ← Mem.load I8 t11
        let mut t15 : Bool := true
        if !((SInt.toS 32 t12) == (34 : I32)) then
          let t13 : Ptr ← Ptr.add cur_2 1 (SInt.toInt (1 : I32))
          let t14 : I8 ← Mem.load I8 t13
          t15 := ((SInt.toS 32 t14) == (92 : I32))
        if t15 then
          let t16 : Ptr := cur_2
          let t17 : Ptr ← Ptr.add t16 1 1
          cur_2 := t17
      let t18 : Ptr := cur_2
      let t19 : Ptr ← Ptr.add t18 1 1
      cur_2 := t19
    let t20 : Ptr ← Ptr.add cur_2 1 (SInt.toInt (0 : I32))
    let t21 : I8 ← Mem.load I8 t20
    if ((SInt.toS 32 t21) != (34 : I32)) then
      return (SInt.ofInt 32 (-1))
    let t22 : Ptr ← Ptr.add cur_2 1 (SInt.toInt (0 : I32))
    let t23 : I8 := (SInt.toS 8 (0 : I32))
    Mem.store t22 t23
    let t24 : Ptr ← Ptr.add cur_2 1 (SInt.toInt (1 : I32))
    Mem.store src_v t24
    if has_escapes_3 then
      Mem.store unescaped_4 Ptr.null
      let t25 : Ptr ← Ptr.add unescaped_4 1 8
      Mem.zero t25 8
      let t26 : Agg ← Misc.Bstr_h.bstr0 fuel str_1
      Mem.storeAgg r_5 t26 8
      let t27 : Bool ← Ext.mp_append_escaped_string.call ta_parent_v unescaped_4 r_5
      if (!t27) then
        return (SInt.ofInt 32 (-1))
      let t28 : Ptr ← Mem.load Ptr unescaped_4
      str_1 := t28
    let t29 : Ptr ← Ptr.add dst_v 1 8
    let t30 : U32 := (SInt.toU 32 (1 : I32))
    Mem.store t29 t30
    Mem.store dst_v str_1
    return (0 : I32)
    : M I32)
  Mem.popFrame [unescaped_4, r_5]
  pure result

mutual

/-- C function `read_sub`, ../.mpv/misc/json.c:135.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def read_sub [Ext.«__errno_location»] [Ext.mp_append_escaped_string] [Ext.strtod] [Ext.strtoll] [Ext.ta_xstrndup] (fuel : Nat) (ta_parent : Ptr) (dst : Ptr) (src : Ptr) (max_depth : I32) : M I32 :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let keynode_5 ← Mem.alloca 16 8
    let result : I32 ← (do
      let mut ta_parent_v : Ptr := ta_parent
      let mut dst_v : Ptr := dst
      let mut src_v : Ptr := src
      let mut max_depth_v : I32 := max_depth
      let t1 : Bool ← Misc.Json_c.eat_c fuel src_v (SInt.toS 8 (91 : I32))
      let mut is_arr_1 : Bool := t1
      let mut t3 : Bool := false
      if (!is_arr_1) then
        let t2 : Bool ← Misc.Json_c.eat_c fuel src_v (SInt.toS 8 (123 : I32))
        t3 := ((SInt.ofBool 32 t2) != 0)
      let mut is_obj_2 : Bool := ((SInt.ofBool 32 t3) != 0)
      if ((!is_arr_1) && (!is_obj_2)) then
        return (SInt.ofInt 32 (-1))
      let mut term_3 : I8 := (SInt.toS 8 (if ((SInt.ofBool 32 is_obj_2) != 0) then (125 : I32) else (93 : I32)))
      let t4 : Ptr ← Talloc.ta_zalloc_size ta_parent_v (24 : U64)
      let t5 : Ptr ← Talloc.ta_dbg_set_loc t4 Statics.str_81
      let t6 : Ptr ← Ta.Ta_h.ta_oom_p fuel t5
      let mut list_4 : Ptr := t6
      for _ in Fuel.mk fuel do
        if !((1 : I32) != 0) then break
        Misc.Json_c.eat_ws fuel src_v
        let t7 : Bool ← Misc.Json_c.eat_c fuel src_v term_3
        if t7 then
          break
        let t8 : I32 ← Mem.load I32 list_4
        let mut t10 : Bool := false
        if (decide (t8 > (0 : I32))) then
          let t9 : Bool ← Misc.Json_c.eat_c fuel src_v (SInt.toS 8 (44 : I32))
          t10 := (!t9)
        if t10 then
          return (SInt.ofInt 32 (-1))
        Misc.Json_c.eat_ws fuel src_v
        let t11 : Bool ← Misc.Json_c.eat_c fuel src_v term_3
        if t11 then
          break
        if is_obj_2 then
          Mem.undefine keynode_5 16
          let t12 : I32 ← Misc.Json_c.read_id fuel list_4 keynode_5 src_v
          let mut t14 : Bool := false
          if (decide (t12 < (0 : I32))) then
            let t13 : I32 ← Misc.Json_c.read_str fuel list_4 keynode_5 src_v
            t14 := (decide (t13 < (0 : I32)))
          if t14 then
            return (SInt.ofInt 32 (-1))
          Misc.Json_c.eat_ws fuel src_v
          let t15 : Bool ← Misc.Json_c.eat_c fuel src_v (SInt.toS 8 (58 : I32))
          let mut t17 : Bool := false
          if (!t15) then
            let t16 : Bool ← Misc.Json_c.eat_c fuel src_v (SInt.toS 8 (61 : I32))
            t17 := (!t16)
          if t17 then
            return (SInt.ofInt 32 (-1))
          Misc.Json_c.eat_ws fuel src_v
          for _ in Fuel.mk fuel do
            for _ in Once.mk do
              let t18 : I32 ← Mem.load I32 list_4
              let mut nextidx__6 : U64 := (SInt.toU 64 t18)
              let t19 : Ptr ← Ptr.add list_4 1 16
              let t20 : Ptr ← Mem.load Ptr t19
              let t21 : U64 ← Talloc.ta_get_size t20
              let t22 : U64 ← UInt.div t21 (8 : U64)
              if (decide (nextidx__6 ≥ t22)) then
                for _ in Fuel.mk fuel do
                  for _ in Once.mk do
                    let t23 : Ptr ← Ptr.add list_4 1 16
                    let t24 : Ptr ← Ptr.add list_4 1 16
                    let t25 : Ptr ← Mem.load Ptr t24
                    let t26 : U64 ← Talloc.ta_calc_prealloc_elems nextidx__6
                    let t27 : U64 ← Talloc.ta_calc_array_size (8 : U64) t26
                    let t28 : Ptr ← Talloc.ta_xrealloc_size list_4 t25 t27
                    let t29 : Ptr ← Talloc.ta_dbg_set_loc t28 Statics.str_82
                    Mem.store t23 t29
                  if !((0 : I32) != 0) then break
            if !((0 : I32) != 0) then break
          let t30 : Ptr ← Ptr.add list_4 1 16
          let t31 : Ptr ← Mem.load Ptr t30
          let t32 : I32 ← Mem.load I32 list_4
          let t33 : Ptr ← Ptr.add t31 8 (SInt.toInt t32)
          let t34 : Ptr ← Mem.load Ptr keynode_5
          Mem.store t33 t34
        for _ in Fuel.mk fuel do
          for _ in Once.mk do
            let t35 : I32 ← Mem.load I32 list_4
            let mut nextidx__7 : U64 := (SInt.toU 64 t35)
            let t36 : Ptr ← Ptr.add list_4 1 8
            let t37 : Ptr ← Mem.load Ptr t36
            let t38 : U64 ← Talloc.ta_get_size t37
            let t39 : U64 ← UInt.div t38 (16 : U64)
            if (decide (nextidx__7 ≥ t39)) then
              for _ in Fuel.mk fuel do
                for _ in Once.mk do
                  let t40 : Ptr ← Ptr.add list_4 1 8
                  let t41 : Ptr ← Ptr.add list_4 1 8
                  let t42 : Ptr ← Mem.load Ptr t41
                  let t43 : U64 ← Talloc.ta_calc_prealloc_elems nextidx__7
                  let t44 : U64 ← Talloc.ta_calc_array_size (16 : U64) t43
                  let t45 : Ptr ← Talloc.ta_xrealloc_size list_4 t42 t44
                  let t46 : Ptr ← Talloc.ta_dbg_set_loc t45 Statics.str_83
                  Mem.store t40 t46
                if !((0 : I32) != 0) then break
          if !((0 : I32) != 0) then break
        let t47 : Ptr ← Ptr.add list_4 1 8
        let t48 : Ptr ← Mem.load Ptr t47
        let t49 : I32 ← Mem.load I32 list_4
        let t50 : Ptr ← Ptr.add t48 16 (SInt.toInt t49)
        let t51 : I32 ← Misc.Json_c.json_parse fuel ta_parent_v t50 src_v max_depth_v
        if (decide (t51 < (0 : I32))) then
          return (SInt.ofInt 32 (-1))
        let t52 : I32 ← Mem.load I32 list_4
        let t53 : I32 ← SInt.add t52 1
        Mem.store list_4 t53
      let t54 : Ptr ← Ptr.add dst_v 1 8
      let t55 : U32 := (SInt.toU 32 (if ((SInt.ofBool 32 is_obj_2) != 0) then (8 : I32) else (7 : I32)))
      Mem.store t54 t55
      Mem.store dst_v list_4
      return (0 : I32)
      : M I32)
    Mem.popFrame [keynode_5]
    pure result
termination_by structural fuel

/-- C function `json_parse`, ../.mpv/misc/json.c:189.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def json_parse [Ext.«__errno_location»] [Ext.mp_append_escaped_string] [Ext.strtod] [Ext.strtoll] [Ext.ta_xstrndup] (fuel : Nat) (ta_parent : Ptr) (dst : Ptr) (src : Ptr) (max_depth : I32) : M I32 :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let nsrci_2 ← Mem.alloca 8 8
    let nsrcf_3 ← Mem.alloca 8 8
    let result : I32 ← (do
      let mut ta_parent_v : Ptr := ta_parent
      let mut dst_v : Ptr := dst
      let mut src_v : Ptr := src
      let mut max_depth_v : I32 := max_depth
      let t1 : I32 ← SInt.sub max_depth_v (1 : I32)
      max_depth_v := t1
      if (decide (max_depth_v < (0 : I32))) then
        return (SInt.ofInt 32 (-1))
      Misc.Json_c.eat_ws fuel src_v
      let t2 : Ptr ← Mem.load Ptr src_v
      let t3 : I8 ← Mem.load I8 t2
      let mut c_1 : I8 := t3
      if (!(c_1 != 0)) then
        return (SInt.ofInt 32 (-1))
      let mut t6 : Bool := false
      if ((SInt.toS 32 c_1) == (110 : I32)) then
        let t4 : Ptr ← Mem.load Ptr src_v
        let t5 : I32 ← Libc.strncmp t4 Statics.str_84 (SInt.toU 64 (4 : I32))
        t6 := (t5 == (0 : I32))
      if t6 then
        let t7 : Ptr ← Mem.load Ptr src_v
        let t8 : Ptr ← Ptr.add t7 1 (SInt.toInt (4 : I32))
        Mem.store src_v t8
        let t9 : Ptr ← Ptr.add dst_v 1 8
        let t10 : U32 := (SInt.toU 32 (0 : I32))
        Mem.store t9 t10
        return (0 : I32)
      else
        let mut t13 : Bool := false
        if ((SInt.toS 32 c_1) == (116 : I32)) then
          let t11 : Ptr ← Mem.load Ptr src_v
          let t12 : I32 ← Libc.strncmp t11 Statics.str_85 (SInt.toU 64 (4 : I32))
          t13 := (t12 == (0 : I32))
        if t13 then
          let t14 : Ptr ← Mem.load Ptr src_v
          let t15 : Ptr ← Ptr.add t14 1 (SInt.toInt (4 : I32))
          Mem.store src_v t15
          let t16 : Ptr ← Ptr.add dst_v 1 8
          let t17 : U32 := (SInt.toU 32 (3 : I32))
          Mem.store t16 t17
          let t18 : I32 := (1 : I32)
          Mem.store dst_v t18
          return (0 : I32)
        else
          let mut t21 : Bool := false
          if ((SInt.toS 32 c_1) == (102 : I32)) then
            let t19 : Ptr ← Mem.load Ptr src_v
            let t20 : I32 ← Libc.strncmp t19 Statics.str_86 (SInt.toU 64 (5 : I32))
            t21 := (t20 == (0 : I32))
          if t21 then
            let t22 : Ptr ← Mem.load Ptr src_v
            let t23 : Ptr ← Ptr.add t22 1 (SInt.toInt (5 : I32))
            Mem.store src_v t23
            let t24 : Ptr ← Ptr.add dst_v 1 8
            let t25 : U32 := (SInt.toU 32 (3 : I32))
            Mem.store t24 t25
            let t26 : I32 := (0 : I32)
            Mem.store dst_v t26
            return (0 : I32)
          else
            if ((SInt.toS 32 c_1) == (34 : I32)) then
              let t27 : I32 ← Misc.Json_c.read_str fuel ta_parent_v dst_v src_v
              return t27
            else
              if (((SInt.toS 32 c_1) == (91 : I32)) || ((SInt.toS 32 c_1) == (123 : I32))) then
                let t28 : I32 ← Misc.Json_c.read_sub fuel ta_parent_v dst_v src_v max_depth_v
                return t28
              else
                if (((SInt.toS 32 c_1) == (45 : I32)) || ((decide ((SInt.toS 32 c_1) ≥ (48 : I32))) && (decide ((SInt.toS 32 c_1) ≤ (57 : I32))))) then
                  let t29 : Ptr ← Mem.load Ptr src_v
                  Mem.store nsrci_2 t29
                  let t30 : Ptr ← Mem.load Ptr src_v
                  Mem.store nsrcf_3 t30
                  let t31 : Ptr ← Ext.«__errno_location».call
                  let t32 : I32 := (0 : I32)
                  Mem.store t31 t32
                  let t33 : Ptr ← Mem.load Ptr src_v
                  let t34 : I64 ← Ext.strtoll.call t33 nsrci_2 (0 : I32)
                  let mut numi_4 : I64 := t34
                  let t35 : Ptr ← Ext.«__errno_location».call
                  let t36 : I32 ← Mem.load I32 t35
                  if (t36 != 0) then
                    let t37 : Ptr ← Mem.load Ptr src_v
                    Mem.store nsrci_2 t37
                  let t38 : Ptr ← Ext.«__errno_location».call
                  let t39 : I32 := (0 : I32)
                  Mem.store t38 t39
                  let t40 : Ptr ← Mem.load Ptr src_v
                  let t41 : F64 ← Ext.strtod.call t40 nsrcf_3
                  let mut numf_5 : F64 := t41
                  let t42 : Ptr ← Ext.«__errno_location».call
                  let t43 : I32 ← Mem.load I32 t42
                  if (t43 != 0) then
                    let t44 : Ptr ← Mem.load Ptr src_v
                    Mem.store nsrcf_3 t44
                  let t45 : Ptr ← Mem.load Ptr nsrci_2
                  let t46 : Ptr ← Mem.load Ptr nsrcf_3
                  let t47 : Bool ← Ptr.ge t45 t46
                  if t47 then
                    let t48 : Ptr ← Mem.load Ptr nsrci_2
                    Mem.store src_v t48
                    let t49 : Ptr ← Ptr.add dst_v 1 8
                    let t50 : U32 := (SInt.toU 32 (4 : I32))
                    Mem.store t49 t50
                    let t51 : I64 := (SInt.toS 64 numi_4)
                    Mem.store dst_v t51
                    return (0 : I32)
                  let t52 : Ptr ← Mem.load Ptr nsrcf_3
                  let t53 : Ptr ← Mem.load Ptr src_v
                  let t54 : Bool ← Ptr.gt t52 t53
                  if (t54 && ((SInt.ofBool 32 (numf_5.isFinite)) != 0)) then
                    let t55 : Ptr ← Mem.load Ptr nsrcf_3
                    Mem.store src_v t55
                    let t56 : Ptr ← Ptr.add dst_v 1 8
                    let t57 : U32 := (SInt.toU 32 (5 : I32))
                    Mem.store t56 t57
                    Mem.store dst_v numf_5
                    return (0 : I32)
                  return (SInt.ofInt 32 (-1))
      return (SInt.ofInt 32 (-1))
      : M I32)
    Mem.popFrame [nsrci_2, nsrcf_3]
    pure result
termination_by structural fuel

end

/-- C function `write_json_str`, ../.mpv/misc/json.c:258.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def write_json_str [Ext.bstr_xappend_asprintf] (fuel : Nat) (b : Ptr) (str : Ptr) : M Unit := do
  let cl15 ← Mem.alloca 16 8
  let cl21 ← Mem.alloca 16 8
  let cl26 ← Mem.alloca 16 8
  let result : Unit ← (do
    let mut b_v : Ptr := b
    let mut str_v : Ptr := str
    let mut t1 : Unit := default
    if (str_v != Ptr.null) then
      t1 := ()
    else
      Libc.«__assert_fail» Statics.str_87 Statics.str_88 (SInt.toU 32 (260 : I32)) Statics.str_89
      t1 := ()
    let t2 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_90
    Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t2
    for _ in Fuel.mk fuel do
      if !((1 : I32) != 0) then break
      let mut cur_1 : Ptr := str_v
      for _ in Fuel.mk fuel do
        let t3 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
        let t4 : U8 ← Mem.load U8 t3
        let mut t7 : Bool := false
        if (decide ((UInt.toS 32 t4) ≥ (32 : I32))) then
          let t5 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
          let t6 : U8 ← Mem.load U8 t5
          t7 := ((UInt.toS 32 t6) != (34 : I32))
        let mut t10 : Bool := false
        if t7 then
          let t8 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
          let t9 : U8 ← Mem.load U8 t8
          t10 := ((UInt.toS 32 t9) != (92 : I32))
        if !t10 then break
        let t11 : Ptr := cur_1
        let t12 : Ptr ← Ptr.add t11 1 1
        cur_1 := t12
      let t13 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
      let t14 : U8 ← Mem.load U8 t13
      if (!(t14 != 0)) then
        break
      Mem.undefine cl15 16
      Mem.store cl15 str_v
      let t16 : I64 ← Ptr.diff cur_1 str_v 1
      let t17 : Ptr ← Ptr.add cl15 1 8
      Mem.store t17 (SInt.toU 64 t16)
      let t18 : Agg ← Mem.loadAgg cl15 16 8
      Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t18
      let t19 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
      let t20 : U8 ← Mem.load U8 t19
      if ((UInt.toS 32 t20) == (34 : I32)) then
        Mem.undefine cl21 16
        Mem.store cl21 Statics.str_91
        let t22 : Ptr ← Ptr.add cl21 1 8
        Mem.store t22 (SInt.toU 64 (2 : I32))
        let t23 : Agg ← Mem.loadAgg cl21 16 8
        Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t23
      else
        let t24 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
        let t25 : U8 ← Mem.load U8 t24
        if ((UInt.toS 32 t25) == (92 : I32)) then
          Mem.undefine cl26 16
          Mem.store cl26 Statics.str_92
          let t27 : Ptr ← Ptr.add cl26 1 8
          Mem.store t27 (SInt.toU 64 (2 : I32))
          let t28 : Agg ← Mem.loadAgg cl26 16 8
          Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t28
        else
          let t29 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
          let t30 : U8 ← Mem.load U8 t29
          let mut t35 : Bool := false
          if (decide ((UInt.toU 64 t30) < (14 : U64))) then
            let t31 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
            let t32 : U8 ← Mem.load U8 t31
            let t33 : Ptr ← Ptr.add Statics.g_Misc_Json_c_special_escape 1 (UInt.toInt t32)
            let t34 : I8 ← Mem.load I8 t33
            t35 := ((SInt.toS 32 t34) != 0)
          if t35 then
            let t36 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
            let t37 : U8 ← Mem.load U8 t36
            let t38 : Ptr ← Ptr.add Statics.g_Misc_Json_c_special_escape 1 (UInt.toInt t37)
            let t39 : I8 ← Mem.load I8 t38
            let t40 : I32 ← Ext.bstr_xappend_asprintf.call Ptr.null b_v Statics.str_93 [(VArg.sint (SInt.toS 32 t39))]
            pure ()
          else
            let t41 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (0 : I32))
            let t42 : U8 ← Mem.load U8 t41
            let t43 : I32 ← Ext.bstr_xappend_asprintf.call Ptr.null b_v Statics.str_94 [(VArg.sint (UInt.toS 32 t42))]
            pure ()
      let t44 : Ptr ← Ptr.add cur_1 1 (SInt.toInt (1 : I32))
      str_v := t44
    let t45 : Agg ← Misc.Bstr_h.bstr0 fuel str_v
    Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t45
    let t46 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_90
    Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t46
    pure ()
    : M Unit)
  Mem.popFrame [cl15, cl21, cl26]
  pure result

/-- C function `add_indent`, ../.mpv/misc/json.c:285.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def add_indent (fuel : Nat) (b : Ptr) (indent : I32) : M Unit := do
  let mut b_v : Ptr := b
  let mut indent_v : I32 := indent
  if (decide (indent_v < (0 : I32))) then
    return ()
  let t1 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_20
  Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t1
  let mut n_1 : I32 := (0 : I32)
  for _ in Fuel.mk fuel do
    if !(decide (n_1 < indent_v)) then break
    for _ in Once.mk do
      let t2 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_95
      Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t2
    let t3 : I32 := n_1
    let t4 : I32 ← SInt.add t3 1
    n_1 := t4
  pure ()

/-- C function `json_append`, ../.mpv/misc/json.c:294.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def json_append [Ext.bstr_xappend_asprintf] (fuel : Nat) (b : Ptr) (src : Ptr) (indent : I32) : M I32 :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let mut b_v : Ptr := b
    let mut src_v : Ptr := src
    let mut indent_v : I32 := indent
    let t1 : Ptr ← Ptr.add src_v 1 8
    let t2 : U32 ← Mem.load U32 t1
    let t3 := t2
    let t4 : Nat := if t3 == (SInt.toU 32 (0 : I32)) then 0 else if t3 == (SInt.toU 32 (3 : I32)) then 1 else if t3 == (SInt.toU 32 (4 : I32)) then 2 else if t3 == (SInt.toU 32 (5 : I32)) then 3 else if t3 == (SInt.toU 32 (1 : I32)) then 4 else if t3 == (SInt.toU 32 (7 : I32)) || t3 == (SInt.toU 32 (8 : I32)) then 5 else 6
    for _ in Once.mk do
      if t4 ≤ 0 then
        let t5 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_84
        Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t5
        return (0 : I32)
      if t4 ≤ 1 then
        let t6 : I32 ← Mem.load I32 src_v
        let t7 : Agg ← Misc.Bstr_h.bstr0 fuel (if (t6 != 0) then Statics.str_85 else Statics.str_86)
        Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t7
        return (0 : I32)
      if t4 ≤ 2 then
        let t8 : I64 ← Mem.load I64 src_v
        let t9 : I32 ← Ext.bstr_xappend_asprintf.call Ptr.null b_v Statics.str_96 [(VArg.sint t8)]
        return (0 : I32)
      if t4 ≤ 3 then
        let t10 : F64 ← Mem.load F64 src_v
        let mut px_1 : Ptr := (if (((SInt.ofBool 32 (t10.isFinite)) != 0) || (indent_v == (0 : I32))) then Statics.str_97 else Statics.str_90)
        let t11 : F64 ← Mem.load F64 src_v
        let t12 : I32 ← Ext.bstr_xappend_asprintf.call Ptr.null b_v Statics.str_98 [(VArg.ptr px_1), (VArg.f64 t11), (VArg.ptr px_1)]
        return (0 : I32)
      if t4 ≤ 4 then
        if (indent_v == (0 : I32)) then
          let t13 : Ptr ← Mem.load Ptr src_v
          let t14 : Agg ← Misc.Bstr_h.bstr0 fuel t13
          Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t14
        else
          let t15 : Ptr ← Mem.load Ptr src_v
          Misc.Json_c.write_json_str fuel b_v t15
        return (0 : I32)
      if t4 ≤ 5 then
        let t16 : Ptr ← Mem.load Ptr src_v
        let mut list_2 : Ptr := t16
        let t17 : Ptr ← Ptr.add src_v 1 8
        let t18 : U32 ← Mem.load U32 t17
        let mut is_obj_3 : Bool := ((SInt.ofBool 32 (t18 == (SInt.toU 32 (8 : I32)))) != 0)
        let t19 : Agg ← Misc.Bstr_h.bstr0 fuel (if ((SInt.ofBool 32 is_obj_3) != 0) then Statics.str_99 else Statics.str_100)
        Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t19
        let mut t21 : I32 := default
        if (decide (indent_v ≥ (0 : I32))) then
          let t20 : I32 ← SInt.add indent_v (1 : I32)
          t21 := t20
        else
          t21 := (SInt.ofInt 32 (-1))
        let mut next_indent_4 : I32 := t21
        let mut n_5 : I32 := (0 : I32)
        for _ in Fuel.mk fuel do
          let t22 : I32 ← Mem.load I32 list_2
          if !(decide (n_5 < t22)) then break
          for _ in Once.mk do
            if (n_5 != 0) then
              let t23 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_101
              Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t23
            Misc.Json_c.add_indent fuel b_v next_indent_4
            if is_obj_3 then
              let t24 : Ptr ← Ptr.add list_2 1 16
              let t25 : Ptr ← Mem.load Ptr t24
              let t26 : Ptr ← Ptr.add t25 8 (SInt.toInt n_5)
              let t27 : Ptr ← Mem.load Ptr t26
              Misc.Json_c.write_json_str fuel b_v t27
              let t28 : Agg ← Misc.Bstr_h.bstr0 fuel Statics.str_102
              Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t28
            let t29 : Ptr ← Ptr.add list_2 1 8
            let t30 : Ptr ← Mem.load Ptr t29
            let t31 : Ptr ← Ptr.add t30 16 (SInt.toInt n_5)
            let t32 : I32 ← Misc.Json_c.json_append fuel b_v t31 next_indent_4
            pure ()
          let t33 : I32 := n_5
          let t34 : I32 ← SInt.add t33 1
          n_5 := t34
        Misc.Json_c.add_indent fuel b_v indent_v
        let t35 : Agg ← Misc.Bstr_h.bstr0 fuel (if ((SInt.ofBool 32 is_obj_3) != 0) then Statics.str_103 else Statics.str_104)
        Misc.Bstr_c.bstr_xappend fuel Ptr.null b_v t35
        return (0 : I32)
    return (SInt.ofInt 32 (-1))
termination_by structural fuel

/-- C function `json_append_str`, ../.mpv/misc/json.c:341.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def json_append_str [Ext.bstr_xappend_asprintf] (fuel : Nat) (dst : Ptr) (src : Ptr) (indent : I32) : M I32 := do
  let buffer_1 ← Mem.alloca 16 8
  let result : I32 ← (do
    let mut dst_v : Ptr := dst
    let mut src_v : Ptr := src
    let mut indent_v : I32 := indent
    let t1 : Ptr ← Mem.load Ptr dst_v
    let t2 : Agg ← Misc.Bstr_h.bstr0 fuel t1
    Mem.storeAgg buffer_1 t2 8
    let t3 : I32 ← Misc.Json_c.json_append fuel buffer_1 src_v indent_v
    let mut r_2 : I32 := t3
    let t4 : Ptr ← Mem.load Ptr buffer_1
    Mem.store dst_v t4
    return r_2
    : M I32)
  Mem.popFrame [buffer_1]
  pure result

/-- C function `json_write`, ../.mpv/misc/json.c:354.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def json_write [Ext.bstr_xappend_asprintf] (fuel : Nat) (dst : Ptr) (src : Ptr) : M I32 := do
  let mut dst_v : Ptr := dst
  let mut src_v : Ptr := src
  let t1 : I32 ← Misc.Json_c.json_append_str fuel dst_v src_v (SInt.ofInt 32 (-1))
  return t1

/-- C function `json_write_pretty`, ../.mpv/misc/json.c:360.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def json_write_pretty [Ext.bstr_xappend_asprintf] (fuel : Nat) (dst : Ptr) (src : Ptr) : M I32 := do
  let mut dst_v : Ptr := dst
  let mut src_v : Ptr := src
  let t1 : I32 ← Misc.Json_c.json_append_str fuel dst_v src_v (0 : I32)
  return t1

end Misc.Misc.Json_c
