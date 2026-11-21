import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_c
import Misc.Misc.Bstr_h
import Misc.Misc.Bstr_h.Part3

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Codepoint_width_c

/-- C function `ucdLookup`, ../.mpv/misc/codepoint_width.c:617.
-/
def ucdLookup (fuel : Nat) (cp : U32) : M I32 := do
  let mut cp_v : U32 := cp
  let t1 : U32 ← UInt.shr cp_v (SInt.toInt (11 : I32))
  let t2 : Ptr ← Ptr.add Statics.g_Misc_Codepoint_width_c_s_stage0 2 (UInt.toInt t1)
  let t3 : U16 ← Mem.load U16 t2
  let mut s0_1 : U16 := t3
  let t4 : U32 ← UInt.shr cp_v (SInt.toInt (6 : I32))
  let t5 : Ptr ← Ptr.add Statics.g_Misc_Codepoint_width_c_s_stage1 2 (UInt.toInt ((UInt.toU 32 s0_1) + (UInt.band t4 (SInt.toU 32 (31 : I32)))))
  let t6 : U16 ← Mem.load U16 t5
  let mut s1_2 : U16 := t6
  let t7 : U32 ← UInt.shr cp_v (SInt.toInt (3 : I32))
  let t8 : Ptr ← Ptr.add Statics.g_Misc_Codepoint_width_c_s_stage2 2 (UInt.toInt ((UInt.toU 32 s1_2) + (UInt.band t7 (SInt.toU 32 (7 : I32)))))
  let t9 : U16 ← Mem.load U16 t8
  let mut s2_3 : U16 := t9
  let t10 : U32 ← UInt.shr cp_v (SInt.toInt (0 : I32))
  let t11 : Ptr ← Ptr.add Statics.g_Misc_Codepoint_width_c_s_stage3 1 (UInt.toInt ((UInt.toU 32 s2_3) + (UInt.band t10 (SInt.toU 32 (7 : I32)))))
  let t12 : U8 ← Mem.load U8 t11
  let mut s3_4 : U8 := t12
  return (UInt.toS 32 s3_4)

/-- C function `ucdGraphemeJoins`, ../.mpv/misc/codepoint_width.c:625.
-/
def ucdGraphemeJoins (fuel : Nat) (state : I32) (lead : I32) (trail : I32) : M I32 := do
  let mut state_v : I32 := state
  let mut lead_v : I32 := lead
  let mut trail_v : I32 := trail
  let mut l_1 : I32 := (SInt.band lead_v (15 : I32))
  let mut t_2 : I32 := (SInt.band trail_v (15 : I32))
  let t1 : Ptr ← Ptr.add Statics.g_Misc_Codepoint_width_c_s_joinRules 64 (SInt.toInt state_v)
  let t2 : Ptr ← Ptr.add t1 4 (SInt.toInt l_1)
  let t3 : U32 ← Mem.load U32 t2
  let t4 : I32 ← SInt.mul t_2 (2 : I32)
  let t5 : U32 ← UInt.shr t3 (SInt.toInt t4)
  return (UInt.toS 32 (UInt.band t5 (SInt.toU 32 (3 : I32))))

/-- C function `ucdGraphemeDone`, ../.mpv/misc/codepoint_width.c:631.
-/
def ucdGraphemeDone (fuel : Nat) (state : I32) : M Bool := do
  let mut state_v : I32 := state
  return ((SInt.ofBool 32 (state_v == (3 : I32))) != 0)

/-- C function `ucdToCharacterWidth`, ../.mpv/misc/codepoint_width.c:635.
-/
def ucdToCharacterWidth (fuel : Nat) (val : I32) : M I32 := do
  let mut val_v : I32 := val
  let t1 : I32 ← SInt.shr val_v (SInt.toInt (6 : I32))
  return t1

/-- C function `is_valid_partial_sequence`, ../.mpv/misc/codepoint_width.c:664.
-/
def is_valid_partial_sequence (fuel : Nat) (seq : Agg) : M Bool := do
  let seq_p ← Mem.alloca 16 8
  let result : Bool ← (do
    Mem.storeAgg seq_p seq 8
    let t1 : Ptr ← Ptr.add seq_p 1 8
    let t2 : U64 ← Mem.load U64 t1
    if (decide (t2 < (SInt.toU 64 (2 : I32)))) then
      return ((1 : I32) != 0)
    let t3 : Ptr ← Mem.load Ptr seq_p
    let t4 : Ptr ← Ptr.add t3 1 (SInt.toInt (0 : I32))
    let t5 : U8 ← Mem.load U8 t4
    if ((UInt.toS 32 t5) == (224 : I32)) then
      let t6 : Ptr ← Mem.load Ptr seq_p
      let t7 : Ptr ← Ptr.add t6 1 (SInt.toInt (1 : I32))
      let t8 : U8 ← Mem.load U8 t7
      return ((SInt.ofBool 32 (decide ((UInt.toS 32 t8) ≥ (160 : I32)))) != 0)
    else
      let t9 : Ptr ← Mem.load Ptr seq_p
      let t10 : Ptr ← Ptr.add t9 1 (SInt.toInt (0 : I32))
      let t11 : U8 ← Mem.load U8 t10
      if ((UInt.toS 32 t11) == (237 : I32)) then
        let t12 : Ptr ← Mem.load Ptr seq_p
        let t13 : Ptr ← Ptr.add t12 1 (SInt.toInt (1 : I32))
        let t14 : U8 ← Mem.load U8 t13
        return ((SInt.ofBool 32 (decide ((UInt.toS 32 t14) ≤ (159 : I32)))) != 0)
      else
        let t15 : Ptr ← Mem.load Ptr seq_p
        let t16 : Ptr ← Ptr.add t15 1 (SInt.toInt (0 : I32))
        let t17 : U8 ← Mem.load U8 t16
        if ((UInt.toS 32 t17) == (240 : I32)) then
          let t18 : Ptr ← Mem.load Ptr seq_p
          let t19 : Ptr ← Ptr.add t18 1 (SInt.toInt (1 : I32))
          let t20 : U8 ← Mem.load U8 t19
          return ((SInt.ofBool 32 (decide ((UInt.toS 32 t20) ≥ (144 : I32)))) != 0)
        else
          let t21 : Ptr ← Mem.load Ptr seq_p
          let t22 : Ptr ← Ptr.add t21 1 (SInt.toInt (0 : I32))
          let t23 : U8 ← Mem.load U8 t22
          if ((UInt.toS 32 t23) == (244 : I32)) then
            let t24 : Ptr ← Mem.load Ptr seq_p
            let t25 : Ptr ← Ptr.add t24 1 (SInt.toInt (1 : I32))
            let t26 : U8 ← Mem.load U8 t25
            return ((SInt.ofBool 32 (decide ((UInt.toS 32 t26) ≤ (143 : I32)))) != 0)
    return ((1 : I32) != 0)
    : M Bool)
  Mem.popFrame [seq_p]
  pure result

/-- C function `term_disp_width`, ../.mpv/misc/codepoint_width.c:680.
Assumes cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign.
-/
def term_disp_width [Ext.mp_log2] (fuel : Nat) (str : Agg) (max_width : I32) (cut_pos : Ptr) : M I32 := do
  let str_p ← Mem.alloca 16 8
  let current_width_4 ← Mem.alloca 4 4
  let cp_5 ← Mem.alloca 4 4
  let v_partial_6 ← Mem.alloca 16 8
  let state_7 ← Mem.alloca 4 4
  let cluster_end_10 ← Mem.alloca 16 8
  let result : I32 ← (do
    Mem.storeAgg str_p str 8
    let mut max_width_v : I32 := max_width
    let mut cut_pos_v : Ptr := cut_pos
    let mut width_2 : I32 := (0 : I32)
    let t1 : Ptr ← Mem.load Ptr str_p
    let mut prev_pos_3 : Ptr := t1
    for _ in Fuel.mk fuel do
      let t2 : Ptr ← Ptr.add str_p 1 8
      let t3 : U64 ← Mem.load U64 t2
      if !(t3 != 0) then break
      for _ in Once.mk do
        Mem.store current_width_4 (0 : I32)
        let t4 : Bool ← Misc.Bstr_h.bstr_eatstart0 fuel str_p Statics.str_37
        if t4 then
          for _ in Fuel.mk fuel do
            let t5 : Ptr ← Ptr.add str_p 1 8
            let t6 : U64 ← Mem.load U64 t5
            let mut t15 : Bool := false
            if (t6 != 0) then
              let t7 : Ptr ← Mem.load Ptr str_p
              let t8 : U8 ← Mem.load U8 t7
              let mut t11 : Bool := false
              if (decide ((UInt.toS 32 t8) ≥ (64 : I32))) then
                let t9 : Ptr ← Mem.load Ptr str_p
                let t10 : U8 ← Mem.load U8 t9
                t11 := (decide ((UInt.toS 32 t10) ≤ (126 : I32)))
              let mut t14 : Bool := true
              if !t11 then
                let t12 : Ptr ← Mem.load Ptr str_p
                let t13 : U8 ← Mem.load U8 t12
                t14 := ((UInt.toS 32 t13) == (109 : I32))
              t15 := (!t14)
            if !t15 then break
            let t16 : Agg ← Mem.loadAgg str_p 16 8
            let t17 : Agg ← Misc.Bstr_h.bstr_cut fuel t16 (1 : I32)
            Mem.storeAgg str_p t17 8
          let t18 : Agg ← Mem.loadAgg str_p 16 8
          let t19 : Agg ← Misc.Bstr_h.bstr_cut fuel t18 (1 : I32)
          Mem.storeAgg str_p t19 8
          break
        let t20 : Ptr ← Mem.load Ptr str_p
        prev_pos_3 := t20
        let t21 : I32 ← Misc.Bstr_c.bstr_decode_partial_utf8 fuel str_p
        Mem.store cp_5 t21
        let t22 : I32 ← Mem.load I32 cp_5
        if (decide (t22 < (0 : I32))) then
          Mem.store v_partial_6 prev_pos_3
          let t23 : Ptr ← Mem.load Ptr str_p
          let t24 : I64 ← Ptr.diff t23 prev_pos_3 1
          let t25 : Ptr ← Ptr.add v_partial_6 1 8
          Mem.store t25 (SInt.toU 64 t24)
          let t26 : I32 ← Mem.load I32 cp_5
          let mut t29 : Bool := false
          if (t26 == (SInt.ofInt 32 (-2))) then
            let t27 : Agg ← Mem.loadAgg v_partial_6 16 8
            let t28 : Bool ← Misc.Codepoint_width_c.is_valid_partial_sequence fuel t27
            t29 := ((SInt.ofBool 32 t28) != 0)
          if t29 then
            let t30 : I32 := (1 : I32)
            Mem.store current_width_4 t30
          else
            let t31 : Ptr ← Ptr.add v_partial_6 1 8
            let t32 : U64 ← Mem.load U64 t31
            let t33 : I32 := (UInt.toS 32 t32)
            Mem.store current_width_4 t33
          break
        let t34 : I32 ← Mem.load I32 cp_5
        if (t34 == (13 : I32)) then
          let t35 : I32 := (0 : I32)
          width_2 := t35
          break
        let t36 : I32 ← Mem.load I32 cp_5
        if (t36 == (9 : I32)) then
          let t37 : I32 ← SInt.rem width_2 (8 : I32)
          let t38 : I32 ← SInt.sub (8 : I32) t37
          Mem.store current_width_4 t38
          break
        let t39 : I32 ← Mem.load I32 cp_5
        if (decide (t39 < (32 : I32))) then
          break
        let t40 : I32 ← Mem.load I32 cp_5
        if (decide (t40 ≤ (126 : I32))) then
          let t41 : I32 := (1 : I32)
          Mem.store current_width_4 t41
          break
        Mem.store state_7 (0 : I32)
        for _ in Fuel.mk fuel do
          if !((1 : I32) != 0) then break
          let t42 : I32 ← Mem.load I32 cp_5
          let t43 : I32 ← Misc.Codepoint_width_c.ucdLookup fuel (SInt.toU 32 t42)
          let mut lead_8 : I32 := t43
          let t44 : I32 ← Misc.Codepoint_width_c.ucdToCharacterWidth fuel lead_8
          let mut w_9 : I32 := t44
          if (w_9 == (3 : I32)) then
            let t45 : I32 ← Mem.load I32 Statics.s_Misc_Codepoint_width_c_term_disp_width_ambiguous_width
            w_9 := t45
          let t46 : I32 ← Mem.load I32 cp_5
          if (t46 == (65039 : I32)) then
            let t47 : I32 := (2 : I32)
            w_9 := t47
          let t48 : I32 ← Mem.load I32 current_width_4
          let t49 : I32 ← SInt.add t48 w_9
          Mem.store current_width_4 t49
          let t50 : Ptr ← Ptr.add str_p 1 8
          let t51 : U64 ← Mem.load U64 t50
          if (!(t51 != 0)) then
            break
          Mem.undefine cluster_end_10 16
          let t52 : Agg ← Mem.loadAgg str_p 16 8
          let t53 : I32 ← Misc.Bstr_c.bstr_decode_utf8 fuel t52 cluster_end_10
          Mem.store cp_5 t53
          let t54 : I32 ← Mem.load I32 cp_5
          if (decide (t54 < (0 : I32))) then
            break
          let t55 : I32 ← Mem.load I32 cp_5
          let t56 : I32 ← Misc.Codepoint_width_c.ucdLookup fuel (SInt.toU 32 t55)
          let mut trail_11 : I32 := t56
          let t57 : I32 ← Mem.load I32 state_7
          let t58 : I32 ← Misc.Codepoint_width_c.ucdGraphemeJoins fuel t57 lead_8 trail_11
          Mem.store state_7 t58
          let t59 : I32 ← Mem.load I32 state_7
          let t60 : Bool ← Misc.Codepoint_width_c.ucdGraphemeDone fuel t59
          if t60 then
            break
          let t61 : Agg ← Mem.loadAgg cluster_end_10 16 8
          Mem.storeAgg str_p t61 8
        let t62 : I32 ← Mem.load I32 current_width_4
        let mut t64 : I32 := default
        if (decide (t62 > (2 : I32))) then
          t64 := (2 : I32)
        else
          let t63 : I32 ← Mem.load I32 current_width_4
          t64 := t63
        Mem.store current_width_4 t64
      let t65 : I32 ← Mem.load I32 current_width_4
      let t66 : I32 ← SInt.add width_2 t65
      if (decide (t66 > max_width_v)) then
        let t67 : Ptr ← Mem.load Ptr str_p
        let t68 : Ptr ← Ptr.add str_p 1 8
        let t69 : U64 ← Mem.load U64 t68
        let t70 : Ptr ← Ptr.add t67 1 (UInt.toInt t69)
        let t71 : Bool ← Ptr.lt prev_pos_3 t70
        let mut t72 : Unit := default
        if t71 then
          t72 := ()
        else
          Libc.«__assert_fail» Statics.str_38 Statics.str_39 (SInt.toU 32 (775 : I32)) Statics.str_40
          t72 := ()
        Mem.store cut_pos_v prev_pos_3
        break
      let t73 : I32 ← Mem.load I32 current_width_4
      let t74 : I32 ← SInt.add width_2 t73
      width_2 := t74
      if (width_2 == max_width_v) then
        let t75 : Ptr ← Ptr.add str_p 1 8
        let t76 : U64 ← Mem.load U64 t75
        if (t76 != 0) then
          let t77 : Ptr ← Mem.load Ptr str_p
          Mem.store cut_pos_v t77
        break
    return width_2
    : M I32)
  Mem.popFrame [str_p, current_width_4, cp_5, v_partial_6, state_7, cluster_end_10]
  pure result

end Misc.Misc.Codepoint_width_c
