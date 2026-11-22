import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Bstr_c
import Misc.Misc.Bstr_c.Part2
import Misc.Misc.Bstr_h
import Misc.Misc.Bstr_h.Part2
import Misc.Misc.Ctype_h
import Misc.Misc.Path_utils_c
import Misc.Sys.Stdlib_bsearch_h
import Misc.Ta.Ta_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Language_c

/-- C function `lang_compare`, ../.mpv/misc/language.c:241.
-/
def lang_compare [Ext.strncasecmp] (fuel : Nat) (key : Ptr) (lang : Ptr) : M I32 := do
  let cl2 ← Mem.alloca 16 8
  let result : I32 ← (do
    let mut key_v : Ptr := key
    let mut lang_v : Ptr := lang
    let mut l_1 : Ptr := lang_v
    let t1 : Agg ← Mem.loadAgg key_v 16 8
    Mem.undefine cl2 16
    Mem.store cl2 l_1
    let t3 : Ptr ← Ptr.add l_1 1 3
    let t4 : U8 ← Mem.load U8 t3
    let t5 : Ptr ← Ptr.add cl2 1 8
    Mem.store t5 (UInt.toU 64 t4)
    let t6 : Agg ← Mem.loadAgg cl2 16 8
    let t7 : I32 ← Misc.Bstr_c.bstrcasecmp fuel t1 t6
    return t7
    : M I32)
  Mem.popFrame [cl2]
  pure result

/-- C function `canonicalize`, ../.mpv/misc/language.c:247.
-/
def canonicalize [Ext.Misc_Language_c_lang_compare] (fuel : Nat) (lang : Agg) : M Agg := do
  let lang_p ← Mem.alloca 16 8
  let cl3 ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg lang_p lang 8
    let t1 : U64 ← UInt.div (1648 : U64) (8 : U64)
    let t2 : Ptr ← Sys.Stdlib_bsearch_h.bsearch fuel lang_p Statics.g_Misc_Language_c_langmap t1 (8 : U64) (Ptr.fn "Misc.Language_c.lang_compare")
    let mut l_1 : Ptr := t2
    let mut t10 : Agg := default
    if (l_1 != Ptr.null) then
      Mem.undefine cl3 16
      let t4 : Ptr ← Ptr.add l_1 1 4
      Mem.store cl3 t4
      let t5 : Ptr ← Ptr.add l_1 1 7
      let t6 : U8 ← Mem.load U8 t5
      let t7 : Ptr ← Ptr.add cl3 1 8
      Mem.store t7 (UInt.toU 64 t6)
      let t8 : Agg ← Mem.loadAgg cl3 16 8
      t10 := t8
    else
      let t9 : Agg ← Mem.loadAgg lang_p 16 8
      t10 := t9
    return t10
    : M Agg)
  Mem.popFrame [lang_p, cl3]
  pure result

/-- C function `mp_match_lang`, ../.mpv/misc/language.c:254.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes external-reads: strncasecmp, strcasecmp and memrchr, taken as parameters, write no memory, as POSIX and glibc specify them; where C leaves the order of a call that reaches one of them and another operand open, the definition relies on this.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_match_lang [Ext.Misc_Language_c_lang_compare] [Ext.strncasecmp] (fuel : Nat) (langs : Ptr) (lang : Ptr) : M I32 := do
  let ta_ctx_1 ← Mem.alloca 8 8
  let lang_parts_n_2 ← Mem.alloca 4 4
  let lang_parts_3 ← Mem.alloca 8 8
  let rest_4 ← Mem.alloca 16 8
  let s_5 ← Mem.alloca 16 8
  let best_score_7 ← Mem.alloca 4 4
  let s_11 ← Mem.alloca 16 8
  let result : I32 ← (do
    let mut langs_v : Ptr := langs
    let mut lang_v : Ptr := lang
    for _ in Once.mk do
      if (!(lang_v != Ptr.null)) then
        return (0 : I32)
      let t1 : Ptr ← Talloc.ta_new_context Ptr.null
      let t2 : Ptr ← Ta.Ta_h.ta_oom_p fuel t1
      Mem.store ta_ctx_1 t2
      Mem.store lang_parts_n_2 (0 : I32)
      Mem.store lang_parts_3 Ptr.null
      let t3 : Agg ← Misc.Bstr_h.bstr0 fuel lang_v
      Mem.storeAgg rest_4 t3 8
      for _ in Fuel.mk fuel do
        let t4 : Ptr ← Ptr.add rest_4 1 8
        let t5 : U64 ← Mem.load U64 t4
        if !(t5 != 0) then break
        let t6 : Agg ← Mem.loadAgg rest_4 16 8
        let t7 : Agg ← Misc.Bstr_c.bstr_split fuel t6 Statics.str_105 rest_4
        Mem.storeAgg s_5 t7 8
        for _ in Fuel.mk fuel do
          for _ in Once.mk do
            for _ in Fuel.mk fuel do
              for _ in Once.mk do
                let t8 : I32 ← Mem.load I32 lang_parts_n_2
                let mut nextidx__6 : U64 := (SInt.toU 64 t8)
                let t9 : Ptr ← Mem.load Ptr lang_parts_3
                let t10 : U64 ← Talloc.ta_get_size t9
                let t11 : U64 ← UInt.div t10 (16 : U64)
                if (decide (nextidx__6 ≥ t11)) then
                  for _ in Fuel.mk fuel do
                    for _ in Once.mk do
                      let t12 : Ptr ← Mem.load Ptr ta_ctx_1
                      let t13 : Ptr ← Mem.load Ptr lang_parts_3
                      let t14 : U64 ← Talloc.ta_calc_prealloc_elems nextidx__6
                      let t15 : U64 ← Talloc.ta_calc_array_size (16 : U64) t14
                      let t16 : Ptr ← Talloc.ta_xrealloc_size t12 t13 t15
                      let t17 : Ptr ← Talloc.ta_dbg_set_loc t16 Statics.str_106
                      Mem.store lang_parts_3 t17
                    if !((0 : I32) != 0) then break
              if !((0 : I32) != 0) then break
            let t18 : Ptr ← Mem.load Ptr lang_parts_3
            let t19 : I32 ← Mem.load I32 lang_parts_n_2
            let t20 : Ptr ← Ptr.add t18 16 (SInt.toInt t19)
            let t21 : Agg ← Mem.loadAgg s_5 16 8
            Mem.storeAgg t20 t21 8
            let t22 : I32 ← Mem.load I32 lang_parts_n_2
            let t23 : I32 ← SInt.add t22 1
            Mem.store lang_parts_n_2 t23
          if !((0 : I32) != 0) then break
      Mem.store best_score_7 (0 : I32)
      let t24 : I32 ← Mem.load I32 lang_parts_n_2
      if (!(t24 != 0)) then
        break
      let mut idx_8 : I32 := (0 : I32)
      for _ in Fuel.mk fuel do
        let mut t27 : Bool := false
        if (langs_v != Ptr.null) then
          let t25 : Ptr ← Ptr.add langs_v 8 (SInt.toInt idx_8)
          let t26 : Ptr ← Mem.load Ptr t25
          t27 := (t26 != Ptr.null)
        if !t27 then break
        for _ in Once.mk do
          let t28 : Ptr ← Ptr.add langs_v 8 (SInt.toInt idx_8)
          let t29 : Ptr ← Mem.load Ptr t28
          let t30 : Agg ← Misc.Bstr_h.bstr0 fuel t29
          Mem.storeAgg rest_4 t30 8
          let mut part_9 : I32 := (0 : I32)
          let mut score_10 : I32 := (0 : I32)
          for _ in Fuel.mk fuel do
            let t31 : Ptr ← Ptr.add rest_4 1 8
            let t32 : U64 ← Mem.load U64 t31
            if !(t32 != 0) then break
            let t33 : Agg ← Mem.loadAgg rest_4 16 8
            let t34 : Agg ← Misc.Bstr_c.bstr_split fuel t33 Statics.str_105 rest_4
            Mem.storeAgg s_11 t34 8
            if (!(part_9 != 0)) then
              let t35 : Ptr ← Mem.load Ptr lang_parts_3
              let t36 : Ptr ← Ptr.add t35 16 (SInt.toInt (0 : I32))
              let t37 : Agg ← Mem.loadAgg t36 16 8
              let t38 : Agg ← Misc.Language_c.canonicalize fuel t37
              let t39 : Agg ← Mem.loadAgg s_11 16 8
              let t40 : Agg ← Misc.Language_c.canonicalize fuel t39
              let t41 : I32 ← Misc.Bstr_c.bstrcasecmp fuel t38 t40
              if (t41 != 0) then
                break
              let t42 : I32 ← SInt.sub (2147483647 : I32) idx_8
              score_10 := t42
              let t43 : I32 := part_9
              let t44 : I32 ← SInt.add t43 1
              part_9 := t44
              continue
            let t45 : I32 ← Mem.load I32 lang_parts_n_2
            if (decide (part_9 ≥ t45)) then
              break
            let t46 : Ptr ← Mem.load Ptr lang_parts_3
            let t47 : Ptr ← Ptr.add t46 16 (SInt.toInt part_9)
            let t48 : Agg ← Mem.loadAgg t47 16 8
            let t49 : Agg ← Mem.loadAgg s_11 16 8
            let t50 : I32 ← Misc.Bstr_c.bstrcasecmp fuel t48 t49
            if (t50 != 0) then
              let t51 : I32 ← SInt.sub score_10 (1000 : I32)
              score_10 := t51
            let t52 : I32 := part_9
            let t53 : I32 ← SInt.add t52 1
            part_9 := t53
          let t54 : I32 ← Mem.load I32 lang_parts_n_2
          let t55 : I32 ← SInt.sub t54 part_9
          let t56 : I32 ← SInt.mul t55 (1000 : I32)
          let t57 : I32 ← SInt.sub score_10 t56
          score_10 := t57
          let t58 : I32 ← Mem.load I32 best_score_7
          let mut t60 : I32 := default
          if (decide (t58 > score_10)) then
            let t59 : I32 ← Mem.load I32 best_score_7
            t60 := t59
          else
            t60 := score_10
          Mem.store best_score_7 t60
        let t61 : I32 := idx_8
        let t62 : I32 ← SInt.add t61 1
        idx_8 := t62
    let t63 : Ptr ← Mem.load Ptr ta_ctx_1
    Talloc.ta_free t63
    let t64 : I32 ← Mem.load I32 best_score_7
    return t64
    : M I32)
  Mem.popFrame [ta_ctx_1, lang_parts_n_2, lang_parts_3, rest_4, s_5, best_score_7, s_11]
  pure result

/-- C function `mp_guess_lang_from_filename`, ../.mpv/misc/language.c:303.
-/
def mp_guess_lang_from_filename [Ext.memrchr] [Ext.strncasecmp] (fuel : Nat) (name : Agg) (lang_start : Ptr) (flags : Ptr) : M Agg := do
  let name_p ← Mem.alloca 16 8
  let tag_8 ← Mem.alloca 16 8
  let cl8 ← Mem.alloca 16 8
  let cl25 ← Mem.alloca 4 4
  let cl70 ← Mem.alloca 16 8
  let cl88 ← Mem.alloca 16 8
  let cl91 ← Mem.alloca 16 8
  let result : Agg ← (do
    Mem.storeAgg name_p name 8
    let mut lang_start_v : Ptr := lang_start
    let mut flags_v : Ptr := flags
    let t1 : Agg ← Mem.loadAgg name_p 16 8
    let t2 : Agg ← Misc.Path_utils_c.mp_strip_ext fuel t1
    let t3 : Agg ← Misc.Bstr_c.bstr_strip fuel t2
    Mem.storeAgg name_p t3 8
    if (lang_start_v != Ptr.null) then
      let t4 : I32 := (SInt.ofInt 32 (-1))
      Mem.store lang_start_v t4
    if (flags_v != Ptr.null) then
      let t5 : U32 := (SInt.toU 32 (0 : I32))
      Mem.store flags_v t5
    let t6 : Ptr ← Ptr.add name_p 1 8
    let t7 : U64 ← Mem.load U64 t6
    if (decide (t7 < (SInt.toU 64 (2 : I32)))) then
      Mem.undefine cl8 16
      Mem.store cl8 Ptr.null
      let t9 : Ptr ← Ptr.add cl8 1 8
      Mem.zero t9 8
      let t10 : Agg ← Mem.loadAgg cl8 16 8
      return t10
    let mut lang_length_1 : I32 := (0 : I32)
    let t11 : Ptr ← Ptr.add name_p 1 8
    let t12 : U64 ← Mem.load U64 t11
    let mut i_2 : I32 := (UInt.toS 32 (t12 - (SInt.toU 64 (1 : I32))))
    let mut suffixes_length_3 : I32 := (0 : I32)
    let mut delimiter_4 : I8 := (SInt.toS 8 (46 : I32))
    let t13 : Ptr ← Mem.load Ptr name_p
    let t14 : Ptr ← Ptr.add t13 1 (SInt.toInt i_2)
    let t15 : U8 ← Mem.load U8 t14
    if ((UInt.toS 32 t15) == (41 : I32)) then
      let t16 : I8 := (SInt.toS 8 (40 : I32))
      delimiter_4 := t16
      let t17 : I32 := i_2
      let t18 : I32 ← SInt.sub t17 1
      i_2 := t18
    let t19 : Ptr ← Mem.load Ptr name_p
    let t20 : Ptr ← Ptr.add t19 1 (SInt.toInt i_2)
    let t21 : U8 ← Mem.load U8 t20
    if ((UInt.toS 32 t21) == (93 : I32)) then
      let t22 : I8 := (SInt.toS 8 (91 : I32))
      delimiter_4 := t22
      let t23 : I32 := i_2
      let t24 : I32 ← SInt.sub t23 1
      i_2 := t24
    let mut t26 : Ptr := default
    if (flags_v != Ptr.null) then
      t26 := flags_v
    else
      Mem.undefine cl25 4
      Mem.store cl25 (SInt.toU 32 (0 : I32))
      t26 := cl25
    let mut f_5 : Ptr := t26
    for _ in Fuel.mk fuel do
      if !((1 : I32) != 0) then break
      for _ in Fuel.mk fuel do
        let mut t31 : Bool := false
        if (decide (i_2 ≥ (0 : I32))) then
          let t27 : Ptr ← Mem.load Ptr name_p
          let t28 : Ptr ← Ptr.add t27 1 (SInt.toInt i_2)
          let t29 : U8 ← Mem.load U8 t28
          let t30 : I32 ← Misc.Ctype_h.mp_isalpha fuel (UInt.toS 8 t29)
          t31 := (t30 != 0)
        if !t31 then break
        let t32 : I32 := lang_length_1
        let t33 : I32 ← SInt.add t32 1
        lang_length_1 := t33
        let t34 : I32 := i_2
        let t35 : I32 ← SInt.sub t34 1
        i_2 := t35
      let mut t39 : Bool := false
      if ((decide (i_2 ≥ (0 : I32))) && (decide (lang_length_1 ≥ (2 : I32)))) then
        let t36 : Ptr ← Mem.load Ptr name_p
        let t37 : Ptr ← Ptr.add t36 1 (SInt.toInt i_2)
        let t38 : U8 ← Mem.load U8 t37
        t39 := ((UInt.toS 32 t38) == (SInt.toS 32 delimiter_4))
      if t39 then
        let mut matched_6 : Bool := ((0 : I32) != 0)
        let t40 : Ptr ← Mem.load Ptr name_p
        let t41 : Ptr ← Ptr.add t40 1 (SInt.toInt i_2)
        let t42 : Ptr ← Ptr.add t41 1 (SInt.toInt (1 : I32))
        Mem.store tag_8 t42
        let t43 : Ptr ← Ptr.add tag_8 1 8
        Mem.store t43 (SInt.toU 64 lang_length_1)
        let mut n_9 : I32 := (0 : I32)
        for _ in Fuel.mk fuel do
          let t44 : U64 ← UInt.div (24 : U64) (8 : U64)
          if !(decide ((SInt.toU 64 n_9) < t44)) then break
          let mut j52 := false
          for _ in Once.mk do
            let t45 : Agg ← Mem.loadAgg tag_8 16 8
            let t46 : Ptr ← Ptr.add Statics.s_Misc_Language_c_mp_guess_lang_from_filename_suffixes 8 (SInt.toInt n_9)
            let t47 : Ptr ← Mem.load Ptr t46
            let t48 : I32 ← Misc.Bstr_h.bstrcasecmp0 fuel t45 t47
            if (!(t48 != 0)) then
              let t49 : U32 ← Mem.load U32 f_5
              let t50 : U32 := (UInt.bor t49 (SInt.toU 32 (4 : I32)))
              Mem.store f_5 t50
              let t51 : Bool := ((1 : I32) != 0)
              matched_6 := t51
              j52 := true
              break
          if j52 then break
          let t53 : I32 := n_9
          let t54 : I32 ← SInt.add t53 1
          n_9 := t54
        let t55 : Agg ← Mem.loadAgg tag_8 16 8
        let t56 : I32 ← Misc.Bstr_h.bstrcasecmp0 fuel t55 Statics.str_111
        if (!(t56 != 0)) then
          let t57 : U32 ← Mem.load U32 f_5
          let t58 : U32 := (UInt.bor t57 (SInt.toU 32 (32 : I32)))
          Mem.store f_5 t58
          let t59 : Bool := ((1 : I32) != 0)
          matched_6 := t59
        let t60 : Agg ← Mem.loadAgg tag_8 16 8
        let t61 : I32 ← Misc.Bstr_h.bstrcasecmp0 fuel t60 Statics.str_112
        if (!(t61 != 0)) then
          let t62 : U32 ← Mem.load U32 f_5
          let t63 : U32 := (UInt.bor t62 (SInt.toU 32 (64 : I32)))
          Mem.store f_5 t63
          let t64 : Bool := ((1 : I32) != 0)
          matched_6 := t64
        if matched_6 then
          let t65 : I32 := (0 : I32)
          lang_length_1 := t65
          let t66 : I32 ← SInt.sub i_2 (if ((SInt.toS 32 delimiter_4) != (46 : I32)) then (2 : I32) else (1 : I32))
          i_2 := t66
          continue
      let t67 : I32 ← SInt.add suffixes_length_3 (1 : I32)
      let mut t69 : Bool := true
      if !(decide (lang_length_1 < t67)) then
        let t68 : I32 ← SInt.add suffixes_length_3 (8 : I32)
        t69 := (decide (lang_length_1 > t68))
      if t69 then
        Mem.undefine cl70 16
        Mem.store cl70 Ptr.null
        let t71 : Ptr ← Ptr.add cl70 1 8
        Mem.zero t71 8
        let t72 : Agg ← Mem.loadAgg cl70 16 8
        return t72
      let mut t76 : Bool := false
      if (decide (i_2 ≥ (0 : I32))) then
        let t73 : Ptr ← Mem.load Ptr name_p
        let t74 : Ptr ← Ptr.add t73 1 (SInt.toInt i_2)
        let t75 : U8 ← Mem.load U8 t74
        t76 := ((UInt.toS 32 t75) == (45 : I32))
      if t76 then
        let t77 : I32 := lang_length_1
        let t78 : I32 ← SInt.add t77 1
        lang_length_1 := t78
        let t79 : I32 := i_2
        let t80 : I32 ← SInt.sub t79 1
        i_2 := t80
        suffixes_length_3 := lang_length_1
      else
        break
    let t81 : I32 ← SInt.add suffixes_length_3 (2 : I32)
    let mut t83 : Bool := true
    if !(decide (lang_length_1 < t81)) then
      let t82 : I32 ← SInt.add suffixes_length_3 (3 : I32)
      t83 := (decide (lang_length_1 > t82))
    let mut t87 : Bool := true
    if !(t83 || (decide (i_2 ≤ (0 : I32)))) then
      let t84 : Ptr ← Mem.load Ptr name_p
      let t85 : Ptr ← Ptr.add t84 1 (SInt.toInt i_2)
      let t86 : U8 ← Mem.load U8 t85
      t87 := ((UInt.toS 32 t86) != (SInt.toS 32 delimiter_4))
    if t87 then
      Mem.undefine cl88 16
      Mem.store cl88 Ptr.null
      let t89 : Ptr ← Ptr.add cl88 1 8
      Mem.zero t89 8
      let t90 : Agg ← Mem.loadAgg cl88 16 8
      return t90
    if (lang_start_v != Ptr.null) then
      Mem.store lang_start_v i_2
    Mem.undefine cl91 16
    let t92 : Ptr ← Mem.load Ptr name_p
    let t93 : Ptr ← Ptr.add t92 1 (SInt.toInt i_2)
    let t94 : Ptr ← Ptr.add t93 1 (SInt.toInt (1 : I32))
    Mem.store cl91 t94
    let t95 : Ptr ← Ptr.add cl91 1 8
    Mem.store t95 (SInt.toU 64 lang_length_1)
    let t96 : Agg ← Mem.loadAgg cl91 16 8
    return t96
    : M Agg)
  Mem.popFrame [name_p, tag_8, cl8, cl25, cl70, cl88, cl91]
  pure result

end Misc.Misc.Language_c
