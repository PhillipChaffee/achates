import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Ctype_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Natural_sort_c

/-- C function `mp_natural_sort_cmp`, ../.mpv/misc/natural_sort.c:26.
-/
def mp_natural_sort_cmp (fuel : Nat) (name1 : Ptr) (name2 : Ptr) : M I32 := do
  let mut name1_v : Ptr := name1
  let mut name2_v : Ptr := name2
  for _ in Fuel.mk fuel do
    let t1 : Ptr ← Ptr.add name1_v 1 (SInt.toInt (0 : I32))
    let t2 : I8 ← Mem.load I8 t1
    let mut t5 : Bool := false
    if ((SInt.toS 32 t2) != 0) then
      let t3 : Ptr ← Ptr.add name2_v 1 (SInt.toInt (0 : I32))
      let t4 : I8 ← Mem.load I8 t3
      t5 := ((SInt.toS 32 t4) != 0)
    if !t5 then break
    let t6 : Ptr ← Ptr.add name1_v 1 (SInt.toInt (0 : I32))
    let t7 : I8 ← Mem.load I8 t6
    let t8 : I32 ← Misc.Ctype_h.mp_isdigit fuel t7
    let mut t12 : Bool := false
    if (t8 != 0) then
      let t9 : Ptr ← Ptr.add name2_v 1 (SInt.toInt (0 : I32))
      let t10 : I8 ← Mem.load I8 t9
      let t11 : I32 ← Misc.Ctype_h.mp_isdigit fuel t10
      t12 := (t11 != 0)
    if t12 then
      for _ in Fuel.mk fuel do
        let t13 : Ptr ← Ptr.add name1_v 1 (SInt.toInt (0 : I32))
        let t14 : I8 ← Mem.load I8 t13
        if !((SInt.toS 32 t14) == (48 : I32)) then break
        let t15 : Ptr := name1_v
        let t16 : Ptr ← Ptr.add t15 1 1
        name1_v := t16
      for _ in Fuel.mk fuel do
        let t17 : Ptr ← Ptr.add name2_v 1 (SInt.toInt (0 : I32))
        let t18 : I8 ← Mem.load I8 t17
        if !((SInt.toS 32 t18) == (48 : I32)) then break
        let t19 : Ptr := name2_v
        let t20 : Ptr ← Ptr.add t19 1 1
        name2_v := t20
      let mut end1_1 : Ptr := name1_v
      let mut end2_2 : Ptr := name2_v
      for _ in Fuel.mk fuel do
        let t21 : I8 ← Mem.load I8 end1_1
        let t22 : I32 ← Misc.Ctype_h.mp_isdigit fuel t21
        if !(t22 != 0) then break
        let t23 : Ptr := end1_1
        let t24 : Ptr ← Ptr.add t23 1 1
        end1_1 := t24
      for _ in Fuel.mk fuel do
        let t25 : I8 ← Mem.load I8 end2_2
        let t26 : I32 ← Misc.Ctype_h.mp_isdigit fuel t25
        if !(t26 != 0) then break
        let t27 : Ptr := end2_2
        let t28 : Ptr ← Ptr.add t27 1 1
        end2_2 := t28
      let t29 : I64 ← Ptr.diff end1_1 name1_v 1
      let t30 : I64 ← Ptr.diff end2_2 name2_v 1
      if (decide (t29 < t30)) then
        return (SInt.ofInt 32 (-1))
      let t31 : I64 ← Ptr.diff end1_1 name1_v 1
      let t32 : I64 ← Ptr.diff end2_2 name2_v 1
      if (decide (t31 > t32)) then
        return (1 : I32)
      for _ in Fuel.mk fuel do
        let t33 : Bool ← Ptr.lt name1_v end1_1
        if !t33 then break
        let t34 : Ptr ← Ptr.add name1_v 1 (SInt.toInt (0 : I32))
        let t35 : I8 ← Mem.load I8 t34
        let t36 : Ptr ← Ptr.add name2_v 1 (SInt.toInt (0 : I32))
        let t37 : I8 ← Mem.load I8 t36
        if (decide ((SInt.toS 32 t35) < (SInt.toS 32 t37))) then
          return (SInt.ofInt 32 (-1))
        let t38 : Ptr ← Ptr.add name1_v 1 (SInt.toInt (0 : I32))
        let t39 : I8 ← Mem.load I8 t38
        let t40 : Ptr ← Ptr.add name2_v 1 (SInt.toInt (0 : I32))
        let t41 : I8 ← Mem.load I8 t40
        if (decide ((SInt.toS 32 t39) > (SInt.toS 32 t41))) then
          return (1 : I32)
        let t42 : Ptr := name1_v
        let t43 : Ptr ← Ptr.add t42 1 1
        name1_v := t43
        let t44 : Ptr := name2_v
        let t45 : Ptr ← Ptr.add t44 1 1
        name2_v := t45
    else
      let t46 : Ptr ← Ptr.add name1_v 1 (SInt.toInt (0 : I32))
      let t47 : I8 ← Mem.load I8 t46
      let t48 : I8 ← Misc.Ctype_h.mp_tolower fuel t47
      let t49 : Ptr ← Ptr.add name2_v 1 (SInt.toInt (0 : I32))
      let t50 : I8 ← Mem.load I8 t49
      let t51 : I8 ← Misc.Ctype_h.mp_tolower fuel t50
      if (decide ((UInt.toS 32 (SInt.toU 8 t48)) < (UInt.toS 32 (SInt.toU 8 t51)))) then
        return (SInt.ofInt 32 (-1))
      let t52 : Ptr ← Ptr.add name1_v 1 (SInt.toInt (0 : I32))
      let t53 : I8 ← Mem.load I8 t52
      let t54 : I8 ← Misc.Ctype_h.mp_tolower fuel t53
      let t55 : Ptr ← Ptr.add name2_v 1 (SInt.toInt (0 : I32))
      let t56 : I8 ← Mem.load I8 t55
      let t57 : I8 ← Misc.Ctype_h.mp_tolower fuel t56
      if (decide ((UInt.toS 32 (SInt.toU 8 t54)) > (UInt.toS 32 (SInt.toU 8 t57)))) then
        return (1 : I32)
      let t58 : Ptr := name1_v
      let t59 : Ptr ← Ptr.add t58 1 1
      name1_v := t59
      let t60 : Ptr := name2_v
      let t61 : Ptr ← Ptr.add t60 1 1
      name2_v := t61
  let t62 : Ptr ← Ptr.add name2_v 1 (SInt.toInt (0 : I32))
  let t63 : I8 ← Mem.load I8 t62
  if (t63 != 0) then
    return (SInt.ofInt 32 (-1))
  let t64 : Ptr ← Ptr.add name1_v 1 (SInt.toInt (0 : I32))
  let t65 : I8 ← Mem.load I8 t64
  if (t65 != 0) then
    return (1 : I32)
  return (0 : I32)

end Misc.Misc.Natural_sort_c
