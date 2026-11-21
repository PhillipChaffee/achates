import Achates
import Misc.Statics
import Misc.Externals

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Random_c

/-- C function `rotl_u64`, ../.mpv/misc/random.c:31.
-/
def rotl_u64 (fuel : Nat) (x : U64) (k : I32) : M U64 := do
  let mut x_v : U64 := x
  let mut k_v : I32 := k
  let t1 : U64 ← UInt.shl x_v (SInt.toInt k_v)
  let t2 : I32 ← SInt.sub (64 : I32) k_v
  let t3 : U64 ← UInt.shr x_v (SInt.toInt t2)
  return (UInt.bor t1 t3)

/-- C function `splitmix64`, ../.mpv/misc/random.c:36.
-/
def splitmix64 (fuel : Nat) (x : Ptr) : M U64 := do
  let mut x_v : Ptr := x
  let t1 : U64 ← Mem.load U64 x_v
  let t2 : U64 := (t1 + (11400714819323198485 : U64))
  Mem.store x_v t2
  let mut z_1 : U64 := t2
  let t3 : U64 ← UInt.shr z_1 (SInt.toInt (30 : I32))
  let t4 : U64 := ((UInt.bxor z_1 t3) * (13787848793156543929 : U64))
  z_1 := t4
  let t5 : U64 ← UInt.shr z_1 (SInt.toInt (27 : I32))
  let t6 : U64 := ((UInt.bxor z_1 t5) * (10723151780598845931 : U64))
  z_1 := t6
  let t7 : U64 ← UInt.shr z_1 (SInt.toInt (31 : I32))
  return (UInt.bxor z_1 t7)

/-- C function `mp_rand_seed`, ../.mpv/misc/random.c:44.
-/
def mp_rand_seed [Ext.av_random_bytes] [Ext.mp_raw_time_ns] (fuel : Nat) (seed : U64) : M Agg := do
  let seed_p ← Mem.alloca 8 8
  let ret_1 ← Mem.alloca 32 8
  let result : Agg ← (do
    Mem.store seed_p seed
    Mem.undefine ret_1 32
    let t1 : U64 ← Mem.load U64 seed_p
    if (t1 == (SInt.toU 64 (0 : I32))) then
      let t2 : I32 ← Ext.av_random_bytes.call ret_1 (32 : U64)
      if (t2 == (0 : I32)) then
        let t3 : Agg ← Mem.loadAgg ret_1 32 8
        return t3
      let t4 : U64 ← Ext.mp_raw_time_ns.call
      Mem.store seed_p t4
      let t5 : U64 ← Mem.load U64 seed_p
      let t6 : Nat ← Ptr.toNat (Ptr.fn "mp_rand_seed")
      let t7 : U64 := (UInt.bxor t5 (UInt.ofNat 64 t6))
      Mem.store seed_p t7
      let t8 : U64 ← Mem.load U64 seed_p
      let t9 : Nat ← Ptr.toNat ret_1
      let t10 : U64 := (t8 + (UInt.ofNat 64 t9))
      Mem.store seed_p t10
    let t11 : Ptr ← Ptr.add ret_1 8 (SInt.toInt (0 : I32))
    let t12 : U64 ← Mem.load U64 seed_p
    Mem.store t11 t12
    let mut i_2 : I32 := (1 : I32)
    for _ in Fuel.mk fuel do
      if !(decide (i_2 < (4 : I32))) then break
      for _ in Once.mk do
        let t13 : Ptr ← Ptr.add ret_1 8 (SInt.toInt i_2)
        let t14 : U64 ← Misc.Random_c.splitmix64 fuel seed_p
        Mem.store t13 t14
      let t15 : I32 := i_2
      let t16 : I32 ← SInt.add t15 1
      i_2 := t16
    let t17 : Agg ← Mem.loadAgg ret_1 32 8
    return t17
    : M Agg)
  Mem.popFrame [seed_p, ret_1]
  pure result

/-- C function `mp_rand_next`, ../.mpv/misc/random.c:67.
-/
def mp_rand_next (fuel : Nat) (s : Ptr) : M U64 := do
  let v_result_1 ← Mem.alloca 8 8
  let t_2 ← Mem.alloca 8 8
  let result : U64 ← (do
    let mut s_v : Ptr := s
    Mem.undefine v_result_1 8
    Mem.undefine t_2 8
    let mut state_3 : Ptr := s_v
    let t1 : Ptr ← Ptr.add state_3 8 (SInt.toInt (1 : I32))
    let t2 : U64 ← Mem.load U64 t1
    let t3 : U64 ← Misc.Random_c.rotl_u64 fuel (t2 * (SInt.toU 64 (5 : I32))) (7 : I32)
    let t4 : U64 := (t3 * (SInt.toU 64 (9 : I32)))
    Mem.store v_result_1 t4
    let t5 : Ptr ← Ptr.add state_3 8 (SInt.toInt (1 : I32))
    let t6 : U64 ← Mem.load U64 t5
    let t7 : U64 ← UInt.shl t6 (SInt.toInt (17 : I32))
    Mem.store t_2 t7
    let t8 : Ptr ← Ptr.add state_3 8 (SInt.toInt (2 : I32))
    let t9 : U64 ← Mem.load U64 t8
    let t10 : Ptr ← Ptr.add state_3 8 (SInt.toInt (0 : I32))
    let t11 : U64 ← Mem.load U64 t10
    let t12 : U64 := (UInt.bxor t9 t11)
    Mem.store t8 t12
    let t13 : Ptr ← Ptr.add state_3 8 (SInt.toInt (3 : I32))
    let t14 : U64 ← Mem.load U64 t13
    let t15 : Ptr ← Ptr.add state_3 8 (SInt.toInt (1 : I32))
    let t16 : U64 ← Mem.load U64 t15
    let t17 : U64 := (UInt.bxor t14 t16)
    Mem.store t13 t17
    let t18 : Ptr ← Ptr.add state_3 8 (SInt.toInt (1 : I32))
    let t19 : U64 ← Mem.load U64 t18
    let t20 : Ptr ← Ptr.add state_3 8 (SInt.toInt (2 : I32))
    let t21 : U64 ← Mem.load U64 t20
    let t22 : U64 := (UInt.bxor t19 t21)
    Mem.store t18 t22
    let t23 : Ptr ← Ptr.add state_3 8 (SInt.toInt (0 : I32))
    let t24 : U64 ← Mem.load U64 t23
    let t25 : Ptr ← Ptr.add state_3 8 (SInt.toInt (3 : I32))
    let t26 : U64 ← Mem.load U64 t25
    let t27 : U64 := (UInt.bxor t24 t26)
    Mem.store t23 t27
    let t28 : Ptr ← Ptr.add state_3 8 (SInt.toInt (2 : I32))
    let t29 : U64 ← Mem.load U64 t28
    let t30 : U64 ← Mem.load U64 t_2
    let t31 : U64 := (UInt.bxor t29 t30)
    Mem.store t28 t31
    let t32 : Ptr ← Ptr.add state_3 8 (SInt.toInt (3 : I32))
    let t33 : Ptr ← Ptr.add state_3 8 (SInt.toInt (3 : I32))
    let t34 : U64 ← Mem.load U64 t33
    let t35 : U64 ← Misc.Random_c.rotl_u64 fuel t34 (45 : I32)
    Mem.store t32 t35
    let t36 : U64 ← Mem.load U64 v_result_1
    return t36
    : M U64)
  Mem.popFrame [v_result_1, t_2]
  pure result

/-- C function `mp_rand_next_double`, ../.mpv/misc/random.c:85.
Assumes signed-zeros: compiled with -fno-signed-zeros, so the compiled C may differ from this definition in the sign of a zero.
-/
def mp_rand_next_double (fuel : Nat) (s : Ptr) : M F64 := do
  let mut s_v : Ptr := s
  let t1 : U64 ← Misc.Random_c.mp_rand_next fuel s_v
  let t2 : U64 ← UInt.shr t1 (SInt.toInt (11 : I32))
  let t3 : F64 ← F64.ofU t2
  return (t3 * (Float.ofBits 0x3ca0000000000000))

/-- C function `mp_rand_in_range32`, ../.mpv/misc/random.c:92.
-/
def mp_rand_in_range32 [Ext.mp_round_next_power_of_2] (fuel : Nat) (s : Ptr) (min : U32) (max : U32) : M U32 := do
  let ret_3 ← Mem.alloca 4 4
  let result : U32 ← (do
    let mut s_v : Ptr := s
    let mut min_v : U32 := min
    let mut max_v : U32 := max
    let mut t1 : Unit := default
    if (decide (min_v < max_v)) then
      t1 := ()
    else
      Libc.«__assert_fail» Statics.str_143 Statics.str_144 (SInt.toU 32 (94 : I32)) Statics.str_145
      t1 := ()
    let mut range_1 : U32 := (max_v - min_v)
    let t2 : U32 ← Ext.mp_round_next_power_of_2.call range_1
    let mut mask_2 : U32 := (t2 - (SInt.toU 32 (1 : I32)))
    Mem.undefine ret_3 4
    for _ in Fuel.mk fuel do
      for _ in Once.mk do
        let t3 : U64 ← Misc.Random_c.mp_rand_next fuel s_v
        let t4 : U32 := (UInt.toU 32 (UInt.band t3 (UInt.toU 64 mask_2)))
        Mem.store ret_3 t4
      let t5 : U32 ← Mem.load U32 ret_3
      if !(decide (t5 ≥ range_1)) then break
    let t6 : U32 ← Mem.load U32 ret_3
    return (min_v + t6)
    : M U32)
  Mem.popFrame [ret_3]
  pure result

end Misc.Misc.Random_c
