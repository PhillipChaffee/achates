import Achates
import Misc.Statics
import Misc.Externals

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Osdep.Threads_posix_h

/-- C function `mp_cond_broadcast`, ../.mpv/osdep/threads-posix.h:165.
-/
def mp_cond_broadcast [Ext.pthread_cond_broadcast] (fuel : Nat) (cond : Ptr) : M I32 := do
  let mut cond_v : Ptr := cond
  let mut t1 : Unit := default
  if (cond_v != Ptr.null) then
    t1 := ()
  else
    Libc.«__assert_fail» Statics.str_61 Statics.str_62 (SInt.toU 32 (167 : I32)) Statics.str_63
    t1 := ()
  let t2 : I32 ← Ext.pthread_cond_broadcast.call cond_v
  return t2

/-- C function `mp_cond_destroy`, ../.mpv/osdep/threads-posix.h:159.
-/
def mp_cond_destroy [Ext.pthread_cond_destroy] (fuel : Nat) (cond : Ptr) : M I32 := do
  let mut cond_v : Ptr := cond
  let mut t1 : Unit := default
  if (cond_v != Ptr.null) then
    t1 := ()
  else
    Libc.«__assert_fail» Statics.str_61 Statics.str_62 (SInt.toU 32 (161 : I32)) Statics.str_64
    t1 := ()
  let t2 : I32 ← Ext.pthread_cond_destroy.call cond_v
  return t2

/-- C function `mp_cond_init`, ../.mpv/osdep/threads-posix.h:138.
-/
def mp_cond_init [Ext.pthread_cond_init] [Ext.pthread_condattr_destroy] [Ext.pthread_condattr_init] [Ext.pthread_condattr_setclock] (fuel : Nat) (cond : Ptr) : M I32 := do
  let attr_2 ← Mem.alloca 4 4
  let result : I32 ← (do
    let mut cond_v : Ptr := cond
    let mut t1 : Unit := default
    if (cond_v != Ptr.null) then
      t1 := ()
    else
      Libc.«__assert_fail» Statics.str_61 Statics.str_62 (SInt.toU 32 (140 : I32)) Statics.str_65
      t1 := ()
    let mut ret_1 : I32 := (0 : I32)
    Mem.undefine attr_2 4
    let t2 : I32 ← Ext.pthread_condattr_init.call attr_2
    ret_1 := t2
    if (ret_1 != 0) then
      return ret_1
    let t3 : Ptr ← Ptr.add cond_v 1 48
    let t4 : I32 := (0 : I32)
    Mem.store t3 t4
    let t5 : I32 ← Ext.pthread_condattr_setclock.call attr_2 (1 : I32)
    if (!(t5 != 0)) then
      let t6 : Ptr ← Ptr.add cond_v 1 48
      let t7 : I32 := (1 : I32)
      Mem.store t6 t7
    let t8 : I32 ← Ext.pthread_cond_init.call cond_v attr_2
    ret_1 := t8
    let t9 : I32 ← Ext.pthread_condattr_destroy.call attr_2
    return ret_1
    : M I32)
  Mem.popFrame [attr_2]
  pure result

/-- C function `mp_cond_timedwait`, ../.mpv/osdep/threads-posix.h:183.
-/
def mp_cond_timedwait [Ext.clock_gettime] [Ext.pthread_cond_timedwait] [Ext.pthread_cond_wait] (fuel : Nat) (cond : Ptr) (mutex : Ptr) (timeout : I64) : M I32 := do
  let ts_1 ← Mem.alloca 16 8
  let result : I32 ← (do
    let mut cond_v : Ptr := cond
    let mut mutex_v : Ptr := mutex
    let mut timeout_v : I64 := timeout
    let mut t1 : Unit := default
    if (cond_v != Ptr.null) then
      t1 := ()
    else
      Libc.«__assert_fail» Statics.str_61 Statics.str_62 (SInt.toU 32 (185 : I32)) Statics.str_66
      t1 := ()
    let t2 : I64 := (if (decide ((SInt.toS 64 (0 : I32)) > timeout_v)) then (SInt.toS 64 (0 : I32)) else timeout_v)
    timeout_v := t2
    let t3 : I32 ← SInt.mul (1000 : I32) (24 : I32)
    let t4 : I32 ← SInt.mul t3 (60 : I32)
    let t5 : I32 ← SInt.mul t4 (60 : I32)
    let t6 : I64 ← SInt.mul (SInt.toS 64 t5) (1000000000 : I64)
    if (decide (timeout_v > t6)) then
      let t7 : I32 ← Ext.pthread_cond_wait.call cond_v mutex_v
      return t7
    Mem.undefine ts_1 16
    let t8 : Ptr ← Ptr.add cond_v 1 48
    let t9 : I32 ← Mem.load I32 t8
    let t10 : I32 ← Ext.clock_gettime.call t9 ts_1
    let t11 : I64 ← Mem.load I64 ts_1
    let t12 : I64 ← SInt.mul (SInt.toS 64 (1 : I32)) (1000000000 : I64)
    let t13 : I64 ← SInt.div timeout_v t12
    let t14 : I64 ← SInt.add t11 t13
    Mem.store ts_1 t14
    let t15 : Ptr ← Ptr.add ts_1 1 8
    let t16 : I64 ← Mem.load I64 t15
    let t17 : I64 ← SInt.mul (SInt.toS 64 (1 : I32)) (1000000000 : I64)
    let t18 : I64 ← SInt.rem timeout_v t17
    let t19 : I64 ← SInt.add t16 t18
    Mem.store t15 t19
    let t20 : Ptr ← Ptr.add ts_1 1 8
    let t21 : I64 ← Mem.load I64 t20
    let t22 : I64 ← SInt.mul (SInt.toS 64 (1 : I32)) (1000000000 : I64)
    if (decide (t21 ≥ t22)) then
      let t23 : Ptr ← Ptr.add ts_1 1 8
      let t24 : I64 ← Mem.load I64 t23
      let t25 : I64 ← SInt.mul (SInt.toS 64 (1 : I32)) (1000000000 : I64)
      let t26 : I64 ← SInt.sub t24 t25
      Mem.store t23 t26
      let t27 : I64 ← Mem.load I64 ts_1
      let t28 : I64 ← SInt.add t27 1
      Mem.store ts_1 t28
    let t29 : I32 ← Ext.pthread_cond_timedwait.call cond_v mutex_v ts_1
    return t29
    : M I32)
  Mem.popFrame [ts_1]
  pure result

/-- C function `mp_cond_timedwait_until`, ../.mpv/osdep/threads-posix.h:204.
-/
def mp_cond_timedwait_until [Ext.clock_gettime] [Ext.mp_time_ns] [Ext.pthread_cond_timedwait] [Ext.pthread_cond_wait] (fuel : Nat) (cond : Ptr) (mutex : Ptr) (v_until : I64) : M I32 := do
  let mut cond_v : Ptr := cond
  let mut mutex_v : Ptr := mutex
  let mut v_until_v : I64 := v_until
  let t1 : I64 ← Ext.mp_time_ns.call
  let t2 : I64 ← SInt.sub v_until_v t1
  let t3 : I32 ← Osdep.Threads_posix_h.mp_cond_timedwait fuel cond_v mutex_v t2
  return t3

/-- C function `mp_cond_wait`, ../.mpv/osdep/threads-posix.h:177.
-/
def mp_cond_wait [Ext.pthread_cond_wait] (fuel : Nat) (cond : Ptr) (mutex : Ptr) : M I32 := do
  let mut cond_v : Ptr := cond
  let mut mutex_v : Ptr := mutex
  let mut t1 : Unit := default
  if (cond_v != Ptr.null) then
    t1 := ()
  else
    Libc.«__assert_fail» Statics.str_61 Statics.str_62 (SInt.toU 32 (179 : I32)) Statics.str_67
    t1 := ()
  let t2 : I32 ← Ext.pthread_cond_wait.call cond_v mutex_v
  return t2

/-- C function `mp_mutex_init`, ../.mpv/osdep/threads-posix.h:112.
-/
def mp_mutex_init [Ext.pthread_mutex_init] [Ext.pthread_mutexattr_destroy] [Ext.pthread_mutexattr_init] [Ext.pthread_mutexattr_settype] (fuel : Nat) (mutex : Ptr) : M I32 := do
  let attr_3 ← Mem.alloca 4 4
  let result : I32 ← (do
    let mut mutex_v : Ptr := mutex
    let mut mutex_type_1 : I32 := (2 : I32)
    let mut ret_2 : I32 := (0 : I32)
    Mem.undefine attr_3 4
    let t1 : I32 ← Ext.pthread_mutexattr_init.call attr_3
    ret_2 := t1
    if (ret_2 != (0 : I32)) then
      return ret_2
    let t2 : I32 ← Ext.pthread_mutexattr_settype.call attr_3 mutex_type_1
    let t3 : I32 ← Ext.pthread_mutex_init.call mutex_v attr_3
    ret_2 := t3
    let t4 : I32 ← Ext.pthread_mutexattr_destroy.call attr_3
    let mut t5 : Unit := default
    if (!(ret_2 != 0)) then
      t5 := ()
    else
      Libc.«__assert_fail» Statics.str_68 Statics.str_62 (SInt.toU 32 (129 : I32)) Statics.str_69
      t5 := ()
    return ret_2
    : M I32)
  Mem.popFrame [attr_3]
  pure result

/-- C function `mp_cond_signal`, ../.mpv/osdep/threads-posix.h:171.
-/
def mp_cond_signal [Ext.pthread_cond_signal] (fuel : Nat) (cond : Ptr) : M I32 := do
  let mut cond_v : Ptr := cond
  let mut t1 : Unit := default
  if (cond_v != Ptr.null) then
    t1 := ()
  else
    Libc.«__assert_fail» Statics.str_61 Statics.str_62 (SInt.toU 32 (173 : I32)) Statics.str_163
    t1 := ()
  let t2 : I32 ← Ext.pthread_cond_signal.call cond_v
  return t2

/-- C function `mp_thread_set_name`, ../.mpv/osdep/threads-posix.h:221.
-/
def mp_thread_set_name [Ext.pthread_self] [Ext.pthread_setname_np] [Ext.strncpy] (fuel : Nat) (name : Ptr) : M Unit := do
  let tname_1 ← Mem.alloca 16 1
  let result : Unit ← (do
    let mut name_v : Ptr := name
    let t1 : U64 ← Ext.pthread_self.call
    let t2 : I32 ← Ext.pthread_setname_np.call t1 name_v
    if (t2 == (34 : I32)) then
      Mem.storeList tname_1 [(SInt.toS 8 (0 : I32))]
      let t3 : Ptr ← Ptr.add tname_1 1 1
      Mem.zero t3 15
      let t4 : Ptr ← Ext.strncpy.call tname_1 name_v ((16 : U64) - (SInt.toU 64 (1 : I32)))
      let t5 : U64 ← Ext.pthread_self.call
      let t6 : I32 ← Ext.pthread_setname_np.call t5 tname_1
      pure ()
    pure ()
    : M Unit)
  Mem.popFrame [tname_1]
  pure result

end Misc.Osdep.Threads_posix_h
