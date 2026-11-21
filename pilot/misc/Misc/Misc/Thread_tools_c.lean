import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Dispatch_c
import Misc.Misc.Thread_pool_c
import Misc.Osdep.Threads_posix_h
import Misc.Ta.Ta_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Thread_tools_c

/-- C function `mp_waiter_wait`, ../.mpv/misc/thread_tools.c:35.
-/
def mp_waiter_wait [Ext.pthread_cond_destroy] [Ext.pthread_cond_wait] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (waiter : Ptr) : M U64 := do
  let mut waiter_v : Ptr := waiter
  let t1 : I32 ← Ext.pthread_mutex_lock.call waiter_v
  for _ in Fuel.mk fuel do
    let t2 : Ptr ← Ptr.add waiter_v 1 96
    let t3 : Bool ← Mem.load Bool t2
    if !(!t3) then break
    let t4 : Ptr ← Ptr.add waiter_v 1 40
    let t5 : I32 ← Osdep.Threads_posix_h.mp_cond_wait fuel t4 waiter_v
    pure ()
  let t6 : I32 ← Ext.pthread_mutex_unlock.call waiter_v
  let t7 : Ptr ← Ptr.add waiter_v 1 104
  let t8 : U64 ← Mem.load U64 t7
  let mut ret_1 : U64 := t8
  let t9 : I32 ← Ext.pthread_mutex_destroy.call waiter_v
  let t10 : Ptr ← Ptr.add waiter_v 1 40
  let t11 : I32 ← Osdep.Threads_posix_h.mp_cond_destroy fuel t10
  let t12 : Ptr ← Libc.memset waiter_v (202 : I32) (112 : U64)
  return ret_1

/-- C function `mp_waiter_wakeup`, ../.mpv/misc/thread_tools.c:60.
-/
def mp_waiter_wakeup [Ext.pthread_cond_signal] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (waiter : Ptr) (value : U64) : M Unit := do
  let mut waiter_v : Ptr := waiter
  let mut value_v : U64 := value
  let t1 : I32 ← Ext.pthread_mutex_lock.call waiter_v
  let t2 : Ptr ← Ptr.add waiter_v 1 96
  let t3 : Bool ← Mem.load Bool t2
  let mut t4 : Unit := default
  if (!t3) then
    t4 := ()
  else
    Libc.«__assert_fail» Statics.str_164 Statics.str_165 (SInt.toU 32 (63 : I32)) Statics.str_166
    t4 := ()
  let t5 : Ptr ← Ptr.add waiter_v 1 96
  let t6 : Bool := ((1 : I32) != 0)
  Mem.store t5 t6
  let t7 : Ptr ← Ptr.add waiter_v 1 104
  Mem.store t7 value_v
  let t8 : Ptr ← Ptr.add waiter_v 1 40
  let t9 : I32 ← Osdep.Threads_posix_h.mp_cond_signal fuel t8
  let t10 : I32 ← Ext.pthread_mutex_unlock.call waiter_v
  pure ()

/-- C function `mp_waiter_poll`, ../.mpv/misc/thread_tools.c:70.
-/
def mp_waiter_poll [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (waiter : Ptr) : M Bool := do
  let mut waiter_v : Ptr := waiter
  let t1 : I32 ← Ext.pthread_mutex_lock.call waiter_v
  let t2 : Ptr ← Ptr.add waiter_v 1 96
  let t3 : Bool ← Mem.load Bool t2
  let mut r_1 : Bool := t3
  let t4 : I32 ← Ext.pthread_mutex_unlock.call waiter_v
  return r_1

/-- C function `mp_cancel_test`, ../.mpv/misc/thread_tools.c:187.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def mp_cancel_test (fuel : Nat) (c : Ptr) : M Bool := do
  let mut c_v : Ptr := c
  let mut t3 : I32 := default
  if (c_v != Ptr.null) then
    let t1 : Ptr ← Ptr.add c_v 1 96
    let t2 : Bool ← Mem.load Bool t1
    t3 := (SInt.ofBool 32 t2)
  else
    t3 := (0 : I32)
  return (t3 != 0)

mutual

/-- C function `cancel_destroy`, ../.mpv/misc/thread_tools.c:101.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def cancel_destroy [Ext.close] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.write] (fuel : Nat) (p : Ptr) : M Unit :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let mut p_v : Ptr := p
    let mut c_1 : Ptr := p_v
    let t1 : Ptr ← Ptr.add c_1 1 136
    let t2 : Ptr ← Mem.load Ptr t1
    let mut t3 : Unit := default
    if (!(t2 != Ptr.null)) then
      t3 := ()
    else
      Libc.«__assert_fail» Statics.str_167 Statics.str_165 (SInt.toU 32 (105 : I32)) Statics.str_168
      t3 := ()
    Misc.Thread_tools_c.mp_cancel_set_parent fuel c_1 Ptr.null
    let t4 : Ptr ← Ptr.add c_1 1 120
    let t5 : Ptr ← Ptr.add t4 4 (SInt.toInt (0 : I32))
    let t6 : I32 ← Mem.load I32 t5
    if (decide (t6 ≥ (0 : I32))) then
      let t7 : Ptr ← Ptr.add c_1 1 120
      let t8 : Ptr ← Ptr.add t7 4 (SInt.toInt (0 : I32))
      let t9 : I32 ← Mem.load I32 t8
      let t10 : I32 ← Ext.close.call t9
      let t11 : Ptr ← Ptr.add c_1 1 120
      let t12 : Ptr ← Ptr.add t11 4 (SInt.toInt (1 : I32))
      let t13 : I32 ← Mem.load I32 t12
      let t14 : I32 ← Ext.close.call t13
      pure ()
    let t15 : I32 ← Ext.pthread_mutex_destroy.call c_1
    let t16 : Ptr ← Ptr.add c_1 1 40
    let t17 : I32 ← Osdep.Threads_posix_h.mp_cond_destroy fuel t16
    pure ()
termination_by structural fuel

/-- C function `trigger_locked`, ../.mpv/misc/thread_tools.c:136.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def trigger_locked [Ext.close] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.write] (fuel : Nat) (c : Ptr) : M Unit :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let cl20 ← Mem.alloca 1 1
    let result : Unit ← (do
      let mut c_v : Ptr := c
      let t1 : Ptr ← Ptr.add c_v 1 96
      Mem.store t1 ((1 : I32) != 0)
      let t2 : Ptr ← Ptr.add c_v 1 40
      let t3 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel t2
      let t4 : Ptr ← Ptr.add c_v 1 104
      let t5 : Ptr ← Mem.load Ptr t4
      if (t5 != Ptr.null) then
        let t6 : Ptr ← Ptr.add c_v 1 104
        let t7 : Ptr ← Mem.load Ptr t6
        let t8 : Ptr ← Ptr.add c_v 1 112
        let t9 : Ptr ← Mem.load Ptr t8
        (match t7 with
          | Ptr.fn "Misc.Dispatch_c.queue_dtor" => Misc.Dispatch_c.queue_dtor fuel t9
          | Ptr.fn "Misc.Thread_pool_c.thread_pool_dtor" => Misc.Thread_pool_c.thread_pool_dtor fuel t9
          | Ptr.fn "Misc.Thread_tools_c.cancel_destroy" => Misc.Thread_tools_c.cancel_destroy fuel t9
          | Ptr.null => ub "call through a null pointer"
          | _ => unsupported "call through a pointer to a function the selection does not know with this type")
      let t10 : Ptr ← Ptr.add c_v 1 136
      let t11 : Ptr ← Mem.load Ptr t10
      let mut sub_1 : Ptr := t11
      for _ in Fuel.mk fuel do
        if !(sub_1 != Ptr.null) then break
        for _ in Once.mk do
          Misc.Thread_tools_c.mp_cancel_trigger fuel sub_1
        let t12 : Ptr ← Ptr.add sub_1 1 160
        let t13 : Ptr ← Mem.load Ptr t12
        sub_1 := t13
      let t14 : Ptr ← Ptr.add c_v 1 120
      let t15 : Ptr ← Ptr.add t14 4 (SInt.toInt (1 : I32))
      let t16 : I32 ← Mem.load I32 t15
      if (decide (t16 ≥ (0 : I32))) then
        let t17 : Ptr ← Ptr.add c_v 1 120
        let t18 : Ptr ← Ptr.add t17 4 (SInt.toInt (1 : I32))
        let t19 : I32 ← Mem.load I32 t18
        Mem.undefine cl20 1
        Mem.store cl20 (SInt.toS 8 (0 : I32))
        let t21 : I64 ← Ext.write.call t19 cl20 (SInt.toU 64 (1 : I32))
        pure ()
      pure ()
      : M Unit)
    Mem.popFrame [cl20]
    pure result
termination_by structural fuel

/-- C function `mp_cancel_trigger`, ../.mpv/misc/thread_tools.c:157.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def mp_cancel_trigger [Ext.close] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.write] (fuel : Nat) (c : Ptr) : M Unit :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let mut c_v : Ptr := c
    let t1 : I32 ← Ext.pthread_mutex_lock.call c_v
    Misc.Thread_tools_c.trigger_locked fuel c_v
    let t2 : I32 ← Ext.pthread_mutex_unlock.call c_v
    pure ()
termination_by structural fuel

/-- C function `retrigger_locked`, ../.mpv/misc/thread_tools.c:207.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def retrigger_locked [Ext.close] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.write] (fuel : Nat) (c : Ptr) : M Unit :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let mut c_v : Ptr := c
    let t1 : Bool ← Misc.Thread_tools_c.mp_cancel_test fuel c_v
    if t1 then
      Misc.Thread_tools_c.trigger_locked fuel c_v
    pure ()
termination_by structural fuel

/-- C function `mp_cancel_set_parent`, ../.mpv/misc/thread_tools.c:222.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def mp_cancel_set_parent [Ext.close] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.write] (fuel : Nat) (slave : Ptr) (parent : Ptr) : M Unit :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let mut slave_v : Ptr := slave
    let mut parent_v : Ptr := parent
    let t1 : Ptr ← Ptr.add slave_v 1 152
    let t2 : Ptr ← Mem.load Ptr t1
    let t3 : Bool ← Ptr.eq t2 parent_v
    if t3 then
      return ()
    let t4 : Ptr ← Ptr.add slave_v 1 152
    let t5 : Ptr ← Mem.load Ptr t4
    if (t5 != Ptr.null) then
      let t6 : Ptr ← Ptr.add slave_v 1 152
      let t7 : Ptr ← Mem.load Ptr t6
      let t8 : I32 ← Ext.pthread_mutex_lock.call t7
      for _ in Fuel.mk fuel do
        for _ in Once.mk do
          let t9 : Ptr ← Ptr.add slave_v 1 168
          let t10 : Ptr ← Mem.load Ptr t9
          if (t10 != Ptr.null) then
            let t11 : Ptr ← Ptr.add slave_v 1 168
            let t12 : Ptr ← Mem.load Ptr t11
            let t13 : Ptr ← Ptr.add t12 1 160
            let t14 : Ptr ← Ptr.add slave_v 1 160
            let t15 : Ptr ← Mem.load Ptr t14
            Mem.store t13 t15
          else
            let t16 : Ptr ← Ptr.add slave_v 1 152
            let t17 : Ptr ← Mem.load Ptr t16
            let t18 : Ptr ← Ptr.add t17 1 136
            let t19 : Ptr ← Ptr.add slave_v 1 160
            let t20 : Ptr ← Mem.load Ptr t19
            Mem.store t18 t20
          let t21 : Ptr ← Ptr.add slave_v 1 160
          let t22 : Ptr ← Mem.load Ptr t21
          if (t22 != Ptr.null) then
            let t23 : Ptr ← Ptr.add slave_v 1 160
            let t24 : Ptr ← Mem.load Ptr t23
            let t25 : Ptr ← Ptr.add t24 1 168
            let t26 : Ptr ← Ptr.add slave_v 1 168
            let t27 : Ptr ← Mem.load Ptr t26
            Mem.store t25 t27
          else
            let t28 : Ptr ← Ptr.add slave_v 1 152
            let t29 : Ptr ← Mem.load Ptr t28
            let t30 : Ptr ← Ptr.add t29 1 136
            let t31 : Ptr ← Ptr.add t30 1 8
            let t32 : Ptr ← Ptr.add slave_v 1 168
            let t33 : Ptr ← Mem.load Ptr t32
            Mem.store t31 t33
        if !((0 : I32) != 0) then break
      let t34 : Ptr ← Ptr.add slave_v 1 152
      let t35 : Ptr ← Mem.load Ptr t34
      let t36 : I32 ← Ext.pthread_mutex_unlock.call t35
      pure ()
    let t37 : Ptr ← Ptr.add slave_v 1 152
    Mem.store t37 parent_v
    let t38 : Ptr ← Ptr.add slave_v 1 152
    let t39 : Ptr ← Mem.load Ptr t38
    if (t39 != Ptr.null) then
      let t40 : Ptr ← Ptr.add slave_v 1 152
      let t41 : Ptr ← Mem.load Ptr t40
      let t42 : I32 ← Ext.pthread_mutex_lock.call t41
      for _ in Fuel.mk fuel do
        for _ in Once.mk do
          let t43 : Ptr ← Ptr.add slave_v 1 168
          let t44 : Ptr ← Ptr.add slave_v 1 152
          let t45 : Ptr ← Mem.load Ptr t44
          let t46 : Ptr ← Ptr.add t45 1 136
          let t47 : Ptr ← Ptr.add t46 1 8
          let t48 : Ptr ← Mem.load Ptr t47
          Mem.store t43 t48
          let t49 : Ptr ← Ptr.add slave_v 1 160
          let t50 : Ptr := Ptr.null
          Mem.store t49 t50
          let t51 : Ptr ← Ptr.add slave_v 1 168
          let t52 : Ptr ← Mem.load Ptr t51
          if (t52 != Ptr.null) then
            let t53 : Ptr ← Ptr.add slave_v 1 168
            let t54 : Ptr ← Mem.load Ptr t53
            let t55 : Ptr ← Ptr.add t54 1 160
            Mem.store t55 slave_v
          else
            let t56 : Ptr ← Ptr.add slave_v 1 152
            let t57 : Ptr ← Mem.load Ptr t56
            let t58 : Ptr ← Ptr.add t57 1 136
            Mem.store t58 slave_v
          let t59 : Ptr ← Ptr.add slave_v 1 160
          let t60 : Ptr ← Mem.load Ptr t59
          if (t60 != Ptr.null) then
            let t61 : Ptr ← Ptr.add slave_v 1 160
            let t62 : Ptr ← Mem.load Ptr t61
            let t63 : Ptr ← Ptr.add t62 1 168
            Mem.store t63 slave_v
          else
            let t64 : Ptr ← Ptr.add slave_v 1 152
            let t65 : Ptr ← Mem.load Ptr t64
            let t66 : Ptr ← Ptr.add t65 1 136
            let t67 : Ptr ← Ptr.add t66 1 8
            Mem.store t67 slave_v
        if !((0 : I32) != 0) then break
      let t68 : Ptr ← Ptr.add slave_v 1 152
      let t69 : Ptr ← Mem.load Ptr t68
      Misc.Thread_tools_c.retrigger_locked fuel t69
      let t70 : Ptr ← Ptr.add slave_v 1 152
      let t71 : Ptr ← Mem.load Ptr t70
      let t72 : I32 ← Ext.pthread_mutex_unlock.call t71
      pure ()
    pure ()
termination_by structural fuel

end

/-- C function `mp_cancel_new`, ../.mpv/misc/thread_tools.c:123.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_cancel_new [Ext.pthread_cond_init] [Ext.pthread_condattr_destroy] [Ext.pthread_condattr_init] [Ext.pthread_condattr_setclock] [Ext.pthread_mutex_init] [Ext.pthread_mutexattr_destroy] [Ext.pthread_mutexattr_init] [Ext.pthread_mutexattr_settype] (fuel : Nat) (talloc_ctx : Ptr) : M Ptr := do
  let cl4 ← Mem.alloca 176 8
  let result : Ptr ← (do
    let mut talloc_ctx_v : Ptr := talloc_ctx
    let t1 : Ptr ← Talloc.ta_alloc_size talloc_ctx_v (176 : U64)
    let t2 : Ptr ← Talloc.ta_dbg_set_loc t1 Statics.str_169
    let t3 : Ptr ← Ta.Ta_h.ta_oom_p fuel t2
    let mut c_1 : Ptr := t3
    Talloc.ta_set_destructor c_1 (Ptr.fn "Misc.Thread_tools_c.cancel_destroy")
    Mem.undefine cl4 176
    Mem.zero cl4 40
    let t5 : Ptr ← Ptr.add cl4 1 40
    Mem.zero t5 56
    let t6 : Ptr ← Ptr.add cl4 1 96
    Mem.store t6 ((0 : I32) != 0)
    let t7 : Ptr ← Ptr.add cl4 1 104
    Mem.zero t7 8
    let t8 : Ptr ← Ptr.add cl4 1 112
    Mem.zero t8 8
    let t9 : Ptr ← Ptr.add cl4 1 120
    Mem.storeList t9 [(SInt.ofInt 32 (-1)), (SInt.ofInt 32 (-1))]
    let t10 : Ptr ← Ptr.add cl4 1 128
    Mem.zero t10 8
    let t11 : Ptr ← Ptr.add cl4 1 136
    Mem.zero t11 16
    let t12 : Ptr ← Ptr.add cl4 1 152
    Mem.zero t12 8
    let t13 : Ptr ← Ptr.add cl4 1 160
    Mem.zero t13 16
    let t14 : Agg ← Mem.loadAgg cl4 176 8
    Mem.storeAgg c_1 t14 8
    let t15 : I32 ← Osdep.Threads_posix_h.mp_mutex_init fuel c_1
    let t16 : Ptr ← Ptr.add c_1 1 40
    let t17 : I32 ← Osdep.Threads_posix_h.mp_cond_init fuel t16
    return c_1
    : M Ptr)
  Mem.popFrame [cl4]
  pure result

/-- C function `mp_cancel_reset`, ../.mpv/misc/thread_tools.c:164.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def mp_cancel_reset [Ext.«__errno_location»] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.read] (fuel : Nat) (c : Ptr) : M Unit := do
  let cl9 ← Mem.alloca 256 1
  let result : Unit ← (do
    let mut c_v : Ptr := c
    let t1 : I32 ← Ext.pthread_mutex_lock.call c_v
    let t2 : Ptr ← Ptr.add c_v 1 96
    Mem.store t2 ((0 : I32) != 0)
    let t3 : Ptr ← Ptr.add c_v 1 120
    let t4 : Ptr ← Ptr.add t3 4 (SInt.toInt (0 : I32))
    let t5 : I32 ← Mem.load I32 t4
    if (decide (t5 ≥ (0 : I32))) then
      for _ in Fuel.mk fuel do
        if !((1 : I32) != 0) then break
        let t6 : Ptr ← Ptr.add c_v 1 120
        let t7 : Ptr ← Ptr.add t6 4 (SInt.toInt (0 : I32))
        let t8 : I32 ← Mem.load I32 t7
        Mem.undefine cl9 256
        Mem.storeList cl9 [(SInt.toS 8 (0 : I32))]
        let t10 : Ptr ← Ptr.add cl9 1 1
        Mem.zero t10 255
        let t11 : I64 ← Ext.read.call t8 cl9 (SInt.toU 64 (256 : I32))
        let mut r_1 : I32 := (SInt.toS 32 t11)
        let mut t15 : Bool := false
        if (decide (r_1 ≤ (0 : I32))) then
          let mut t14 : Bool := false
          if (decide (r_1 < (0 : I32))) then
            let t12 : Ptr ← Ext.«__errno_location».call
            let t13 : I32 ← Mem.load I32 t12
            t14 := (t13 == (4 : I32))
          t15 := (!t14)
        if t15 then
          break
    let t16 : I32 ← Ext.pthread_mutex_unlock.call c_v
    pure ()
    : M Unit)
  Mem.popFrame [cl9]
  pure result

/-- C function `mp_cancel_wait`, ../.mpv/misc/thread_tools.c:192.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def mp_cancel_wait [Ext.clock_gettime] [Ext.mp_time_ns] [Ext.mp_time_ns_add] [Ext.pthread_cond_timedwait] [Ext.pthread_cond_wait] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (c : Ptr) (timeout : F64) : M Bool := do
  let mut c_v : Ptr := c
  let mut timeout_v : F64 := timeout
  let t1 : I64 ← Ext.mp_time_ns.call
  let t2 : I64 ← Ext.mp_time_ns_add.call t1 timeout_v
  let mut wait_until_1 : I64 := t2
  let t3 : I32 ← Ext.pthread_mutex_lock.call c_v
  for _ in Fuel.mk fuel do
    let t4 : Bool ← Misc.Thread_tools_c.mp_cancel_test fuel c_v
    if !(!t4) then break
    let t5 : Ptr ← Ptr.add c_v 1 40
    let t6 : I32 ← Osdep.Threads_posix_h.mp_cond_timedwait_until fuel t5 c_v wait_until_1
    if (t6 != 0) then
      break
  let t7 : I32 ← Ext.pthread_mutex_unlock.call c_v
  let t8 : Bool ← Misc.Thread_tools_c.mp_cancel_test fuel c_v
  return t8

/-- C function `mp_cancel_set_cb`, ../.mpv/misc/thread_tools.c:213.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def mp_cancel_set_cb [Ext.close] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.write] (fuel : Nat) (c : Ptr) (cb : Ptr) (ctx : Ptr) : M Unit := do
  let mut c_v : Ptr := c
  let mut cb_v : Ptr := cb
  let mut ctx_v : Ptr := ctx
  let t1 : I32 ← Ext.pthread_mutex_lock.call c_v
  let t2 : Ptr ← Ptr.add c_v 1 104
  Mem.store t2 cb_v
  let t3 : Ptr ← Ptr.add c_v 1 112
  Mem.store t3 ctx_v
  Misc.Thread_tools_c.retrigger_locked fuel c_v
  let t4 : I32 ← Ext.pthread_mutex_unlock.call c_v
  pure ()

/-- C function `mp_cancel_get_fd`, ../.mpv/misc/thread_tools.c:243.
Assumes sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs.
-/
def mp_cancel_get_fd [Ext.close] [Ext.mp_make_wakeup_pipe] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.write] (fuel : Nat) (c : Ptr) : M I32 := do
  let mut c_v : Ptr := c
  let t1 : I32 ← Ext.pthread_mutex_lock.call c_v
  let t2 : Ptr ← Ptr.add c_v 1 120
  let t3 : Ptr ← Ptr.add t2 4 (SInt.toInt (0 : I32))
  let t4 : I32 ← Mem.load I32 t3
  if (decide (t4 < (0 : I32))) then
    let t5 : Ptr ← Ptr.add c_v 1 120
    let t6 : I32 ← Ext.mp_make_wakeup_pipe.call t5
    Misc.Thread_tools_c.retrigger_locked fuel c_v
  let t7 : I32 ← Ext.pthread_mutex_unlock.call c_v
  let t8 : Ptr ← Ptr.add c_v 1 120
  let t9 : Ptr ← Ptr.add t8 4 (SInt.toInt (0 : I32))
  let t10 : I32 ← Mem.load I32 t9
  return t10

end Misc.Misc.Thread_tools_c
