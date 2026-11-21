import Achates
import Misc.Statics
import Misc.Externals
import Misc.Osdep.Threads_posix_h
import Misc.Ta.Ta_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Dispatch_c

/-- C function `queue_dtor`, ../.mpv/misc/dispatch.c:63.
-/
def queue_dtor [Ext.pthread_cond_destroy] [Ext.pthread_mutex_destroy] (fuel : Nat) (p : Ptr) : M Unit := do
  let mut p_v : Ptr := p
  let mut queue_1 : Ptr := p_v
  let t1 : Ptr ← Mem.load Ptr queue_1
  let mut t2 : Unit := default
  if (!(t1 != Ptr.null)) then
    t2 := ()
  else
    Libc.«__assert_fail» Statics.str_41 Statics.str_42 (SInt.toU 32 (66 : I32)) Statics.str_43
    t2 := ()
  let t3 : Ptr ← Ptr.add queue_1 1 153
  let t4 : Bool ← Mem.load Bool t3
  let mut t5 : Unit := default
  if (!t4) then
    t5 := ()
  else
    Libc.«__assert_fail» Statics.str_44 Statics.str_42 (SInt.toU 32 (67 : I32)) Statics.str_43
    t5 := ()
  let t6 : Ptr ← Ptr.add queue_1 1 176
  let t7 : U64 ← Mem.load U64 t6
  let mut t8 : Unit := default
  if (!(t7 != 0)) then
    t8 := ()
  else
    Libc.«__assert_fail» Statics.str_45 Statics.str_42 (SInt.toU 32 (68 : I32)) Statics.str_43
    t8 := ()
  let t9 : Ptr ← Ptr.add queue_1 1 168
  let t10 : Bool ← Mem.load Bool t9
  let mut t11 : Unit := default
  if (!t10) then
    t11 := ()
  else
    Libc.«__assert_fail» Statics.str_46 Statics.str_42 (SInt.toU 32 (69 : I32)) Statics.str_43
    t11 := ()
  let t12 : Ptr ← Ptr.add queue_1 1 56
  let t13 : I32 ← Osdep.Threads_posix_h.mp_cond_destroy fuel t12
  let t14 : Ptr ← Ptr.add queue_1 1 16
  let t15 : I32 ← Ext.pthread_mutex_destroy.call t14
  pure ()

/-- C function `mp_dispatch_create`, ../.mpv/misc/dispatch.c:83.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_dispatch_create [Ext.pthread_cond_init] [Ext.pthread_condattr_destroy] [Ext.pthread_condattr_init] [Ext.pthread_condattr_setclock] [Ext.pthread_mutex_init] [Ext.pthread_mutexattr_destroy] [Ext.pthread_mutexattr_init] [Ext.pthread_mutexattr_settype] (fuel : Nat) (ta_parent : Ptr) : M Ptr := do
  let cl4 ← Mem.alloca 200 8
  let result : Ptr ← (do
    let mut ta_parent_v : Ptr := ta_parent
    let t1 : Ptr ← Talloc.ta_alloc_size ta_parent_v (200 : U64)
    let t2 : Ptr ← Talloc.ta_dbg_set_loc t1 Statics.str_47
    let t3 : Ptr ← Ta.Ta_h.ta_oom_p fuel t2
    let mut queue_1 : Ptr := t3
    Mem.undefine cl4 200
    Mem.store cl4 Ptr.null
    let t5 : Ptr ← Ptr.add cl4 1 8
    Mem.zero t5 8
    let t6 : Ptr ← Ptr.add cl4 1 16
    Mem.zero t6 40
    let t7 : Ptr ← Ptr.add cl4 1 56
    Mem.zero t7 56
    let t8 : Ptr ← Ptr.add cl4 1 112
    Mem.zero t8 8
    let t9 : Ptr ← Ptr.add cl4 1 120
    Mem.zero t9 8
    let t10 : Ptr ← Ptr.add cl4 1 128
    Mem.zero t10 8
    let t11 : Ptr ← Ptr.add cl4 1 136
    Mem.zero t11 8
    let t12 : Ptr ← Ptr.add cl4 1 144
    Mem.zero t12 8
    let t13 : Ptr ← Ptr.add cl4 1 152
    Mem.zero t13 1
    let t14 : Ptr ← Ptr.add cl4 1 153
    Mem.zero t14 1
    let t15 : Ptr ← Ptr.add cl4 1 160
    Mem.zero t15 8
    let t16 : Ptr ← Ptr.add cl4 1 168
    Mem.zero t16 1
    let t17 : Ptr ← Ptr.add cl4 1 176
    Mem.zero t17 8
    let t18 : Ptr ← Ptr.add cl4 1 184
    Mem.zero t18 1
    let t19 : Ptr ← Ptr.add cl4 1 192
    Mem.zero t19 8
    let t20 : Agg ← Mem.loadAgg cl4 200 8
    Mem.storeAgg queue_1 t20 8
    Talloc.ta_set_destructor queue_1 (Ptr.fn "Misc.Dispatch_c.queue_dtor")
    let t21 : Ptr ← Ptr.add queue_1 1 16
    let t22 : I32 ← Osdep.Threads_posix_h.mp_mutex_init fuel t21
    let t23 : Ptr ← Ptr.add queue_1 1 56
    let t24 : I32 ← Osdep.Threads_posix_h.mp_cond_init fuel t23
    return queue_1
    : M Ptr)
  Mem.popFrame [cl4]
  pure result

/-- C function `mp_dispatch_set_wakeup_fn`, ../.mpv/misc/dispatch.c:102.
-/
def mp_dispatch_set_wakeup_fn (fuel : Nat) (queue : Ptr) (wakeup_fn : Ptr) (wakeup_ctx : Ptr) : M Unit := do
  let mut queue_v : Ptr := queue
  let mut wakeup_fn_v : Ptr := wakeup_fn
  let mut wakeup_ctx_v : Ptr := wakeup_ctx
  let t1 : Ptr ← Ptr.add queue_v 1 112
  Mem.store t1 wakeup_fn_v
  let t2 : Ptr ← Ptr.add queue_v 1 120
  Mem.store t2 wakeup_ctx_v
  pure ()

/-- C function `mp_dispatch_set_onlock_fn`, ../.mpv/misc/dispatch.c:118.
-/
def mp_dispatch_set_onlock_fn (fuel : Nat) (queue : Ptr) (onlock_fn : Ptr) (onlock_ctx : Ptr) : M Unit := do
  let mut queue_v : Ptr := queue
  let mut onlock_fn_v : Ptr := onlock_fn
  let mut onlock_ctx_v : Ptr := onlock_ctx
  let t1 : Ptr ← Ptr.add queue_v 1 128
  Mem.store t1 onlock_fn_v
  let t2 : Ptr ← Ptr.add queue_v 1 136
  Mem.store t2 onlock_ctx_v
  pure ()

/-- C function `mp_dispatch_append`, ../.mpv/misc/dispatch.c:126.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_dispatch_append [Ext.Misc_Thread_pool_c_thread_pool_dtor] [Ext.Misc_Thread_tools_c_cancel_destroy] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (queue : Ptr) (item : Ptr) : M Unit := do
  let mut queue_v : Ptr := queue
  let mut item_v : Ptr := item
  let t1 : Ptr ← Ptr.add queue_v 1 16
  let t2 : I32 ← Ext.pthread_mutex_lock.call t1
  let t3 : Ptr ← Ptr.add item_v 1 17
  let t4 : Bool ← Mem.load Bool t3
  if t4 then
    let t5 : Ptr ← Mem.load Ptr queue_v
    let mut cur_1 : Ptr := t5
    for _ in Fuel.mk fuel do
      if !(cur_1 != Ptr.null) then break
      for _ in Once.mk do
        let t6 : Ptr ← Ptr.add cur_1 1 17
        let t7 : Bool ← Mem.load Bool t6
        let mut t11 : Bool := false
        if ((SInt.ofBool 32 t7) != 0) then
          let t8 : Ptr ← Mem.load Ptr cur_1
          let t9 : Ptr ← Mem.load Ptr item_v
          let t10 : Bool ← Ptr.eq t8 t9
          t11 := t10
        let mut t17 : Bool := false
        if t11 then
          let t12 : Ptr ← Ptr.add cur_1 1 8
          let t13 : Ptr ← Mem.load Ptr t12
          let t14 : Ptr ← Ptr.add item_v 1 8
          let t15 : Ptr ← Mem.load Ptr t14
          let t16 : Bool ← Ptr.eq t13 t15
          t17 := t16
        if t17 then
          Talloc.ta_free item_v
          let t18 : Ptr ← Ptr.add queue_v 1 16
          let t19 : I32 ← Ext.pthread_mutex_unlock.call t18
          return ()
      let t20 : Ptr ← Ptr.add cur_1 1 24
      let t21 : Ptr ← Mem.load Ptr t20
      cur_1 := t21
  let t22 : Ptr ← Ptr.add queue_v 1 8
  let t23 : Ptr ← Mem.load Ptr t22
  if (t23 != Ptr.null) then
    let t24 : Ptr ← Ptr.add queue_v 1 8
    let t25 : Ptr ← Mem.load Ptr t24
    let t26 : Ptr ← Ptr.add t25 1 24
    Mem.store t26 item_v
  else
    Mem.store queue_v item_v
  let t27 : Ptr ← Ptr.add queue_v 1 8
  Mem.store t27 item_v
  let t28 : Ptr ← Ptr.add queue_v 1 56
  let t29 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel t28
  let t30 : Ptr ← Ptr.add queue_v 1 112
  let t31 : Ptr ← Mem.load Ptr t30
  if (!(t31 != Ptr.null)) then
    let t32 : Ptr ← Ptr.add queue_v 1 152
    let t33 : Bool := ((1 : I32) != 0)
    Mem.store t32 t33
  let t34 : Ptr ← Ptr.add queue_v 1 16
  let t35 : I32 ← Ext.pthread_mutex_unlock.call t34
  let t36 : Ptr ← Ptr.add queue_v 1 112
  let t37 : Ptr ← Mem.load Ptr t36
  if (t37 != Ptr.null) then
    let t38 : Ptr ← Ptr.add queue_v 1 112
    let t39 : Ptr ← Mem.load Ptr t38
    let t40 : Ptr ← Ptr.add queue_v 1 120
    let t41 : Ptr ← Mem.load Ptr t40
    (match t39 with
      | Ptr.fn "Misc.Dispatch_c.queue_dtor" => Misc.Dispatch_c.queue_dtor fuel t41
      | Ptr.fn "Misc.Thread_pool_c.thread_pool_dtor" => Ext.Misc_Thread_pool_c_thread_pool_dtor.call t41
      | Ptr.fn "Misc.Thread_tools_c.cancel_destroy" => Ext.Misc_Thread_tools_c_cancel_destroy.call t41
      | Ptr.null => ub "call through a null pointer"
      | _ => unsupported "call through a pointer to a function the selection does not know with this type")
  pure ()

/-- C function `mp_dispatch_enqueue`, ../.mpv/misc/dispatch.c:168.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_dispatch_enqueue [Ext.Misc_Thread_pool_c_thread_pool_dtor] [Ext.Misc_Thread_tools_c_cancel_destroy] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (queue : Ptr) (fn : Ptr) (fn_data : Ptr) : M Unit := do
  let cl4 ← Mem.alloca 32 8
  let result : Unit ← (do
    let mut queue_v : Ptr := queue
    let mut fn_v : Ptr := fn
    let mut fn_data_v : Ptr := fn_data
    let t1 : Ptr ← Talloc.ta_alloc_size Ptr.null (32 : U64)
    let t2 : Ptr ← Talloc.ta_dbg_set_loc t1 Statics.str_48
    let t3 : Ptr ← Ta.Ta_h.ta_oom_p fuel t2
    let mut item_1 : Ptr := t3
    Mem.undefine cl4 32
    Mem.store cl4 fn_v
    let t5 : Ptr ← Ptr.add cl4 1 8
    Mem.store t5 fn_data_v
    let t6 : Ptr ← Ptr.add cl4 1 16
    Mem.store t6 ((1 : I32) != 0)
    let t7 : Ptr ← Ptr.add cl4 1 17
    Mem.zero t7 1
    let t8 : Ptr ← Ptr.add cl4 1 18
    Mem.zero t8 1
    let t9 : Ptr ← Ptr.add cl4 1 24
    Mem.zero t9 8
    let t10 : Agg ← Mem.loadAgg cl4 32 8
    Mem.storeAgg item_1 t10 8
    Misc.Dispatch_c.mp_dispatch_append fuel queue_v item_1
    pure ()
    : M Unit)
  Mem.popFrame [cl4]
  pure result

/-- C function `mp_dispatch_enqueue_autofree`, ../.mpv/misc/dispatch.c:184.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_dispatch_enqueue_autofree [Ext.Misc_Thread_pool_c_thread_pool_dtor] [Ext.Misc_Thread_tools_c_cancel_destroy] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (queue : Ptr) (fn : Ptr) (fn_data : Ptr) : M Unit := do
  let cl4 ← Mem.alloca 32 8
  let result : Unit ← (do
    let mut queue_v : Ptr := queue
    let mut fn_v : Ptr := fn
    let mut fn_data_v : Ptr := fn_data
    let t1 : Ptr ← Talloc.ta_alloc_size Ptr.null (32 : U64)
    let t2 : Ptr ← Talloc.ta_dbg_set_loc t1 Statics.str_49
    let t3 : Ptr ← Ta.Ta_h.ta_oom_p fuel t2
    let mut item_1 : Ptr := t3
    Mem.undefine cl4 32
    Mem.store cl4 fn_v
    let t5 : Ptr ← Talloc.ta_steal_ item_1 fn_data_v
    let t6 : Ptr ← Ptr.add cl4 1 8
    Mem.store t6 t5
    let t7 : Ptr ← Ptr.add cl4 1 16
    Mem.store t7 ((1 : I32) != 0)
    let t8 : Ptr ← Ptr.add cl4 1 17
    Mem.zero t8 1
    let t9 : Ptr ← Ptr.add cl4 1 18
    Mem.zero t9 1
    let t10 : Ptr ← Ptr.add cl4 1 24
    Mem.zero t10 8
    let t11 : Agg ← Mem.loadAgg cl4 32 8
    Mem.storeAgg item_1 t11 8
    Misc.Dispatch_c.mp_dispatch_append fuel queue_v item_1
    pure ()
    : M Unit)
  Mem.popFrame [cl4]
  pure result

/-- C function `mp_dispatch_enqueue_notify`, ../.mpv/misc/dispatch.c:197.
Assumes alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_dispatch_enqueue_notify [Ext.Misc_Thread_pool_c_thread_pool_dtor] [Ext.Misc_Thread_tools_c_cancel_destroy] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (queue : Ptr) (fn : Ptr) (fn_data : Ptr) : M Unit := do
  let cl4 ← Mem.alloca 32 8
  let result : Unit ← (do
    let mut queue_v : Ptr := queue
    let mut fn_v : Ptr := fn
    let mut fn_data_v : Ptr := fn_data
    let t1 : Ptr ← Talloc.ta_alloc_size Ptr.null (32 : U64)
    let t2 : Ptr ← Talloc.ta_dbg_set_loc t1 Statics.str_50
    let t3 : Ptr ← Ta.Ta_h.ta_oom_p fuel t2
    let mut item_1 : Ptr := t3
    Mem.undefine cl4 32
    Mem.store cl4 fn_v
    let t5 : Ptr ← Ptr.add cl4 1 8
    Mem.store t5 fn_data_v
    let t6 : Ptr ← Ptr.add cl4 1 16
    Mem.store t6 ((1 : I32) != 0)
    let t7 : Ptr ← Ptr.add cl4 1 17
    Mem.store t7 ((1 : I32) != 0)
    let t8 : Ptr ← Ptr.add cl4 1 18
    Mem.zero t8 1
    let t9 : Ptr ← Ptr.add cl4 1 24
    Mem.zero t9 8
    let t10 : Agg ← Mem.loadAgg cl4 32 8
    Mem.storeAgg item_1 t10 8
    Misc.Dispatch_c.mp_dispatch_append fuel queue_v item_1
    pure ()
    : M Unit)
  Mem.popFrame [cl4]
  pure result

/-- C function `mp_dispatch_cancel_fn`, ../.mpv/misc/dispatch.c:218.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_dispatch_cancel_fn [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (queue : Ptr) (fn : Ptr) (fn_data : Ptr) : M Unit := do
  let mut queue_v : Ptr := queue
  let mut fn_v : Ptr := fn
  let mut fn_data_v : Ptr := fn_data
  let t1 : Ptr ← Ptr.add queue_v 1 16
  let t2 : I32 ← Ext.pthread_mutex_lock.call t1
  let mut pcur_1 : Ptr := queue_v
  let t3 : Ptr ← Ptr.add queue_v 1 8
  let t4 : Ptr := Ptr.null
  Mem.store t3 t4
  for _ in Fuel.mk fuel do
    let t5 : Ptr ← Mem.load Ptr pcur_1
    if !(t5 != Ptr.null) then break
    let t6 : Ptr ← Mem.load Ptr pcur_1
    let mut cur_2 : Ptr := t6
    let t7 : Ptr ← Mem.load Ptr cur_2
    let t8 : Bool ← Ptr.eq t7 fn_v
    let mut t12 : Bool := false
    if t8 then
      let t9 : Ptr ← Ptr.add cur_2 1 8
      let t10 : Ptr ← Mem.load Ptr t9
      let t11 : Bool ← Ptr.eq t10 fn_data_v
      t12 := t11
    if t12 then
      let t13 : Ptr ← Ptr.add cur_2 1 24
      let t14 : Ptr ← Mem.load Ptr t13
      Mem.store pcur_1 t14
      Talloc.ta_free cur_2
    else
      let t15 : Ptr ← Ptr.add queue_v 1 8
      Mem.store t15 cur_2
      let t16 : Ptr ← Ptr.add cur_2 1 24
      pcur_1 := t16
  let t17 : Ptr ← Ptr.add queue_v 1 16
  let t18 : I32 ← Ext.pthread_mutex_unlock.call t17
  pure ()

/-- C function `mp_dispatch_run`, ../.mpv/misc/dispatch.c:241.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_dispatch_run [Ext.Misc_Thread_pool_c_thread_pool_dtor] [Ext.Misc_Thread_tools_c_cancel_destroy] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_cond_wait] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (queue : Ptr) (fn : Ptr) (fn_data : Ptr) : M Unit := do
  let item_1 ← Mem.alloca 32 8
  let result : Unit ← (do
    let mut queue_v : Ptr := queue
    let mut fn_v : Ptr := fn
    let mut fn_data_v : Ptr := fn_data
    Mem.store item_1 fn_v
    let t1 : Ptr ← Ptr.add item_1 1 8
    Mem.store t1 fn_data_v
    let t2 : Ptr ← Ptr.add item_1 1 16
    Mem.zero t2 1
    let t3 : Ptr ← Ptr.add item_1 1 17
    Mem.zero t3 1
    let t4 : Ptr ← Ptr.add item_1 1 18
    Mem.zero t4 1
    let t5 : Ptr ← Ptr.add item_1 1 24
    Mem.zero t5 8
    Misc.Dispatch_c.mp_dispatch_append fuel queue_v item_1
    let t6 : Ptr ← Ptr.add queue_v 1 16
    let t7 : I32 ← Ext.pthread_mutex_lock.call t6
    for _ in Fuel.mk fuel do
      let t8 : Ptr ← Ptr.add item_1 1 18
      let t9 : Bool ← Mem.load Bool t8
      if !(!t9) then break
      let t10 : Ptr ← Ptr.add queue_v 1 56
      let t11 : Ptr ← Ptr.add queue_v 1 16
      let t12 : I32 ← Osdep.Threads_posix_h.mp_cond_wait fuel t10 t11
      pure ()
    let t13 : Ptr ← Ptr.add queue_v 1 16
    let t14 : I32 ← Ext.pthread_mutex_unlock.call t13
    pure ()
    : M Unit)
  Mem.popFrame [item_1]
  pure result

/-- C function `mp_dispatch_queue_process`, ../.mpv/misc/dispatch.c:272.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_dispatch_queue_process [Ext.Misc_Thread_pool_c_thread_pool_dtor] [Ext.Misc_Thread_tools_c_cancel_destroy] [Ext.clock_gettime] [Ext.mp_time_ns] [Ext.mp_time_ns_add] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_cond_timedwait] [Ext.pthread_cond_wait] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.pthread_self] (fuel : Nat) (queue : Ptr) (timeout : F64) : M Unit := do
  let mut queue_v : Ptr := queue
  let mut timeout_v : F64 := timeout
  let t1 : Ptr ← Ptr.add queue_v 1 16
  let t2 : I32 ← Ext.pthread_mutex_lock.call t1
  let t3 : Ptr ← Ptr.add queue_v 1 144
  let t4 : F64 ← F64.ofS (0 : I32)
  let mut t7 : I64 := default
  if (decide (timeout_v > t4)) then
    let t5 : I64 ← Ext.mp_time_ns.call
    let t6 : I64 ← Ext.mp_time_ns_add.call t5 timeout_v
    t7 := t6
  else
    t7 := (SInt.toS 64 (0 : I32))
  Mem.store t3 t7
  let t8 : Ptr ← Ptr.add queue_v 1 153
  let t9 : Bool ← Mem.load Bool t8
  let mut t10 : Unit := default
  if (!t9) then
    t10 := ()
  else
    Libc.«__assert_fail» Statics.str_44 Statics.str_42 (SInt.toU 32 (276 : I32)) Statics.str_51
    t10 := ()
  let t11 : Ptr ← Ptr.add queue_v 1 153
  let t12 : Bool := ((1 : I32) != 0)
  Mem.store t11 t12
  let t13 : Ptr ← Ptr.add queue_v 1 160
  let t14 : U64 ← Ext.pthread_self.call
  Mem.store t13 t14
  let t15 : Ptr ← Ptr.add queue_v 1 176
  let t16 : U64 ← Mem.load U64 t15
  if (t16 != 0) then
    let t17 : Ptr ← Ptr.add queue_v 1 56
    let t18 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel t17
    pure ()
  for _ in Fuel.mk fuel do
    if !((1 : I32) != 0) then break
    let t19 : Ptr ← Ptr.add queue_v 1 176
    let t20 : U64 ← Mem.load U64 t19
    if (t20 != 0) then
      let t21 : Ptr ← Ptr.add queue_v 1 56
      let t22 : Ptr ← Ptr.add queue_v 1 16
      let t23 : I32 ← Osdep.Threads_posix_h.mp_cond_wait fuel t21 t22
      pure ()
    else
      let t24 : Ptr ← Mem.load Ptr queue_v
      if (t24 != Ptr.null) then
        let t25 : Ptr ← Mem.load Ptr queue_v
        let mut item_1 : Ptr := t25
        let t26 : Ptr ← Ptr.add item_1 1 24
        let t27 : Ptr ← Mem.load Ptr t26
        Mem.store queue_v t27
        let t28 : Ptr ← Mem.load Ptr queue_v
        if (!(t28 != Ptr.null)) then
          let t29 : Ptr ← Ptr.add queue_v 1 8
          let t30 : Ptr := Ptr.null
          Mem.store t29 t30
        let t31 : Ptr ← Ptr.add item_1 1 24
        let t32 : Ptr := Ptr.null
        Mem.store t31 t32
        let t33 : Ptr ← Ptr.add queue_v 1 168
        let t34 : Bool ← Mem.load Bool t33
        let mut t35 : Unit := default
        if (!t34) then
          t35 := ()
        else
          Libc.«__assert_fail» Statics.str_46 Statics.str_42 (SInt.toU 32 (296 : I32)) Statics.str_51
          t35 := ()
        let t36 : Ptr ← Ptr.add queue_v 1 168
        let t37 : Bool := ((1 : I32) != 0)
        Mem.store t36 t37
        let t38 : Ptr ← Ptr.add queue_v 1 16
        let t39 : I32 ← Ext.pthread_mutex_unlock.call t38
        let t40 : Ptr ← Mem.load Ptr item_1
        let t41 : Ptr ← Ptr.add item_1 1 8
        let t42 : Ptr ← Mem.load Ptr t41
        (match t40 with
          | Ptr.fn "Misc.Dispatch_c.queue_dtor" => Misc.Dispatch_c.queue_dtor fuel t42
          | Ptr.fn "Misc.Thread_pool_c.thread_pool_dtor" => Ext.Misc_Thread_pool_c_thread_pool_dtor.call t42
          | Ptr.fn "Misc.Thread_tools_c.cancel_destroy" => Ext.Misc_Thread_tools_c_cancel_destroy.call t42
          | Ptr.null => ub "call through a null pointer"
          | _ => unsupported "call through a pointer to a function the selection does not know with this type")
        let t43 : Ptr ← Ptr.add queue_v 1 16
        let t44 : I32 ← Ext.pthread_mutex_lock.call t43
        let t45 : Ptr ← Ptr.add queue_v 1 168
        let t46 : Bool ← Mem.load Bool t45
        let mut t47 : Unit := default
        if ((SInt.ofBool 32 t46) != 0) then
          t47 := ()
        else
          Libc.«__assert_fail» Statics.str_52 Statics.str_42 (SInt.toU 32 (303 : I32)) Statics.str_51
          t47 := ()
        let t48 : Ptr ← Ptr.add queue_v 1 168
        let t49 : Bool := ((0 : I32) != 0)
        Mem.store t48 t49
        let t50 : Ptr ← Ptr.add queue_v 1 56
        let t51 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel t50
        let t52 : Ptr ← Ptr.add item_1 1 16
        let t53 : Bool ← Mem.load Bool t52
        if t53 then
          Talloc.ta_free item_1
        else
          let t54 : Ptr ← Ptr.add item_1 1 18
          let t55 : Bool := ((1 : I32) != 0)
          Mem.store t54 t55
      else
        let t56 : Ptr ← Ptr.add queue_v 1 144
        let t57 : I64 ← Mem.load I64 t56
        let mut t60 : Bool := false
        if (decide (t57 > (SInt.toS 64 (0 : I32)))) then
          let t58 : Ptr ← Ptr.add queue_v 1 152
          let t59 : Bool ← Mem.load Bool t58
          t60 := (!t59)
        if t60 then
          let t61 : Ptr ← Ptr.add queue_v 1 56
          let t62 : Ptr ← Ptr.add queue_v 1 16
          let t63 : Ptr ← Ptr.add queue_v 1 144
          let t64 : I64 ← Mem.load I64 t63
          let t65 : I32 ← Osdep.Threads_posix_h.mp_cond_timedwait_until fuel t61 t62 t64
          if (t65 != 0) then
            let t66 : Ptr ← Ptr.add queue_v 1 144
            let t67 : I64 := (SInt.toS 64 (0 : I32))
            Mem.store t66 t67
        else
          break
  let t68 : Ptr ← Ptr.add queue_v 1 168
  let t69 : Bool ← Mem.load Bool t68
  let mut t70 : Unit := default
  if (!t69) then
    t70 := ()
  else
    Libc.«__assert_fail» Statics.str_46 Statics.str_42 (SInt.toU 32 (319 : I32)) Statics.str_51
    t70 := ()
  let t71 : Ptr ← Ptr.add queue_v 1 153
  let t72 : Bool := ((0 : I32) != 0)
  Mem.store t71 t72
  let t73 : Ptr ← Ptr.add queue_v 1 152
  let t74 : Bool := ((0 : I32) != 0)
  Mem.store t73 t74
  let t75 : Ptr ← Ptr.add queue_v 1 16
  let t76 : I32 ← Ext.pthread_mutex_unlock.call t75
  pure ()

/-- C function `mp_dispatch_interrupt`, ../.mpv/misc/dispatch.c:331.
-/
def mp_dispatch_interrupt [Ext.pthread_cond_broadcast] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (queue : Ptr) : M Unit := do
  let mut queue_v : Ptr := queue
  let t1 : Ptr ← Ptr.add queue_v 1 16
  let t2 : I32 ← Ext.pthread_mutex_lock.call t1
  let t3 : Ptr ← Ptr.add queue_v 1 152
  let t4 : Bool := ((1 : I32) != 0)
  Mem.store t3 t4
  let t5 : Ptr ← Ptr.add queue_v 1 56
  let t6 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel t5
  let t7 : Ptr ← Ptr.add queue_v 1 16
  let t8 : I32 ← Ext.pthread_mutex_unlock.call t7
  pure ()

/-- C function `mp_dispatch_adjust_timeout`, ../.mpv/misc/dispatch.c:347.
-/
def mp_dispatch_adjust_timeout [Ext.pthread_cond_broadcast] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (queue : Ptr) (v_until : I64) : M Unit := do
  let mut queue_v : Ptr := queue
  let mut v_until_v : I64 := v_until
  let t1 : Ptr ← Ptr.add queue_v 1 16
  let t2 : I32 ← Ext.pthread_mutex_lock.call t1
  let t3 : Ptr ← Ptr.add queue_v 1 153
  let t4 : Bool ← Mem.load Bool t3
  let mut t7 : Bool := false
  if ((SInt.ofBool 32 t4) != 0) then
    let t5 : Ptr ← Ptr.add queue_v 1 144
    let t6 : I64 ← Mem.load I64 t5
    t7 := (decide (t6 > v_until_v))
  if t7 then
    let t8 : Ptr ← Ptr.add queue_v 1 144
    Mem.store t8 v_until_v
    let t9 : Ptr ← Ptr.add queue_v 1 56
    let t10 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel t9
    pure ()
  let t11 : Ptr ← Ptr.add queue_v 1 16
  let t12 : I32 ← Ext.pthread_mutex_unlock.call t11
  pure ()

/-- C function `mp_dispatch_lock`, ../.mpv/misc/dispatch.c:364.
Assumes external-order: where C leaves the order of two operands open and one calls a function taken as a parameter while the other reads memory, that function does not write what the other reads; operands are evaluated left to right.
-/
def mp_dispatch_lock [Ext.Misc_Thread_pool_c_thread_pool_dtor] [Ext.Misc_Thread_tools_c_cancel_destroy] [Ext.pthread_cond_destroy] [Ext.pthread_cond_wait] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.pthread_self] (fuel : Nat) (queue : Ptr) : M Unit := do
  let mut queue_v : Ptr := queue
  let t1 : Ptr ← Ptr.add queue_v 1 16
  let t2 : I32 ← Ext.pthread_mutex_lock.call t1
  let t3 : Ptr ← Ptr.add queue_v 1 153
  let t4 : Bool ← Mem.load Bool t3
  if t4 then
    let t5 : Ptr ← Ptr.add queue_v 1 160
    let t6 : U64 ← Mem.load U64 t5
    let t7 : U64 ← Ext.pthread_self.call
    let mut t8 : Unit := default
    if (!(t6 == t7)) then
      t8 := ()
    else
      Libc.«__assert_fail» Statics.str_53 Statics.str_42 (SInt.toU 32 (369 : I32)) Statics.str_54
      t8 := ()
  let t9 : Ptr ← Ptr.add queue_v 1 184
  let t10 : Bool ← Mem.load Bool t9
  if t10 then
    let t11 : Ptr ← Ptr.add queue_v 1 192
    let t12 : U64 ← Mem.load U64 t11
    let t13 : U64 ← Ext.pthread_self.call
    let mut t14 : Unit := default
    if (!(t12 == t13)) then
      t14 := ()
    else
      Libc.«__assert_fail» Statics.str_55 Statics.str_42 (SInt.toU 32 (372 : I32)) Statics.str_54
      t14 := ()
  let t15 : Ptr ← Ptr.add queue_v 1 176
  let t16 : U64 ← Mem.load U64 t15
  let t17 : U64 := (t16 + (SInt.toU 64 (1 : I32)))
  Mem.store t15 t17
  let t18 : Ptr ← Ptr.add queue_v 1 128
  let t19 : Ptr ← Mem.load Ptr t18
  if (t19 != Ptr.null) then
    let t20 : Ptr ← Ptr.add queue_v 1 128
    let t21 : Ptr ← Mem.load Ptr t20
    let t22 : Ptr ← Ptr.add queue_v 1 136
    let t23 : Ptr ← Mem.load Ptr t22
    (match t21 with
      | Ptr.fn "Misc.Dispatch_c.queue_dtor" => Misc.Dispatch_c.queue_dtor fuel t23
      | Ptr.fn "Misc.Thread_pool_c.thread_pool_dtor" => Ext.Misc_Thread_pool_c_thread_pool_dtor.call t23
      | Ptr.fn "Misc.Thread_tools_c.cancel_destroy" => Ext.Misc_Thread_tools_c_cancel_destroy.call t23
      | Ptr.null => ub "call through a null pointer"
      | _ => unsupported "call through a pointer to a function the selection does not know with this type")
  for _ in Fuel.mk fuel do
    let t24 : Ptr ← Ptr.add queue_v 1 153
    let t25 : Bool ← Mem.load Bool t24
    if !(!t25) then break
    let t26 : Ptr ← Ptr.add queue_v 1 16
    let t27 : I32 ← Ext.pthread_mutex_unlock.call t26
    let t28 : Ptr ← Ptr.add queue_v 1 112
    let t29 : Ptr ← Mem.load Ptr t28
    if (t29 != Ptr.null) then
      let t30 : Ptr ← Ptr.add queue_v 1 112
      let t31 : Ptr ← Mem.load Ptr t30
      let t32 : Ptr ← Ptr.add queue_v 1 120
      let t33 : Ptr ← Mem.load Ptr t32
      (match t31 with
        | Ptr.fn "Misc.Dispatch_c.queue_dtor" => Misc.Dispatch_c.queue_dtor fuel t33
        | Ptr.fn "Misc.Thread_pool_c.thread_pool_dtor" => Ext.Misc_Thread_pool_c_thread_pool_dtor.call t33
        | Ptr.fn "Misc.Thread_tools_c.cancel_destroy" => Ext.Misc_Thread_tools_c_cancel_destroy.call t33
        | Ptr.null => ub "call through a null pointer"
        | _ => unsupported "call through a pointer to a function the selection does not know with this type")
    let t34 : Ptr ← Ptr.add queue_v 1 16
    let t35 : I32 ← Ext.pthread_mutex_lock.call t34
    let t36 : Ptr ← Ptr.add queue_v 1 153
    let t37 : Bool ← Mem.load Bool t36
    if t37 then
      break
    let t38 : Ptr ← Ptr.add queue_v 1 56
    let t39 : Ptr ← Ptr.add queue_v 1 16
    let t40 : I32 ← Osdep.Threads_posix_h.mp_cond_wait fuel t38 t39
    pure ()
  for _ in Fuel.mk fuel do
    let t41 : Ptr ← Ptr.add queue_v 1 153
    let t42 : Bool ← Mem.load Bool t41
    let mut t45 : Bool := true
    if !(!t42) then
      let t43 : Ptr ← Ptr.add queue_v 1 168
      let t44 : Bool ← Mem.load Bool t43
      t45 := ((SInt.ofBool 32 t44) != 0)
    if !t45 then break
    let t46 : Ptr ← Ptr.add queue_v 1 56
    let t47 : Ptr ← Ptr.add queue_v 1 16
    let t48 : I32 ← Osdep.Threads_posix_h.mp_cond_wait fuel t46 t47
    pure ()
  let t49 : Ptr ← Ptr.add queue_v 1 176
  let t50 : U64 ← Mem.load U64 t49
  let mut t51 : Unit := default
  if (t50 != 0) then
    t51 := ()
  else
    Libc.«__assert_fail» Statics.str_56 Statics.str_42 (SInt.toU 32 (392 : I32)) Statics.str_54
    t51 := ()
  let t52 : Ptr ← Ptr.add queue_v 1 168
  let t53 : Bool ← Mem.load Bool t52
  let mut t54 : Unit := default
  if (!t53) then
    t54 := ()
  else
    Libc.«__assert_fail» Statics.str_46 Statics.str_42 (SInt.toU 32 (393 : I32)) Statics.str_54
    t54 := ()
  let t55 : Ptr ← Ptr.add queue_v 1 184
  let t56 : Bool ← Mem.load Bool t55
  let mut t57 : Unit := default
  if (!t56) then
    t57 := ()
  else
    Libc.«__assert_fail» Statics.str_57 Statics.str_42 (SInt.toU 32 (394 : I32)) Statics.str_54
    t57 := ()
  let t58 : Ptr ← Ptr.add queue_v 1 168
  let t59 : Bool := ((1 : I32) != 0)
  Mem.store t58 t59
  let t60 : Ptr ← Ptr.add queue_v 1 184
  let t61 : Bool := ((1 : I32) != 0)
  Mem.store t60 t61
  let t62 : Ptr ← Ptr.add queue_v 1 192
  let t63 : U64 ← Ext.pthread_self.call
  Mem.store t62 t63
  let t64 : Ptr ← Ptr.add queue_v 1 16
  let t65 : I32 ← Ext.pthread_mutex_unlock.call t64
  pure ()

/-- C function `mp_dispatch_unlock`, ../.mpv/misc/dispatch.c:402.
Assumes external-order: where C leaves the order of two operands open and one calls a function taken as a parameter while the other reads memory, that function does not write what the other reads; operands are evaluated left to right.
-/
def mp_dispatch_unlock [Ext.pthread_cond_broadcast] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.pthread_self] (fuel : Nat) (queue : Ptr) : M Unit := do
  let mut queue_v : Ptr := queue
  let t1 : Ptr ← Ptr.add queue_v 1 16
  let t2 : I32 ← Ext.pthread_mutex_lock.call t1
  let t3 : Ptr ← Ptr.add queue_v 1 168
  let t4 : Bool ← Mem.load Bool t3
  let mut t5 : Unit := default
  if ((SInt.ofBool 32 t4) != 0) then
    t5 := ()
  else
    Libc.«__assert_fail» Statics.str_52 Statics.str_42 (SInt.toU 32 (405 : I32)) Statics.str_58
    t5 := ()
  let t6 : Ptr ← Ptr.add queue_v 1 184
  let t7 : Bool ← Mem.load Bool t6
  let mut t8 : Unit := default
  if ((SInt.ofBool 32 t7) != 0) then
    t8 := ()
  else
    Libc.«__assert_fail» Statics.str_59 Statics.str_42 (SInt.toU 32 (407 : I32)) Statics.str_58
    t8 := ()
  let t9 : Ptr ← Ptr.add queue_v 1 192
  let t10 : U64 ← Mem.load U64 t9
  let t11 : U64 ← Ext.pthread_self.call
  let mut t12 : Unit := default
  if (t10 == t11) then
    t12 := ()
  else
    Libc.«__assert_fail» Statics.str_60 Statics.str_42 (SInt.toU 32 (408 : I32)) Statics.str_58
    t12 := ()
  let t13 : Ptr ← Ptr.add queue_v 1 168
  let t14 : Bool := ((0 : I32) != 0)
  Mem.store t13 t14
  let t15 : Ptr ← Ptr.add queue_v 1 184
  let t16 : Bool := ((0 : I32) != 0)
  Mem.store t15 t16
  let t17 : Ptr ← Ptr.add queue_v 1 176
  let t18 : U64 ← Mem.load U64 t17
  let t19 : U64 := (t18 - (SInt.toU 64 (1 : I32)))
  Mem.store t17 t19
  let t20 : Ptr ← Ptr.add queue_v 1 56
  let t21 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel t20
  let t22 : Ptr ← Ptr.add queue_v 1 16
  let t23 : I32 ← Ext.pthread_mutex_unlock.call t22
  pure ()

end Misc.Misc.Dispatch_c
