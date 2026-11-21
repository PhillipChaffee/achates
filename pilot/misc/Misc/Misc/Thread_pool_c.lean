import Achates
import Misc.Statics
import Misc.Externals
import Misc.Misc.Dispatch_c
import Misc.Osdep.Threads_posix_h
import Misc.Ta.Ta_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Thread_pool_c

/-- C function `thread_pool_dtor`, ../.mpv/misc/thread_pool.c:115.
-/
def thread_pool_dtor [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (ctx : Ptr) : M Unit := do
  let mut ctx_v : Ptr := ctx
  let mut pool_1 : Ptr := ctx_v
  let t1 : Ptr ← Ptr.add pool_1 1 8
  let t2 : I32 ← Ext.pthread_mutex_lock.call t1
  let t3 : Ptr ← Ptr.add pool_1 1 120
  let t4 : Bool := ((1 : I32) != 0)
  Mem.store t3 t4
  let t5 : Ptr ← Ptr.add pool_1 1 48
  let t6 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel t5
  let t7 : Ptr ← Ptr.add pool_1 1 104
  let t8 : Ptr ← Mem.load Ptr t7
  let mut threads_2 : Ptr := t8
  let t9 : Ptr ← Ptr.add pool_1 1 112
  let t10 : I32 ← Mem.load I32 t9
  let mut num_threads_3 : I32 := t10
  let t11 : Ptr ← Ptr.add pool_1 1 104
  let t12 : Ptr := Ptr.null
  Mem.store t11 t12
  let t13 : Ptr ← Ptr.add pool_1 1 112
  let t14 : I32 := (0 : I32)
  Mem.store t13 t14
  let t15 : Ptr ← Ptr.add pool_1 1 8
  let t16 : I32 ← Ext.pthread_mutex_unlock.call t15
  let mut n_4 : I32 := (0 : I32)
  for _ in Fuel.mk fuel do
    if !(decide (n_4 < num_threads_3)) then break
    for _ in Once.mk do
      let t17 : Ptr ← Ptr.add threads_2 8 (SInt.toInt n_4)
      let t18 : U64 ← Mem.load U64 t17
      let t19 : I32 ← Ext.pthread_join.call t18 Ptr.null
      pure ()
    let t20 : I32 := n_4
    let t21 : I32 ← SInt.add t20 1
    n_4 := t21
  let t22 : Ptr ← Ptr.add pool_1 1 136
  let t23 : I32 ← Mem.load I32 t22
  let mut t24 : Unit := default
  if (t23 == (0 : I32)) then
    t24 := ()
  else
    Libc.«__assert_fail» Statics.str_150 Statics.str_148 (SInt.toU 32 (136 : I32)) Statics.str_151
    t24 := ()
  let t25 : Ptr ← Ptr.add pool_1 1 112
  let t26 : I32 ← Mem.load I32 t25
  let mut t27 : Unit := default
  if (t26 == (0 : I32)) then
    t27 := ()
  else
    Libc.«__assert_fail» Statics.str_152 Statics.str_148 (SInt.toU 32 (137 : I32)) Statics.str_151
    t27 := ()
  let t28 : Ptr ← Ptr.add pool_1 1 48
  let t29 : I32 ← Osdep.Threads_posix_h.mp_cond_destroy fuel t28
  let t30 : Ptr ← Ptr.add pool_1 1 8
  let t31 : I32 ← Ext.pthread_mutex_destroy.call t30
  pure ()

/-- C function `worker_thread`, ../.mpv/misc/thread_pool.c:51.
Assumes external-order: where C leaves the order of two operands open and one calls a function taken as a parameter while the other reads memory, that function does not write what the other reads; operands are evaluated left to right.
-/
def worker_thread [Ext.Misc_Thread_tools_c_cancel_destroy] [Ext.clock_gettime] [Ext.mp_time_ns] [Ext.pthread_cond_broadcast] [Ext.pthread_cond_destroy] [Ext.pthread_cond_timedwait] [Ext.pthread_cond_wait] [Ext.pthread_detach] [Ext.pthread_join] [Ext.pthread_mutex_destroy] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.pthread_self] [Ext.pthread_setname_np] [Ext.strncpy] (fuel : Nat) (arg : Ptr) : M Ptr := do
  let work_4 ← Mem.alloca 16 8
  let result : Ptr ← (do
    let mut arg_v : Ptr := arg
    let mut pool_1 : Ptr := arg_v
    Osdep.Threads_posix_h.mp_thread_set_name fuel Statics.str_146
    let t1 : Ptr ← Ptr.add pool_1 1 8
    let t2 : I32 ← Ext.pthread_mutex_lock.call t1
    let mut destroy_deadline_2 : I64 := (SInt.toS 64 (0 : I32))
    let mut got_timeout_3 : Bool := ((0 : I32) != 0)
    for _ in Fuel.mk fuel do
      if !((1 : I32) != 0) then break
      Mem.store work_4 Ptr.null
      let t3 : Ptr ← Ptr.add work_4 1 8
      Mem.zero t3 8
      let t4 : Ptr ← Ptr.add pool_1 1 136
      let t5 : I32 ← Mem.load I32 t4
      if (decide (t5 > (0 : I32))) then
        let t6 : Ptr ← Ptr.add pool_1 1 128
        let t7 : Ptr ← Mem.load Ptr t6
        let t8 : Ptr ← Ptr.add pool_1 1 136
        let t9 : I32 ← Mem.load I32 t8
        let t10 : I32 ← SInt.sub t9 (1 : I32)
        let t11 : Ptr ← Ptr.add t7 16 (SInt.toInt t10)
        let t12 : Agg ← Mem.loadAgg t11 16 8
        Mem.storeAgg work_4 t12 8
        let t13 : Ptr ← Ptr.add pool_1 1 136
        let t14 : I32 ← Mem.load I32 t13
        let t15 : I32 ← SInt.sub t14 (1 : I32)
        Mem.store t13 t15
      let t16 : Ptr ← Mem.load Ptr work_4
      if (!(t16 != Ptr.null)) then
        let mut t19 : Bool := true
        if !((SInt.ofBool 32 got_timeout_3) != 0) then
          let t17 : Ptr ← Ptr.add pool_1 1 120
          let t18 : Bool ← Mem.load Bool t17
          t19 := ((SInt.ofBool 32 t18) != 0)
        if t19 then
          break
        let t20 : Ptr ← Ptr.add pool_1 1 112
        let t21 : I32 ← Mem.load I32 t20
        let t22 : I32 ← Mem.load I32 pool_1
        if (decide (t21 > t22)) then
          if (!(destroy_deadline_2 != 0)) then
            let t23 : I64 ← Ext.mp_time_ns.call
            let t24 : I64 ← SInt.mul (SInt.toS 64 (10 : I32)) (1000000000 : I64)
            let t25 : I64 ← SInt.add t23 t24
            destroy_deadline_2 := t25
          let t26 : Ptr ← Ptr.add pool_1 1 48
          let t27 : Ptr ← Ptr.add pool_1 1 8
          let t28 : I32 ← Osdep.Threads_posix_h.mp_cond_timedwait_until fuel t26 t27 destroy_deadline_2
          if (t28 != 0) then
            let t29 : Ptr ← Ptr.add pool_1 1 112
            let t30 : I32 ← Mem.load I32 t29
            let t31 : I32 ← Mem.load I32 pool_1
            let t32 : Bool := ((SInt.ofBool 32 (decide (t30 > t31))) != 0)
            got_timeout_3 := t32
        else
          let t33 : Ptr ← Ptr.add pool_1 1 48
          let t34 : Ptr ← Ptr.add pool_1 1 8
          let t35 : I32 ← Osdep.Threads_posix_h.mp_cond_wait fuel t33 t34
          pure ()
        continue
      let t36 : Ptr ← Ptr.add pool_1 1 116
      let t37 : I32 ← Mem.load I32 t36
      let t38 : I32 ← SInt.add t37 (1 : I32)
      Mem.store t36 t38
      let t39 : Ptr ← Ptr.add pool_1 1 8
      let t40 : I32 ← Ext.pthread_mutex_unlock.call t39
      let t41 : Ptr ← Mem.load Ptr work_4
      let t42 : Ptr ← Ptr.add work_4 1 8
      let t43 : Ptr ← Mem.load Ptr t42
      (match t41 with
        | Ptr.fn "Misc.Dispatch_c.queue_dtor" => Misc.Dispatch_c.queue_dtor fuel t43
        | Ptr.fn "Misc.Thread_pool_c.thread_pool_dtor" => Misc.Thread_pool_c.thread_pool_dtor fuel t43
        | Ptr.fn "Misc.Thread_tools_c.cancel_destroy" => Ext.Misc_Thread_tools_c_cancel_destroy.call t43
        | Ptr.null => ub "call through a null pointer"
        | _ => unsupported "call through a pointer to a function the selection does not know with this type")
      let t44 : Ptr ← Ptr.add pool_1 1 8
      let t45 : I32 ← Ext.pthread_mutex_lock.call t44
      let t46 : Ptr ← Ptr.add pool_1 1 116
      let t47 : I32 ← Mem.load I32 t46
      let t48 : I32 ← SInt.sub t47 (1 : I32)
      Mem.store t46 t48
      let t49 : I64 := (SInt.toS 64 (0 : I32))
      destroy_deadline_2 := t49
      let t50 : Bool := ((0 : I32) != 0)
      got_timeout_3 := t50
    let t51 : Ptr ← Ptr.add pool_1 1 120
    let t52 : Bool ← Mem.load Bool t51
    if (!t52) then
      let mut n_5 : I32 := (0 : I32)
      for _ in Fuel.mk fuel do
        let t53 : Ptr ← Ptr.add pool_1 1 112
        let t54 : I32 ← Mem.load I32 t53
        if !(decide (n_5 < t54)) then break
        for _ in Once.mk do
          let t55 : Ptr ← Ptr.add pool_1 1 104
          let t56 : Ptr ← Mem.load Ptr t55
          let t57 : Ptr ← Ptr.add t56 8 (SInt.toInt n_5)
          let t58 : U64 ← Mem.load U64 t57
          let t59 : U64 ← Ext.pthread_self.call
          if (t58 == t59) then
            let t60 : Ptr ← Ptr.add pool_1 1 104
            let t61 : Ptr ← Mem.load Ptr t60
            let t62 : Ptr ← Ptr.add t61 8 (SInt.toInt n_5)
            let t63 : U64 ← Mem.load U64 t62
            let t64 : I32 ← Ext.pthread_detach.call t63
            for _ in Fuel.mk fuel do
              for _ in Once.mk do
                let mut at__6 : U64 := (SInt.toU 64 n_5)
                let t65 : Ptr ← Ptr.add pool_1 1 112
                let t66 : I32 ← Mem.load I32 t65
                let mut t67 : Unit := default
                if (decide (at__6 < (SInt.toU 64 t66))) then
                  t67 := ()
                else
                  Libc.«__assert_fail» Statics.str_147 Statics.str_148 (SInt.toU 32 (103 : I32)) Statics.str_149
                  t67 := ()
                let t68 : Ptr ← Ptr.add pool_1 1 104
                let t69 : Ptr ← Mem.load Ptr t68
                let t70 : Ptr ← Ptr.add t69 8 (UInt.toInt at__6)
                let t71 : Ptr ← Ptr.add pool_1 1 104
                let t72 : Ptr ← Mem.load Ptr t71
                let t73 : Ptr ← Ptr.add t72 8 (UInt.toInt at__6)
                let t74 : Ptr ← Ptr.add t73 8 (SInt.toInt (1 : I32))
                let t75 : Ptr ← Ptr.add pool_1 1 112
                let t76 : I32 ← Mem.load I32 t75
                let t77 : Ptr ← Libc.memmove t70 t74 ((((SInt.toU 64 t76) - at__6) - (SInt.toU 64 (1 : I32))) * (8 : U64))
                let t78 : Ptr ← Ptr.add pool_1 1 112
                let t79 : I32 ← Mem.load I32 t78
                let t80 : I32 ← SInt.sub t79 1
                Mem.store t78 t80
              if !((0 : I32) != 0) then break
            let t81 : Ptr ← Ptr.add pool_1 1 8
            let t82 : I32 ← Ext.pthread_mutex_unlock.call t81
            return Ptr.null
        let t83 : I32 := n_5
        let t84 : I32 ← SInt.add t83 1
        n_5 := t84
      let mut t85 : Unit := default
      if (!(Statics.str_133 != Ptr.null)) then
        t85 := ()
      else
        Libc.«__assert_fail» Statics.str_134 Statics.str_148 (SInt.toU 32 (108 : I32)) Statics.str_149
        t85 := ()
      Libc.abort
    let t86 : Ptr ← Ptr.add pool_1 1 8
    let t87 : I32 ← Ext.pthread_mutex_unlock.call t86
    return Ptr.null
    : M Ptr)
  Mem.popFrame [work_4]
  pure result

/-- C function `add_thread`, ../.mpv/misc/thread_pool.c:142.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def add_thread [Ext.pthread_create] (fuel : Nat) (pool : Ptr) : M Bool := do
  let thread_1 ← Mem.alloca 8 8
  let result : Bool ← (do
    let mut pool_v : Ptr := pool
    Mem.undefine thread_1 8
    let t1 : I32 ← Ext.pthread_create.call thread_1 Ptr.null (Ptr.fn "Misc.Thread_pool_c.worker_thread") pool_v
    if (t1 != (0 : I32)) then
      return ((0 : I32) != 0)
    for _ in Fuel.mk fuel do
      for _ in Once.mk do
        for _ in Fuel.mk fuel do
          for _ in Once.mk do
            let t2 : Ptr ← Ptr.add pool_v 1 112
            let t3 : I32 ← Mem.load I32 t2
            let mut nextidx__2 : U64 := (SInt.toU 64 t3)
            let t4 : Ptr ← Ptr.add pool_v 1 104
            let t5 : Ptr ← Mem.load Ptr t4
            let t6 : U64 ← Talloc.ta_get_size t5
            let t7 : U64 ← UInt.div t6 (8 : U64)
            if (decide (nextidx__2 ≥ t7)) then
              for _ in Fuel.mk fuel do
                for _ in Once.mk do
                  let t8 : Ptr ← Ptr.add pool_v 1 104
                  let t9 : Ptr ← Ptr.add pool_v 1 104
                  let t10 : Ptr ← Mem.load Ptr t9
                  let t11 : U64 ← Talloc.ta_calc_prealloc_elems nextidx__2
                  let t12 : U64 ← Talloc.ta_calc_array_size (8 : U64) t11
                  let t13 : Ptr ← Talloc.ta_xrealloc_size pool_v t10 t12
                  let t14 : Ptr ← Talloc.ta_dbg_set_loc t13 Statics.str_153
                  Mem.store t8 t14
                if !((0 : I32) != 0) then break
          if !((0 : I32) != 0) then break
        let t15 : Ptr ← Ptr.add pool_v 1 104
        let t16 : Ptr ← Mem.load Ptr t15
        let t17 : Ptr ← Ptr.add pool_v 1 112
        let t18 : I32 ← Mem.load I32 t17
        let t19 : Ptr ← Ptr.add t16 8 (SInt.toInt t18)
        let t20 : U64 ← Mem.load U64 thread_1
        Mem.store t19 t20
        let t21 : Ptr ← Ptr.add pool_v 1 112
        let t22 : I32 ← Mem.load I32 t21
        let t23 : I32 ← SInt.add t22 1
        Mem.store t21 t23
      if !((0 : I32) != 0) then break
    return ((1 : I32) != 0)
    : M Bool)
  Mem.popFrame [thread_1]
  pure result

/-- C function `mp_thread_pool_create`, ../.mpv/misc/thread_pool.c:153.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_thread_pool_create [Ext.pthread_cond_init] [Ext.pthread_condattr_destroy] [Ext.pthread_condattr_init] [Ext.pthread_condattr_setclock] [Ext.pthread_create] [Ext.pthread_mutex_init] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] [Ext.pthread_mutexattr_destroy] [Ext.pthread_mutexattr_init] [Ext.pthread_mutexattr_settype] (fuel : Nat) (ta_parent : Ptr) (init_threads : I32) (min_threads : I32) (max_threads : I32) : M Ptr := do
  let pool_1 ← Mem.alloca 8 8
  let result : Ptr ← (do
    let mut ta_parent_v : Ptr := ta_parent
    let mut init_threads_v : I32 := init_threads
    let mut min_threads_v : I32 := min_threads
    let mut max_threads_v : I32 := max_threads
    let mut t1 : Unit := default
    if (decide (min_threads_v ≥ (0 : I32))) then
      t1 := ()
    else
      Libc.«__assert_fail» Statics.str_154 Statics.str_148 (SInt.toU 32 (156 : I32)) Statics.str_155
      t1 := ()
    let mut t2 : Unit := default
    if (decide (init_threads_v ≤ min_threads_v)) then
      t2 := ()
    else
      Libc.«__assert_fail» Statics.str_156 Statics.str_148 (SInt.toU 32 (157 : I32)) Statics.str_155
      t2 := ()
    let mut t3 : Unit := default
    if ((decide (max_threads_v > (0 : I32))) && (decide (max_threads_v ≥ min_threads_v))) then
      t3 := ()
    else
      Libc.«__assert_fail» Statics.str_157 Statics.str_148 (SInt.toU 32 (158 : I32)) Statics.str_155
      t3 := ()
    let t4 : Ptr ← Talloc.ta_zalloc_size ta_parent_v (144 : U64)
    let t5 : Ptr ← Talloc.ta_dbg_set_loc t4 Statics.str_158
    let t6 : Ptr ← Ta.Ta_h.ta_oom_p fuel t5
    Mem.store pool_1 t6
    let t7 : Ptr ← Mem.load Ptr pool_1
    Talloc.ta_set_destructor t7 (Ptr.fn "Misc.Thread_pool_c.thread_pool_dtor")
    let t8 : Ptr ← Mem.load Ptr pool_1
    let t9 : Ptr ← Ptr.add t8 1 8
    let t10 : I32 ← Osdep.Threads_posix_h.mp_mutex_init fuel t9
    let t11 : Ptr ← Mem.load Ptr pool_1
    let t12 : Ptr ← Ptr.add t11 1 48
    let t13 : I32 ← Osdep.Threads_posix_h.mp_cond_init fuel t12
    let t14 : Ptr ← Mem.load Ptr pool_1
    Mem.store t14 min_threads_v
    let t15 : Ptr ← Mem.load Ptr pool_1
    let t16 : Ptr ← Ptr.add t15 1 4
    Mem.store t16 max_threads_v
    let t17 : Ptr ← Mem.load Ptr pool_1
    let t18 : Ptr ← Ptr.add t17 1 8
    let t19 : I32 ← Ext.pthread_mutex_lock.call t18
    let mut n_2 : I32 := (0 : I32)
    for _ in Fuel.mk fuel do
      if !(decide (n_2 < init_threads_v)) then break
      for _ in Once.mk do
        let t20 : Ptr ← Mem.load Ptr pool_1
        let t21 : Bool ← Misc.Thread_pool_c.add_thread fuel t20
        pure ()
      let t22 : I32 := n_2
      let t23 : I32 ← SInt.add t22 1
      n_2 := t23
    let t24 : Ptr ← Mem.load Ptr pool_1
    let t25 : Ptr ← Ptr.add t24 1 112
    let t26 : I32 ← Mem.load I32 t25
    let mut ok_3 : Bool := ((SInt.ofBool 32 (decide (t26 ≥ init_threads_v))) != 0)
    let t27 : Ptr ← Mem.load Ptr pool_1
    let t28 : Ptr ← Ptr.add t27 1 8
    let t29 : I32 ← Ext.pthread_mutex_unlock.call t28
    if (!ok_3) then
      for _ in Fuel.mk fuel do
        for _ in Once.mk do
          let t30 : Ptr ← Mem.load Ptr pool_1
          Talloc.ta_free t30
          let t31 : Ptr := Ptr.null
          Mem.store pool_1 t31
        if !((0 : I32) != 0) then break
    let t32 : Ptr ← Mem.load Ptr pool_1
    return t32
    : M Ptr)
  Mem.popFrame [pool_1]
  pure result

/-- C function `thread_pool_add`, ../.mpv/misc/thread_pool.c:181.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def thread_pool_add [Ext.pthread_cond_signal] [Ext.pthread_create] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (pool : Ptr) (fn : Ptr) (fn_ctx : Ptr) (allow_queue : Bool) : M Bool := do
  let work_2 ← Mem.alloca 16 8
  let result : Bool ← (do
    let mut pool_v : Ptr := pool
    let mut fn_v : Ptr := fn
    let mut fn_ctx_v : Ptr := fn_ctx
    let mut allow_queue_v : Bool := allow_queue
    let mut ok_1 : Bool := ((1 : I32) != 0)
    let mut t1 : Unit := default
    if (fn_v != Ptr.null) then
      t1 := ()
    else
      Libc.«__assert_fail» Statics.str_159 Statics.str_148 (SInt.toU 32 (186 : I32)) Statics.str_160
      t1 := ()
    let t2 : Ptr ← Ptr.add pool_v 1 8
    let t3 : I32 ← Ext.pthread_mutex_lock.call t2
    Mem.store work_2 fn_v
    let t4 : Ptr ← Ptr.add work_2 1 8
    Mem.store t4 fn_ctx_v
    let t5 : Ptr ← Ptr.add pool_v 1 116
    let t6 : I32 ← Mem.load I32 t5
    let t7 : Ptr ← Ptr.add pool_v 1 136
    let t8 : I32 ← Mem.load I32 t7
    let t9 : I32 ← SInt.add t6 t8
    let t10 : I32 ← SInt.add t9 (1 : I32)
    let t11 : Ptr ← Ptr.add pool_v 1 112
    let t12 : I32 ← Mem.load I32 t11
    let mut t17 : Bool := false
    if (decide (t10 > t12)) then
      let t13 : Ptr ← Ptr.add pool_v 1 112
      let t14 : I32 ← Mem.load I32 t13
      let t15 : Ptr ← Ptr.add pool_v 1 4
      let t16 : I32 ← Mem.load I32 t15
      t17 := (decide (t14 < t16))
    if t17 then
      let t18 : Bool ← Misc.Thread_pool_c.add_thread fuel pool_v
      if (!t18) then
        let mut t21 : Bool := false
        if ((SInt.ofBool 32 allow_queue_v) != 0) then
          let t19 : Ptr ← Ptr.add pool_v 1 112
          let t20 : I32 ← Mem.load I32 t19
          t21 := (decide (t20 > (0 : I32)))
        let t22 : Bool := ((SInt.ofBool 32 t21) != 0)
        ok_1 := t22
    if ok_1 then
      for _ in Fuel.mk fuel do
        for _ in Once.mk do
          let mut at__3 : U64 := (SInt.toU 64 (0 : I32))
          let t23 : Ptr ← Ptr.add pool_v 1 136
          let t24 : I32 ← Mem.load I32 t23
          let mut t25 : Unit := default
          if (decide (at__3 ≤ (SInt.toU 64 t24))) then
            t25 := ()
          else
            Libc.«__assert_fail» Statics.str_161 Statics.str_148 (SInt.toU 32 (205 : I32)) Statics.str_160
            t25 := ()
          for _ in Fuel.mk fuel do
            for _ in Once.mk do
              let t26 : Ptr ← Ptr.add pool_v 1 136
              let t27 : I32 ← Mem.load I32 t26
              let mut nextidx__4 : U64 := (SInt.toU 64 t27)
              let t28 : Ptr ← Ptr.add pool_v 1 128
              let t29 : Ptr ← Mem.load Ptr t28
              let t30 : U64 ← Talloc.ta_get_size t29
              let t31 : U64 ← UInt.div t30 (16 : U64)
              if (decide (nextidx__4 ≥ t31)) then
                for _ in Fuel.mk fuel do
                  for _ in Once.mk do
                    let t32 : Ptr ← Ptr.add pool_v 1 128
                    let t33 : Ptr ← Ptr.add pool_v 1 128
                    let t34 : Ptr ← Mem.load Ptr t33
                    let t35 : U64 ← Talloc.ta_calc_prealloc_elems nextidx__4
                    let t36 : U64 ← Talloc.ta_calc_array_size (16 : U64) t35
                    let t37 : Ptr ← Talloc.ta_xrealloc_size pool_v t34 t36
                    let t38 : Ptr ← Talloc.ta_dbg_set_loc t37 Statics.str_162
                    Mem.store t32 t38
                  if !((0 : I32) != 0) then break
            if !((0 : I32) != 0) then break
          let t39 : Ptr ← Ptr.add pool_v 1 128
          let t40 : Ptr ← Mem.load Ptr t39
          let t41 : Ptr ← Ptr.add t40 16 (UInt.toInt at__3)
          let t42 : Ptr ← Ptr.add t41 16 (SInt.toInt (1 : I32))
          let t43 : Ptr ← Ptr.add pool_v 1 128
          let t44 : Ptr ← Mem.load Ptr t43
          let t45 : Ptr ← Ptr.add t44 16 (UInt.toInt at__3)
          let t46 : Ptr ← Ptr.add pool_v 1 136
          let t47 : I32 ← Mem.load I32 t46
          let t48 : Ptr ← Libc.memmove t42 t45 (((SInt.toU 64 t47) - at__3) * (16 : U64))
          let t49 : Ptr ← Ptr.add pool_v 1 136
          let t50 : I32 ← Mem.load I32 t49
          let t51 : I32 ← SInt.add t50 1
          Mem.store t49 t51
          let t52 : Ptr ← Ptr.add pool_v 1 128
          let t53 : Ptr ← Mem.load Ptr t52
          let t54 : Ptr ← Ptr.add t53 16 (UInt.toInt at__3)
          let t55 : Agg ← Mem.loadAgg work_2 16 8
          Mem.storeAgg t54 t55 8
        if !((0 : I32) != 0) then break
      let t56 : Ptr ← Ptr.add pool_v 1 48
      let t57 : I32 ← Osdep.Threads_posix_h.mp_cond_signal fuel t56
      pure ()
    let t58 : Ptr ← Ptr.add pool_v 1 8
    let t59 : I32 ← Ext.pthread_mutex_unlock.call t58
    return ok_1
    : M Bool)
  Mem.popFrame [work_2]
  pure result

/-- C function `mp_thread_pool_queue`, ../.mpv/misc/thread_pool.c:213.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_thread_pool_queue [Ext.pthread_cond_signal] [Ext.pthread_create] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (pool : Ptr) (fn : Ptr) (fn_ctx : Ptr) : M Bool := do
  let mut pool_v : Ptr := pool
  let mut fn_v : Ptr := fn
  let mut fn_ctx_v : Ptr := fn_ctx
  let t1 : Bool ← Misc.Thread_pool_c.thread_pool_add fuel pool_v fn_v fn_ctx_v ((1 : I32) != 0)
  return t1

/-- C function `mp_thread_pool_run`, ../.mpv/misc/thread_pool.c:219.
Assumes alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported.
Assumes talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported.
-/
def mp_thread_pool_run [Ext.pthread_cond_signal] [Ext.pthread_create] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (pool : Ptr) (fn : Ptr) (fn_ctx : Ptr) : M Bool := do
  let mut pool_v : Ptr := pool
  let mut fn_v : Ptr := fn
  let mut fn_ctx_v : Ptr := fn_ctx
  let t1 : Bool ← Misc.Thread_pool_c.thread_pool_add fuel pool_v fn_v fn_ctx_v ((0 : I32) != 0)
  return t1

end Misc.Misc.Thread_pool_c
