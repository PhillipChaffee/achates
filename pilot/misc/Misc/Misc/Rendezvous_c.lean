import Achates
import Misc.Statics
import Misc.Externals
import Misc.Osdep.Threads_posix_h

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Misc.Rendezvous_c

/-- C function `mp_rendezvous`, ../.mpv/misc/rendezvous.c:32.
-/
def mp_rendezvous [Ext.pthread_cond_broadcast] [Ext.pthread_cond_wait] [Ext.pthread_mutex_lock] [Ext.pthread_mutex_unlock] (fuel : Nat) (tag : Ptr) (value : I64) : M I64 := do
  let value_p ← Mem.alloca 8 8
  let wait_1 ← Mem.alloca 24 8
  let prev_2 ← Mem.alloca 8 8
  let result : I64 ← (do
    let mut tag_v : Ptr := tag
    Mem.store value_p value
    for _ in Once.mk do
      Mem.store wait_1 tag_v
      let t1 : Ptr ← Ptr.add wait_1 1 8
      Mem.zero t1 8
      let t2 : Ptr ← Ptr.add wait_1 1 16
      Mem.store t2 value_p
      let t3 : I32 ← Ext.pthread_mutex_lock.call Statics.g_Misc_Rendezvous_c_lock
      Mem.store prev_2 Statics.g_Misc_Rendezvous_c_waiters
      let mut j30 := false
      for _ in Fuel.mk fuel do
        let t4 : Ptr ← Mem.load Ptr prev_2
        let t5 : Ptr ← Mem.load Ptr t4
        if !(t5 != Ptr.null) then break
        let t6 : Ptr ← Mem.load Ptr prev_2
        let t7 : Ptr ← Mem.load Ptr t6
        let t8 : Ptr ← Mem.load Ptr t7
        let t9 : Bool ← Ptr.eq t8 tag_v
        if t9 then
          let t10 : Ptr ← Mem.load Ptr prev_2
          let t11 : Ptr ← Mem.load Ptr t10
          let t12 : Ptr ← Ptr.add t11 1 16
          let t13 : Ptr ← Mem.load Ptr t12
          let t14 : I64 ← Mem.load I64 t13
          let mut tmp_3 : I64 := t14
          let t15 : Ptr ← Mem.load Ptr prev_2
          let t16 : Ptr ← Mem.load Ptr t15
          let t17 : Ptr ← Ptr.add t16 1 16
          let t18 : Ptr ← Mem.load Ptr t17
          let t19 : I64 ← Mem.load I64 value_p
          Mem.store t18 t19
          Mem.store value_p tmp_3
          let t20 : Ptr ← Mem.load Ptr prev_2
          let t21 : Ptr ← Mem.load Ptr t20
          let t22 : Ptr ← Ptr.add t21 1 16
          let t23 : Ptr := Ptr.null
          Mem.store t22 t23
          let t24 : Ptr ← Mem.load Ptr prev_2
          let t25 : Ptr ← Mem.load Ptr prev_2
          let t26 : Ptr ← Mem.load Ptr t25
          let t27 : Ptr ← Ptr.add t26 1 8
          let t28 : Ptr ← Mem.load Ptr t27
          Mem.store t24 t28
          let t29 : I32 ← Osdep.Threads_posix_h.mp_cond_broadcast fuel Statics.g_Misc_Rendezvous_c_wakeup
          j30 := true
          break
        let t31 : Ptr ← Mem.load Ptr prev_2
        let t32 : Ptr ← Mem.load Ptr t31
        let t33 : Ptr ← Ptr.add t32 1 8
        Mem.store prev_2 t33
      if j30 then break
      let t34 : Ptr ← Mem.load Ptr prev_2
      Mem.store t34 wait_1
      for _ in Fuel.mk fuel do
        let t35 : Ptr ← Ptr.add wait_1 1 16
        let t36 : Ptr ← Mem.load Ptr t35
        if !(t36 != Ptr.null) then break
        let t37 : I32 ← Osdep.Threads_posix_h.mp_cond_wait fuel Statics.g_Misc_Rendezvous_c_wakeup Statics.g_Misc_Rendezvous_c_lock
        pure ()
    let t38 : I32 ← Ext.pthread_mutex_unlock.call Statics.g_Misc_Rendezvous_c_lock
    let t39 : I64 ← Mem.load I64 value_p
    return t39
    : M I64)
  Mem.popFrame [value_p, wait_1, prev_2]
  pure result

end Misc.Misc.Rendezvous_c
