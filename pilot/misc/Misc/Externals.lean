import Achates

/-! Functions the emitted code calls and the selection does not define.
Each is a parameter: a definition that needs one says so in its signature.
Emitted by Achates from C; do not edit. -/

open Achates

namespace Misc

/-- C function `Misc.Language_c.lang_compare`. -/
class Ext.Misc_Language_c_lang_compare where
  call : Ptr → Ptr → M I32

/-- C function `Misc.Thread_pool_c.thread_pool_dtor`. -/
class Ext.Misc_Thread_pool_c_thread_pool_dtor where
  call : Ptr → M Unit

/-- C function `Misc.Thread_tools_c.cancel_destroy`. -/
class Ext.Misc_Thread_tools_c_cancel_destroy where
  call : Ptr → M Unit

/-- C function `__errno_location`. -/
class Ext.«__errno_location» where
  call : M Ptr

/-- C function `av_hash_alloc`. -/
class Ext.av_hash_alloc where
  call : Ptr → Ptr → M I32

/-- C function `av_hash_final`. -/
class Ext.av_hash_final where
  call : Ptr → Ptr → M Unit

/-- C function `av_hash_freep`. -/
class Ext.av_hash_freep where
  call : Ptr → M Unit

/-- C function `av_hash_get_size`. -/
class Ext.av_hash_get_size where
  call : Ptr → M I32

/-- C function `av_hash_init`. -/
class Ext.av_hash_init where
  call : Ptr → M Unit

/-- C function `av_hash_update`. -/
class Ext.av_hash_update where
  call : Ptr → Ptr → U64 → M Unit

/-- C function `av_random_bytes`. -/
class Ext.av_random_bytes where
  call : Ptr → U64 → M I32

/-- C function `clock_gettime`. -/
class Ext.clock_gettime where
  call : I32 → Ptr → M I32

/-- C function `close`. -/
class Ext.close where
  call : I32 → M I32

/-- C function `fclose`. -/
class Ext.fclose where
  call : Ptr → M I32

/-- C function `fdopen`. -/
class Ext.fdopen where
  call : I32 → Ptr → M Ptr

/-- C function `fwrite`. -/
class Ext.fwrite where
  call : Ptr → U64 → U64 → Ptr → M U64

/-- C function `getcwd`. -/
class Ext.getcwd where
  call : Ptr → U64 → M Ptr

/-- C function `getenv`. -/
class Ext.getenv where
  call : Ptr → M Ptr

/-- C function `memrchr`. -/
class Ext.memrchr where
  call : Ptr → I32 → U64 → M Ptr

/-- C function `mkdir`. -/
class Ext.mkdir where
  call : Ptr → U32 → M I32

/-- C function `mp_append_escaped_string`. -/
class Ext.mp_append_escaped_string where
  call : Ptr → Ptr → Ptr → M Bool

/-- C function `mp_append_utf8_bstr`. -/
class Ext.mp_append_utf8_bstr where
  call : Ptr → Ptr → U32 → M Unit

/-- C function `mp_log2`. -/
class Ext.mp_log2 where
  call : U32 → M U32

/-- C function `mp_make_wakeup_pipe`. -/
class Ext.mp_make_wakeup_pipe where
  call : Ptr → M I32

/-- C function `mp_msg`. -/
class Ext.mp_msg where
  call : Ptr → I32 → Ptr → List VArg → M Unit

/-- C function `mp_raw_time_ns`. -/
class Ext.mp_raw_time_ns where
  call : M U64

/-- C function `mp_round_next_power_of_2`. -/
class Ext.mp_round_next_power_of_2 where
  call : U32 → M U32

/-- C function `mp_time_ns`. -/
class Ext.mp_time_ns where
  call : M I64

/-- C function `mp_time_ns_add`. -/
class Ext.mp_time_ns_add where
  call : I64 → F64 → M I64

/-- C function `mp_tprintf_buf`. -/
class Ext.mp_tprintf_buf where
  call : Ptr → U64 → Ptr → List VArg → M Ptr

/-- C function `open`. -/
class Ext.«open» where
  call : Ptr → I32 → List VArg → M I32

/-- C function `pthread_cond_broadcast`. -/
class Ext.pthread_cond_broadcast where
  call : Ptr → M I32

/-- C function `pthread_cond_destroy`. -/
class Ext.pthread_cond_destroy where
  call : Ptr → M I32

/-- C function `pthread_cond_init`. -/
class Ext.pthread_cond_init where
  call : Ptr → Ptr → M I32

/-- C function `pthread_cond_signal`. -/
class Ext.pthread_cond_signal where
  call : Ptr → M I32

/-- C function `pthread_cond_timedwait`. -/
class Ext.pthread_cond_timedwait where
  call : Ptr → Ptr → Ptr → M I32

/-- C function `pthread_cond_wait`. -/
class Ext.pthread_cond_wait where
  call : Ptr → Ptr → M I32

/-- C function `pthread_condattr_destroy`. -/
class Ext.pthread_condattr_destroy where
  call : Ptr → M I32

/-- C function `pthread_condattr_init`. -/
class Ext.pthread_condattr_init where
  call : Ptr → M I32

/-- C function `pthread_condattr_setclock`. -/
class Ext.pthread_condattr_setclock where
  call : Ptr → I32 → M I32

/-- C function `pthread_create`. -/
class Ext.pthread_create where
  call : Ptr → Ptr → Ptr → Ptr → M I32

/-- C function `pthread_detach`. -/
class Ext.pthread_detach where
  call : U64 → M I32

/-- C function `pthread_join`. -/
class Ext.pthread_join where
  call : U64 → Ptr → M I32

/-- C function `pthread_mutex_destroy`. -/
class Ext.pthread_mutex_destroy where
  call : Ptr → M I32

/-- C function `pthread_mutex_init`. -/
class Ext.pthread_mutex_init where
  call : Ptr → Ptr → M I32

/-- C function `pthread_mutex_lock`. -/
class Ext.pthread_mutex_lock where
  call : Ptr → M I32

/-- C function `pthread_mutex_unlock`. -/
class Ext.pthread_mutex_unlock where
  call : Ptr → M I32

/-- C function `pthread_mutexattr_destroy`. -/
class Ext.pthread_mutexattr_destroy where
  call : Ptr → M I32

/-- C function `pthread_mutexattr_init`. -/
class Ext.pthread_mutexattr_init where
  call : Ptr → M I32

/-- C function `pthread_mutexattr_settype`. -/
class Ext.pthread_mutexattr_settype where
  call : Ptr → I32 → M I32

/-- C function `pthread_self`. -/
class Ext.pthread_self where
  call : M U64

/-- C function `pthread_setname_np`. -/
class Ext.pthread_setname_np where
  call : U64 → Ptr → M I32

/-- C function `read`. -/
class Ext.read where
  call : I32 → Ptr → U64 → M I64

/-- C function `realpath`. -/
class Ext.realpath where
  call : Ptr → Ptr → M Ptr

/-- C function `rename`. -/
class Ext.rename where
  call : Ptr → Ptr → M I32

/-- C function `stat`. -/
class Ext.stat where
  call : Ptr → Ptr → M I32

/-- C function `strcasecmp`. -/
class Ext.strcasecmp where
  call : Ptr → Ptr → M I32

/-- C function `strncasecmp`. -/
class Ext.strncasecmp where
  call : Ptr → Ptr → U64 → M I32

/-- C function `strncpy`. -/
class Ext.strncpy where
  call : Ptr → Ptr → U64 → M Ptr

/-- C function `strtod`. -/
class Ext.strtod where
  call : Ptr → Ptr → M F64

/-- C function `strtoll`. -/
class Ext.strtoll where
  call : Ptr → Ptr → I32 → M I64

/-- C function `ta_asprintf`. -/
class Ext.ta_asprintf where
  call : Ptr → Ptr → List VArg → M Ptr

/-- C function `ta_talloc_strdup_append_buffer`. -/
class Ext.ta_talloc_strdup_append_buffer where
  call : Ptr → Ptr → M Ptr

/-- C function `ta_talloc_strndup_append_buffer`. -/
class Ext.ta_talloc_strndup_append_buffer where
  call : Ptr → Ptr → U64 → M Ptr

/-- C function `unlink`. -/
class Ext.unlink where
  call : Ptr → M I32

/-- C function `vsnprintf`. -/
class Ext.vsnprintf where
  call : Ptr → U64 → Ptr → Ptr → M I32

/-- C function `vsscanf`. -/
class Ext.vsscanf where
  call : Ptr → Ptr → Ptr → M I32

/-- C function `write`. -/
class Ext.write where
  call : I32 → Ptr → U64 → M I64

end Misc
