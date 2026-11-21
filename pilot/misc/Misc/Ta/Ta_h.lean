import Achates
import Misc.Statics
import Misc.Externals

/-! Emitted by Achates from C; do not edit. -/

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Achates

namespace Misc.Ta.Ta_h

/-- C function `ta_oom_p`, ../.mpv/ta/ta.h:161.
-/
def ta_oom_p (fuel : Nat) (p : Ptr) : M Ptr := do
  let mut p_v : Ptr := p
  if (!(p_v != Ptr.null)) then
    Libc.abort
  return p_v

/-- C function `ta_oom_s`, ../.mpv/ta/ta.h:174.
-/
def ta_oom_s (fuel : Nat) (s : Ptr) : M Ptr := do
  let mut s_v : Ptr := s
  if (!(s_v != Ptr.null)) then
    Libc.abort
  return s_v

end Misc.Ta.Ta_h
