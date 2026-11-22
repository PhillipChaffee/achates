import Equiv.Simp
/-!
The fixed tactic scripts of the proof tiers. The generator writes one of
these as the proof of every theorem, with the names of the definitions to
unfold; nothing here is specific to one function.
-/

/-- A kernel-checked closer for bit-vector goals: every bit-vector term
becomes its natural number (`bv_omega`'s rewriting, plus sign extension,
signed comparison and the overflow tests), the `if`s that introduces are
split, and `omega` decides the rest. `bv_decide` would be faster, but it
checks its certificate by compiled code and adds an axiom the kernel does
not check, so no tier uses it. -/
macro "bvk" : tactic => `(tactic| ((try simp only [bitvec_to_nat, BitVec.toNat_signExtend,
    BitVec.sle_iff_toInt_le, BitVec.slt_iff_toInt_lt, BitVec.toInt_eq_toNat_cond,
    BitVec.saddOverflow, BitVec.ssubOverflow, BitVec.uaddOverflow, BitVec.usubOverflow,
    BitVec.smulOverflow, BitVec.umulOverflow, Bool.or_eq_true, decide_eq_true_eq,
    BitVec.msb_eq_decide] at *) <;> (try split_ifs at *) <;> omega))

/-- Tier 0: unfold both sides and simplify, with no case split; then one
call of each decision procedure. Loop-free functions only: the fuel bound
is taken to be 0. -/
syntax "equiv_tier0" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| equiv_tier0 [$xs,*]) => `(tactic| (
      refine ⟨0, fun _ _ => ?_⟩
      try simp only [equiv_unfold, Equiv.unchanged_refl, and_true, true_and, $xs,*]
      all_goals try first | rfl | (simp_all; done) | bvk))

/-- Tier 1: as tier 0, then split every `if` on either side, dropping each
branch whose path condition `bvk` refutes, and close each leaf with `bvk`. -/
syntax "equiv_tier1" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| equiv_tier1 [$xs,*]) => `(tactic| (
      refine ⟨0, fun _ _ => ?_⟩
      simp only [equiv_unfold, $xs,*]
      repeat' (first
        | (split <;> try (exfalso; first | (simp_all; done) | bvk))
        | (simp only [equiv_unfold, $xs,*] at ⊢; done)
        | (fail_if_no_progress simp only [equiv_unfold, $xs,*]))
      all_goals try simp only [equiv_unfold, Equiv.unchanged_refl, and_true, true_and]
      all_goals try first | rfl | (simp_all; done) | bvk))

open Lean Elab Command in
/-- `equiv_budget n in cmd` elaborates `cmd` with `maxHeartbeats n` and then
logs the heartbeats it used, as `heartbeats used: k` in the units of
`maxHeartbeats`, for the runner's records. Elaboration is synchronous so
that the proof's heartbeats are counted on this thread (as Mathlib's
`#count_heartbeats` does); unlike that command, the limit stays. -/
elab "equiv_budget " n:num " in" ppLine cmd:command : command => do
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option Elab.async false in set_option maxHeartbeats $n in $cmd))
  finally
    logInfo m!"heartbeats used: {((← IO.getNumHeartbeats) - start) / 1000}"
