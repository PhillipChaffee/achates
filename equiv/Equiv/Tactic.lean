import Equiv.Simp
/-!
The fixed tactic scripts of the proof tiers. The generator writes one of
these as the proof of every theorem, with the names of the definitions to
unfold; nothing here is specific to one function.
-/

/-- Tier 0: unfold both sides and simplify, with no case split; then one
call of each decision procedure. Loop-free functions only: the fuel bound
is taken to be 0. -/
syntax "equiv_tier0" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| equiv_tier0 [$xs,*]) => `(tactic| (
      refine ⟨0, fun _ _ => ?_⟩
      try simp only [equiv_unfold, Equiv.unchanged_refl, and_true, true_and, $xs,*]
      all_goals try first | rfl | bv_omega | omega))

/-- Tier 1: as tier 0, then split every `if` on either side, dropping each
branch whose path condition `bv_omega` refutes, and close each leaf with
`bv_omega` or `omega`. Not `bv_decide`: it checks its certificate by compiled
code, which adds an axiom the kernel does not check. -/
syntax "equiv_tier1" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| equiv_tier1 [$xs,*]) => `(tactic| (
      refine ⟨0, fun _ _ => ?_⟩
      simp only [equiv_unfold, $xs,*]
      repeat' (first
        | (split <;> try (exfalso; bv_omega))
        | (simp only [equiv_unfold, $xs,*] at ⊢; done)
        | (fail_if_no_progress simp only [equiv_unfold, $xs,*]))
      all_goals try simp only [equiv_unfold, Equiv.unchanged_refl, and_true, true_and]
      all_goals try first | rfl | bv_omega | omega))
