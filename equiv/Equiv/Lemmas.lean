import Equiv.Tactic
import Equiv.Libc
import Equiv.Port
import Misc
/-!
Tier 2: general lemmas, each proved once, and the tactics that use them.
Also the one precondition that needs the emitted project: the static
objects.
-/
namespace Equiv

/-- `m'` holds every block of `m`, unchanged, and maybe more after them. -/
def Extends (m m' : Achates.Mem) : Prop :=
  m.blocks.size ≤ m'.blocks.size ∧ ∀ i (h : i < m.blocks.size), m'.blocks[i]? = some m.blocks[i]

/-- The memory starts with the static objects (string literals and
file-scope variables) as `Statics.init` leaves them; the emitted code
refers to them by their block numbers. -/
def StaticsReady (m : Achates.Mem) : Prop :=
  ∃ m0, Misc.Statics.init.run {} = .ok ((), m0) ∧ Extends m0 m

end Equiv

open Lean Elab Tactic Meta in
/-- Adds `s.val.length < 2 ^ 64` for every byte slice `s` in the context:
`omega` relates C `size_t` lengths to slice lengths only with it. -/
elab "add_len_bounds" : tactic => do
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``Aeneas.Std.Slice 1 then
      let pf ← mkAppM ``Equiv.length_lt #[d.toExpr]
      liftMetaTactic fun g => do
        let g ← g.assert `h_len (← inferType pf) pf
        let (_, g) ← g.intro1P
        return [g]

macro "frame" : tactic => `(tactic| (intro i hi; simp (disch := first | omega | (simp only [Array.size_push]; omega)) only [Array.getElem?_modify, Equiv.ite_of_not, Option.some.injEq, Array.getElem?_eq_getElem, Array.getElem_push_lt]))

macro "len_omega" : tactic => `(tactic| ((try simp only [Aeneas.Std.Slice.length] at *) <;> omega))

macro "unchanged" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_⟩
  · simp only [Array.size_modify, Array.size_push]; omega
  · intro i hi
    simp (disch := first | omega | (simp only [Array.size_push, Array.size_modify]; omega)) only
      [Array.getElem?_modify, Equiv.ite_of_not, Array.getElem?_push_lt, Array.getElem_push_lt]
  · intro i hi hk
    simp only [Array.size_modify, Array.size_push] at hi
    simp only [Array.getElem_modify]
    split_ifs <;> simp_all [Equiv.kill] <;> omega))

/-- One step of symbolic execution of the C side's memory operations on
the caller's memory extended by the call's locals, or of the Rust side's
library calls, or one case split whose infeasible branch is dropped. -/
macro "sym_step_mem" : tactic => `(tactic| first
    | (rw [Equiv.s_alloca]; on_goal 2 => decide)
    | (rw [Equiv.s_storeBytes]; on_goal 2 => (simp only [equiv_mem, *] <;> omega))
    | (rw [Equiv.s_add]; on_goal 2 => (simp only [equiv_mem, *] <;> omega))
    | (rw [Equiv.s_load]; on_goal 2 => (simp only [equiv_mem, *] <;> omega))
    | (rw [Equiv.write_fresh']; on_goal 2 => assumption)
    | fail_if_no_progress simp only [StateT.run_bind, StateT.run_pure, Equiv.except_bind_ok,
        Array.size_push, equiv_mem, Equiv.run_ite, Equiv.uofNat_bne_zero,
        Aeneas.Std.core.slice.Slice.is_empty, Aeneas.Std.bind_ok, Equiv.result_bind_ok,
        Aeneas.Std.lift, Aeneas.Std.core.cmp.impls.OrdUsize.min, *]
    | (split <;> (rename_i hsplit; try simp only [equiv_nat] at hsplit) <;> try (exfalso; omega)))

/-- One use of the `memcmp` lemmas: the C model's over two regions, the
port's over two slices. -/
macro "sym_step_memcmp" : tactic => `(tactic| first
    | (rw [Equiv.run_memcmp (Equiv.region_frame ?ra ?fa) (Equiv.region_frame ?rb ?fb)]
       case ra => assumption
       case rb => assumption
       case fa => frame
       case fb => frame
       case hna => len_omega
       case hnb => len_omega
       case hn => len_omega)
    | (rw [Equiv.memcmp_ok]
       case hna => (simp only [equiv_nat] at *; omega)
       case hnb => (simp only [equiv_nat] at *; omega)))

/-- Closes the leaves symbolic execution leaves: both sides returned, or
both stopped. -/
macro "leaf_close" : tactic => `(tactic| (
      all_goals simp only [Equiv.agree_ok_ok, Equiv.agree_ok_fail, Equiv.agree_err_ok,
        Equiv.agree_err_fail, Equiv.except_pure, StateT.run_pure, Equiv.except_bind_ok, Equiv.Stop]
      all_goals try refine ⟨?_, ?_⟩
      all_goals try unchanged
      all_goals try simp only [Aeneas.Std.Slice.len_val, Equiv.len_bv, Aeneas.Std.Slice.length,
        Aeneas.Std.UScalar.val] at *
      all_goals try simp only [equiv_unfold]
      all_goals try rfl
      all_goals try bv_omega))

/-- What both tier 2 entries do first: take the representation hypotheses
apart, add the length bounds, take fuel 0 and unfold both sides. -/
macro "tier2_intro" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
      unfold Equiv.IsBstr at *
      casesm* _ ∧ _, ∃ _, _
      add_len_bounds
      simp only [Aeneas.Std.Slice.length, Nat.reducePow] at *
      refine ⟨0, fun _ _ => ?_⟩
      simp only [StateT.run_bind, Equiv.except_bind_ok, Achates.Mem.storeAgg, $xs,*]))

/-- Tier 2, memory lemmas only: the C side's locals and loads through the
`Equiv.Mem` lemmas. Loop-free C only (fuel bound 0). -/
syntax "equiv_tier2_mem" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| equiv_tier2_mem [$xs,*]) => `(tactic| (
      tier2_intro [$xs,*]
      repeat' sym_step_mem
      leaf_close))

/-- Tier 2 with the `memcmp` lemmas as well. -/
syntax "equiv_tier2_memcmp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| equiv_tier2_memcmp [$xs,*]) => `(tactic| (
      tier2_intro [$xs,*]
      repeat' (first | sym_step_memcmp | sym_step_mem)
      leaf_close))
