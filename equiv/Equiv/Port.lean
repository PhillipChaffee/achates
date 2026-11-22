import Equiv.Simp
import MiscRec
/-!
Tier 2, Rust side: facts about the port's own definitions that the
Aeneas library does not give, proved once, and its version of `memcmp`
related to the C model's.
-/
open Aeneas.Std
namespace Equiv


theorem index_ok {α : Type} (v : Slice α) (i : Usize) (h : i.val < v.length) :
    v.index_usize i = .ok (v.val[i.val]'h) := by
  grind [Slice.index_usize]

theorem spec_exists {α : Type} {m : Result α} {p : α → Prop} (h : WP.spec m p) :
    ∃ x, m = .ok x ∧ p x := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis e k => exact ((WP.spec_vis e k).mp h).elim
  | div => exact (WP.spec_div.mp h).elim


theorem toU8_inj {x y : Aeneas.Std.U8} (h : toU8 x = toU8 y) : x = y := by
  have : x.bv = y.bv := congrArg UInt8.toBitVec h
  cases x; cases y; simp_all

theorem byte_sub_no_overflow (x y : BitVec 8) :
    ¬ ((x.setWidth 32).ssubOverflow (y.setWidth 32) = true) := by
  have hx := x.isLt; have hy := y.isLt
  have ex : (x.setWidth 32).toInt = x.toNat := by
    rw [BitVec.toInt_setWidth, Int.bmod_def]; split <;> omega
  have ey : (y.setWidth 32).toInt = y.toNat := by
    rw [BitVec.toInt_setWidth, Int.bmod_def]; split <;> omega
  simp only [BitVec.ssubOverflow, ex, ey, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem ofInt_sub_toNat (x y : BitVec 8) :
    BitVec.ofInt 32 ((x.toNat : Int) - y.toNat) = x.setWidth 32 - y.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := y.isLt
  simp only [BitVec.toNat_ofInt, BitVec.toNat_sub, BitVec.toNat_setWidth]
  omega

theorem succ_ok (i : Usize) (h : i.val + 1 ≤ Usize.max) :
    ∃ j : Usize, (i + 1#usize : Result Usize) = .ok j ∧ j.val = i.val + 1 :=
  spec_exists (UScalar.add_spec (x := i) (y := 1#usize) (by rw [UScalar.max_USize_eq]; simpa using h))

theorem memcmp_loop_ok (a b : Slice U8) (n : Usize) (hna : n.val ≤ a.length) (hnb : n.val ≤ b.length) :
    ∀ k (i : Usize), i.val + k = n.val →
      rmpv_misc.clib.memcmp_loop a b n i =
        .ok (i32 (Achates.Libc.firstDiff (((a.val.drop i.val).take k).map toU8)
          (((b.val.drop i.val).take k).map toU8))) := by
  have ha' : n.val ≤ a.val.length := hna
  have hb' : n.val ≤ b.val.length := hnb
  intro k
  induction k with
  | zero =>
    intro i hi
    rw [rmpv_misc.clib.memcmp_loop.eq_1, if_neg (by simp [r_ult, BitVec.lt_def]; scalar_tac)]
    simp [Achates.Libc.firstDiff]
    rfl
  | succ k ih =>
    intro i hi
    have hlt : i.val < n.val := by omega
    rw [rmpv_misc.clib.memcmp_loop.eq_1, if_pos (by simpa using hlt)]
    rw [index_ok a i (by omega), index_ok b i (by omega)]
    simp only [result_bind_ok, Aeneas.Std.bind_ok]
    have htake_a : (a.val.drop i.val).take (k + 1) = a.val[i.val] :: (a.val.drop (i.val + 1)).take k := by
      rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons]
    have htake_b : (b.val.drop i.val).take (k + 1) = b.val[i.val] :: (b.val.drop (i.val + 1)).take k := by
      rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons]
    rw [htake_a, htake_b]
    simp only [List.map_cons, Achates.Libc.firstDiff]
    by_cases he : a.val[i.val] = b.val[i.val]
    · have he' : toU8 a.val[i.val] = toU8 b.val[i.val] := by rw [he]
      simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false, he', ite_true]
      obtain ⟨j, hj, hjv⟩ := succ_ok i (by
        have := a.property; have := Usize.max_def; scalar_tac)
      rw [hj]
      simp only [result_bind_ok, Aeneas.Std.bind_ok]
      rw [ih j (by omega), hjv]
    · have he' : toU8 a.val[i.val] ≠ toU8 b.val[i.val] := fun h => he (toU8_inj h)
      simp only [bne_iff_ne, ne_eq, he, not_false_eq_true, decide_true, ite_true, he', ite_false,
        lift, result_bind_ok, Aeneas.Std.bind_ok, r_isub]
      generalize a.val[i.val] = x
      generalize b.val[i.val] = y
      have hov : ¬ ((UScalar.hcast IScalarTy.I32 x).bv.ssubOverflow (UScalar.hcast IScalarTy.I32 y).bv = true) := by
        exact byte_sub_no_overflow x.bv y.bv
      rw [if_neg hov]
      simp only [i32, Achates.SInt.ofInt, toU8, UInt8.toNat_ofBitVec]
      congr 2
      rw [ofInt_sub_toNat]
      rfl
/-- The port's `memcmp` from the start, as the callers use it. -/
theorem memcmp_ok (a b : Slice U8) (n : Usize) (hna : n.val ≤ a.length) (hnb : n.val ≤ b.length) :
    rmpv_misc.clib.memcmp_loop a b n 0#usize =
      .ok (i32 (Achates.Libc.firstDiff ((a.val.take n.val).map toU8) ((b.val.take n.val).map toU8))) := by
  have := memcmp_loop_ok a b n hna hnb n.val 0#usize (by simp)
  simpa using this

end Equiv
