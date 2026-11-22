import Equiv.Mem
import Equiv.Simp
/-!
Tier 2, C side: the runtime's models of the C library over memory that
corresponds to Rust slices.
-/
open Achates
namespace Equiv


theorem length_lt (s : Aeneas.Std.Slice Aeneas.Std.U8) : s.length < 2 ^ 64 := by
  have h := s.property
  rw [Aeneas.Std.Usize.max_def, Aeneas.Std.Usize.numBits_def] at h
  rcases System.Platform.numBits_eq with h' | h' <;>
    simp only [Aeneas.Std.UScalarTy.numBits, h'] at h <;> simp <;> omega


theorem run_loadByte {m : Mem} {b : Nat} {off : Int} {blk : Block} {x : UInt8}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (h0 : 0 ≤ off)
    (hn : off + 1 ≤ blk.data.size) (hx : blk.data[off.toNat]? = some (.byte x)) :
    (Mem.loadByte (.obj b off)).run m = .ok (x, m) := by
  unfold Mem.loadByte
  simp only [StateT.run, bind, StateT.bind]
  have := run_loadBytes (al := 1) hb hl h0 hn (by simp)
  simp only [StateT.run] at this
  rw [this]
  simp only [Except.bind]
  have : (blk.data.extract off.toNat (off.toNat + 1))[0]? = some (MByte.byte x) := by
    rw [Array.getElem?_extract]; simp only [Nat.add_zero]
    rw [if_pos (by have := (Array.getElem?_eq_some_iff.mp hx).1; omega)]; exact hx
  simp only [this]
  rfl

/-- The C model's `bytesAt` over a region gives the region's bytes. -/
theorem run_bytesAt {m : Mem} {p : Ptr} {bs : List Aeneas.Std.U8} (h : Region m p bs)
    (n : Nat) (hn : n ≤ bs.length) :
    (Libc.bytesAt p n).run m = .ok ((bs.take n).map toU8, m) := by
  obtain ⟨b, off, blk, rfl, hb, hl, h0, hsz, hd⟩ := h
  unfold Libc.bytesAt
  suffices ∀ (l : List Nat), (∀ i ∈ l, i < bs.length) →
      (l.mapM fun (i : Nat) => do Mem.loadByte (← (Ptr.obj b off).add 1 i)).run m =
        .ok (l.map fun i => toU8 (bs[i]!), m) by
    rw [this (List.range n) (by intro i hi; simp at hi; omega)]
    congr 2
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_take]
      rw [getElem!_pos bs i (by simp at h1; omega)]
  intro l hl'
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hi := hl' i (by simp)
    simp only [List.mapM_cons, StateT.run_bind]
    have hadd := run_add (off := off) (es := 1) (i := (i : Int)) hb hl (by push_cast; omega) (by push_cast; omega)
    rw [hadd]
    simp only [Equiv.except_bind_ok]
    have hx := hd i hi
    have ht : (off + (i : Int) * ((1 : Nat) : Int)).toNat = off.toNat + i := by push_cast; omega
    rw [run_loadByte (off := off + (i : Int) * ((1 : Nat) : Int)) hb hl (by push_cast; omega) (by push_cast; omega) (by rw [ht]; exact hx)]
    simp only [Equiv.except_bind_ok]
    rw [ih (fun j hj => hl' j (by simp [hj]))]
    simp only [Equiv.except_bind_ok, List.map_cons, getElem!_pos bs i hi]
    rfl

theorem run_checkRange {m : Mem} {p : Ptr} {bs : List Aeneas.Std.U8} (h : Region m p bs)
    (what : String) (n : Nat) (hn : n ≤ bs.length) :
    (Libc.checkRange what p n).run m = .ok ((), m) := by
  obtain ⟨b, off, blk, rfl, hb, hl, h0, hsz, hd⟩ := h
  unfold Libc.checkRange
  simp only [StateT.run_bind]
  have hnull : ((Ptr.obj b off == Ptr.null) = true) = False := by simp
  simp only [hnull, ite_false, StateT.run_pure, Equiv.except_bind_ok]
  simp only [discard, Functor.mapConst, Function.comp, StateT.run, StateT.map]
  have := run_loadBytes (al := 1) hb hl h0 (show off + (n : Int) ≤ blk.data.size by omega) (by simp)
  simp only [StateT.run] at this
  rw [this]
  rfl

/-- The C model's `memcmp` over two regions of at least `n` bytes. -/
theorem run_memcmp {m : Mem} {p q : Ptr} {a b : List Aeneas.Std.U8} (ha : Region m p a)
    (hb : Region m q b) (n : Nat) (hna : n ≤ a.length) (hnb : n ≤ b.length) (hn : n < 2 ^ 64) :
    (Libc.memcmp p q (UInt.ofNat 64 n)).run m =
      .ok (Libc.firstDiff ((a.take n).map toU8) ((b.take n).map toU8), m) := by
  have hn' : (UInt.ofNat 64 n).toNat = n := by
    simp only [UInt.toNat, UInt.ofNat, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  unfold Libc.memcmp
  simp only [StateT.run_bind, hn', run_checkRange ha _ n hna, run_checkRange hb _ n hnb,
    Equiv.except_bind_ok, run_bytesAt ha n hna, run_bytesAt hb n hnb, StateT.run_pure]
  rfl

theorem uofNat_bne_zero (n : Nat) : (UInt.ofNat 64 n != 0) = !decide (n % 2 ^ 64 = 0) := by
  simp only [Equiv.c_ubne, Equiv.c_uofNat, Equiv.c_ulit]
  congr 1

theorem bv_eq_toNat {w : Nat} (x y : BitVec w) : (x = y) = (x.toNat = y.toNat) := by
  apply propext; exact BitVec.toNat_inj.symm

theorem len_bv (s : Aeneas.Std.Slice Aeneas.Std.U8) : (Aeneas.Std.Slice.len s).bv.toNat = s.length :=
  Aeneas.Std.Slice.len_val s

attribute [equiv_nat] Aeneas.Std.Slice.length len_bv decide_eq_false_iff_not uofNat_bne_zero Equiv.c_ugt Equiv.c_ult Equiv.c_uge Equiv.c_ule Equiv.c_ueq
  Equiv.c_ubeq Equiv.c_uofNat Equiv.r_ugt Equiv.r_ult Equiv.r_uge Equiv.r_ule Equiv.r_ueq
  BitVec.lt_def BitVec.le_def BitVec.toNat_ofNat bv_eq_toNat decide_eq_true_eq
  Bool.not_eq_true' bne_iff_ne ne_eq Nat.reducePow decide_not Bool.not_eq_eq_eq_not Bool.not_true
  Bool.not_false Bool.false_eq_true Bool.true_eq_false not_false_eq_true not_true_eq_false
  Aeneas.Std.Slice.len_val Equiv.r_uval Equiv.c_sbne Equiv.c_sbeq Equiv.c_slit Equiv.c_seq
  Equiv.r_ieq Equiv.i32 decide_true decide_false Bool.not_true Bool.not_false
  Aeneas.Std.IScalar.ofInt Aeneas.Std.IScalar.ofIntCore BitVec.ofFin_eq_ofNat Int.reduceMod Int.reduceToNat
  Nat.reduceMod Aeneas.Std.IScalarTy.numBits Aeneas.Std.UScalarTy.numBits

end Equiv
