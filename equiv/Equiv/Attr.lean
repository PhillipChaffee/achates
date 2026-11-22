import Lean
/-! The simp sets of the proof tiers. They are declared apart from their
lemmas because Lean does not allow an attribute to be used in the file that
declares it. -/

/-- Rewrites both sides' primitive operations into `if`s over plain values,
so that `split` sees every branch. -/
register_simp_attr equiv_unfold

/-- Facts about the bit-vector forms `equiv_unfold` leaves, for the
arithmetic closers. -/
register_simp_attr equiv_arith

/-- Evaluates the C side's memory operations on a memory built from the
caller's by pushes and stores, for tier 2. -/
register_simp_attr equiv_mem

/-- Turns comparisons of C `size_t` values and Rust `usize` values made
from lengths into comparisons of the lengths, for `omega`. -/
register_simp_attr equiv_nat
