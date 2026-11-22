import Equiv.Basic
import Equiv.Attr
/-!
The rewriting tier 1 runs on both sides. Every primitive operation becomes
an `if` whose condition and branches are bit-vector terms: a C signed
overflow check and an Aeneas `tryMk` both become `BitVec.saddOverflow`,
a C `int` comparison and an Aeneas `i32` comparison both become
`BitVec.sle`. After `split`, each branch is a question about fixed-width
bit-vectors, which `bvk` (`Equiv.Tactic`) decides when they are arithmetic.

Each lemma is an unfolding of a runtime or library definition or a fact
about bit-vectors; none mentions a particular mpv function.
-/
namespace Equiv
open Aeneas.Std (UScalar IScalar UScalarTy IScalarTy)

/-! ## Binds over `if`, on both monads

`split` does not look under a binder, so an `if` that is the first step of
a `do` block is lifted out of its bind first. -/

@[equiv_unfold] theorem except_ite_bind {ε α β} (c : Prop) [Decidable c] (x y : Except ε α)
    (f : α → Except ε β) : (ite c x y >>= f) = ite c (x >>= f) (y >>= f) := by
  split <;> rfl

@[equiv_unfold] theorem result_ite_bind {α β} (c : Prop) [Decidable c]
    (x y : Aeneas.Std.Result α) (f : α → Aeneas.Std.Result β) :
    (ite c x y >>= f) = ite c (x >>= f) (y >>= f) := by
  split <;> rfl

@[equiv_unfold] theorem run_ite {α} (c : Prop) [Decidable c] (x y : Achates.M α) (m : Achates.Mem) :
    (ite c x y).run m = ite c (x.run m) (y.run m) := by
  split <;> rfl

@[equiv_unfold] theorem except_map_ite {ε α β} (c : Prop) [Decidable c] (x y : Except ε α)
    (f : α → β) : (f <$> ite c x y) = ite c (f <$> x) (f <$> y) := by
  split <;> rfl

@[equiv_unfold] theorem except_map_ok {ε α β} (a : α) (f : α → β) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl
@[equiv_unfold] theorem except_map_error {ε α β} (e : ε) (f : α → β) :
    (f <$> (Except.error e : Except ε α)) = .error e := rfl

@[equiv_unfold] theorem except_bind_error {ε α β} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl
@[equiv_unfold] theorem except_bind_ok {ε α β} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
@[equiv_unfold] theorem except_pure {ε α} (a : α) : (pure a : Except ε α) = .ok a := rfl
@[equiv_unfold] theorem except_throw {ε α} (e : ε) : (throw e : Except ε α) = .error e := rfl
@[equiv_unfold] theorem result_bind_ok {α β} (a : α) (f : α → Aeneas.Std.Result β) :
    (Aeneas.Std.Result.ok a >>= f) = f a := Aeneas.Std.bind_ok a f
@[equiv_unfold] theorem result_bind_fail {α β} (e) (f : α → Aeneas.Std.Result β) :
    (Aeneas.Std.Result.fail e >>= f) = .fail e := Aeneas.Std.bind_fail e f
@[equiv_unfold] theorem result_pure {α} (a : α) :
    (pure a : Aeneas.Std.Result α) = .ok a := rfl

/-! ## Rust -/

section Rust
variable {ty ty' : UScalarTy} {sty sty' : IScalarTy}

@[equiv_unfold] theorem r_uadd (x y : UScalar ty) :
    (x + y : Aeneas.Std.Result (UScalar ty)) =
      if x.bv.uaddOverflow y.bv then .fail .integerOverflow else .ok ⟨x.bv + y.bv⟩ := by
  change UScalar.add x y = _
  simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds,
    BitVec.uaddOverflow, UScalar.val]
  by_cases h : x.bv.toNat + y.bv.toNat < 2 ^ ty.numBits
  · have h' : ¬ (x.bv.toNat + y.bv.toNat ≥ 2 ^ ty.numBits) := by omega
    simp only [h, h', decide_true, decide_false, ↓reduceDIte, ↓reduceIte,
      Aeneas.Std.Result.ofOption, UScalar.ofNatCore, Bool.false_eq_true]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]; rfl
  · have h' : (x.bv.toNat + y.bv.toNat ≥ 2 ^ ty.numBits) := by omega
    simp only [h, h', decide_true, decide_false, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte,
      Aeneas.Std.Result.ofOption]

@[equiv_unfold] theorem r_usub (x y : UScalar ty) :
    (x - y : Aeneas.Std.Result (UScalar ty)) =
      if x.bv < y.bv then .fail .integerOverflow else .ok ⟨x.bv - y.bv⟩ := by
  change UScalar.sub x y = _
  simp only [UScalar.sub, UScalar.val, BitVec.lt_def]
  split
  · rfl
  · rename_i h
    congr 2
    apply BitVec.eq_of_toNat_eq
    have := x.bv.isLt
    have := y.bv.isLt
    rw [BitVec.toNat_ofNat, BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega)]
    rw [show 2 ^ ty.numBits - y.bv.toNat + x.bv.toNat = (x.bv.toNat - y.bv.toNat) + 2 ^ ty.numBits by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

@[equiv_unfold] theorem r_umul (x y : UScalar ty) :
    (x * y : Aeneas.Std.Result (UScalar ty)) =
      if x.bv.umulOverflow y.bv then .fail .integerOverflow else .ok ⟨x.bv * y.bv⟩ := by
  change UScalar.mul x y = _
  simp only [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds,
    BitVec.umulOverflow, UScalar.val]
  by_cases h : x.bv.toNat * y.bv.toNat < 2 ^ ty.numBits
  · have h' : ¬ (x.bv.toNat * y.bv.toNat ≥ 2 ^ ty.numBits) := by omega
    simp only [h, h', decide_true, decide_false, ↓reduceDIte, ↓reduceIte,
      Aeneas.Std.Result.ofOption, UScalar.ofNatCore, Bool.false_eq_true]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]; rfl
  · have h' : (x.bv.toNat * y.bv.toNat ≥ 2 ^ ty.numBits) := by omega
    simp only [h, h', decide_true, decide_false, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte,
      Aeneas.Std.Result.ofOption]

theorem r_itryMk_ok (x : Int) (h : -2 ^ (sty.numBits - 1) ≤ x ∧ x < 2 ^ (sty.numBits - 1)) :
    IScalar.tryMk sty x = .ok ⟨BitVec.ofInt _ x⟩ := by
  simp only [IScalar.tryMk, IScalar.tryMkOpt, IScalar.check_bounds, h, decide_true,
    ↓reduceDIte, Aeneas.Std.Result.ofOption, IScalar.ofIntCore, and_self]
  congr 2

theorem r_itryMk_fail (x : Int) (h : ¬(-2 ^ (sty.numBits - 1) ≤ x ∧ x < 2 ^ (sty.numBits - 1))) :
    IScalar.tryMk sty x = .fail .integerOverflow := by
  simp only [IScalar.tryMk, IScalar.tryMkOpt, IScalar.check_bounds, h, decide_false,
    ↓reduceIte, ↓reduceDIte, Aeneas.Std.Result.ofOption, Bool.false_eq_true]

@[equiv_unfold] theorem r_iadd (x y : IScalar sty) :
    (x + y : Aeneas.Std.Result (IScalar sty)) =
      if x.bv.saddOverflow y.bv then .fail .integerOverflow else .ok ⟨x.bv + y.bv⟩ := by
  change IScalar.tryMk sty (x.bv.toInt + y.bv.toInt) = _
  by_cases h : x.bv.saddOverflow y.bv
  · rw [if_pos h, r_itryMk_fail]
    simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
    omega
  · rw [if_neg h, r_itryMk_ok, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
    simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
    omega

@[equiv_unfold] theorem r_isub (x y : IScalar sty) :
    (x - y : Aeneas.Std.Result (IScalar sty)) =
      if x.bv.ssubOverflow y.bv then .fail .integerOverflow else .ok ⟨x.bv - y.bv⟩ := by
  change IScalar.tryMk sty (x.bv.toInt - y.bv.toInt) = _
  by_cases h : x.bv.ssubOverflow y.bv
  · rw [if_pos h, r_itryMk_fail]
    simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
    omega
  · rw [if_neg h, r_itryMk_ok, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
      BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.sub_eq_add_neg]
    simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
    omega

@[equiv_unfold] theorem r_imul (x y : IScalar sty) :
    (x * y : Aeneas.Std.Result (IScalar sty)) =
      if x.bv.smulOverflow y.bv then .fail .integerOverflow else .ok ⟨x.bv * y.bv⟩ := by
  change IScalar.tryMk sty (x.bv.toInt * y.bv.toInt) = _
  by_cases h : x.bv.smulOverflow y.bv
  · rw [if_pos h, r_itryMk_fail]
    simp only [BitVec.smulOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
    omega
  · rw [if_neg h, r_itryMk_ok, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
    simp only [BitVec.smulOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
    omega

@[equiv_unfold] theorem r_shl_ui (x : UScalar ty) (s : IScalar sty) :
    (x <<< s : Aeneas.Std.Result (UScalar ty)) = UScalar.shiftLeft_IScalar x s := rfl
@[equiv_unfold] theorem r_shr_ui (x : UScalar ty) (s : IScalar sty) :
    (x >>> s : Aeneas.Std.Result (UScalar ty)) = UScalar.shiftRight_IScalar x s := rfl
@[equiv_unfold] theorem r_shl_uu (x : UScalar ty) (s : UScalar ty') :
    (x <<< s : Aeneas.Std.Result (UScalar ty)) = UScalar.shiftLeft_UScalar x s := rfl
@[equiv_unfold] theorem r_shr_uu (x : UScalar ty) (s : UScalar ty') :
    (x >>> s : Aeneas.Std.Result (UScalar ty)) = UScalar.shiftRight_UScalar x s := rfl
@[equiv_unfold] theorem r_uor (x y : UScalar ty) : (x ||| y) = ⟨x.bv ||| y.bv⟩ := rfl
@[equiv_unfold] theorem r_uand (x y : UScalar ty) : (x &&& y) = ⟨x.bv &&& y.bv⟩ := rfl
@[equiv_unfold] theorem r_uxor (x y : UScalar ty) : (x ^^^ y) = ⟨x.bv ^^^ y.bv⟩ := rfl
@[equiv_unfold] theorem r_ior (x y : IScalar sty) : (x ||| y) = ⟨x.bv ||| y.bv⟩ := rfl
@[equiv_unfold] theorem r_iand (x y : IScalar sty) : (x &&& y) = ⟨x.bv &&& y.bv⟩ := rfl
@[equiv_unfold] theorem r_ixor (x y : IScalar sty) : (x ^^^ y) = ⟨x.bv ^^^ y.bv⟩ := rfl
@[equiv_unfold] theorem r_itoNat (x : IScalar sty) : x.toNat = x.bv.toInt.toNat := rfl

@[equiv_unfold] theorem r_ule (x y : UScalar ty) : (x ≤ y) = (x.bv ≤ y.bv) := rfl
@[equiv_unfold] theorem r_ult (x y : UScalar ty) : (x < y) = (x.bv < y.bv) := rfl
@[equiv_unfold] theorem r_uge (x y : UScalar ty) : (x ≥ y) = (y.bv ≤ x.bv) := rfl
@[equiv_unfold] theorem r_ugt (x y : UScalar ty) : (x > y) = (y.bv < x.bv) := rfl
@[equiv_unfold] theorem r_ile (x y : IScalar sty) : (x ≤ y) = (x.bv.sle y.bv = true) := by
  simp only [BitVec.sle_iff_toInt_le]; rfl
@[equiv_unfold] theorem r_ilt (x y : IScalar sty) : (x < y) = (x.bv.slt y.bv = true) := by
  simp only [BitVec.slt_iff_toInt_lt]; rfl
@[equiv_unfold] theorem r_ige (x y : IScalar sty) : (x ≥ y) = (y.bv.sle x.bv = true) := by
  simp only [BitVec.sle_iff_toInt_le]; rfl
@[equiv_unfold] theorem r_igt (x y : IScalar sty) : (x > y) = (y.bv.slt x.bv = true) := by
  simp only [BitVec.slt_iff_toInt_lt]; rfl
@[equiv_unfold] theorem r_ueq (x y : UScalar ty) : (x = y) = (x.bv = y.bv) := by
  cases x; cases y; simp
@[equiv_unfold] theorem r_ieq (x y : IScalar sty) : (x = y) = (x.bv = y.bv) := by
  cases x; cases y; simp
@[equiv_unfold] theorem r_ubeq (x y : UScalar ty) : (x == y) = decide (x.bv = y.bv) := by
  cases x; cases y; rfl
@[equiv_unfold] theorem r_ibeq (x y : IScalar sty) : (x == y) = decide (x.bv = y.bv) := by
  cases x; cases y; rfl
@[equiv_unfold] theorem r_ubne (x y : UScalar ty) : (x != y) = !decide (x.bv = y.bv) := by
  cases x; cases y; rfl
@[equiv_unfold] theorem r_ibne (x y : IScalar sty) : (x != y) = !decide (x.bv = y.bv) := by
  cases x; cases y; rfl
@[equiv_unfold] theorem r_shl_ii (x : IScalar sty) (s : IScalar sty') :
    (x <<< s : Aeneas.Std.Result (IScalar sty)) = IScalar.shiftLeft_IScalar x s := rfl
@[equiv_unfold] theorem r_shr_ii (x : IScalar sty) (s : IScalar sty') :
    (x >>> s : Aeneas.Std.Result (IScalar sty)) = IScalar.shiftRight_IScalar x s := rfl
@[equiv_unfold] theorem r_shl_iu (x : IScalar sty) (s : UScalar ty) :
    (x <<< s : Aeneas.Std.Result (IScalar sty)) = IScalar.shiftLeft_UScalar x s := rfl
@[equiv_unfold] theorem r_shr_iu (x : IScalar sty) (s : UScalar ty) :
    (x >>> s : Aeneas.Std.Result (IScalar sty)) = IScalar.shiftRight_UScalar x s := rfl
@[equiv_unfold] theorem r_uval (x : UScalar ty) : x.val = x.bv.toNat := rfl
@[equiv_unfold] theorem r_ival (x : IScalar sty) : x.val = x.bv.toInt := rfl

attribute [equiv_unfold] UScalar.shiftLeft_IScalar UScalar.shiftRight_IScalar UScalar.shiftLeft
  UScalar.shiftRight UScalar.shiftLeft_UScalar UScalar.shiftRight_UScalar
  IScalar.shiftLeft_IScalar IScalar.shiftRight_IScalar IScalar.shiftLeft IScalar.shiftRight
  IScalar.shiftLeft_UScalar IScalar.shiftRight_UScalar
  UScalar.hcast UScalar.cast IScalar.hcast IScalar.cast Aeneas.Std.lift
  Aeneas.Std.bind_ok Aeneas.Std.bind_fail UScalarTy.numBits IScalarTy.numBits
  UScalar.ofNat UScalar.ofNatCore IScalar.ofInt IScalar.ofIntCore BitVec.ofFin_eq_ofNat
  u8 u16 u32 u64 i8 i16 i32 i64 charU8 ofBool

end Rust

/-! ## C -/

section C
variable {w : Nat}

@[equiv_unfold] theorem c_sadd (a b : Achates.SInt w) :
    Achates.SInt.add a b =
      if a.bv.saddOverflow b.bv then
        .error (.ub s!"signed overflow in addition: {a.toInt + b.toInt} does not fit in {w} bits")
      else .ok ⟨a.bv + b.bv⟩ := by
  simp only [Achates.SInt.add, Achates.SInt.checked, Achates.SInt.ofInt]
  by_cases h : a.bv.saddOverflow b.bv
  · have h' : ¬ (-(2:Int) ^ (w - 1) ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt < 2 ^ (w - 1)) := by
      simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [Achates.SInt.toInt]; omega
    simp only [h, h', ↓reduceIte]; rfl
  · have h' : (-(2:Int) ^ (w - 1) ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt < 2 ^ (w - 1)) := by
      simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [Achates.SInt.toInt]; omega
    simp only [h, h', ↓reduceIte, Bool.false_eq_true]
    simp only [Achates.SInt.toInt, BitVec.ofInt_add, BitVec.ofInt_toInt]; rfl

@[equiv_unfold] theorem c_ssub (a b : Achates.SInt w) :
    Achates.SInt.sub a b =
      if a.bv.ssubOverflow b.bv then
        .error (.ub s!"signed overflow in subtraction: {a.toInt - b.toInt} does not fit in {w} bits")
      else .ok ⟨a.bv - b.bv⟩ := by
  simp only [Achates.SInt.sub, Achates.SInt.checked, Achates.SInt.ofInt]
  by_cases h : a.bv.ssubOverflow b.bv
  · have h' : ¬ (-(2:Int) ^ (w - 1) ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 2 ^ (w - 1)) := by
      simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [Achates.SInt.toInt]; omega
    simp only [h, h', ↓reduceIte]; rfl
  · have h' : (-(2:Int) ^ (w - 1) ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 2 ^ (w - 1)) := by
      simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [Achates.SInt.toInt]; omega
    simp only [h, h', ↓reduceIte, Bool.false_eq_true]
    simp only [Achates.SInt.toInt, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_toInt, ← BitVec.sub_eq_add_neg]; rfl

@[equiv_unfold] theorem c_smul (a b : Achates.SInt w) :
    Achates.SInt.mul a b =
      if a.bv.smulOverflow b.bv then
        .error (.ub s!"signed overflow in multiplication: {a.toInt * b.toInt} does not fit in {w} bits")
      else .ok ⟨a.bv * b.bv⟩ := by
  simp only [Achates.SInt.mul, Achates.SInt.checked, Achates.SInt.ofInt]
  by_cases h : a.bv.smulOverflow b.bv
  · have h' : ¬ (-(2:Int) ^ (w - 1) ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt < 2 ^ (w - 1)) := by
      simp only [BitVec.smulOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [Achates.SInt.toInt]; omega
    simp only [h, h', ↓reduceIte]; rfl
  · have h' : (-(2:Int) ^ (w - 1) ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt < 2 ^ (w - 1)) := by
      simp only [BitVec.smulOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [Achates.SInt.toInt]; omega
    simp only [h, h', ↓reduceIte, Bool.false_eq_true]
    simp only [Achates.SInt.toInt, BitVec.ofInt_mul, BitVec.ofInt_toInt]; rfl

@[equiv_unfold] theorem c_sle (a b : Achates.SInt w) : (a ≤ b) = (a.bv.sle b.bv = true) := by
  simp only [BitVec.sle_iff_toInt_le]; rfl
@[equiv_unfold] theorem c_slt (a b : Achates.SInt w) : (a < b) = (a.bv.slt b.bv = true) := by
  simp only [BitVec.slt_iff_toInt_lt]; rfl
@[equiv_unfold] theorem c_sge (a b : Achates.SInt w) : (a ≥ b) = (b.bv.sle a.bv = true) := by
  simp only [BitVec.sle_iff_toInt_le]; rfl
@[equiv_unfold] theorem c_sgt (a b : Achates.SInt w) : (a > b) = (b.bv.slt a.bv = true) := by
  simp only [BitVec.slt_iff_toInt_lt]; rfl
@[equiv_unfold] theorem c_ule (a b : Achates.UInt w) : (a ≤ b) = (a.bv ≤ b.bv) := rfl
@[equiv_unfold] theorem c_ult (a b : Achates.UInt w) : (a < b) = (a.bv < b.bv) := rfl
@[equiv_unfold] theorem c_uge (a b : Achates.UInt w) : (a ≥ b) = (b.bv ≤ a.bv) := rfl
@[equiv_unfold] theorem c_ugt (a b : Achates.UInt w) : (a > b) = (b.bv < a.bv) := rfl
@[equiv_unfold] theorem c_seq (a b : Achates.SInt w) : (a = b) = (a.bv = b.bv) := by
  cases a; cases b; simp
@[equiv_unfold] theorem c_ueq (a b : Achates.UInt w) : (a = b) = (a.bv = b.bv) := by
  cases a; cases b; simp
@[equiv_unfold] theorem c_stoS (v : Nat) (a : Achates.SInt w) :
    Achates.SInt.toS v a = ⟨a.bv.signExtend v⟩ := rfl
@[equiv_unfold] theorem c_stoU (v : Nat) (a : Achates.SInt w) :
    Achates.SInt.toU v a = ⟨a.bv.signExtend v⟩ := rfl
@[equiv_unfold] theorem c_utoS (v : Nat) (a : Achates.UInt w) :
    Achates.UInt.toS v a = ⟨a.bv.setWidth v⟩ := rfl
@[equiv_unfold] theorem c_utoU (v : Nat) (a : Achates.UInt w) :
    Achates.UInt.toU v a = ⟨a.bv.setWidth v⟩ := rfl
@[equiv_unfold] theorem c_sofBool (b : Bool) :
    Achates.SInt.ofBool w b = ⟨if b then 1#w else 0#w⟩ := by
  cases b <;> rfl
@[equiv_unfold] theorem c_sofInt (i : Int) : Achates.SInt.ofInt w i = ⟨BitVec.ofInt w i⟩ := rfl
@[equiv_unfold] theorem c_uofNat (n : Nat) : Achates.UInt.ofNat w n = ⟨BitVec.ofNat w n⟩ := rfl
@[equiv_unfold] theorem c_slit (n : Nat) :
    (OfNat.ofNat n : Achates.SInt w) = ⟨BitVec.ofNat w n⟩ := by
  change (⟨BitVec.ofInt w (n : Int)⟩ : Achates.SInt w) = _
  rw [BitVec.ofInt_natCast]
@[equiv_unfold] theorem c_ulit (n : Nat) :
    (OfNat.ofNat n : Achates.UInt w) = ⟨BitVec.ofNat w n⟩ := rfl
@[equiv_unfold] theorem c_uadd (a b : Achates.UInt w) : a + b = ⟨a.bv + b.bv⟩ := rfl
@[equiv_unfold] theorem c_usub (a b : Achates.UInt w) : a - b = ⟨a.bv - b.bv⟩ := rfl
@[equiv_unfold] theorem c_umul (a b : Achates.UInt w) : a * b = ⟨a.bv * b.bv⟩ := rfl
@[equiv_unfold] theorem c_bor (a b : Achates.UInt w) : Achates.UInt.bor a b = ⟨a.bv ||| b.bv⟩ := rfl
@[equiv_unfold] theorem c_band (a b : Achates.UInt w) : Achates.UInt.band a b = ⟨a.bv &&& b.bv⟩ := rfl
@[equiv_unfold] theorem c_bxor (a b : Achates.UInt w) : Achates.UInt.bxor a b = ⟨a.bv ^^^ b.bv⟩ := rfl
@[equiv_unfold] theorem c_sbor (a b : Achates.SInt w) : Achates.SInt.bor a b = ⟨a.bv ||| b.bv⟩ := rfl
@[equiv_unfold] theorem c_sband (a b : Achates.SInt w) : Achates.SInt.band a b = ⟨a.bv &&& b.bv⟩ := rfl
@[equiv_unfold] theorem c_sbxor (a b : Achates.SInt w) : Achates.SInt.bxor a b = ⟨a.bv ^^^ b.bv⟩ := rfl
@[equiv_unfold] theorem c_sbnot (a : Achates.SInt w) : Achates.SInt.bnot a = ⟨~~~a.bv⟩ := rfl
@[equiv_unfold] theorem c_ubnot (a : Achates.UInt w) : Achates.UInt.bnot a = ⟨~~~a.bv⟩ := rfl
@[equiv_unfold] theorem c_sbeq (a b : Achates.SInt w) : (a == b) = decide (a.bv = b.bv) := by
  rw [beq_eq_decide]; simp only [c_seq]
@[equiv_unfold] theorem c_ubeq (a b : Achates.UInt w) : (a == b) = decide (a.bv = b.bv) := by
  rw [beq_eq_decide]; simp only [c_ueq]
@[equiv_unfold] theorem c_sbne (a b : Achates.SInt w) : (a != b) = !decide (a.bv = b.bv) := by
  rw [bne, c_sbeq]
@[equiv_unfold] theorem c_ubne (a b : Achates.UInt w) : (a != b) = !decide (a.bv = b.bv) := by
  rw [bne, c_ubeq]
@[equiv_unfold] theorem c_stoInt (a : Achates.SInt w) : a.toInt = a.bv.toInt := rfl
@[equiv_unfold] theorem c_utoNat (a : Achates.UInt w) : a.toNat = a.bv.toNat := rfl

attribute [equiv_unfold] Achates.UInt.shl Achates.UInt.shr Achates.SInt.shl Achates.SInt.shr
  BitVec.toInt_ofNat BitVec.toNat_ofNat
  StateT.run_monadLift monadLift_self bind_pure_comp StateT.run_bind StateT.run_pure
  StateT.run_map Except.map Int.reduceMod Int.reduceToNat
  Nat.reducePow Int.reducePow Nat.reduceMod Bool.and_eq_true Bool.or_eq_true decide_eq_true_eq
  Bool.not_eq_true' bne_iff_ne beq_iff_eq ne_eq Bool.not_eq_eq_eq_not Bool.not_true Bool.not_false

end C

/-! ## Outcomes -/

@[equiv_unfold] theorem agree_ok_ok {α β} {R : α → Achates.Mem → β → Prop} {a m b} :
    Agree R (.ok (a, m)) (.ok b) ↔ R a m b := by
  simp [Agree]

@[equiv_unfold] theorem agree_ok_fail {α β} {R : α → Achates.Mem → β → Prop} {a m f} :
    Agree R (.ok (a, m)) (.fail f) ↔ False := by
  simp [Agree]

@[equiv_unfold] theorem agree_err_ok {α β} {R : α → Achates.Mem → β → Prop} {e b} :
    Agree R (.error e) (.ok b) ↔ False := by
  simp [Agree]

@[equiv_unfold] theorem agree_err_fail {α β} {R : α → Achates.Mem → β → Prop} {e f} :
    Agree R (.error e) (.fail f : Aeneas.Std.Result β) ↔ Stop e := by
  simp [Agree]

attribute [equiv_unfold] Stop

theorem unchanged_refl (m : Achates.Mem) : Unchanged m m :=
  ⟨Nat.le_refl _, fun i h => by simp [h], fun i h h' => absurd h (by omega)⟩

end Equiv
