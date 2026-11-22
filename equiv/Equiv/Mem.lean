import Equiv.Basic
import Equiv.Attr
open Achates
namespace Equiv

theorem run_alloc (kind : BlockKind) (size align : Nat) (fill : MByte) (m : Mem) (h : size < Mem.allocLimit) :
    (Mem.alloc kind size align fill).run m =
      .ok (.obj m.blocks.size 0,
        { m with blocks := m.blocks.push { data := Array.replicate size fill, align, kind } }) := by
  unfold Mem.alloc
  rw [if_neg (Nat.not_le.mpr h)]
  rfl

theorem run_access {m : Mem} {b : Nat} {off : Int} {n al : Nat} {w : Bool} {blk : Block}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (h0 : 0 ≤ off)
    (hn : off + n ≤ blk.data.size) (hro : w = true → blk.readonly = false)
    (hal : al ≤ 1 ∨ (off.toNat % al = 0 ∧ blk.align % al = 0)) :
    (Mem.access (.obj b off) n al w).run m = .ok ((b, off.toNat), m) := by
  unfold Mem.access
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, hb,
    pure, StateT.pure, Except.pure, Except.bind]
  have h1 : ¬ ((!blk.live) = true) := by simp [hl]
  have h2 : ¬ (off < 0 ∨ off + ↑n > ↑blk.data.size) := by omega
  have h3 : ¬ (w = true ∧ blk.readonly = true) := by
    cases w <;> simp_all
  have h4 : ¬ (al > 1 ∧ ((off.toNat % al != 0) = true ∨ (blk.align % al != 0) = true)) := by
    rcases hal with h | ⟨h, h'⟩
    · omega
    · simp [h, h']
  simp only [h1, h2, h3, h4, ite_false]
  rfl

theorem run_loadBytes {m : Mem} {b : Nat} {off : Int} {n al : Nat} {blk : Block}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (h0 : 0 ≤ off)
    (hn : off + n ≤ blk.data.size)
    (hal : al ≤ 1 ∨ (off.toNat % al = 0 ∧ blk.align % al = 0)) :
    (Mem.loadBytes (.obj b off) n al).run m =
      .ok (blk.data.extract off.toNat (off.toNat + n), m) := by
  unfold Mem.loadBytes
  simp only [StateT.run, bind, StateT.bind]
  have := run_access (w := false) hb hl h0 hn (by simp) hal
  simp only [StateT.run] at this
  rw [this]
  simp only [Except.bind, get, getThe, MonadStateOf.get, StateT.get, hb, pure, StateT.pure, Except.pure]

/-- The runtime's byte-wise write, as `Mem.storeBytes` does it. -/
def write (d : Array MByte) (off : Nat) (bs : Array MByte) : Array MByte :=
  (List.range bs.size).foldl (init := d) fun d i => d.setIfInBounds (off + i) (bs[i]?.getD .undef)

theorem run_storeBytes {m : Mem} {b : Nat} {off : Int} {bs : Array MByte} {al : Nat} {blk : Block}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (h0 : 0 ≤ off)
    (hn : off + bs.size ≤ blk.data.size) (hro : blk.readonly = false)
    (hal : al ≤ 1 ∨ (off.toNat % al = 0 ∧ blk.align % al = 0)) :
    (Mem.storeBytes (.obj b off) bs al).run m =
      .ok ((), { m with blocks := m.blocks.modify b fun blk =>
        { blk with data := write blk.data off.toNat bs } }) := by
  unfold Mem.storeBytes
  simp only [StateT.run, bind, StateT.bind]
  have := run_access (w := true) hb hl h0 hn (by simp [hro]) hal
  simp only [StateT.run] at this
  rw [this]
  rfl

theorem write_prefix (x : MByte) (bs : Array MByte) (k : Nat) (hk : k ≤ bs.size) :
    (List.range k).foldl (init := Array.replicate bs.size x)
        (fun d i => d.setIfInBounds (0 + i) (bs[i]?.getD .undef)) =
      Array.ofFn (n := bs.size) fun i => if i.val < k then bs[i] else x := by
  induction k with
  | zero =>
    apply Array.ext
    · simp
    · intro i h1 h2; simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Array.getElem_setIfInBounds,
        Array.getElem_ofFn, Array.size_ofFn]
      rw [Array.getElem_setIfInBounds (by simpa using h2)]
      by_cases hi : k = i
      · subst hi; simp [Array.getElem?_eq_getElem (show k < bs.size by omega)]
      · rw [if_neg hi, Array.getElem_ofFn]
        by_cases h : i < k
        · simp [h, show i < k + 1 by omega]
        · simp [h, show ¬ i < k + 1 by omega]

theorem write_fresh (x : MByte) (bs : Array MByte) :
    write (Array.replicate bs.size x) 0 bs = bs := by
  unfold write
  rw [write_prefix x bs bs.size (Nat.le_refl _)]
  apply Array.ext
  · simp
  · intro i h1 h2; simp

theorem run_load {α : Type} [CVal α] {m : Mem} {b : Nat} {off : Int} {blk : Block} {v : α}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (h0 : 0 ≤ off)
    (hn : off + CVal.size α ≤ blk.data.size)
    (hal : CVal.align α ≤ 1 ∨ (off.toNat % CVal.align α = 0 ∧ blk.align % CVal.align α = 0))
    (hv : CVal.decode (blk.data.extract off.toNat (off.toNat + CVal.size α)) = .ok v) :
    (Mem.load α (.obj b off)).run m = .ok (v, m) := by
  unfold Mem.load
  simp only [StateT.run, bind, StateT.bind]
  have := run_loadBytes hb hl h0 hn hal
  simp only [StateT.run] at this
  rw [this]
  simp only [Except.bind, StateT.run_monadLift, MonadLift.monadLift, liftM, monadLift, hv]
  rfl

theorem run_live {m : Mem} {b : Nat} {off : Int} {blk : Block}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) :
    (Ptr.live (.obj b off)).run m = .ok (some (b, off, blk.data.size), m) := by
  unfold Ptr.live
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
  simp only [pure, Except.pure, Except.bind, hb, hl, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

theorem run_add {m : Mem} {b : Nat} {off : Int} {es : Nat} {i : Int} {blk : Block}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (h0 : 0 ≤ off + i * es)
    (hn : off + i * es ≤ blk.data.size) :
    (Ptr.add (.obj b off) es i).run m = .ok (.obj b (off + i * es), m) := by
  unfold Ptr.add
  simp only [StateT.run, bind, StateT.bind]
  have := run_live (off := off) hb hl
  simp only [StateT.run] at this
  rw [this]
  simp only [Except.bind]
  rw [if_neg (by omega)]
  rfl

/-! ## The same, in the form the simplifier uses

Each lemma's side condition mentions only what its left side does, so
`simp` can discharge it by computing the block the pointer designates. -/

/-- The access `Mem.access (.obj b off) n al w` succeeds in `m`. -/
def AccessOk (m : Mem) (b : Nat) (off : Int) (n al : Nat) (w : Bool) : Prop :=
  match m.blocks[b]? with
  | some blk => blk.live = true ∧ 0 ≤ off ∧ off + n ≤ blk.data.size ∧
    (w = true → blk.readonly = false) ∧ (al ≤ 1 ∨ (off.toNat % al = 0 ∧ blk.align % al = 0))
  | none => False

/-- The block `b` of `m`, or a dead empty one. -/
def blockOf (m : Mem) (b : Nat) : Block := (m.blocks[b]?).getD default

theorem blockOf_eq {m : Mem} {b : Nat} {blk : Block} (h : m.blocks[b]? = some blk) :
    blockOf m b = blk := by simp [blockOf, h]

theorem s_loadBytes {m : Mem} {b : Nat} {off : Int} {n al : Nat} (h : AccessOk m b off n al false) :
    (Mem.loadBytes (.obj b off) n al).run m =
      .ok ((blockOf m b).data.extract off.toNat (off.toNat + n), m) := by
  unfold AccessOk at h
  split at h
  · rename_i blk hb
    obtain ⟨hl, h0, hn, -, hal⟩ := h
    rw [run_loadBytes hb hl h0 hn hal, blockOf_eq hb]
  · exact h.elim

theorem s_storeBytes {m : Mem} {b : Nat} {off : Int} {bs : Array MByte} {al : Nat}
    (h : AccessOk m b off bs.size al true) :
    (Mem.storeBytes (.obj b off) bs al).run m =
      .ok ((), { m with blocks := m.blocks.modify b fun blk =>
        { blk with data := write blk.data off.toNat bs } }) := by
  unfold AccessOk at h
  split at h
  · rename_i blk hb
    obtain ⟨hl, h0, hn, hro, hal⟩ := h
    exact run_storeBytes hb hl h0 hn (hro rfl) hal
  · exact h.elim

theorem s_load {α : Type} [CVal α] {m : Mem} {b : Nat} {off : Int}
    (h : AccessOk m b off (CVal.size α) (CVal.align α) false) :
    (Mem.load α (.obj b off)).run m =
      match CVal.decode (α := α) ((blockOf m b).data.extract off.toNat (off.toNat + CVal.size α)) with
      | .ok v => .ok (v, m)
      | .error e => .error e := by
  unfold Mem.load
  simp only [StateT.run, bind, StateT.bind]
  have := s_loadBytes h
  simp only [StateT.run] at this
  rw [this]
  simp only [Except.bind, StateT.run_monadLift, MonadLift.monadLift, liftM, monadLift]
  split <;> rename_i h' <;> simp only [h'] <;> rfl

/-- `p + i` stays in its object. -/
def AddOk (m : Mem) (b : Nat) (off : Int) (es : Nat) (i : Int) : Prop :=
  match m.blocks[b]? with
  | some blk => blk.live = true ∧ 0 ≤ off + i * es ∧ off + i * es ≤ blk.data.size
  | none => False

theorem s_add {m : Mem} {b : Nat} {off : Int} {es : Nat} {i : Int} (h : AddOk m b off es i) :
    (Ptr.add (.obj b off) es i).run m = .ok (.obj b (off + i * es), m) := by
  unfold AddOk at h
  split at h
  · rename_i blk hb
    obtain ⟨hl, h0, hn⟩ := h
    exact run_add hb hl h0 hn
  · exact h.elim

theorem s_alloca (size align : Nat) (m : Mem) (h : size < Mem.allocLimit) :
    (Mem.alloca size align).run m =
      .ok (.obj m.blocks.size 0,
        { m with blocks := m.blocks.push { data := Array.replicate size .undef, align, kind := .stack } }) :=
  run_alloc _ _ _ _ _ h

theorem write_fresh' (x : MByte) (bs : Array MByte) (n : Nat) (h : bs.size = n) :
    write (Array.replicate n x) 0 bs = bs := by
  subst h; exact write_fresh x bs

/-- A load of `α` at `off` from an aggregate's bytes is the C model's member access. -/
theorem decode_extract (α : Type) [CVal α] (a : Agg) (off : Nat) :
    CVal.decode (α := α) (a.bytes.extract off (off + CVal.size α)) = Agg.get α a off := rfl

theorem eq_self_add (a b : Nat) : (a = a + b) = (b = 0) := by
  apply propext; omega
theorem self_add_eq (a b : Nat) : (a + b = a) = (b = 0) := by
  apply propext; omega

/-- The members of a `struct bstr` value, at the offsets clang gives them. -/
theorem decode_bstr_start (a : Agg) : CVal.decode (α := Ptr) (a.bytes.extract 0 8) = Agg.get Ptr a 0 := rfl
theorem decode_bstr_len (a : Agg) : CVal.decode (α := U64) (a.bytes.extract 8 16) = Agg.get U64 a 8 := rfl

theorem size_uint (w : Nat) : CVal.size (UInt w) = w / 8 := rfl
theorem align_uint (w : Nat) : CVal.align (UInt w) = w / 8 := rfl
theorem size_sint (w : Nat) : CVal.size (SInt w) = w / 8 := rfl
theorem align_sint (w : Nat) : CVal.align (SInt w) = w / 8 := rfl
theorem size_ptr : CVal.size Ptr = 8 := rfl
theorem align_ptr : CVal.align Ptr = 8 := rfl

attribute [equiv_mem] decode_bstr_start decode_bstr_len size_uint align_uint size_sint align_sint size_ptr align_ptr Nat.reduceDiv
  Nat.cast_one Int.mul_one Int.one_mul Nat.cast_zero Int.reduceToNat
attribute [equiv_mem] s_loadBytes s_storeBytes s_load s_add s_alloca write_fresh' decode_extract
  AccessOk AddOk blockOf Array.getElem?_push Array.size_push Array.getElem?_modify Array.size_modify
  Array.size_replicate Option.some.injEq exists_eq_left' eq_self_add self_add_eq Nat.add_left_cancel_iff
  Nat.reduceEqDiff Int.reduceLE Int.reduceAdd Int.reduceMul Int.reduceLT Nat.cast_ofNat Int.toNat_zero
  Nat.reduceMod Nat.reduceAdd Nat.reduceLeDiff and_true true_and le_refl implies_true or_true
  true_or Option.getD_some Option.map_some Mem.storeAgg ite_true ite_false Int.reduceToNat
  zero_add Nat.cast_ofNat Int.natCast_add

theorem ite_of_not {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : ite c a b = b := by
  simp [h]

/-- What a call does to the blocks after the caller's does not change a
region in the caller's. -/
theorem region_frame {m m' : Mem} {p : Ptr} {bs : List Aeneas.Std.U8} (h : Region m p bs)
    (hf : ∀ i, i < m.blocks.size → m'.blocks[i]? = m.blocks[i]?) : Region m' p bs := by
  obtain ⟨b, off, blk, rfl, hb, hl, h0, hsz, hd⟩ := h
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  exact ⟨b, off, blk, rfl, by rw [hf b hlt, hb], hl, h0, hsz, hd⟩

/-- Ends the lifetime of the block `b` holds, as `Mem.popFrame` does. -/
def kill (blk : Block) : Block := { blk with live := false, data := #[] }

theorem s_popFrame (ps : List Ptr) (m : Mem) :
    (Mem.popFrame ps).run m =
      .ok ((), { m with blocks := ps.foldl (init := m.blocks) fun bs p =>
        match p with
        | .obj b _ => bs.modify b kill
        | _ => bs }) := rfl

attribute [equiv_mem] s_popFrame List.foldl_cons List.foldl_nil

end Equiv
