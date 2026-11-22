import Achates
import Aeneas
/-!
How a C function emitted by Achates and a Rust function translated by
Aeneas are said to be equal.

The two sides do not share a single type: C runs in `Achates.M`, a state
monad over block memory with failure, and takes pointers and aggregates;
Rust runs in `Aeneas.Std.Result` and takes values. Each definition below
is one rule of the correspondence, and `Agree` puts them together into
the statement every generated theorem has.

Neither namespace is opened: both define `U8`, `I32`, `Slice`-like names
and `Result`-like monads, and an unqualified name would pick one silently.
-/
namespace Equiv

/-! ## Integers

C and Aeneas integers are both a `BitVec` of the type's width. A value
corresponds to the one with the same bits; for a C `char` (signed here)
and a Rust `u8`, that is the same byte. -/

def u8 (x : Achates.U8) : Aeneas.Std.U8 := ⟨x.bv⟩
def u16 (x : Achates.U16) : Aeneas.Std.U16 := ⟨x.bv⟩
def u32 (x : Achates.U32) : Aeneas.Std.U32 := ⟨x.bv⟩
def u64 (x : Achates.U64) : Aeneas.Std.U64 := ⟨x.bv⟩
def i8 (x : Achates.I8) : Aeneas.Std.I8 := ⟨x.bv⟩
def i16 (x : Achates.I16) : Aeneas.Std.I16 := ⟨x.bv⟩
def i32 (x : Achates.I32) : Aeneas.Std.I32 := ⟨x.bv⟩
def i64 (x : Achates.I64) : Aeneas.Std.I64 := ⟨x.bv⟩
/-- A C `char` passed where the port takes a byte. -/
def charU8 (x : Achates.I8) : Aeneas.Std.U8 := ⟨x.bv⟩

/-- A C truth value (`int` 0 or 1) where the port returns `bool`. The C
result must be exactly 0 or 1, not merely nonzero. -/
def ofBool (b : Bool) : Achates.I32 := Achates.SInt.ofBool 32 b

/-! ## Outcomes

C stops in one of five ways (`Achates.Err`); Rust in three (`ok`, `fail`,
`div`). The correspondence:

* C returns a value ↔ Rust returns `ok`, and the values correspond.
* C stops with undefined behaviour, a failed `assert` or `abort` ↔ Rust
  fails (`fail e`, any `e`: overflow, out of bounds, `assert!`, panic).
  The two are not matched by kind: C's undefined behaviour is not a
  defined result, and the port turns each case into a panic.
* C runs out of fuel: excluded, by taking enough fuel (see `Equal`).
* C reaches `unsupported`: never allowed. The model does not know what
  the C does there, so no claim about it can be made.
* Rust diverges (`div`): never allowed.
-/

/-- The C stops that a Rust failure stands for. -/
def Stop : Achates.Err → Prop
  | .ub _ => True
  | .assertFail .. => True
  | .abort => True
  | .unsupported _ => False
  | .outOfFuel => False

/-- The outcome `c` of a C call and the result `r` of the Rust call agree,
with `R` relating a C result and the memory after the call to a Rust
result. -/
def Agree {α β : Type} (R : α → Achates.Mem → β → Prop)
    (c : Except Achates.Err (α × Achates.Mem)) (r : Aeneas.Std.Result β) : Prop :=
  (∃ a m', c = .ok (a, m') ∧ ∃ b, r = .ok b ∧ R a m' b) ∨
  (∃ e, c = .error e ∧ Stop e ∧ ∃ f, r = .fail f)

/-- With enough fuel the C call `c fuel`, run from memory `m`, agrees
with `r`. The bound may depend on the arguments; every fuel above it must
give the same agreement, so a result that only appears for some fuels
does not count. -/
def Equal {α β : Type} (R : α → Achates.Mem → β → Prop) (c : Nat → Achates.M α)
    (m : Achates.Mem) (r : Aeneas.Std.Result β) : Prop :=
  ∃ n, ∀ fuel, n ≤ fuel → Agree R ((c fuel).run m) r

/-! ## Memory

What C does to memory that Rust cannot see must be nothing: the blocks
that existed before the call are unchanged, and every block the call
allocated is dead again (its locals were freed, and it allocated nothing
it kept). -/

/-- `m'` is `m` plus blocks that are no longer live. -/
def Unchanged (m m' : Achates.Mem) : Prop :=
  m.blocks.size ≤ m'.blocks.size ∧
  (∀ i (h : i < m.blocks.size), m'.blocks[i]? = some m.blocks[i]) ∧
  (∀ i (h : i < m'.blocks.size), m.blocks.size ≤ i → m'.blocks[i].live = false)

/-- A Rust byte as the C model's byte. -/
def toU8 (x : Aeneas.Std.U8) : UInt8 := UInt8.ofBitVec x.bv

/-- A Rust byte as a byte of C memory. -/
def byte (x : Aeneas.Std.U8) : Achates.MByte := .byte (toU8 x)

/-- In `m`, the `bs.length` bytes at `p` are live, readable and equal
`bs`. `p` is an object pointer even when `bs` is empty. -/
def Region (m : Achates.Mem) (p : Achates.Ptr) (bs : List Aeneas.Std.U8) : Prop :=
  ∃ b off blk, p = .obj b off ∧ m.blocks[b]? = some blk ∧ blk.live = true ∧
    0 ≤ off ∧ off + bs.length ≤ blk.data.size ∧
    ∀ i (h : i < bs.length), blk.data[off.toNat + i]? = some (byte bs[i])

/-- In `m`, the `bstr` value `v` (a `struct bstr { unsigned char *start;
size_t len; }`, 16 bytes with no padding) is a view of the bytes of `s`:
its members, read as the C model reads them, are a pointer `p` and the
length of `s`, and `Region m p s` holds.

Excludes a `bstr` whose `start` is NULL, which `Region` does: in the C
model, `start + 0` on NULL is undefined (C17), so the C functions that
compute `start + i` stop there while the port returns the empty slice. -/
def IsBstr (m : Achates.Mem) (v : Achates.Agg) (s : Aeneas.Std.Slice Aeneas.Std.U8) : Prop :=
  v.bytes.size = 16 ∧ ∃ p, Achates.Agg.get Achates.Ptr v 0 = .ok p ∧
    Achates.Agg.get Achates.U64 v 8 = .ok (Achates.UInt.ofNat 64 s.length) ∧ Region m p s.val

/-- In `m`, `p` points to the bytes of `s` followed by a NUL byte: the
port's convention for a `const char *`, whose content ends at the first
NUL. `s` may itself hold a NUL; both sides then stop there. -/
def IsCStr (m : Achates.Mem) (p : Achates.Ptr) (s : Aeneas.Std.Slice Aeneas.Std.U8) : Prop :=
  Region m p (s.val ++ [⟨0⟩])

end Equiv
