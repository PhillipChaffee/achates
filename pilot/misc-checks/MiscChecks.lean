import Misc
/-!
Hand-written checks on the emitted definitions for mpv's `misc/`: that they
run, that they agree with values obtained outside Lean, and that plain Lean
proofs go through on them. The build fails if any check does.
-/
open Achates

namespace MiscChecks

/-- `rotl_u64` has no loop and no call, so its result ignores the fuel. -/
theorem rotl_u64_fuel (f g : Nat) (x : U64) (k : I32) :
    Misc.Misc.Random_c.rotl_u64 f x k = Misc.Misc.Random_c.rotl_u64 g x k := rfl

example : (Misc.Misc.Random_c.rotl_u64 0 1 1).eval = .ok 2 := by rfl

/-- mpv's `rotl_u64(x, 0)` shifts right by 64: undefined behaviour, reported. -/
example : (Misc.Misc.Random_c.rotl_u64 0 1 0).eval
    = .error (.ub "shift by 64 of a 64-bit value") := by rfl

def splitmixOfZero : M U64 := do
  let p ← Mem.alloca 8 8
  Mem.store p (0 : U64)
  Misc.Misc.Random_c.splitmix64 0 p

-- The published first output of splitmix64 for seed 0.
#guard match splitmixOfZero.eval with
  | .ok v => v.toNat == 0xe220a8397b1dcdaf
  | .error _ => false

def names : List String :=
  ["a10", "a9", "A9", "a009", "abc", "abd", "x1y2", "x1y10", "", "0", "file2.mkv",
   "File10.mkv", "1.5", "1.05"]

def cString (s : String) : M Ptr := do
  let p ← Mem.alloc .malloc (s.utf8ByteSize + 1) 1 (.byte 0)
  Mem.storeRaw p (s.toUTF8.toList.map (·.toNat))
  pure p

def naturalSortTable : M (List Int) := do
  Misc.Statics.init
  let ps ← names.mapM cString
  let mut out := []
  for a in ps do
    for b in ps do
      out := out ++ [(← Misc.Misc.Natural_sort_c.mp_natural_sort_cmp 1000 a b).toInt]
  pure out

-- `mp_natural_sort_cmp` on every pair of `names`, as mpv's own
-- `misc/natural_sort.c` compiled by gcc returns it.
#guard match naturalSortTable.eval with
  | .ok l => l == [0, 1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 0, 0, 0, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 0, 0, 0, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 0, 0, 0, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 0, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 0, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 0, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 0, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 0, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, 0, 0]
  | .error _ => false

end MiscChecks
