import Achates.Libc
/-!
A model of mpv's talloc (`ta/ta.c`, `ta/ta_utils.c`) as allocation and
freeing of blocks, with the parent of each allocation kept so that freeing a
parent frees its children.

Not modelled, and reported when reached:
- destructors: `ta_set_destructor` records the function, and freeing an
  allocation that has one fails as unsupported, because the model cannot
  call back into emitted code;
- running out of memory: every allocation below 2^47 bytes succeeds, larger
  ones fail as unsupported.
The leak report and the debugging canaries have no counterpart.
-/
namespace Achates.Talloc

open Achates

/-- The block of a talloc allocation, `none` for a null pointer. talloc finds
its header just below the pointer, so any other pointer is undefined. -/
def block (what : String) (p : Ptr) : M (Option Nat) := do
  match p with
  | .null => pure none
  | .obj b 0 =>
    let some blk := (← get).blocks[b]? | ub s!"{what}: pointer to no object"
    if !blk.live then ub s!"{what}: allocation already freed"
    if blk.kind != .talloc then ub s!"{what}: not a talloc allocation"
    pure (some b)
  | _ => ub s!"{what}: not the start of a talloc allocation"

def setParent (b : Nat) (parent : Option Nat) : M Unit :=
  modify fun m => { m with blocks := m.blocks.modify b fun blk => { blk with parent } }

def ta_set_parent (p parent : Ptr) : M Unit := do
  let some b ← block "ta_set_parent" p | pure ()
  setParent b (← block "ta_set_parent" parent)

def ta_alloc_size (parent : Ptr) (size : U64) : M Ptr := do
  discard <| block "ta_alloc_size" parent
  let p ← Mem.alloc .talloc size.toNat 16 .undef
  ta_set_parent p parent
  pure p

def ta_zalloc_size (parent : Ptr) (size : U64) : M Ptr := do
  discard <| block "ta_zalloc_size" parent
  let p ← Mem.alloc .talloc size.toNat 16 (.byte 0)
  ta_set_parent p parent
  pure p

def ta_new_context (parent : Ptr) : M Ptr := ta_alloc_size parent 0

def ta_steal_ (parent p : Ptr) : M Ptr := do
  ta_set_parent p parent
  pure p

def ta_get_size (p : Ptr) : M U64 := do
  let some b ← block "ta_get_size" p | pure 0
  pure (UInt.ofNat 64 ((← get).blocks[b]?.map (·.data.size) |>.getD 0))

def ta_dbg_set_loc (p _loc : Ptr) : M Ptr := do
  discard <| block "ta_dbg_set_loc" p
  pure p

def ta_set_destructor (p dtor : Ptr) : M Unit := do
  let some b ← block "ta_set_destructor" p | pure ()
  let d := if dtor == .null then none else some dtor
  modify fun m => { m with blocks := m.blocks.modify b fun blk => { blk with dtor := d } }

/-- The live talloc blocks whose chain of parents reaches `root`, `root`
included. Each pass adds one more generation, so as many passes as there are
blocks reach every descendant. -/
def descendants (m : Mem) (root : Nat) : List Nat :=
  let step (acc : List Nat) : List Nat :=
    (List.range m.blocks.size).filter fun i =>
      acc.contains i || (match m.blocks[i]? with
        | some blk => blk.live && blk.kind == .talloc && (match blk.parent with
          | some par => acc.contains par
          | none => false)
        | none => false)
  (List.range m.blocks.size).foldl (fun acc _ => step acc) [root]

def freeBlocks (what : String) (bs : List Nat) : M Unit := do
  let m ← get
  if bs.any fun b => (m.blocks[b]?.bind (·.dtor)).isSome then
    unsupported s!"{what} of an allocation with a destructor"
  Mem.popFrame (bs.map fun b => .obj b 0)

def ta_free (p : Ptr) : M Unit := do
  let some b ← block "ta_free" p | pure ()
  freeBlocks "ta_free" (descendants (← get) b)

def ta_free_children (p : Ptr) : M Unit := do
  let some b ← block "ta_free_children" p | pure ()
  freeBlocks "ta_free_children" ((descendants (← get) b).filter (· != b))

/-- Always moves the allocation to a new block, so every pointer into the
old one becomes dangling, as C says it may. Children, parent and destructor
follow the allocation. -/
def ta_realloc_size (parent p : Ptr) (size : U64) : M Ptr := do
  if size.toNat ≥ 2 ^ 47 then unsupported s!"allocation of {size.toNat} bytes"
  if size.toNat = 0 then
    ta_free p
    return .null
  let some b ← block "ta_realloc_size" p | ta_alloc_size parent size
  let some old := (← get).blocks[b]? | ub "ta_realloc_size: pointer to no object"
  if old.data.size = size.toNat then return p
  let q ← Mem.alloc .talloc size.toNat 16 .undef
  let .obj nb _ := q | ub "ta_realloc_size: allocation failed"
  Mem.storeBytes q (old.data.extract 0 (min old.data.size size.toNat))
  modify fun m => { m with blocks := (m.blocks.modify nb fun blk =>
      { blk with parent := old.parent, dtor := old.dtor }).map fun blk =>
        if blk.parent == some b then { blk with parent := some nb } else blk }
  Mem.popFrame [p]
  pure q

/-- `ta_realloc_size` that aborts when allocation fails, which the model's
allocation never does. -/
def ta_xrealloc_size (parent p : Ptr) (size : U64) : M Ptr := ta_realloc_size parent p size

def ta_calc_array_size (elementSize count : U64) : M U64 := do
  if elementSize.toNat = 0 then ub "division by zero"
  if count.toNat > (2 ^ 64 - 1) / elementSize.toNat then pure (UInt.ofNat 64 (2 ^ 64 - 1))
  else pure (elementSize * count)

def ta_calc_prealloc_elems (nextidx : U64) : M U64 :=
  if nextidx.toNat ≥ (2 ^ 64 - 1) / 2 - 1 then pure (UInt.ofNat 64 (2 ^ 64 - 1))
  else pure ((nextidx + 1) * 2)

end Achates.Talloc
