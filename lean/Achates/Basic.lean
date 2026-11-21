/-!
The monad emitted C code runs in: a memory state plus failure.

Failure is final: no emitted code catches it, so the memory at the point of
failure is not kept.
-/
namespace Achates

/-- Why an execution stopped without a result. -/
inductive Err where
  /-- The C standard gives the execution no meaning from this point. -/
  | ub (reason : String)
  /-- `assert` failed: glibc's `__assert_fail` was called. -/
  | assertFail (expr file : String) (line : Nat) (func : String)
  /-- `abort` was called. -/
  | abort
  /-- The execution is defined C, but reached something the model does not cover. -/
  | unsupported (what : String)
  /-- A loop or a recursion used up the fuel; says nothing about the C. -/
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-- A C pointer value. Object pointers keep their provenance: the block they
were derived from, and an offset in bytes that arithmetic may move only
within that block. -/
inductive Ptr where
  | null
  | obj (block : Nat) (off : Int)
  /-- The address of a function, by its C name. -/
  | fn (name : String)
  /-- A nonzero integer converted to a pointer; it designates no object. -/
  | addr (a : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One byte of memory. -/
inductive MByte where
  /-- Never written: an indeterminate value. -/
  | undef
  | byte (b : UInt8)
  /-- Byte `i` of the representation of a stored pointer. -/
  | frag (p : Ptr) (i : Nat)
  deriving Repr, DecidableEq, Inhabited

inductive BlockKind where
  | static
  | stack
  | malloc
  | talloc
  deriving Repr, DecidableEq, Inhabited

structure Block where
  data : Array MByte
  /-- Alignment of the block's first byte, in bytes. -/
  align : Nat
  live : Bool := true
  /-- A string literal or a `const` object: writing to it is undefined. -/
  readonly : Bool := false
  kind : BlockKind
  /-- talloc parent: freeing the parent frees this block. -/
  parent : Option Nat := none
  /-- talloc destructor, as set by `ta_set_destructor`. -/
  dtor : Option Ptr := none
  deriving Repr, Inhabited

/-- Memory: blocks are never reused, so a pointer to a freed block stays
recognisable as dangling. -/
structure Mem where
  blocks : Array Block := #[]
  deriving Repr, Inhabited

abbrev M := StateT Mem (Except Err)

def ub {α : Type} (reason : String) : M α := throw (.ub reason)
def unsupported {α : Type} (what : String) : M α := throw (.unsupported what)

/-- Runs a computation from an empty memory and drops the final memory. -/
def M.eval {α : Type} (x : M α) : Except Err α := (x.run {}).map (·.1)

/-- The iteration budget of a loop: `for _ in Fuel.mk n do ..` runs the body
until it breaks, and fails with `outOfFuel` if it has not after `n` rounds. -/
structure Fuel where
  n : Nat

def Fuel.loop {β : Type} (body : β → M (ForInStep β)) : Nat → β → M β
  | 0, _ => throw .outOfFuel
  | n + 1, b => do
    match ← body b with
    | .done b => pure b
    | .yield b => Fuel.loop body n b

instance : ForIn M Fuel Unit where
  forIn f init body := Fuel.loop (body ()) f.n init

/-- `for _ in Once.mk do ..` runs the body exactly once; `break` leaves it.
It gives `switch`, `goto` to a later label and `continue` a place to jump to. -/
structure Once where

instance : ForIn M Once Unit where
  forIn _ init body := do
    match ← body () init with
    | .done b => pure b
    | .yield b => pure b

end Achates
