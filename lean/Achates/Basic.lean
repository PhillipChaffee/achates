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
  /-- Byte `i` of a `va_list` object that holds the list numbered `list`
  (see `Mem.vaLists`). C gives these bytes no meaning of their own. -/
  | va (list : Nat) (i : Nat)
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

/-- The C type of an argument passed through `...`, after the default
argument promotions, as far as `va_arg` must match it. -/
inductive VTy where
  /-- An integer type: its signedness, width, and rank by its C name without
  `signed`/`unsigned` (`int`, `long`, `long long`, `__int128`). -/
  | int (signed : Bool) (bits : Nat) (rank : String)
  | double
  /-- A pointer, by the C spelling of the type it points to. -/
  | ptr (pointee : String)
  /-- A struct or union, by its C spelling. -/
  | agg (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- The `...` arguments of one call of a variadic function: each with its
promoted type and its bytes, as memory would hold them. They exist while the
call runs. -/
structure VaArgs where
  args : Array (VTy × Array MByte)
  live : Bool := true
  deriving Repr, Inhabited

/-- One `va_list` value, made by `va_start` or `va_copy`. -/
structure VaState where
  /-- The arguments it walks, as an index into `Mem.vaArgs`. -/
  args : Nat
  /-- How many `va_arg` have read from it. -/
  pos : Nat := 0
  /-- The call of the function that made it, which must end it with `va_end`. -/
  owner : Nat
  ended : Bool := false
  /-- Passed to a function that read from it: its value in the passing
  function is indeterminate, and only `va_end` may be applied (C11 7.16p3). -/
  spent : Bool := false
  deriving Repr, Inhabited

/-- Memory: blocks are never reused, so a pointer to a freed block stays
recognisable as dangling. The variadic argument lists and `va_list` values
live beside the blocks; the bytes of a `va_list` object refer to one of
`vaLists` (`MByte.va`). -/
structure Mem where
  blocks : Array Block := #[]
  vaArgs : Array VaArgs := #[]
  vaLists : Array VaState := #[]
  /-- Calls of functions that use `va_start`, `va_copy` or `va_end` so far. -/
  vaCalls : Nat := 0
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
