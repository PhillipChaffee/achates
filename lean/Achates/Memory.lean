import Achates.Float
/-!
Memory in the style of CompCert: blocks of bytes addressed by block and
offset, typed access by encoding and decoding for x86-64 (little-endian,
8-bit bytes, 64-bit pointers), with bounds, liveness and alignment checked
on every access.
-/
namespace Achates

/-- How a C scalar type is laid out in memory. -/
class CVal (α : Type) where
  size : Nat
  align : Nat
  encode : α → Array MByte
  decode : Array MByte → Except Err α

def leBytes (n : Nat) (v : Nat) : Array MByte :=
  Array.ofFn (n := n) fun i => .byte (UInt8.ofNat (v >>> (8 * i.val)))

/-- The integer a byte sequence encodes, least significant byte first.
C leaves the value of an uninitialised object indeterminate, and using it
is undefined except through a character type, where it is unspecified;
the second case is reported as unsupported, since no value would be faithful. -/
def leNat (bs : Array MByte) : Except Err Nat :=
  bs.foldrM (init := 0) fun b acc =>
    match b with
    | .byte v => pure (acc * 256 + v.toNat)
    | .undef =>
      if bs.size = 1 then
        throw (.unsupported "read of an uninitialised byte through a character type (unspecified value)")
      else throw (.ub "read of uninitialised memory")
    | .frag _ _ => throw (.unsupported "read of a stored pointer's bytes as an integer")

instance {w : Nat} : CVal (UInt w) where
  size := w / 8
  align := w / 8
  encode a := leBytes (w / 8) a.toNat
  decode bs := do pure (UInt.ofNat w (← leNat bs))

instance {w : Nat} : CVal (SInt w) where
  size := w / 8
  align := w / 8
  encode a := leBytes (w / 8) a.bv.toNat
  decode bs := do pure ⟨BitVec.ofNat w (← leNat bs)⟩

instance : CVal Bool where
  size := 1
  align := 1
  encode b := leBytes 1 (if b then 1 else 0)
  decode bs := do
    match ← leNat bs with
    | 0 => pure false
    | 1 => pure true
    | n => throw (.ub s!"read of a _Bool object holding {n}")

instance : CVal Float where
  size := 8
  align := 8
  encode x := leBytes 8 x.toBits.toNat
  decode bs := do pure (Float.ofBits (UInt64.ofNat (← leNat bs)))

instance : CVal Float32 where
  size := 4
  align := 4
  encode x := leBytes 4 x.toBits.toNat
  decode bs := do pure (Float32.ofBits (UInt32.ofNat (← leNat bs)))

def Ptr.decode (bs : Array MByte) : Except Err Ptr :=
  match (bs[0]? : Option MByte) with
  | some (.frag p 0) =>
    if (List.range 8).all fun i => bs[i]? == some (.frag p i) then pure p
    else throw (.unsupported "read of a pointer assembled from parts of different pointers")
  | some (.frag _ _) =>
    throw (.unsupported "read of a pointer assembled from parts of different pointers")
  | _ => do
    match ← leNat bs with
    | 0 => pure .null
    | n => pure (.addr n)

instance : CVal Ptr where
  size := 8
  align := 8
  -- The null pointer is all-bits-zero on this ABI, so zeroed memory reads back as null.
  encode
    | .null => leBytes 8 0
    | .addr a => leBytes 8 a
    | p => Array.ofFn (n := 8) fun i => .frag p i.val
  decode := Ptr.decode

/-- The value of a struct, union or array: its bytes, as memory holds them.
Members may be uninitialised, which C allows in a copied aggregate. -/
structure Agg where
  bytes : Array MByte
  deriving Repr, Inhabited, DecidableEq

instance : Inhabited Float32 := ⟨Float32.ofBits 0⟩

/-- An argument passed through `...`, after the default argument promotions. -/
inductive VArg where
  | sint {w : Nat} (v : SInt w)
  | uint {w : Nat} (v : UInt w)
  | f64 (v : Float)
  | ptr (p : Ptr)
  | agg (a : Agg)

namespace Mem

/-- The largest allocation the model makes. Whether a real allocator grants
a larger request depends on the machine's memory, which the model does not
know, and the model holds every byte, so a request of this size or more is
`unsupported` rather than assumed to succeed. -/
def allocLimit : Nat := 2 ^ 26

def alloc (kind : BlockKind) (size align : Nat) (fill : MByte) : M Ptr := do
  if size ≥ allocLimit then unsupported s!"allocation of {size} bytes"
  -- The number is read before the push: reading it after would keep the
  -- old array alive across the push, which then copies every block.
  let n := (← get).blocks.size
  modify fun m => { m with blocks := m.blocks.push { data := Array.replicate size fill, align, kind } }
  pure (.obj n 0)

/-- A local variable: uninitialised until stored to. -/
def alloca (size align : Nat) : M Ptr := alloc .stack size align .undef

/-- Ends the lifetime of a function's local variables. -/
def popFrame (ps : List Ptr) : M Unit :=
  modify fun m => { m with blocks := ps.foldl (init := m.blocks) fun bs p =>
    match p with
    | .obj b _ => bs.modify b fun blk => { blk with live := false, data := #[] }
    | _ => bs }

/-- A file-scope object, zero-initialised as C requires. `expect` is the block
number the emitted code refers to it by. -/
def allocStatic (expect size align : Nat) : M Unit := do
  let p ← alloc .static size align (.byte 0)
  if p != .obj expect 0 then unsupported "static objects were not allocated in emitted order"

def setReadonly (b : Nat) : M Unit :=
  modify fun m => { m with blocks := m.blocks.modify b fun blk => { blk with readonly := true } }

/-- The block and offset of an access of `n` bytes at `p`, or the undefined
behaviour the access is. -/
def access (p : Ptr) (n align : Nat) (write : Bool) : M (Nat × Nat) := do
  match p with
  | .null => ub "dereference of a null pointer"
  | .fn name => ub s!"access to memory through the address of function {name}"
  | .addr a => ub s!"dereference of a pointer made from the integer {a}"
  | .obj b off =>
    let some blk := (← get).blocks[b]? | ub "dereference of a pointer to no object"
    if !blk.live then ub "access to an object after its lifetime ended"
    if off < 0 ∨ off + n > blk.data.size then
      ub s!"access of {n} bytes at offset {off} of an object of {blk.data.size} bytes"
    if write ∧ blk.readonly then ub "write to a string literal or a const object"
    if align > 1 ∧ (off.toNat % align != 0 ∨ blk.align % align != 0) then
      ub s!"access at offset {off} of an object aligned to {blk.align} needs alignment {align}"
    pure (b, off.toNat)

def loadBytes (p : Ptr) (n : Nat) (align : Nat := 1) : M (Array MByte) := do
  let (b, off) ← access p n align false
  let some blk := (← get).blocks[b]? | ub "dereference of a pointer to no object"
  pure (blk.data.extract off (off + n))

def storeBytes (p : Ptr) (bs : Array MByte) (align : Nat := 1) : M Unit := do
  let (b, off) ← access p bs.size align true
  modify fun m => { m with blocks := m.blocks.modify b fun blk =>
    { blk with data := (List.range bs.size).foldl (init := blk.data) fun d i =>
        d.setIfInBounds (off + i) (bs[i]?.getD .undef) } }

def load (α : Type) [CVal α] (p : Ptr) : M α := do
  let bs ← loadBytes p (CVal.size α) (CVal.align α)
  CVal.decode bs

def store {α : Type} [CVal α] (p : Ptr) (v : α) : M Unit :=
  storeBytes p (CVal.encode v) (CVal.align α)

def loadAgg (p : Ptr) (size align : Nat) : M Agg := do
  pure ⟨← loadBytes p size align⟩

def storeAgg (p : Ptr) (a : Agg) (align : Nat) : M Unit := storeBytes p a.bytes align

def fill (p : Ptr) (n : Nat) (b : MByte) : M Unit := storeBytes p (Array.replicate n b)

/-- Zero-initialisation: every scalar member becomes zero or null. -/
def zero (p : Ptr) (n : Nat) : M Unit := fill p n (.byte 0)

/-- A declaration without an initialiser is reached: the object's value is
indeterminate again. -/
def undefine (p : Ptr) (n : Nat) : M Unit := fill p n .undef

def storeList {α : Type} [CVal α] (p : Ptr) (vs : List α) : M Unit :=
  storeBytes p (vs.foldl (init := #[]) fun acc v => acc ++ CVal.encode v) (CVal.align α)

/-- Stores plain bytes, as a string literal initialises a character array. -/
def storeRaw (p : Ptr) (bytes : List Nat) : M Unit :=
  storeBytes p (bytes.toArray.map fun b => .byte (UInt8.ofNat b))

/-- A string literal: `bytes` followed by zeros up to `size`, read-only. -/
def allocString (expect : Nat) (bytes : List Nat) (size : Nat) : M Unit := do
  allocStatic expect size 1
  storeRaw (.obj expect 0) bytes
  setReadonly expect

/-- One defined byte, as the `mem*` and `str*` functions read memory. -/
def loadByte (p : Ptr) : M UInt8 := do
  match ((← loadBytes p 1)[0]? : Option MByte) with
  | some (.byte v) => pure v
  | some (.frag _ _) => unsupported "read of a stored pointer's bytes as an integer"
  | _ => unsupported "read of an uninitialised byte through a character type (unspecified value)"

end Mem

namespace Agg

/-- Member access on an aggregate that is a value, such as a function result. -/
def get (α : Type) [CVal α] (a : Agg) (off : Nat) : Except Err α :=
  CVal.decode (a.bytes.extract off (off + CVal.size α))

def sub (a : Agg) (off size : Nat) : Agg := ⟨a.bytes.extract off (off + size)⟩

end Agg

namespace Ptr

/-- The live block a pointer value refers to, with its size. Using the value
of a pointer to an object whose lifetime ended is undefined. -/
def live (p : Ptr) : M (Option (Nat × Int × Nat)) := do
  match p with
  | .obj b off =>
    let some blk := (← get).blocks[b]? | ub "use of a pointer to no object"
    if !blk.live then ub "use of a pointer to an object after its lifetime ended"
    pure (some (b, off, blk.data.size))
  | _ => pure none

/-- `p + i` for elements of `esize` bytes: defined only while the result
stays within the object or one past its end. -/
def add (p : Ptr) (esize : Nat) (i : Int) : M Ptr := do
  match ← p.live with
  | some (b, off, size) =>
    let off' := off + i * esize
    if off' < 0 ∨ off' > size then
      ub s!"pointer arithmetic leaves the object: offset {off'} of {size} bytes"
    pure (.obj b off')
  | none =>
    match p with
    -- Undefined in C17 even for `i = 0`; C2y defines that one case.
    | .null => ub "arithmetic on a null pointer"
    | _ => ub "arithmetic on a pointer that designates no object"

def sub (p : Ptr) (esize : Nat) (i : Int) : M Ptr := add p esize (-i)

/-- `p - q` in elements of `esize` bytes. -/
def diff (p q : Ptr) (esize : Nat) : M I64 := do
  match ← p.live, ← q.live with
  | some (b, o, _), some (b', o', _) =>
    if b != b' then ub "subtraction of pointers into different objects"
    if esize = 0 ∨ (o - o') % esize != 0 then ub "subtraction of misaligned pointers"
    pure (SInt.ofInt 64 ((o - o') / esize))
  | _, _ => ub "subtraction of pointers that designate no object"

def eq (p q : Ptr) : M Bool := do
  match ← p.live, ← q.live with
  | some (b, o, s), some (b', o', s') =>
    if b = b' then pure (o == o')
    -- One past the end of an object may or may not equal the start of another.
    else if o == s ∨ o' == s' then
      unsupported "comparison of a one-past-the-end pointer with a pointer to another object"
    else pure false
  | _, _ => pure (p == q)

def ne (p q : Ptr) : M Bool := do pure !(← eq p q)

def cmp (p q : Ptr) (f : Int → Int → Bool) : M Bool := do
  match ← p.live, ← q.live with
  | some (b, o, _), some (b', o', _) =>
    if b != b' then ub "ordering of pointers into different objects"
    pure (f o o')
  | _, _ => ub "ordering of pointers that designate no object"

def lt (p q : Ptr) : M Bool := cmp p q (· < ·)
def le (p q : Ptr) : M Bool := cmp p q (· ≤ ·)
def gt (p q : Ptr) : M Bool := cmp p q (· > ·)
def ge (p q : Ptr) : M Bool := cmp p q (· ≥ ·)

/-- An integer converted to a pointer: zero is null; anything else designates
no object the model knows. -/
def ofNat (n : Nat) : Ptr := if n = 0 then .null else .addr n

/-- A pointer converted to an integer. The model gives objects no addresses. -/
def toNat (p : Ptr) : M Nat :=
  match p with
  | .null => pure 0
  | .addr a => pure a
  | _ => unsupported "conversion of an object or function address to an integer"

end Ptr

end Achates
