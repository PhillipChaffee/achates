import Achates
/-!
Executable models of functions the emitted code takes as parameters, for the
differential check only (`achates check`). They are not part of the runtime
and no emitted definition refers to them: the check supplies them as
instances of the `Ext` classes, and its agreement with compiled C is
evidence about the emitted definition and the model together.

Each model states the function it stands for and where its behaviour is
fixed.
-/
namespace AchatesCheck.Models

open Achates

/-- ASCII lower case, as `tolower` in the "C" locale. -/
def lower (b : UInt8) : UInt8 := if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b + 32 else b

/-- POSIX `strncasecmp` in the "C" locale, which mpv never leaves for
`LC_CTYPE`. POSIX fixes the sign only; glibc returns the difference of the
lower-cased bytes, and the model does the same. -/
def strncasecmp (a b : Ptr) (n : U64) : M I32 := do
  let rec go : Nat → Nat → M I32
    | 0, _ => pure 0
    | k + 1, i => do
      let x := lower (← Mem.loadByte (← a.add 1 i))
      let y := lower (← Mem.loadByte (← b.add 1 i))
      if x != y then pure (SInt.ofInt 32 ((x.toNat : Int) - y.toNat))
      else if x = 0 then pure 0
      else go k (i + 1)
  if n.toNat > 0 ∧ (a == .null ∨ b == .null) then ub "strncasecmp with a null pointer"
  go n.toNat 0

/-- POSIX `strcasecmp` in the "C" locale; the result is as for `strncasecmp`. -/
def strcasecmp (a b : Ptr) : M I32 := do
  let x := (← Libc.cstr a).map lower ++ [0]
  let y := (← Libc.cstr b).map lower ++ [0]
  pure (Libc.firstDiff x y)

/-- GNU `memrchr`: the last of the first `n` bytes of `s` equal to `c`. All
`n` bytes must be readable. -/
def memrchr (s : Ptr) (c : I32) (n : U64) : M Ptr := do
  if s == .null then ub "memrchr with a null pointer"
  let c := UInt8.ofNat (SInt.toU 8 c).toNat
  let bs ← Libc.bytesAt s n.toNat
  let rec last : List UInt8 → Nat → Option Nat → Option Nat
    | [], _, found => found
    | b :: rest, i, found => last rest (i + 1) (if b = c then some i else found)
  match last bs 0 none with
  | some i => s.add 1 i
  | none => pure .null

/-- mpv's `mp_log2` (`common/common.c`): the position of the highest set
bit, and 0 for 0. -/
def mp_log2 (v : U32) : M U32 := pure (UInt.ofNat 32 v.toNat.log2)

/-- mpv's `mp_round_next_power_of_2` (`common/common.c`): `v` if it is a
power of two, 1 for 0, the next power of two otherwise, and 0 when that is
2^32. -/
def mp_round_next_power_of_2 (v : U32) : M U32 :=
  let n := v.toNat
  if n = 0 then pure 1
  else if 2 ^ n.log2 = n then pure v
  else pure (UInt.ofNat 32 (2 ^ (n.log2 + 1)))

/-- The value of a digit character in bases up to 36. -/
def digit (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 122 then some (n - 87)
  else if 65 ≤ n ∧ n ≤ 90 then some (n - 55)
  else none

def isSpace (b : UInt8) : Bool := b.toNat = 32 ∨ (9 ≤ b.toNat ∧ b.toNat ≤ 13)

/-- The digits of `bs` valid in `base`: their value and how many there are. -/
def digits (base : Nat) : List UInt8 → Nat → Nat → Nat × Nat
  | [], acc, n => (acc, n)
  | b :: rest, acc, n =>
    match digit b with
    | some d => if d < base then digits base rest (acc * base + d) (n + 1) else (acc, n)
    | none => (acc, n)

/-- `strtoll` on the bytes of a string: the value and the number of bytes
consumed. `binary` says whether a `0b` prefix is accepted for base 0 and 2:
C23 says yes, C17 and earlier say no. -/
def strtollBytes (binary : Bool) (bs : List UInt8) (base : Nat) : Int × Nat :=
  let ws := (bs.takeWhile isSpace).length
  let s := bs.drop ws
  let (neg, sign) := match s with
    | 45 :: _ => (true, 1)
    | 43 :: _ => (false, 1)
    | _ => (false, 0)
  let s := s.drop sign
  let isX (c : UInt8) := c = 120 ∨ c = 88
  let isB (c : UInt8) := c = 98 ∨ c = 66
  let valid (b : Nat) (c : Option UInt8) : Bool :=
    match c.bind digit with
    | some d => d < b
    | none => false
  -- A prefix counts only when a digit of the base follows it; otherwise the
  -- subject sequence is the "0" alone.
  let (base, pre) := match s with
    | 48 :: c :: rest =>
      if isX c ∧ (base = 0 ∨ base = 16) ∧ valid 16 rest.head? then (16, 2)
      else if binary ∧ isB c ∧ (base = 0 ∨ base = 2) ∧ valid 2 rest.head? then (2, 2)
      else if base = 0 then (8, 0)
      else (base, 0)
    | 48 :: _ => (if base = 0 then 8 else base, 0)
    | _ => (if base = 0 then 10 else base, 0)
  let (v, n) := digits base (s.drop pre) 0 0
  if n = 0 then (0, 0)
  else
    let v : Int := if neg then -(v : Int) else v
    let v := if v > 2 ^ 63 - 1 then 2 ^ 63 - 1 else if v < -(2 ^ 63 : Int) then -(2 ^ 63 : Int) else v
    (v, ws + sign + pre + n)

def strtollWith (binary : Bool) (s endp : Ptr) (base : I32) : M I64 := do
  let b := base.toInt
  -- An unsupported base makes glibc return 0 with EINVAL and leave `*endp`
  -- alone; C says nothing about it, so the model does not either.
  if b < 0 ∨ b = 1 ∨ b > 36 then unsupported s!"strtoll with base {b}"
  let bs ← Libc.cstr s
  let (v, n) := strtollBytes binary bs b.toNat
  if endp != .null then Mem.store endp (← s.add 1 n)
  pure (SInt.ofInt 64 v)

/-- What the compiled C calls when the source says `strtoll`: glibc 2.38 and
later, under `_GNU_SOURCE` or C23, redirect it to `__isoc23_strtoll`, which
accepts a `0b` prefix. `errno` is not modelled. -/
def strtoll (s endp : Ptr) (base : I32) : M I64 := strtollWith true s endp base

/-- `strtoll` as C17 and earlier define it, without the `0b` prefix. Kept to
show that the check tells the two apart. -/
def strtollC17 (s endp : Ptr) (base : I32) : M I64 := strtollWith false s endp base

end AchatesCheck.Models
