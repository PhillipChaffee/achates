import AchatesCheck.Printf
/-!
A model of `vsscanf` (C11 7.21.6.2, 7.21.6.12) for the differential check,
in the "C" locale, for the integer conversions and text.

Covered: white space and ordinary characters in the format; `%%`; the
assignment-suppressing `*`; field widths; the conversions `d`, `i`, `u`,
`o`, `x`, `X` with the length modifiers `hh`, `h`, `l`, `ll`, `j`, `z`,
`t`; `c`, `s` and `n`. `%i` of a `0b` prefix is `unsupported`: C23 reads
it as binary and C17 as 0, and glibc gives a program the one its feature
macros ask for (the C23 one under `_GNU_SOURCE`, as in mpv).

Undefined, as C says: a converted value the object cannot represent, an
argument of the wrong type, a target too small or overlapping the input or
the format, `%n` with `*` or a width, an invalid specification.

`unsupported`, where glibc does what C does not say or says otherwise:
floating-point and other conversions (`f`, `e`, `g`, `a`, `[`, `p`, `b`,
wide characters); an input item that is a prefix of a number but not a
number (`0x` with no hexadecimal digit after it, which glibc reads as 0);
a negative number for an unsigned conversion (glibc negates it in the
unsigned type); `%Nc` with fewer than `N` characters left (glibc stores
them and counts the conversion); and an input failure after a conversion
completed but before anything was assigned (glibc returns `EOF`, C the
count, 0).
-/
namespace AchatesCheck.Scanf

open Achates AchatesCheck.Printf

def isSpace (b : UInt8) : Bool := b.toNat = 32 ∨ (9 ≤ b.toNat ∧ b.toNat ≤ 13)

def digitVal (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55)
  else none

/-- Why one directive stopped. -/
inductive Stop where
  | input
  | matching

/-- The integer at the start of `bs`, read as `%d` (base 10), `%o`, `%x`
or `%i` (base 0) read it, in at most `width` bytes: its value and the
bytes it took, or why it stopped. -/
def readInt (bs : List UInt8) (width : Nat) (base : Nat) : M (Except Stop (Int × Nat)) := do
  let bs := bs.take width
  if bs.isEmpty then return .error .input
  let (neg, sgn) := match bs with
    | 45 :: _ => (true, 1)
    | 43 :: _ => (false, 1)
    | _ => (false, 0)
  let rest := bs.drop sgn
  let isX (c : UInt8) := c = 120 ∨ c = 88
  let isB (c : UInt8) := c = 98 ∨ c = 66
  let binary : Bool := match rest with
    | 48 :: c :: _ => isB c
    | _ => false
  if base = 0 ∧ binary then
    unsupported "vsscanf: %i of a 0b prefix, which C23 reads as binary and C17 as the number 0"
  let (base, pre) : Nat × Nat := match rest with
    | 48 :: c :: _ =>
      if isX c ∧ (base = 0 ∨ base = 16) then (16, 2)
      else (if base = 0 then 8 else base, 0)
    | _ => (if base = 0 then 10 else base, 0)
  let body := rest.drop pre
  let ds := body.takeWhile fun c => (digitVal c).any (· < base)
  if ds.isEmpty then
    if pre > 0 then
      unsupported "vsscanf: a 0x or 0b prefix with no digit after it, which glibc reads as 0"
    return .error .matching
  let v := ds.foldl (fun acc c => acc * base + (digitVal c).getD 0) 0
  pure (.ok (if neg then -(v : Int) else v, sgn + pre + ds.length))

/-- The object a length modifier gives an integer conversion: the type's
spelling, its width, and whether it is signed. -/
def target (len : String) (signed : Bool) : Option (String × Nat) :=
  let s := fun (t : String) => if signed then t else s!"unsigned {t}"
  match len with
  | "" => some (s "int", 32)
  | "hh" => some (if signed then "signed char" else "unsigned char", 8)
  | "h" => some (s "short", 16)
  | "l" | "j" | "z" | "t" => some (s "long", 64)
  | "ll" => some (s "long long", 64)
  | _ => none

def overlaps (a : Ptr) (n : Nat) (srcs : List Src) : Bool := srcs.any (Printf.overlaps a n)

/-- Stores `bytes` at the next argument, a pointer to `pointee` (or to any
character type, when `pointee` is `char`). -/
def put (ap : Ptr) (pointee : String) (bytes : Array MByte) (align : Nat) (srcs : List Src) : M Unit := do
  let p ← if pointee == "char" then do
      let (t, bs) ← VaList.next ap
      match t with
      | .ptr q =>
        if !VaList.isChar (VaList.stripQuals q) then
          ub s!"vsscanf: %c or %s with an argument of type {q} *"
        let p : Ptr ← CVal.decode bs
        pure p
      | _ => ub s!"vsscanf: %c or %s with an argument of type {t.spell}"
    else VaList.argPtr ap pointee
  if overlaps p bytes.size srcs then ub "vsscanf: a target overlaps the input or the format"
  Mem.storeBytes p bytes align

/-- `vsscanf(s, format, ap)`: the number of items assigned, or `EOF`. -/
def vsscanf (s fmt ap : Ptr) : M I32 := do
  if s == .null ∨ fmt == .null then ub "vsscanf with a null pointer"
  let input ← Libc.cstr s
  let f ← Libc.cstr fmt
  let srcs : List Src := [(s, input.length + 1), (fmt, f.length + 1)]
  let mut pos := 0
  let mut count := 0
  -- A conversion completed: one that assigned, one suppressed, or `%n`.
  let mut done := false
  let mut stop : Option Stop := none
  let mut rest := f
  for _ in List.range (f.length + 1) do
    match rest with
    | [] => break
    | c :: tl =>
      if isSpace c then
        pos := pos + ((input.drop pos).takeWhile isSpace).length
        rest := tl.dropWhile isSpace
        continue
      if c != ch '%' then
        match input[pos]? with
        | none =>
          stop := some .input
          break
        | some x =>
          if x != c then
            stop := some .matching
            break
          pos := pos + 1
          rest := tl
          continue
      -- A conversion specification.
      let (skip, r) := match tl with
        | 42 :: t => (true, t)
        | t => (false, t)
      let (width, r) := if r.head?.any isDigit then
          let (n, t) := number r 0
          (some n, t)
        else (none, r)
      if width == some 0 then ub "vsscanf: a field width of 0"
      let mut len := ""
      let mut r := r
      for l in ["hh", "ll", "h", "l", "j", "z", "t", "L"] do
        if len == "" ∧ (bytesOf l).isPrefixOf r then
          len := l
          r := r.drop l.length
      let some conv := r.head? | ub "vsscanf: a format that ends inside a conversion specification"
      rest := r.drop 1
      let conv := Char.ofNat conv.toNat
      match conv with
      | '%' =>
        if skip ∨ width.isSome ∨ len != "" then ub "vsscanf: %% with *, a width or a length"
        pos := pos + ((input.drop pos).takeWhile isSpace).length
        match input[pos]? with
        | none =>
          stop := some .input
          break
        | some x =>
          if x != ch '%' then
            stop := some .matching
            break
          pos := pos + 1
      | 'n' =>
        if skip ∨ width.isSome then ub "vsscanf: %n with * or a field width"
        let some (ty, w) := target len true | ub s!"vsscanf: length modifier {len} with %n"
        put ap ty (leBytes (w / 8) (Int.toNat ((pos : Int) % (2 ^ w : Int)))) (w / 8) srcs
        done := true
      | 'd' | 'i' | 'u' | 'o' | 'x' | 'X' =>
        let signed := conv == 'd' ∨ conv == 'i'
        let some (ty, w) := target len signed
          | ub s!"vsscanf: length modifier {len} with %{conv}"
        pos := pos + ((input.drop pos).takeWhile isSpace).length
        let base := match conv with
          | 'd' | 'u' => 10
          | 'i' => 0
          | 'o' => 8
          | _ => 16
        match ← readInt (input.drop pos) (width.getD (input.length + 1)) base with
        | .error e =>
          stop := some e
          break
        | .ok (v, n) =>
          pos := pos + n
          if !signed ∧ v < 0 then
            unsupported "vsscanf: a negative number for an unsigned conversion, which glibc negates"
          let lo : Int := if signed then -(2 ^ (w - 1) : Int) else 0
          let hi : Int := if signed then 2 ^ (w - 1) - 1 else 2 ^ w - 1
          if v < lo ∨ v > hi then ub s!"vsscanf: {v} does not fit the target of %{len}{conv}"
          if !skip then
            put ap ty (leBytes (w / 8) (Int.toNat (v % (2 ^ w : Int)))) (w / 8) srcs
            count := count + 1
          done := true
      | 'c' =>
        if len != "" then unsupported "vsscanf: %lc (wide characters)"
        let n := width.getD 1
        let avail := input.length - pos
        if avail = 0 then
          stop := some .input
          break
        if avail < n then
          unsupported "vsscanf: %c with fewer characters left than its width, which glibc stores and counts"
        if !skip then
          put ap "char" ((input.drop pos).take n |>.toArray.map .byte) 1 srcs
          count := count + 1
        pos := pos + n
        done := true
      | 's' =>
        if len != "" then unsupported "vsscanf: %ls (wide characters)"
        pos := pos + ((input.drop pos).takeWhile isSpace).length
        let word := ((input.drop pos).takeWhile (!isSpace ·)).take (width.getD (input.length + 1))
        if word.isEmpty then
          stop := some .input
          break
        if !skip then
          put ap "char" ((word ++ [0]).toArray.map .byte) 1 srcs
          count := count + 1
        pos := pos + word.length
        done := true
      | 'f' | 'F' | 'e' | 'E' | 'g' | 'G' | 'a' | 'A' | '[' | 'p' | 'b' | 'C' | 'S' | 'm' =>
        unsupported s!"vsscanf: conversion %{conv} is not modelled"
      | c => ub s!"vsscanf: invalid conversion specification %{c}"
  match stop with
  | some .input =>
    if count = 0 ∧ done then
      unsupported "vsscanf: an input failure after a conversion that assigned nothing, where glibc returns EOF and C the count"
    if count = 0 then return SInt.ofInt 32 (-1)
    pure (SInt.ofInt 32 count)
  | _ => pure (SInt.ofInt 32 count)

end AchatesCheck.Scanf
