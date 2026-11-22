import Achates
/-!
A model of `vsnprintf` (C11 7.21.6.1, 7.21.6.12) for the differential
check, in the "C" locale, with glibc's choices where C leaves one.

Covered: the flags `-`, `+`, space, `#`, `0`; field width and precision,
given or `*`; the conversions `d`, `i`, `u`, `o`, `x`, `X` with the length
modifiers `hh`, `h`, `l`, `ll`, `j`, `z`, `t`; `c`, `s`, `f`, `F` and `%%`.
`%f` prints the exactly rounded decimal value, rounding a tie to even, as
glibc does in the default rounding mode; infinities and NaNs print as
`inf` (`INF` for `F`). A NaN is `unsupported`: glibc prints its sign, and
Lean's `Float` does not keep it.

Undefined, as C says: an invalid conversion specification, a flag,
precision or length modifier with a conversion it does not apply to, an
argument of the wrong type (checked as `va_arg` checks it), `%s` with a
null pointer or without a terminator, an output buffer too small for what
is written, and copying between overlapping objects.

Not covered, and `unsupported`: the other conversions (`e`, `g`, `a`,
`p`, `n`, wide characters, `long double`), and an output longer than
`INT_MAX`.
-/
namespace AchatesCheck.Printf

open Achates

structure Spec where
  minus : Bool := false
  plus : Bool := false
  space : Bool := false
  hash : Bool := false
  zero : Bool := false
  width : Nat := 0
  prec : Option Nat := none
  len : String := ""
  conv : Char := '%'

def ch (c : Char) : UInt8 := c.toNat.toUInt8

def bytesOf (s : String) : List UInt8 := s.toList.map ch

/-- A decimal number at the start of `bs`, and the rest. -/
def number : List UInt8 → Nat → Nat × List UInt8
  | b :: rest, acc =>
    if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then number rest (acc * 10 + (b.toNat - 48)) else (acc, b :: rest)
  | [], acc => (acc, [])

def isDigit (b : UInt8) : Bool := 48 ≤ b.toNat ∧ b.toNat ≤ 57

/-- The digits of `n` in `base`, most significant first; `0` for zero. -/
def natDigits (base : Nat) (upper : Bool) (n : Nat) : List UInt8 :=
  let digit (d : Nat) : UInt8 :=
    if d < 10 then (48 + d).toUInt8 else ((if upper then 55 else 87) + d).toUInt8
  let rec go (fuel n : Nat) (acc : List UInt8) : List UInt8 :=
    match fuel with
    | 0 => acc
    | k + 1 => if n < base then digit n :: acc else go k (n / base) (digit (n % base) :: acc)
  go (n + 1) n []

/-- `body` padded with spaces to `width`, on the left unless `left`. -/
def pad (width : Nat) (left : Bool) (body : List UInt8) : List UInt8 :=
  let fill := List.replicate (width - body.length) (ch ' ')
  if left then body ++ fill else fill ++ body

/-- A converted number: its sign or base prefix and its digits, with zero
padding between the two when `zeros`. -/
def field (s : Spec) (pre digits : List UInt8) (zeros : Bool) : List UInt8 :=
  if zeros ∧ !s.minus then
    pre ++ List.replicate (s.width - pre.length - digits.length) (ch '0') ++ digits
  else pad s.width s.minus (pre ++ digits)

def fmtInt (s : Spec) (signed : Bool) (v : Int) : List UInt8 :=
  let base := match s.conv with
    | 'o' => 8
    | 'x' | 'X' => 16
    | _ => 10
  let upper := s.conv == 'X'
  let mag := v.natAbs
  let ds := if s.prec == some 0 ∧ mag = 0 then [] else natDigits base upper mag
  let ds := List.replicate (s.prec.getD 1 - ds.length) (ch '0') ++ ds
  -- `#` with `o` makes the first digit a zero.
  let ds := if s.hash ∧ base = 8 ∧ ds.head? != some (ch '0') then ch '0' :: ds else ds
  let pre :=
    if signed then
      if v < 0 then [ch '-'] else if s.plus then [ch '+'] else if s.space then [ch ' '] else []
    else if s.hash ∧ base = 16 ∧ mag ≠ 0 then bytesOf (if upper then "0X" else "0x")
    else []
  field s pre ds (s.zero ∧ s.prec.isNone)

def fmtFloat (s : Spec) (x : Float) : List UInt8 :=
  let bits := x.toBits.toNat
  let neg := bits >>> 63 = 1
  let ex := (bits >>> 52) % 2048
  let frac := bits % 2 ^ 52
  let upper := s.conv == 'F'
  let sign := if neg then [ch '-'] else if s.plus then [ch '+'] else if s.space then [ch ' '] else []
  if ex = 2047 then
    let word := if frac = 0 then "inf" else "nan"
    pad s.width s.minus (sign ++ bytesOf (if upper then word.toUpper else word))
  else
    let (m, e) : Nat × Int := if ex = 0 then (frac, -1074) else (frac + 2 ^ 52, (ex : Int) - 1075)
    let p := s.prec.getD 6
    -- The value times 10^p, rounded to an integer, a tie to even.
    let n : Nat :=
      if e ≥ 0 then m * 2 ^ e.toNat * 10 ^ p
      else
        let num := m * 10 ^ p
        let den := 2 ^ e.natAbs
        let q := num / den
        let r := num % den
        if 2 * r > den ∨ (2 * r = den ∧ q % 2 = 1) then q + 1 else q
    let ds := natDigits 10 false n
    let ds := List.replicate (p + 1 - ds.length) (ch '0') ++ ds
    let whole := ds.take (ds.length - p)
    let part := ds.drop (ds.length - p)
    let body := whole ++ (if p > 0 ∨ s.hash then [ch '.'] else []) ++ part
    field s sign body s.zero

/-- The bytes `%s` prints from `p`: up to the terminator, or at most `prec`. -/
def strBytes (p : Ptr) (prec : Option Nat) : M (List UInt8) := do
  if p == .null then ub "%s with a null pointer"
  let limit := prec.getD (2 ^ 31)
  let rec go : Nat → Nat → List UInt8 → M (List UInt8)
    | 0, _, acc => pure acc.reverse
    | k + 1, i, acc => do
      if i ≥ limit then return acc.reverse
      let c ← Mem.loadByte (← p.add 1 i)
      if c = 0 then pure acc.reverse else go k (i + 1) (c :: acc)
  go (limit + 1) 0 []

/-- The integer argument of `d`, `i` (`signed`) or `u`, `o`, `x`, `X`,
read as `va_arg` reads it, converted to the type the length modifier names. -/
def intArg (ap : Ptr) (signed : Bool) (len : String) : M Int := do
  let (w, rank, narrow) : Nat × String × Option Nat := match len with
    | "hh" => (32, "int", some 8)
    | "h" => (32, "int", some 16)
    | "l" | "j" | "z" | "t" => (64, "long", none)
    | "ll" => (64, "long long", none)
    | _ => (32, "int", none)
  let v : Int ←
    if signed then do pure (← VaList.argS ap w rank).toInt else do pure (← VaList.argU ap w rank).toInt
  match narrow with
  | some n =>
    -- The value is converted to `signed char`/`short` or their unsigned types.
    let u := v % (2 ^ n : Int)
    pure (if signed ∧ u ≥ 2 ^ (n - 1) then u - 2 ^ n else u)
  | none => pure v

/-- A source of bytes the output was made from: pointer and length. -/
abbrev Src := Ptr × Nat

/-- Renders the format `f`, reading arguments from `ap`. -/
def render (f : List UInt8) (ap : Ptr) : M (List UInt8 × List Src) := do
  let mut out : Array UInt8 := #[]
  let mut srcs : List Src := []
  let mut rest := f
  for _ in List.range (f.length + 1) do
    match rest with
    | [] => break
    | c :: tl =>
      if c != ch '%' then
        out := out.push c
        rest := tl
        continue
      -- A conversion specification.
      let mut s : Spec := {}
      let mut r := tl
      for _ in List.range 6 do
        match r with
        | b :: t =>
          if b = ch '-' then
            s := { s with minus := true }
          else if b = ch '+' then
            s := { s with plus := true }
          else if b = ch ' ' then
            s := { s with space := true }
          else if b = ch '#' then
            s := { s with hash := true }
          else if b = ch '0' then
            s := { s with zero := true }
          else
            break
          r := t
        | [] => break
      match r with
      | b :: t =>
        if b = ch '*' then
          let w ← (VaList.argS ap 32 "int")
          if w.toInt < 0 then s := { s with minus := true, width := w.toInt.natAbs }
          else s := { s with width := w.toInt.toNat }
          r := t
        else if isDigit b then
          let (n, t') := number r 0
          s := { s with width := n }
          r := t'
      | [] => pure ()
      match r with
      | b :: t =>
        if b = ch '.' then
          match t with
          | b' :: t' =>
            if b' = ch '*' then
              let p ← (VaList.argS ap 32 "int")
              s := { s with prec := if p.toInt < 0 then none else some p.toInt.toNat }
              r := t'
            else
              let (n, t'') := number t 0
              s := { s with prec := some n }
              r := t''
          | [] =>
            s := { s with prec := some 0 }
            r := []
      | [] => pure ()
      if s.width > 2 ^ 20 ∨ s.prec.getD 0 > 2 ^ 20 then
        unsupported "vsnprintf with a field width or precision above 2^20"
      for l in ["hh", "ll", "h", "l", "j", "z", "t", "L"] do
        if s.len == "" ∧ (bytesOf l).isPrefixOf r then
          s := { s with len := l }
          r := r.drop l.length
      let some conv := r.head? | ub "vsnprintf: a format that ends inside a conversion specification"
      r := r.drop 1
      s := { s with conv := Char.ofNat conv.toNat }
      let intConv := "diouxX".toList.contains s.conv
      let lenOk := s.len == "" ∨ (intConv ∧ s.len != "L")
      match s.conv with
      | '%' =>
        if s.minus ∨ s.plus ∨ s.space ∨ s.hash ∨ s.zero ∨ s.width ≠ 0 ∨ s.prec.isSome ∨ s.len != "" then
          ub "vsnprintf: a conversion specification %% with flags, width, precision or length"
        out := out.push (ch '%')
      | 'd' | 'i' | 'u' | 'o' | 'x' | 'X' =>
        if !lenOk then ub s!"vsnprintf: length modifier {s.len} with %{s.conv}"
        let signed := s.conv == 'd' ∨ s.conv == 'i'
        if s.hash ∧ (signed ∨ s.conv == 'u') then ub s!"vsnprintf: flag # with %{s.conv}"
        let v ← intArg ap signed s.len
        -- `+` and space apply to signed conversions only.
        out := out ++ (fmtInt s signed v).toArray
      | 'c' =>
        if s.len != "" then unsupported "vsnprintf: %lc (wide characters)"
        if s.hash ∨ s.zero ∨ s.prec.isSome then ub "vsnprintf: flag # or 0, or a precision, with %c"
        let v ← VaList.argS ap 32 "int"
        out := out ++ (pad s.width s.minus [(v.toInt % 256).toNat.toUInt8]).toArray
      | 's' =>
        if s.len != "" then unsupported "vsnprintf: %ls (wide characters)"
        if s.hash ∨ s.zero then ub "vsnprintf: flag # or 0 with %s"
        let (t, bs) ← VaList.next ap
        match t with
        | .ptr q =>
          if !VaList.isChar (VaList.stripQuals q) then
            ub s!"vsnprintf: %s with an argument of type {q} *"
          let p : Ptr ← CVal.decode bs
          let str ← strBytes p s.prec
          srcs := (p, if s.prec.isSome then str.length else str.length + 1) :: srcs
          out := out ++ (pad s.width s.minus str).toArray
        | _ => ub s!"vsnprintf: %s with an argument of type {t.spell}"
      | 'f' | 'F' =>
        if s.len == "L" then unsupported "vsnprintf: %Lf (long double)"
        if s.len != "" ∧ s.len != "l" then ub s!"vsnprintf: length modifier {s.len} with %{s.conv}"
        let x ← VaList.argF64 ap
        if x.isNaN then
          unsupported "vsnprintf: %f of a NaN, whose sign glibc prints and the model does not keep"
        out := out ++ (fmtFloat s x).toArray
      | 'e' | 'E' | 'g' | 'G' | 'a' | 'A' | 'p' | 'n' | 'C' | 'S' | 'm' =>
        unsupported s!"vsnprintf: conversion %{s.conv} is not modelled"
      | c => ub s!"vsnprintf: invalid conversion specification %{c}"
      if out.size > 2 ^ 31 - 1 then unsupported "vsnprintf: output longer than INT_MAX"
      rest := r
  pure (out.toList, srcs)

def overlaps (a : Ptr) (n : Nat) (b : Src) : Bool :=
  match a, b.1 with
  | .obj x o, .obj y o' => x == y && o < o' + b.2 && o' < o + n
  | _, _ => false

/-- `vsnprintf(s, n, format, ap)`: writes at most `n - 1` bytes of the
output and a terminator, and returns the length of the whole output. -/
def vsnprintf (s : Ptr) (n : U64) (fmt ap : Ptr) : M I32 := do
  if fmt == .null then ub "vsnprintf with a null format"
  let f ← Libc.cstr fmt
  let (out, srcs) ← render f ap
  if out.length > 2 ^ 31 - 1 then unsupported "vsnprintf: output longer than INT_MAX"
  if n.toNat > 0 then
    let k := min out.length (n.toNat - 1)
    if ((fmt, f.length + 1) :: srcs).any (overlaps s (k + 1)) then
      ub "vsnprintf: the output overlaps the format or an argument"
    Mem.storeBytes s ((out.take k ++ [0]).toArray.map .byte)
  pure (SInt.ofInt 32 out.length)

end AchatesCheck.Printf
