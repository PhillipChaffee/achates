# What Aeneas produces from Rust, and what Achates must match

Hands-on spike, 2026-11-21. Everything below comes from running Charon and
Aeneas on a probe crate and type-checking the output in Lean, unless a line
says otherwise. The working setup is in `/home/user/spike-aeneas` (see its
`README.md`). File references below are relative to that folder.

## Summary

- Aeneas works end to end here: Rust crate → Charon (LLBC) → Aeneas (Lean)
  → `lake build` against Aeneas's Lean library and Mathlib → proofs.
- It needs Lean `v4.36.0` and Mathlib `v4.36.0` (rev `fc4f59e5`). Both match
  the Lean already at `~/.local/lean`, so no second toolchain was needed.
- 137 probe functions. 119 translate and type-check with no `sorry`. 18 are
  rejected or produce bad output. The rejections that matter most for mpv:
  all floating point, function pointers, `dyn Trait`, `return` or labelled
  `break` inside nested loops, and generics instantiated with `&mut`.
- Many standard-library calls translate only as `axiom`s with no
  specification. You can state theorems about code that calls them, but you
  cannot prove anything about what those calls return.
- Two places where the Lean model disagrees with Rust (checked by `rfl` in
  Lean): `i32::MIN % -1` returns `ok 0` (Rust panics), and `Vec::insert` at
  `index == len` fails (Rust allows it).
- I proved four theorems about the output. The main one: the `strcmp` probe
  returns 0 on equal inputs and never fails on any inputs. Each loop proof
  took about ten lines. Most of the work is done by the `step*` tactic.

## 1. Versions and install

| Component | Version | Source |
| --- | --- | --- |
| Aeneas | `nightly-2026.11.21-2e3d448` (commit `2e3d4488280bb8a95411db81019a7854a784861f`) | GitHub release asset `aeneas-linux-x86_64.tar.gz` |
| Charon | `0.1.322` (commit `9e193f0317dacc822cc864c1798b117c70dcf7df`, matches Aeneas `charon-pin`) | bundled in the same archive |
| Rust for Charon | `nightly-2026-09-17` (rustc 1.100.0-nightly 923c95cdf), components rustc-dev, llvm-tools, rust-src, miri | `rust-toolchain` file in the archive |
| Lean | `v4.36.0` | `dist/backends/lean/lean-toolchain`; already at `~/.local/lean` |
| Mathlib | `v4.36.0`, rev `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` | pinned by Aeneas's `lake-manifest.json` |
| Aeneas Lean library | same commit as Aeneas | `dist/backends/lean` plus release asset `lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz` (prebuilt oleans) |

No OCaml or opam was needed. The release archive holds a static `aeneas`
binary, `charon`, `charon-driver` and the Lean library sources.

Exact commands that worked:

```sh
cd /home/user/spike-aeneas
T=nightly-2026.11.21-2e3d448
U=https://github.com/AeneasVerif/aeneas/releases/download/$T
curl -sSfL -o dl/aeneas-linux-x86_64.tar.gz $U/aeneas-linux-x86_64.tar.gz
curl -sSfL -o dl/lean-build-aeneas.tar.gz \
  $U/lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz
mkdir -p dist && tar xzf dl/aeneas-linux-x86_64.tar.gz -C dist

rustup toolchain install nightly-2026-09-17 --profile minimal \
  -c rustc-dev,llvm-tools,rust-src
rustup component add --toolchain nightly-2026-09-17 miri

# Lean project
export PATH=$HOME/.local/lean/bin:$PATH
mkdir lean && cd lean
cp ../dist/backends/lean/lean-toolchain .
# lakefile.toml: [[require]] name = "aeneas", path = "../dist/backends/lean"
lake update
mkdir -p ../dist/backends/lean/.lake/build
tar xzf ../dl/lean-build-aeneas.tar.gz -C ../dist/backends/lean/.lake/build
lake build

# Translate a crate (from inside it)
../dist/charon cargo --preset=aeneas --dest-file OUT/crate.llbc
../dist/aeneas -backend lean -no-progress-bar -dest OUT OUT/crate.llbc
```

`gh release list` and the GitHub REST API were blocked in this session.
Plain HTTPS downloads from `github.com/.../releases/download/` and anonymous
`git clone` worked.

Timings on this machine:

| Step | Time |
| --- | --- |
| `rustup toolchain install nightly-2026-09-17` | 38 s |
| First `charon cargo` run (builds a MIR sysroot with miri) | 3 min 23 s |
| Later `charon cargo` runs on the probe crate | about 2 s |
| `aeneas` on the whole probe crate (about 140 functions) | 9 to 15 s |
| `lake update` (Mathlib clone plus cache download of 9117 files) | 3 min 41 s |
| Download of the Aeneas olean archive (69 MB) | under a minute (not timed precisely) |
| First `lake build` (nothing compiled, only `Probes` elaborated) | 52 s |
| Rebuild after changing the generated file | 10 to 17 s |
| `lake env lean` on one proof file | 15 to 60 s, most of it loading Mathlib |

I did not try building the Aeneas Lean library from source, so I do not know
how long that takes. Twice the kernel killed a process for lack of memory
during parallel work (once during `lake update`, once during the probe
sweep). The builds still completed. I did not find out which process it was.

Without the `miri` component, Charon warns and falls back to the default
sysroot. The output file was the same size in both cases. I did not compare
it further.

## 2. Lean project setup

`lean/lakefile.toml`:

```toml
name = "probes"
defaultTargets = ["Probes"]

[[require]]
name = "aeneas"
path = "../dist/backends/lean"

[[lean_lib]]
name = "Probes"
# Generated code must not silently bind unknown names (e.g. F64) as implicits.
leanOptions = { autoImplicit = false, relaxedAutoImplicit = false }
```

The setting `autoImplicit = false` is required. Lean's default is
`autoImplicit = true`. With that default, a generated signature that mentions
a type the library does not define (`F64`) still type-checks: Lean turns `F64`
into an implicit type variable. I saw this happen: `#check @p05_fabs` printed
`{F64 : Type u_1} → F64 → Result F64`. With `autoImplicit = false` the same
file fails with `Unknown identifier F64`.

A path dependency does not download the prebuilt Aeneas oleans. Unpacking the
release archive into `dist/backends/lean/.lake/build` was enough for Lake to
reuse it. The first build compiled nothing from Aeneas or Mathlib.

Generated files start like this (verbatim):

```lean
-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [probes]
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
...
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section

namespace probes
```

They use the Lean module system (`module`, `public import`). The
`noncomputable section` appears only when the crate calls standard-library
functions that Aeneas has no model for. `#eval` still worked on generated
functions in such a file, loops and `partial_fixpoint` recursion included
(see `lean/Probes/Eval.lean`).

## 3. Probe results

The crate is `probes/src/lib.rs`. Each function was translated in isolation
(`scripts/probe_each.py`, Charon `--start-from`) and each output type-checked
as its own module (`lean_lib ProbesEach`). The full table is
`out/summary.tsv`. "Accepted" means Aeneas reported no error and the Lean
file type-checks with `autoImplicit = false` and no `sorry`. "Axioms" lists
the standard-library calls that came out as `axiom` with no body or spec.

### Integers

| Probe | Construct | Result | Note |
| --- | --- | --- | --- |
| p01 | `+` on u8, i8, u16, i32, u64, i64, usize, u128 | Accepted | `a + b : Result U8`. It fails with `integerOverflow`. |
| p01 | `-`, `*`, `/`, `%` on i32; unary `-` | Accepted | Each op is a monadic bind. Unary minus is `-. a`. |
| p02 | `wrapping_add/sub/mul` | Accepted | Pure function inside `ok (...)` or `lift (...)`. |
| p02 | `checked_add/mul` | Accepted | Returns `Option`, pure. |
| p02 | `saturating_add`, `overflowing_add` | Accepted | Pure. `overflowing_add` returns `U32 × Bool`. |
| p03 | `as` casts i32→u32, u64→u8, u8→i64, i64→usize, bool→u8 | Accepted | `IScalar.hcast`, `UScalar.cast`, `UScalar.cast_fromBool`. Truncates or sign-extends. |
| p03 | `u32::from(u8)` | Accepted | `core.convert.num.FromU32U8.from`. |
| p03 | `i32::try_from(i64).ok()` | Accepted | Axioms: `try_from`, `Result.ok`. |
| p04 | `<`, `!=`, `>=`, `&&`, `\|\|`, `if` | Accepted | Comparisons are pure `Bool`. `&&` and `\|\|` become nested `if`. |
| p04 | `a.max(b)`, `core::cmp::min` | Accepted | `core.cmp.impls.OrdI64.max` (pure), `core.cmp.min` (monadic). |
| p04 | `&`, `\|`, `^`, `!`, `<<`, `>>` | Accepted | Bit ops pure. Shifts are monadic and fail when the shift amount is at least the width. |
| p22 | `a % b`, `a / b` on i32 with variable divisor | Accepted | `%` does not fail on `MIN % -1`; see section 7. |
| p26 | `from_le_bytes`, `leading_zeros`, `wrapping_mul` on i128 | Accepted | |
| p26 | `i64::abs`, `u8::is_ascii_digit`, `u8::to_ascii_lowercase` | Accepted | Axioms. |

### Floats

| Probe | Construct | Result | Note |
| --- | --- | --- | --- |
| p05 | `f64` `+ * - /` with literals | Rejected | `[Error] Improperly typed constant value`. Body becomes `sorry`. |
| p05 | `f64 <`, `f32 *`, float clamp | Rejected | `[Error] Invalid inputs for binop`. Body becomes `sorry`. |
| p05 | `f64 as i64`, `i64 as f64` | Rejected | `[Error] Unreachable`. The output is malformed (`ok (` with nothing after it). |
| p05 | `f64::abs`, `f64::is_nan` | Bad output | Aeneas reports no error. The Lean file uses the type `F64`, which the library does not define. |
| p17 | `(x >> 11) as f64 * (1.0 / ...)` | Rejected | Same constant error. |

The Aeneas Lean library has no float type at all: `grep -r 'F64\|F32\|Float'`
over `backends/lean/Aeneas` finds nothing.

### Slices, loops, `&mut`

| Probe | Construct | Result | Note |
| --- | --- | --- | --- |
| p06 | `strcmp` over `&[u8]`, `while`, indexing, early `return` in the loop | Accepted | |
| p06 | `bstrcmp`, length-based compare | Accepted | |
| p07 | Natural sort compare: inner `while` loops with `return` inside them | Rejected | `[Error] Breaks to outer loops are not supported yet`. The function becomes an `axiom`. |
| p08 | Early `return` in a single loop | Accepted | |
| p09 | Nested `while` loops, no return in the inner one | Accepted | Two loop functions, `_loop0` and `_loop0_loop0`. |
| p10 | `for i in 0..n`, `for x in a.iter()`, `loop { break }` | Accepted | Iterators are threaded as loop state. |
| p23 | `while let Some(x) = v.pop()` | Accepted | `Vec.pop` is an axiom. |
| p23 | `break 'outer` from an inner loop | Rejected | `Breaks to outer loops are not supported yet`. Becomes an axiom. |
| p23 | `return` inside a nested loop | Rejected | `Returns inside of nested loops are not supported yet`. Becomes an axiom. |
| p11 | Swap and write through `&mut [i32]`, `slice::swap`, fill, reverse | Accepted | Slice returned updated. |
| p11 | `&mut u32` increment; `[u8; 4]` by value | Accepted | |
| p24 | `iter().enumerate()`, `iter_mut()`, `chunks(2)` | Accepted | `chunks` and the `Chunks` type are axioms. |
| p24 | `iter().sum()`, `iter().map().fold()` | Accepted | All iterator adapter methods are axioms. |
| p26 | `&a[1..3]`, `split_at`, `copy_from_slice`, `a == b` on slices, `sort` | Accepted | `sort` is an axiom. |
| p32 | Two `&mut u32` params; `&mut [u8]` and `&mut Vec<u8>` together | Accepted | |

### Vec, structs, enums, Option, Result

| Probe | Construct | Result | Note |
| --- | --- | --- | --- |
| p12 | `Vec::push`, `insert`, `new`, `v[i]`, `v[i] = x`, `len` | Accepted | Modelled in the library. |
| p12 | `Vec::remove`, `pop`, `as_slice` | Accepted | Axioms. |
| p13 | Struct with `&self` and `&mut self` methods | Accepted | `Rect.p13_translate (self : Rect) ... : Result Rect`. |
| p13 | Returning `&mut r.x0` | Accepted | Returns the value plus a backward function. |
| p28 | Struct holding `Vec`; `&mut self.data[i]`; `first_mut` returning `Option<&mut u8>` | Accepted | `first_mut` is an axiom. |
| p29 | Struct with a `&'a [u8]` field | Accepted | The reference is erased: the field has type `Slice U8`. |
| p29 | `id(&mut x)` where `fn id<T>(x: T) -> T` | Bad output | Aeneas reports no error. Lean rejects the file: `expected a product type`. |
| p14 | Enum with tuple, struct and unit variants; `match` | Accepted | Lean `inductive`. |
| p14 | C-like enum with explicit discriminants, `as i32` | Accepted | `@[discriminant isize [10,20,30]]`, `read_discriminant`. |
| p31 | `match` on a tuple, match guard | Accepted | Becomes nested `match` and `if`. |
| p15 | `Option` return; `Result<u32, ParseErr>` return; `?` | Accepted | `?` becomes `branch` and `from_residual` calls. |
| p15 | `match` on `Option`, `unwrap_or` | Accepted | |
| p16 | Recursion (`gcd`, recursion over a slice index) | Accepted | `partial_fixpoint`. |
| p17 | xoshiro256 `next` with `wrapping_mul`, hand-written `rotl`, shifts, XOR on `[u64; 4]` | Accepted | |
| p17 | `rotate_left`, splitmix64 on `&mut u64` | Accepted | |
| p27 | `const` and `static` lookup tables | Accepted | `@[global_simps, irreducible] def TABLE : Array U8 4#usize`. |
| p25 | `Box<u32>` | Accepted | The `Box` disappears: the parameter is a plain `U32`. |

### Functions, traits, strings, panics

| Probe | Construct | Result | Note |
| --- | --- | --- | --- |
| p18 | Parameter of type `fn(u32) -> u32` | Rejected | `Arrow types are not supported yet`, `Function pointers are not supported yet`. Signature dropped. |
| p18 | Passing a `fn` item as a pointer | Rejected | `Invalid input for unop: fn_def_to_fn_ptr`. Body becomes `sorry`. |
| p18 | Generic `F: Fn(u32) -> u32`, closure capturing a value | Accepted | Closure becomes a state type plus `Fn`/`FnMut`/`FnOnce` instances. |
| p18 | Insertion sort with an `Fn(&u32, &u32) -> bool` comparator | Accepted | |
| p19 | Trait with a default method, two impls, generic use | Accepted | Trait becomes a `structure` of methods. Instances are passed explicitly. |
| p25 | `&dyn Codec` | Rejected | `Function pointers are not supported yet`. Body becomes `sorry`. |
| p20 | `str::len`, `as_bytes`, `==` on `&str`, `String::new`, `push`, `push_str`, `format!`, `chars().count()` | Accepted | Every one is an axiom. |
| p20 | `str::starts_with("http")` | Rejected | Aeneas crashes: `Fatal error: exception Aeneas.Errors.CFailure`, `[Error] Unimplemented` in `core/src/str/pattern.rs`. No file is written. |
| p20 | `c as u32` with `c: char` | Rejected | `[Error] Unreachable`. Output malformed. |
| p21 | Index out of range, `unwrap` on `None`, divide by zero, `panic!`, `assert!`, `expect` | Accepted | Each becomes a failing `Result`. See section 4.6. |

A malformed definition (`ok (` with nothing after it) breaks every
definition that follows it in the same file. In a whole-crate run, the
definitions after `p05_f64_to_i64` were parsed as part of its body. One bad
function can therefore hide errors in all the functions after it.

## 4. Conventions Achates must match

### 4.1 The result monad

```lean
inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error

@[irreducible]
def Result (α : Type u) : Type u := ITree RustEffect α

def Result.ok {α} (a : α) : Result α := .ret a
def Result.fail {α} (e : Error) : Result α := Result.vis (.fail e) PEmpty.elim
def Result.div {α} : Result α := ITree.div
```

(From `Aeneas/Std/Primitives.lean`.) Important facts:

- `Result` is not an inductive type. It is a coinductive interaction tree
  (`Aeneas.Data.Coinductive.ITree`) with one effect, `fail e`. It has three
  shapes: `ok a`, `fail e`, and `div` (non-termination). Older Aeneas
  versions, and most published examples, use an inductive
  `ok | fail | div` type. Do not copy those.
- `Result` is `@[irreducible]`. Reason about it with the provided lemmas
  (`bind_ok`, `bind_fail`, `Result.ok.injEq`, `ok_not_fail`, and so on), not
  by unfolding. You cannot `match` on a `Result` directly. Use
  `Result.match`, which returns an inductive `MatchResult`.
- It is a `Monad` and a `LawfulMonad`. Generated code uses `do`, `let x ← e`
  and `ok`.
- `Result` has no `DecidableEq`, so `decide` cannot compare two results.
  `rfl` worked for closed terms, for example
  `p01_add_u8 255#u8 1#u8 = fail .integerOverflow`.
- `massert (b : Prop) [Decidable b] : Result Unit` returns
  `fail assertionFailure` when `b` is false.
- `lift (x : α) : Result α := ok x`. The generated code wraps calls to pure
  library functions in `lift` so that the `step` tactic can find spec lemmas
  for them.

Specifications use a Hoare-triple notation: `e ⦃ r => P r ⦄`. It means
`WP.spec e P`. This is total correctness: `spec_fail` and `spec_div` both
reduce to `False`. So a proved `⦃ ⦄` triple also proves that the function does
not fail and terminates. A partial-correctness variant, `dspec`, exists
(`dspec_div ↔ True`). I did not use it.

### 4.2 Machine integers

```lean
structure UScalar (ty : UScalarTy) where  bv : BitVec ty.numBits
structure IScalar (ty : IScalarTy) where  bv : BitVec ty.numBits
@[reducible] def U8 := UScalar UScalarTy.U8      -- likewise U16 ... U128, Usize
                                                  -- and I8 ... I128, Isize
```

- The value is a `BitVec`. `x.val` is a `Nat` for unsigned types and an `Int`
  for signed ones. Literals are written `5#u8`, `(-1)#i32`, `0#usize`.
- `usize` and `isize` have width `System.Platform.numBits`, which Lean only
  knows to be 32 or 64. Proofs about `usize` must hold for both widths.
  `Usize.max` is an `irreducible_def`.
- `+ - *` are defined as `HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty))`
  and so on. They compute the exact result in `Nat` or `Int` and call
  `tryMk`, which returns `fail integerOverflow` when the result is out of
  range. This is Rust's debug-build behaviour. The `wrapping_*` model of
  release builds is not used for plain operators.
- `/` and `%` return `fail divisionByZero` for a zero divisor. Signed `/`
  returns `fail integerOverflow` for `MIN / -1`. Signed `%` does not fail for
  `MIN % -1` (section 7).
- Shifts are monadic. `x <<< s` fails with `integerOverflow` if
  `s ≥ width`, and also if `s` is a negative signed value. The shift amount
  can be of any integer type.
- `wrapping_*`, `checked_*`, `saturating_*`, `overflowing_*`, `rotate_left`,
  bitwise operators, `min`/`max` on integers and casts are pure functions.
  For example, `core.num.U32.wrapping_add : U32 → U32 → U32` is defined as
  `⟨ x.bv + y.bv ⟩`.
- Casts: `UScalar.cast` (unsigned to unsigned) and `UScalar.hcast` (unsigned
  to signed) zero-extend or truncate. `IScalar.cast` (signed to signed) and
  `IScalar.hcast` (signed to unsigned) sign-extend or truncate. This matches
  Rust `as`. Checked: `(-1 : i32) as u32 = 4294967295` and
  `257u64 as u8 = 1`, both by `rfl`.

Verbatim (integer overflow, wrapping, checked):

```lean
def p01_add_u8 (a : Std.U8) (b : Std.U8) : Result Std.U8 := do
  a + b

def p01_sub_mul_div_rem_i32 (a : Std.I32) (b : Std.I32) : Result Std.I32 := do
  let i ← a - b
  let i1 ← i * a
  let i2 ← i1 / b
  i2 % 7#i32

def p02_wrapping_add_u32 (a : Std.U32) (b : Std.U32) : Result Std.U32 := do
  ok (core.num.U32.wrapping_add a b)

def p02_checked_add_u32
  (a : Std.U32) (b : Std.U32) : Result (Option Std.U32) := do
  ok (U32.checked_add a b)

def p03_cast_i32_u32 (a : Std.I32) : Result Std.U32 := do
  ok (IScalar.hcast .U32 a)
```

Verbatim (xoshiro: wrapping multiplication, rotation, shifts, array state
updated through `&mut self`):

```lean
def rotl (x : Std.U64) (k : Std.U32) : Result Std.U64 := do
  let i ← x <<< k
  let i1 ← 64#u32 - k
  let i2 ← x >>> i1
  ok (i ||| i2)

def Xoshiro.p17_next (self : Xoshiro) : Result (Std.U64 × Xoshiro) := do
  let i ← Array.index_usize self.s 1#usize
  let i1 ← lift (core.num.U64.wrapping_mul i 5#u64)
  let i2 ← rotl i1 7#u32
  let result ← lift (core.num.U64.wrapping_mul i2 9#u64)
  let t ← i <<< 17#i32
  let i3 ← Array.index_usize self.s 0#usize
  let i4 ← Array.index_usize self.s 2#usize
  let i5 ← lift (i4 ^^^ i3)
  let a ← Array.update self.s 2#usize i5
  ...
  let i18 ← rotl i17 45#u32
  let a5 ← Array.update a4 3#usize i18
  ok (result, { s := a5 })
```

The hand-written `rotl` fails when `k = 0`, because `x >> 64` overflows. That
is what Rust does too. `u64::rotate_left` (probe `p17_next_std_rotate`) is a
pure total function.

### 4.3 Loops and recursion

By default each loop becomes two definitions: a body that returns
`ControlFlow` and a wrapper that calls the library combinator `loop`.

```lean
inductive ControlFlow (α : Type u) (β : Type v) where
  | cont (v : α) -- continue
  | done (v : β) -- break

def loop {α : Type u} {β : Type v} (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  bind (body x) fun r =>
  match r with
  | ControlFlow.cont x => loop body x
  | ControlFlow.done x => ok x
partial_fixpoint
```

Verbatim (`strcmp`, loop with early return):

```rust
pub fn p06_strcmp(a: &[u8], b: &[u8]) -> i32 {
    let mut i: usize = 0;
    while i < a.len() && i < b.len() {
        let ca = a[i];
        let cb = b[i];
        if ca != cb || ca == 0 {
            return ca as i32 - cb as i32;
        }
        i += 1;
    }
    let ca = if i < a.len() { a[i] } else { 0 };
    let cb = if i < b.len() { b[i] } else { 0 };
    ca as i32 - cb as i32
}
```

```lean
@[rust_loop_body]
def p06_strcmp_loop.body
  (a : Slice Std.U8) (b : Slice Std.U8) (i : Std.Usize) :
  Result (ControlFlow Std.Usize Std.I32)
  := do
  let i1 := Slice.len a
  if i < i1
  then
    let i2 := Slice.len b
    if i < i2
    then
      let ca ← Slice.index_usize a i
      let cb ← Slice.index_usize b i
      if ca != cb
      then
        let i3 ← lift (UScalar.hcast .I32 ca)
        let i4 ← lift (UScalar.hcast .I32 cb)
        let i5 ← i3 - i4
        ok (done i5)
      else
        if ca = 0#u8
        then
          let i3 ← lift (UScalar.hcast .I32 ca)
          let i4 ← lift (UScalar.hcast .I32 cb)
          let i5 ← i3 - i4
          ok (done i5)
        else let i3 ← i + 1#usize
             ok (cont i3)
    else
      let i3 := Slice.len a
      let ca ← if i < i3
                 then Slice.index_usize a i
                 else ok 0#u8
      ... -- the code after the loop is duplicated into each exit branch
      ok (done i7)
  else
    ... -- same code after the loop, duplicated again
    ok (done i6)

@[rust_loop]
def p06_strcmp_loop
  (a : Slice Std.U8) (b : Slice Std.U8) (i : Std.Usize) : Result Std.I32 := do
  loop
    (fun i1 => p06_strcmp_loop.body a b i1)
    i

@[reducible]
def p06_strcmp (a : Slice Std.U8) (b : Slice Std.U8) : Result Std.I32 := do
  p06_strcmp_loop a b 0#usize
```

Facts:

- The loop state (`α`) is a tuple of the variables the loop changes, for
  example `(s, i)` or `(iter, s)`. Variables the loop only reads become
  plain parameters. The result type (`β`) is what the loop's exits produce.
- Code after the loop is moved into the loop body and duplicated in each exit
  branch (the `strcmp` output above). Short-circuit `&&` and `||` are also
  expanded into nested `if`s, which duplicates more code.
- Nested loops become separate functions (`f_loop0`, `f_loop0_loop0`). The
  inner one is called from the outer body.
- `for` over a range or an iterator keeps the iterator struct
  (`core.ops.range.Range U32`, `core.slice.iter.Iter U8`) in the loop state
  and calls its `next` model.
- Recursive Rust functions use Lean's `partial_fixpoint`:

```lean
def p16_gcd (a : Std.U64) (b : Std.U64) : Result Std.U64 := do
  if b = 0#u64
  then ok a
  else let i ← a % b
       p16_gcd b i
partial_fixpoint
```

- No termination argument, `partial`, fuel or `decreasing_by` appears in the
  default output. Definitions are accepted without any proof obligation,
  because `partial_fixpoint` only needs monotonicity, which Aeneas's library
  provides. Termination is proved later, inside a spec, by giving a measure
  and an invariant to `loop.spec_decr_nat` (or `loop.spec` for any
  well-founded order). For `partial_fixpoint` recursion I did not prove
  anything, so I have not checked how its termination is proved.
- `-loops-to-rec` turns each loop into a single recursive function with
  `partial_fixpoint` and no `ControlFlow`. Its output type-checks.
- `-decreases-clauses` adds `termination_by p06_strcmp_loop_terminates ...`
  and a `decreasing_by` macro that expands to `sorry`. On the default `loop`
  output, Lean ignores them ("function is not recursive"). Lean printed no
  error about the undefined `p06_strcmp_loop_terminates`.
- `-use-fuel`: `[Error] The Lean backend doesn't support the -use-fuel option`.

### 4.4 Slices, arrays, vectors, strings

| Rust | Lean | Definition |
| --- | --- | --- |
| `&[T]`, `&mut [T]` | `Slice T` | `structure Slice (α) where leng : ℕ; list : ListN α leng; bound : leng ≤ Usize.max` |
| `[T; N]` | `Array T N#usize` | `structure Array (α) (n : Usize) where list : ListN α ↑n` (the Aeneas one, not Lean's `Array`) |
| `Vec<T>` | `alloc.vec.Vec T` | `structure Vec (α) where slice : Slice α` |
| `&str` | `Str` | `def Str := Slice U8`. There is no UTF-8 invariant. |
| `String` | Lean core `String` | All operations are axioms in this version. |
| `char` | Lean `Char` | `c as u32` is rejected. |
| `Box<T>` | `T` | |
| `&T` | `T` | Shared references are erased, in struct fields too. |

- `Slice.len`, `Vec.len` and `Array` length are pure and return `Usize`.
- `Slice.index_usize`, `Array.index_usize`, `Slice.update` and
  `Array.update` are monadic and fail with `arrayOutOfBounds`.
- `Vec.push` fails with `maximumSizeExceeded` when the new length would pass
  `Usize.max`. The model checks element count, not byte size.
- `v[i]` on a `Vec` goes through the `Index` trait:
  `alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) v i`.
- `&a[1..3]` becomes
  `core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) a { start := 1#usize, «end» := 3#usize }`.
- `const` and `static` arrays become `@[global_simps, irreducible] def`s
  built with `Array.make`.

Library models present and used by accepted probes (not axioms):
`Vec.new/push/insert/len/index/index_mut/deref/deref_mut`,
`Slice.len/index_usize/update/swap/iter/iter_mut/split_at/copy_from_slice`,
slice equality, range indexing, `Range` and slice-iterator `next`,
`Enumerate`, `Option.unwrap/expect/unwrap_or`, the `?` machinery for
`Result`, and the integer operations above. I did not check which of these
have `@[step]` spec lemmas. `Slice.index_usize`, `Vec.insert` and
`Vec.push` do.

Axioms in the accepted probes (30 in `lean/Probes/Accepted.lean`), for
example: `alloc.vec.Vec.remove`, `Vec.pop`, `Vec.as_slice`,
`core.slice.Slice.first_mut`, `Slice.chunks`, `alloc.slice.Slice.sort`,
`Iterator.sum/map/fold/count`, `core.num.I64.abs`,
`core.num.U8.is_ascii_digit`, `core.num.U8.to_ascii_lowercase`,
`core.str.Str.len`, `Str.as_bytes`, `str ==`, all `String` functions,
`alloc.fmt.format`, `i32::try_from(i64)`, `Result::ok`. These axioms are
declared inside the crate's namespace (for example
`probes.alloc.vec.Vec.remove`), so two crates would each declare their own
copy. `#print axioms probes.p12_vec_remove` lists
`probes.alloc.vec.Vec.remove`. Aeneas suggests `-split-files` to get a
template file where these can be replaced by hand-written models. I did not
try it.

### 4.5 `&mut` parameters and returned borrows

`&mut` parameters are passed by value. The updated values come back in the
result tuple. The Rust return value comes first, then each `&mut` argument
in order. A function that returns `()` returns only the updated values.

```lean
def p11_swap
  (a : Slice Std.I32) (i : Std.Usize) (j : Std.Usize) :
  Result (Slice Std.I32)
  := do
  let t ← Slice.index_usize a i
  let i1 ← Slice.index_usize a j
  let a1 ← Slice.update a i i1
  Slice.update a1 j t

def Rect.p13_translate
  (self : Rect) (dx : Std.I32) (dy : Std.I32) : Result Rect := do
  let i ← self.x0 + dx
  let i1 ← self.x1 + dx
  let i2 ← self.y0 + dy
  let i3 ← self.y1 + dy
  ok { x0 := i, y0 := i2, x1 := i1, y1 := i3 }

def Rect.p13_intersect (self : Rect) (o : Rect) : Result (Bool × Rect) := ...

def p32_two_mut
  (a : Std.U32) (b : Std.U32) (c : Std.U32) :
  Result (Bool × Std.U32 × Std.U32)
  := do
  let a1 ← lift (core.num.U32.wrapping_add a c)
  ok (c > 1#u32, a1, 0#u32)

def p17_splitmix (x : Std.U64) : Result (Std.U64 × Std.U64) := ...
  -- (return value, new *x)
```

A function that returns a `&mut` returns the current value plus a "backward
function". The caller applies the backward function to the new value to get
the updated owner:

```lean
def p13_field_borrow (r : Rect) : Result (Std.I32 × (Std.I32 → Rect)) := do
  let back := fun i => { r with x0 := i }
  ok (r.x0, back)

def p12_vec_index_mut
  (v : alloc.vec.Vec Std.U32) (i : Std.Usize) :
  Result (alloc.vec.Vec Std.U32)
  := do
  let (_, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Std.U32) v i
  ok (index_mut_back 0#u32)

def Buf.p28_first_mut
  (self : Buf) : Result ((Option Std.U8) × (Option Std.U8 → Buf)) := ...
```

A loop over `iter_mut()` carries a backward function in its loop state
(`p24_iter_mut`). In this version the backward functions are pure
(`T → Parent`), not `Result`-valued.

### 4.6 Panics

| Rust | Lean | Failure |
| --- | --- | --- |
| `a[10]` out of range | `Slice.index_usize a 10#usize` | `arrayOutOfBounds` |
| `o.unwrap()` | `core.option.Option.unwrap o` (`Result.ofOption x Error.panic`) | `panic` |
| `o.expect("none")` | `core.option.Option.expect o (toStr "none")` | not checked |
| `a / b` | `a / b` | `divisionByZero` |
| `if x > 5 { panic!(..) }` | `massert (¬ (x > 5#u32))` | `assertionFailure` |
| `assert!(x < 100)` | `massert (x < 100#u32)` | `assertionFailure` |
| `core::panicking::panic` | library def | `panic` |

`panic!` and `assert!` both produce `assertionFailure`, not `panic` (checked
by `simp` in `lean/Probes/Semantics.lean`). The panic message is dropped.

### 4.7 Structs, enums, traits, closures, names

- A struct becomes a Lean `structure` with the same field names. A unit
  struct becomes `Unit` (`def Opus := Unit`).
- An enum becomes an `inductive` with the same constructor names, marked
  `@[discriminant isize]`, or `@[discriminant isize [10,20,30]]` when the
  discriminants are explicit. `l as i32` becomes
  `IScalar.cast .I32 (read_discriminant l)`.
- `Option<T>` is Lean `Option T`. `Result<T, E>` is
  `core.result.Result T E` with constructors `Ok` and `Err`. It is not
  Aeneas's monad `Result`.
- A trait becomes a `structure` of method fields. Generic functions take the
  instance as an explicit argument (`(CodecInst : Codec C)`). An impl becomes
  `def Aac.Insts.ProbesCodec : Codec Aac := { ... }`. Default methods become
  `Codec.score.default`. Derived `Clone`, `Copy`, `PartialEq` and `Debug`
  impls are translated too.
- A closure becomes a type for its captured state, plus generated
  `Fn`/`FnMut`/`FnOnce` instances. A closure that captures `k : u32` has
  state type `U32`. A closure that takes `(&u32, &u32)` receives a pair
  `U32 × U32`.
- Names: everything goes in `namespace <crate>`. Inherent methods are
  `Type.method`. Trait impl items are `Type.Insts.<TraitPath>.<method>`.
  Loops are `f_loop` and `f_loop.body`, nested loops `f_loop0_loop0`.
  Library functions keep their Rust path (`core.num.U32.wrapping_add`,
  `alloc.vec.Vec.push`). Each definition carries a doc comment with the Rust
  path and source span. Some loop definitions show a wrong span
  (`lines 1:0-81:1`).

### 4.8 Floats

There is no float type, no float operation and nothing to prove about
floats. See section 3. A float-using Rust function cannot be translated with
this version of Aeneas.

### 4.9 Tactics and simp sets for proofs

From `documentation/tactics-reference.md` in the Aeneas repo. The ones marked
"used" I ran in section 5.

| Tactic | Purpose |
| --- | --- |
| `step`, `step*`, `step*?`, `step as ⟨...⟩` | Used. Symbolic execution: applies `@[step]` spec lemmas to each `let x ← f ...`. `step*?` prints the full proof script it found. The tactic was called `progress` in older versions. `progress` still parses and emits a warning saying it was renamed to `step` (`Aeneas/Tactic/Step/Deprecated.lean`). |
| `@[step]` | Attribute that registers a spec lemma of the form `f args ⦃ r => ... ⦄`. |
| `loop.spec_decr_nat`, `loop.spec` | Used. Loop rule: Nat measure (or any well-founded relation), invariant, postcondition. |
| `scalar_tac` (`+nonLin`) | Used. Linear arithmetic over the scalar types, their bounds and list lengths. The docs say never to use `omega` directly. |
| `simp_scalar`, `simp_lists`, `simp_ifs`, `simp_bool_prop` | `simp` with curated sets (`simp_scalar_simps`, `simp_lists_simps`, ...). |
| `bvify n`, `bv_tac n` | Move goals to `BitVec n` and decide them. For wrapping arithmetic and bit tricks. |
| `natify`, `zmodify` | Move goals to `ℕ` or `ZMod n`. |
| `agrind` | `grind` restricted to `@[agrind]` lemmas. |
| `split_conjs`, `fcongr`, `#setup_aeneas_simps` | Helpers. |

## 5. End-to-end proof

File `lean/Probes/Proofs.lean`, checked by `lake build`. `#print axioms`
shows only `propext`, `Classical.choice` and `Quot.sound` for all four
theorems.

```lean
import Probes.Accepted
open Aeneas Aeneas.Std Result ControlFlow
namespace probes

/-- Comparing a byte string with itself returns 0 (loop proof). -/
theorem p06_strcmp_self (a : Slice U8) : p06_strcmp a a ⦃ r => r = 0#i32 ⦄ := by
  unfold p06_strcmp p06_strcmp_loop
  apply loop.spec_decr_nat (fun i => a.length - i.val) (fun i => i.val ≤ a.length)
  · intro i hi
    unfold p06_strcmp_loop.body
    step*
    all_goals simp_all
    all_goals scalar_tac
  · simp

-- Use the in-bounds cast spec (value preserved) instead of the bit-vector one.
attribute [-step] UScalar.hcast.step_spec
attribute [local step] UScalar.hcast_inBounds_spec

/-- `strcmp` never fails (no panic, no overflow, terminates) on any two slices. -/
theorem p06_strcmp_total (a b : Slice U8) : p06_strcmp a b ⦃ _ => True ⦄ := by
  unfold p06_strcmp p06_strcmp_loop
  apply loop.spec_decr_nat (fun i => a.length - i.val)
    (fun i => i.val ≤ a.length ∧ i.val ≤ b.length)
  · intro i hi
    unfold p06_strcmp_loop.body
    step*
    split <;> step*
  · simp

/-- Plain `+` on u8: if the sum fits, the call succeeds with the sum. -/
theorem p01_add_u8_spec (a b : U8) (h : a.val + b.val ≤ U8.max) :
    p01_add_u8 a b ⦃ r => r.val = a.val + b.val ⦄ := by
  unfold p01_add_u8
  step*

theorem p01_add_u8_overflow : p01_add_u8 255#u8 1#u8 = fail .integerOverflow := by
  rfl

/-- Wrapping add is total and equals addition mod 2^32. -/
theorem p02_wrapping_add_u32_spec (a b : U32) :
    p02_wrapping_add_u32 a b ⦃ r => r.val = (a.val + b.val) % 2^32 ⦄ := by
  unfold p02_wrapping_add_u32
  simp only [WP.spec_ok, core.num.U32.wrapping_add_val_eq, UScalar.size_def,
    UScalarTy.numBits]
end probes
```

How hard it was: easy once the pattern was known. About three iterations per
theorem. `step*?` printed a skeleton with the remaining goals as `sorry`. The
goals left after `step*` were the `i32` subtraction overflow checks, and in
the self-comparison the fact that `a[i] - a[i] = 0`.

One thing was not obvious. The default spec for `u8 as i32`
(`UScalar.hcast.step_spec`) states the result as a bit-vector cast, which
`scalar_tac` cannot use. I swapped it for `UScalar.hcast_inBounds_spec`,
which says the value is unchanged. Then `step*` discharged the overflow
checks by itself. In the totality proof, `step*` stopped at a
`let cb ← if ... then ... else ...` and needed a manual `split`.

The loop invariant and measure had to be written by hand. Aeneas does not
generate them. Each `lake env lean` run took 15 to 60 s, mostly loading
Mathlib, so iteration is slow.

Concrete evaluation also works, which is useful for differential testing
against C (`lean/Probes/Eval.lean`):

```
#eval probes.p06_strcmp (bs [104,105,0]) (bs [104,106,0])  -- ok 0xffffffff#32  (-1)
#eval probes.p17_splitmix 0#u64      -- ok (0xe220a8397b1dcdaf, 0x9e3779b97f4a7c15)
#eval probes.p16_gcd 12#u64 18#u64   -- ok 6
#eval probes.p10_loop_break 27#u32   -- ok 111 (Collatz steps)
```

The splitmix64 output for seed 0 equals the published reference value.

## 6. Constraints on the hand-written Rust

Verified by probes unless marked "README".

1. No `f32` or `f64` anywhere in a function to be proved: no arithmetic,
   comparisons, literals, casts or `f64::` methods. The library has no float
   type. About 9% of `misc/` functions use floats
   (`misc-constructs.md`). They need another plan: keep them out of the
   proved set, or use fixed-point integers if the C allows it.
2. No `return` inside an inner loop and no `break`/`continue` to an outer
   label. Move the inner loop into its own function that returns a value or
   a flag, and test it in the outer loop. mpv's `natural_sort_cmp` shape is
   rejected as written.
3. No function pointers (`fn(..)` types or `fn` items passed as values) and
   no `dyn Trait`. Use generics with `Fn` bounds or traits with static
   dispatch. Both of those translated.
4. Do not instantiate a generic with a `&mut` type, for example
   `id(&mut x)`. Aeneas reports no error, but the Lean output does not
   type-check (README lists this limitation too).
5. Write `wrapping_*` explicitly wherever the C relies on unsigned
   wraparound. Plain `+ - * <<` model Rust debug builds: they fail on
   overflow. A shift by the full width fails.
6. Prefer explicit `while` loops with indexing over iterator adapters.
   `iter().sum()`, `map`, `fold`, `count` and `chunks` translate only as
   axioms, so nothing can be proved about them. Plain `for x in a.iter()`,
   `for i in 0..n`, `enumerate` and `iter_mut` have models.
7. Treat strings as `&[u8]`. `&str` is modelled as bytes, and every `str`
   and `String` method seen here is an axiom. `str::starts_with` crashes
   Aeneas for the whole crate. `char as u32` is rejected. `format!` is an
   axiom.
8. Avoid `Vec::remove`, `Vec::pop`, `as_slice`, `slice::sort`, `first_mut`,
   `i64::abs` and `u8::is_ascii_*` / `to_ascii_*` in proved code, or provide
   hand-written Lean models. They are all axioms.
9. `Vec::insert(len, x)` and `i32::MIN % -1` are modelled incorrectly
   (section 7). Avoid them in proved code until that is fixed upstream.
10. No `unsafe` code and no concurrency (README, not probed). Raw pointers
    were not probed.
11. Every translation must be checked: run Aeneas, fail on any `[Error]`
    line or a non-zero exit code, type-check with `autoImplicit = false`, and
    reject output that contains `sorry` or a crate-local `axiom` for one of
    our own functions. Aeneas turns untranslatable functions into axioms
    (`p07_natural_cmp`, `p23_*`) and the file still builds.

## 7. What did not work, and model disagreements

Tool failures:

- Floats (all probes in section 3).
- `str::starts_with`: Aeneas crashes (`Fatal error ... CFailure`), so no
  output at all for the crate. Workaround used: keep the function out of
  the crate (`#[cfg(not(accepted_only))]`).
- Charon `--exclude` did not exclude inherent methods with any pattern I
  tried (`probes::Xoshiro::p17_next_double`,
  `probes::{probes::Xoshiro}::p17_next_double`,
  `probes::{impl probes::Xoshiro}::p17_next_double`, `crate::...`). A `cfg`
  attribute plus `--rustc-arg=--cfg=accepted_only` worked. `--start-from`
  did work with `probes::Rect::p13_width`.
- `-use-fuel` is not supported by the Lean backend.
- Malformed output after some errors (`ok (` with nothing after it) breaks
  the rest of the file.

Places where the Lean model disagrees with Rust, each checked by `rfl` in
`lean/Probes/Semantics.lean`:

- `p22_rem_i32 (-2147483648) (-1) = ok 0`. Rust panics on `i32::MIN % -1`
  ("attempt to calculate the remainder with overflow"). Charon's LLBC marks
  the operation as panicking (`panic.%`). Aeneas's `IScalar.rem` checks only
  for a zero divisor. So a proof that such a function "never fails" can be
  wrong about the real Rust. Division is correct:
  `p22_div_i32 (-2147483648) (-1) = fail integerOverflow`.
- `p12_vec_insert (Vec.new U32) 0 5 = fail arrayOutOfBounds`. Rust's
  `Vec::insert` accepts `index == len` and appends. The model requires
  `index < len`.

Both should be reported upstream. Until they are fixed, Achates-side
theorems that mention `%` on signed integers or `Vec::insert` need care.

## 8. Not verified

- Building the Aeneas Lean library from source (time, memory).
- Proving termination of a `partial_fixpoint` recursive function. I proved
  loops only.
- Whether `-split-files` and hand-written models for the axioms work.
- `unsafe`, raw pointers, `Rc`/`RefCell`, `HashMap`, threads, atomics,
  `goto`-style state machines: not probed.
- Which library functions have `@[step]` specs. I only know the ones my
  proofs used (`Slice.index_usize_spec`, `Usize.add_spec`, `I32.sub_spec`,
  `UScalar.hcast.step_spec`, `UScalar.hcast_inBounds_spec`) and the ones I
  read (`Vec.insert_spec`, `Vec.push_spec`, `Option.unwrap.spec`).
- Proof effort on larger functions (for example the natural-sort compare
  after restructuring) or on code with backward functions.
- Behaviour with a 32-bit `usize`. The model leaves the width abstract, so
  proofs must cover both widths. I did not test the effect on real proofs.
- Whether the memory kills seen during parallel work came from Lean, Lake or
  Charon.

## 9. Design notes for Achates

These follow from the facts above. They are recommendations, not findings.

- Emit Achates definitions in the same monad (`Aeneas.Std.Result`) over the
  same scalar types (`Std.U8`, `Std.I32`, ..., `Slice`, `Array`). Then the
  theorem can be stated with the same `⦃ ⦄` notation, and `step`,
  `scalar_tac` and the library lemmas work on both sides. A plain equality
  `achates_f x = aeneas_f x` is possible, but it is only useful where both
  sides fail in the same way.
- C undefined behaviour (signed overflow, out-of-bounds access) has no Rust
  counterpart. Rust fails with a specific `Error`. A practical theorem shape
  is: under a precondition that excludes C undefined behaviour, both sides
  succeed with the same value:
  `pre x → achates_f x ⦃ r => aeneas_f x ⦃ r' => r = r' ⦄ ⦄`, or the same
  written as two specs.
- Model C `unsigned` arithmetic with the `wrapping_*` functions, and C
  `int` arithmetic with the failing `+`/`-`/`*` (failure standing in for
  undefined behaviour). The two sides then line up wherever the Rust port
  uses `wrapping_*` for the same operations.
- `&mut` outputs come back as extra tuple components in a fixed order
  (return value first). A C function that writes through pointers has to be
  translated into the same tuple shape, or a wrapper has to reshape one
  side.
- Loops come out as `loop` plus `ControlFlow`, with the loop state tuple
  holding exactly the variables the loop changes. If Achates emits C loops
  the same way, the two loop bodies can be compared step by step with one
  shared invariant.
