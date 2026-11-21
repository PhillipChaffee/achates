# c2rust on mpv `misc/`: spike results

This spike runs c2rust over mpv's `misc/` folder, makes the output build, measures it, checks its behaviour against the C on a sample, and rates how close each function is to what Aeneas (via Charon) can accept.

Source: mpv commit d11ffba253def00b5172c4b8b47e6b2eb765cae1. Work directory: `/home/user/spike-c2rust`. The crate is at `/home/user/spike-c2rust/misc-c2rust`.

## Summary

- All 15 compiled files transpiled. c2rust printed no errors for any of them.
- The 15 modules compile together as one crate after one manual edit (3 lines in `thread_tools.rs`). The crate needs the pinned nightly `nightly-2023-04-15`. It does not build on stable.
- Every function is `unsafe`: 223 of 223 Rust functions, and 141 of the 141 functions that come from the `.c` files.
- Differential test, C vs. transpiled Rust, 22 functions from three files, 100,000 random inputs per function: 21 functions agree on every input. `bstrtoll` differs on inputs that contain a `0b` prefix. The cause: glibc renames `strtoll` to `__isoc23_strtoll` through an asm label, and c2rust drops the label. The C object calls `__isoc23_strtoll`, which accepts `0b101`. The Rust calls the old `strtoll`, which does not.
- Aeneas readiness (rule-based, 141 functions from the `.c` files): 4 are plausible as is, 8 need only a mechanical cleanup, and 129 are structural (pointer arithmetic, FFI, unions, variadics, atomics, function pointers).
- Verdict: c2rust output is not a usable starting point for an Aeneas-verified port. It is useful as an executable reference: it links where the C links and can be differential-tested.

## Versions and commands

| item | version |
|---|---|
| c2rust | 0.22.1 (crates.io), `c2rust-transpile` 0.22.1 |
| c2rust-analyze, c2rust-refactor | from git tag `v0.22.1`, commit e9ccd715597f7d63e8635629f4450e040a230118 |
| LLVM / clang used by c2rust | 18.1.3 (Ubuntu `llvm-18-dev`, `libclang-18-dev`) |
| toolchain for the transpiled crate | `nightly-2023-04-15` (rustc 1.70.0-nightly 84dd17b56). c2rust writes it to `rust-toolchain.toml`, and rustup installed it on first use. |
| toolchain for c2rust-analyze and c2rust-refactor | `nightly-2022-08-08` (rustc 1.65.0-nightly d394408fb), with `rustc-dev` |
| stable rustc (for comparison only) | 1.97.0 |
| C compiler of the real mpv build | gcc 13.3.0 (from `meson-log.txt`) |

Install. The released crate built against LLVM 18 at the first attempt. No older LLVM or git revision was needed.

```sh
apt-get install -y llvm-18-dev libclang-18-dev cmake libssl-dev pkg-config
LLVM_CONFIG_PATH=/usr/lib/llvm-18/bin/llvm-config cargo install --locked c2rust --version 0.22.1
```

The released `c2rust` binary lists `refactor` and `analyze` subcommands, but they fail with "known subcommand not found (probably not built)". To get them, build from the git tag:

```sh
git clone --depth 1 --branch v0.22.1 https://github.com/immunant/c2rust.git c2rust-src
cd c2rust-src && LLVM_CONFIG_PATH=/usr/lib/llvm-18/bin/llvm-config \
  cargo build --release -p c2rust-analyze -p c2rust-refactor -p c2rust   # 17 min on 4 cores
```

Compile commands: I copied the 15 `misc/` entries out of `.mpv-build/compile_commands.json` and made each `file` absolute. Nothing else changed: the flags and the `directory` are as built. The copy is at `/home/user/spike-c2rust/cc/compile_commands.json`.

Transpile:

```sh
c2rust transpile cc/compile_commands.json -e -o /home/user/spike-c2rust/misc-c2rust
```

Use an absolute `-o` path. With a relative path, c2rust writes the files and then reports `file ... does not exist` and `rustfmt failed` for each one. It runs rustfmt from a different directory.

Build: `cd misc-c2rust && cargo build`.

## Per-file results (steps 2 to 4)

How to read the table:

- Every file transpiled. "Compiles" means the module builds as part of the whole crate. c2rust emits one crate, not one crate per file.
- "Rust fns" counts every function c2rust emitted. The number in parentheses is how many of them are copies of `static inline` helpers from headers (`bstr0`, `mp_isdigit`, `mp_cond_wait`, ...). c2rust copies each helper into every module that uses it.
- "C fns" counts the function definitions in the `.c` file. I took these from clang's JSON AST with the real flags.
- `*mut` and `*const` count occurrences in the source text. About 370 of the `*const` occurrences are in `__assert_fail` arguments, `__ASSERT_FUNCTION` constants and `b"...\0" as *const c_char` string casts.
- "unsafe blocks" counts explicit `unsafe {}` blocks. They are few because every function is already an `unsafe fn`.
- Extern items count per-module `extern "C"` declarations (functions, statics and opaque types), split by origin. "mpv-misc" means a function defined in another `misc/` module of this same crate. c2rust does not link modules: it declares the function again as an extern.

| file | transpiled | compiles | C lines | Rust lines | C fns | Rust fns (header copies) | unsafe fns | unsafe blocks | `*mut` | `*const` | extern items libc / talloc / FFmpeg / mpv-misc / mpv-other | `static mut` | unions mpv / libc | variadic fns | nightly features hit |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| bstr.c | yes | yes | 496 | 920 | 36 | 48 (12) | 48 | 1 | 92 | 56 | 14 / 7 / 0 / 0 / 2 | 0 | 0 / 0 | 2 | c_variadic, raw_ref_op |
| charset_conv.c | yes | yes | 235 | 203 | 5 | 8 (3) | 8 | 0 | 8 | 60 | 4 / 0 / 0 / 3 / 2 | 2 | 0 / 0 | 0 | extern_types |
| codepoint_width.c | yes | yes | 788 | 5879 | 6 | 9 (3) | 9 | 1 | 8 | 15 | 2 / 0 / 0 / 3 / 0 | 6 | 0 / 0 | 0 | raw_ref_op |
| dispatch.c | yes | yes | 417 | 862 | 15 | 23 (8) | 23 | 0 | 117 | 147 | 19 / 5 / 0 / 0 / 2 | 0 | 0 / 5 | 0 | raw_ref_op |
| hash.c | yes | yes | 41 | 143 | 1 | 1 (0) | 1 | 1 | 15 | 15 | 1 / 0 / 7 / 1 / 0 | 0 | 0 / 0 | 0 | extern_types, raw_ref_op |
| io_utils.c | yes | yes | 88 | 226 | 2 | 3 (1) | 3 | 1 | 42 | 30 | 16 / 2 / 0 / 2 / 1 | 0 | 0 / 0 | 0 | extern_types, raw_ref_op |
| json.c | yes | yes | 363 | 713 | 13 | 20 (7) | 20 | 1 | 103 | 73 | 7 / 7 / 0 / 2 / 1 | 1 | 1 / 0 | 0 | raw_ref_op |
| language.c | yes | yes | 388 | 2891 | 4 | 12 (8) | 12 | 0 | 30 | 46 | 2 / 7 / 0 / 4 / 0 | 2 | 0 / 0 | 0 | raw_ref_op |
| natural_sort.c | yes | yes | 67 | 98 | 1 | 4 (3) | 4 | 0 | 0 | 4 | 0 / 0 / 0 / 0 / 0 | 0 | 0 / 0 | 0 | none |
| node.c | yes | yes | 171 | 523 | 13 | 19 (6) | 19 | 0 | 103 | 101 | 5 / 8 / 0 / 1 / 0 | 0 | 1 / 0 | 0 | raw_ref_op |
| path_utils.c | yes | yes | 338 | 712 | 17 | 27 (10) | 27 | 1 | 81 | 74 | 12 / 13 / 0 / 5 / 0 | 1 | 0 / 0 | 0 | raw_ref_op |
| random.c | yes | yes | 102 | 130 | 6 | 6 (0) | 6 | 1 | 10 | 7 | 1 / 0 / 1 / 0 / 2 | 0 | 0 / 0 | 0 | raw_ref_op |
| rendezvous.c | yes | yes | 55 | 216 | 1 | 3 (2) | 3 | 0 | 22 | 15 | 5 / 0 / 0 / 0 / 0 | 3 | 1 / 2 | 0 | raw_ref_op |
| thread_pool.c | yes | yes | 223 | 751 | 7 | 17 (10) | 17 | 0 | 107 | 120 | 26 / 8 / 0 / 0 / 1 | 0 | 0 / 6 | 0 | raw_ref_op |
| thread_tools.c | yes | yes (after edit) | 275 | 898 | 14 | 23 (9) | 23 | 0 | 91 | 65 | 24 / 3 / 0 / 0 / 3 | 0 | 0 / 5 | 0 | core_intrinsics, raw_ref_op |
| **total** | 15/15 | 15/15 | 4047 | 15165 | 141 | 223 (82) | 223 | 7 | 829 | 828 | 138 / 60 / 8 / 21 / 14 | 15 | 2 / 18 | 2 | |

Notes on the table:

- `misc/jni.c` is not in the build, so it was not translated. 15 of the 16 `.c` files in `misc/` were in scope.
- Distinct extern names across the crate: 60 libc/pthread, 16 talloc (`ta_*`), 8 FFmpeg (`av_hash_*`, `av_random_bytes`, `AVHashContext`), 20 functions that this crate itself defines in another module, and 11 other mpv items (`mp_msg`, `mp_log`, `mp_log2`, `mp_round_next_power_of_2`, `mp_raw_time_ns`, `mp_time_ns`, `mp_time_ns_add`, `mp_tprintf_buf`, `mp_make_wakeup_pipe`, `mp_append_utf8_bstr`, `mp_append_escaped_string`).
- Rust lines: two files hold large data tables. They take 5879 + 2891 lines because rustfmt puts one element per line. Without codepoint_width and language, the ratio is 6395 Rust lines to 2871 C lines (2.2x).
- `static mut`: 12 of the 15 are C `static const` tables (`s_stage0..3`, `s_joinRules`, `langmap`, `utf_bom`, `utf_enc`, `special_escape`, `mp_path_separators`) and two function-local constants (`ambiguous_width`, `suffixes`). c2rust makes them `static mut`, so every read is an unsafe operation. The other 3 are real mutable globals in rendezvous.c (`lock`, `wakeup`, `waiters`).
- `langmap` (language.c) is a `static const` array in C. c2rust zero-fills it and fills it at load time from a function registered in `.init_array` (`run_static_initializers`). It does this because the C initializer writes string literals into `char[3]` fields.
- mpv unions: `mpv_node.u` (json.c, node.c) and `mp_static_mutex` (rendezvous.c). The libc unions are pthread types and `__atomic_wide_counter`.
- Variadic functions: `bstr_sscanf` and `bstr_xappend_asprintf`. Both use `VaListImpl` and `as_va_list()`. Calls to variadic externs (`mp_msg`, `ta_asprintf`) appear in more functions. See the reasons table below.
- Crate-level features in the generated `lib.rs`: `c_variadic`, `core_intrinsics`, `extern_types`, `raw_ref_op`. `raw_ref_op` (`&raw mut`) is stable in current Rust. The other three are still nightly-only. `cargo +stable build` gives 8 errors: the `#![feature]` attribute, `VaListImpl` and `as_va_list` (4), and the atomic intrinsics (3).
- `goto`-style control flow: c2rust's relooper emits `current_block` state variables in 10 modules. path_utils.rs has the most (17 lines).
- Assertions become `__assert_fail(b"...\0", b"../.mpv/misc/random.c\0", line, ...)` calls. The relative C path and the line number are baked into the Rust.

## Manual edits

There is one edit, in one file. `diff -r misc-c2rust.pristine/src misc-c2rust/src` shows exactly these three lines.

`src/thread_tools.rs` lines 504, 532 and 810. c2rust translates the C `atomic_bool triggered` operations to `core::intrinsics::atomic_store_seqcst` and `atomic_load_relaxed` on a `*mut bool`. rustc rejects this with E0511, because these intrinsics take integer types only. The edit casts the pointer to `*mut u8` and the stored value to `u8`:

```rust
// before
::core::intrinsics::atomic_store_seqcst(&raw mut (*c).triggered, 1 as ::core::ffi::c_int != 0);
// after
::core::intrinsics::atomic_store_seqcst(&raw mut (*c).triggered as *mut u8, (1 as ::core::ffi::c_int != 0) as u8);
```

`bool` and `u8` have the same size and layout. I did not test this edit at run time: thread_tools.c is not part of the differential test.

I added no extern declarations and changed no features. The crate builds as an rlib and a staticlib. It does not link by itself, because most of its externs are in the rest of mpv, FFmpeg and libc.

## Differential test (step 5)

Method:

1. I extracted the original objects `misc_bstr.c.o`, `misc_random.c.o` and `misc_natural_sort.c.o` from `.mpv-build/libmpv.a` with `ar x`. These are the gcc-13 `-O2` objects of the real build.
2. For every global symbol they define, `objcopy --redefine-syms` renames `name` to `c_name`. This produced 39 symbols. Internal calls inside each object are renamed too, so the C copy of `bstr_find` calls the C copy of `bstr_splice`.
3. A Rust binary (`/home/user/spike-c2rust/difftest`) depends on the transpiled crate by path. It links, in one `--start-group` group, the renamed C objects, `libmpv.a` and the libraries in `harness-link.rsp`, plus `-lc`.
4. Callees outside the functions under test resolve to the same code for both versions: talloc, `mp_log2`, `mp_round_next_power_of_2` and `mp_append_utf8_bstr` from `libmpv.a`, and libc. The test therefore compares only the translated function bodies. The transpiled crate defines the unrenamed mpv names, so the linker never pulls the misc objects of `libmpv.a`. There were no duplicate-symbol errors.
5. Inputs come from a splitmix64 generator in the test. It has no relation to the code under test. Bytes are biased towards collisions: digits and runs of `0`, case pairs, whitespace, `+ - . _`, UTF-8 lead and continuation bytes (including invalid ones such as `0xc0`, `0xff`, `0xed 0xa0`), and uniform bytes. Strings are 0 to 16 bytes. Needles are often slices of the haystack, sometimes uppercased.
6. Results are compared exactly: integer results, the full `mp_rand_state`, `f64` bit patterns, and for returned `bstr` values the (offset from input start, length) pair. `bstr_sanitize_utf8_latin1` is compared by output bytes.
7. I ran seeds 1, 2 and 3. Each function got 100,000 cases per seed, except as noted below.

Results for seed 1. Seeds 2 and 3 give the same pattern: 0 differences everywhere except the `0b` row (874 and 829 differences).

| function | comparisons | differences | first difference |
|---|---|---|---|
| mp_natural_sort_cmp | 100000 | 0 | none |
| mp_rand_seed (seed != 0) | 100000 | 0 | none |
| mp_rand_next | 800000 | 0 | none |
| mp_rand_next_double (bitwise) | 800000 | 0 | none |
| mp_rand_in_range32 | 600468 | 0 | none |
| full state after each step | 800000 | 0 | none |
| bstr_parse_utf8_code_length (all 256 bytes) | 256 | 0 | none |
| bstrcmp | 100000 | 0 | none |
| bstrcasecmp | 100000 | 0 | none |
| bstr_find | 100000 | 0 | none |
| bstr_case_startswith | 100000 | 0 | none |
| bstrchr | 100000 | 0 | none |
| bstrrchr | 100000 | 0 | none |
| bstrspn | 100000 | 0 | none |
| bstrcspn | 100000 | 0 | none |
| bstr_strip | 100000 | 0 | none |
| bstr_splice (start/end in [-len-3, len+3]) | 100000 | 0 | none |
| bstr_decode_utf8 | 100000 | 0 | none |
| bstr_validate_utf8 | 100000 | 0 | none |
| bstr_sanitize_utf8_latin1 | 100000 | 0 | none |
| bstrtoll, no `0b`/`0B` in input (bases 0, 2, 8, 10, 16, 36) | 77282 | 0 | none |
| bstrtoll, input contains `0b`/`0B` | 22718 | 855 | `"0b0..."`, base 2: C returns 0 and rest at offset 3; Rust returns 0 and rest at offset 1 |

The `bstrtoll` difference is real, and it comes from c2rust:

- glibc 2.39 declares `strtoll` with `__REDIRECT_NTH(strtoll, ..., __isoc23_strtoll)` when `_GNU_SOURCE` is set (`/usr/include/stdlib.h:238`). mpv builds with `-D_GNU_SOURCE`.
- `nm -u` on the C object lists `__isoc23_strtoll` and `__isoc23_vsscanf`. On the transpiled rlib it lists `strtoll` and `vsscanf`. c2rust drops the asm label and binds to the pre-C23 functions.
- C23 `strtol` accepts a `0b`/`0B` prefix for base 0 and base 2. The old function does not. So `bstrtoll("0b11", 0)` is 3 in mpv and 0 in the transpiled Rust.
- `bstr_sscanf` has the same problem with `vsscanf` (`%i` and `%b`). I inferred this from the symbol and did not test it, because `bstr_sscanf` is variadic.
- Any other glibc function that the headers redirect is affected in the same way. I did not audit them.

Not covered:

- `mp_rand_seed(0)`. It seeds from `av_random_bytes` and the clock, so it is not deterministic.
- NULL `bstr` inputs. They are undefined behaviour in the C (`memcmp(NULL, ..., 0)`).
- All of the other 12 files, including the threading code and the file that carries the manual edit.
- The output of c2rust-refactor. Its rewrite of random.rs compiles, but I did not re-run the test on it.

Reproduce:

```sh
cd /home/user/spike-c2rust/difftest && cargo build && ./target/debug/difftest 1
```

The renamed objects are in `difftest/corig/`, and the rename list is `corig/syms.txt`.

## Aeneas readiness (step 6)

I did not run Aeneas or Charon. This is a classification by rules over the syn AST of each function, followed by manual review of a sample. Tools: `tools/rsmetrics` (syn visitor) and `tools/analyze.py`. Per-function output: `/home/user/spike-c2rust/classification.json`.

The classes:

- **A, as is**: no raw pointers, no externs, no `static mut`, no unsafe operations. The only change needed is dropping the `unsafe extern "C"` qualifier and `#[no_mangle]`. I have not verified whether Charon needs these dropped.
- **B, mechanical cleanup**: needs only some of these rewrites:
  - raw pointer parameter to `&T`/`&mut T` (or `Option<&T>` where it is null-checked);
  - `__assert_fail` to `assert!`;
  - `static mut` that was C `const` to `static`/`const`;
  - constant pointer offsets that are dereferenced right away (`*p.offset(2)`) to array indexing;
  - calls to other mpv functions that will be ported too.

  `bstr`-taking functions also need the crate-wide change of `bstr { start: *mut u8, len }` to `&[u8]`.
- **C, structural**: any of these:
  - pointer arithmetic that walks a pointer (`p = p.offset(1)`, `offset_from`);
  - FFI calls to libc, pthread, talloc or FFmpeg;
  - unions;
  - variadics, or calls to variadic externs;
  - atomic intrinsics;
  - `transmute` or function-pointer types;
  - `void*` casts;
  - mutable globals.
- A function is never better than the in-crate functions it calls. This includes calls across modules through the extern redeclarations.

Counts:

| scope | A as is | B mechanical | C structural | total |
|---|---|---|---|---|
| functions from the `.c` files | 4 | 8 | 129 | 141 |
| all emitted functions (with header copies) | 23 | 18 | 182 | 223 |

| file | A | B | C |
|---|---|---|---|
| bstr.c | 1 | 1 | 34 |
| charset_conv.c | 0 | 0 | 5 |
| codepoint_width.c | 2 | 3 | 1 |
| dispatch.c | 0 | 0 | 15 |
| hash.c | 0 | 0 | 1 |
| io_utils.c | 0 | 0 | 2 |
| json.c | 0 | 0 | 13 |
| language.c | 0 | 0 | 4 |
| natural_sort.c | 0 | 0 | 1 |
| node.c | 0 | 0 | 13 |
| path_utils.c | 0 | 0 | 17 |
| random.c | 1 | 4 | 1 |
| rendezvous.c | 0 | 0 | 1 |
| thread_pool.c | 0 | 0 | 7 |
| thread_tools.c | 0 | 0 | 14 |

The A functions are `rotl_u64`, `h_to_i`, `ucdGraphemeDone` and `ucdToCharacterWidth`. The B functions are `splitmix64`, `mp_rand_next`, `mp_rand_next_double`, `mp_rand_in_range32`, `bstr_parse_utf8_code_length`, `is_valid_partial_sequence`, `ucdLookup` and `ucdGraphemeJoins`.

Reasons for class C. One function can have several reasons. "Only via callee" means the function is C only because it calls a C function.

| reason | functions |
|---|---|
| FFI call (libc/pthread/talloc/FFmpeg) | 68 |
| pointer arithmetic (walking) | 47 |
| `void*` cast | 40 |
| only via callee | 32 |
| union access | 14 |
| `transmute` or function pointer | 14 |
| call to variadic extern (`mp_msg`, `ta_asprintf`, ...) | 7 |
| variadic definition or `VaList` | 3 |
| atomic intrinsic | 3 |
| mutable global | 1 |
| pointer-to-integer cast | 1 |

Limits of this classification:

- The rules are syntactic. "Structural" means a person must redesign the function, for example memchr plus pointer subtraction becomes a slice `position`. It does not mean the function cannot be ported.
- "Mechanical" means a known rewrite. It does not mean a tool performs it today: c2rust-analyze failed on 2 of the 4 B functions in random.rs (see below).
- I read random.rs, natural_sort.rs, the `bstr` functions under test and codepoint_width's lookup functions. The rules agree with my reading on those. I did not read the other ~180 functions one by one.

### Excerpts

Easy, class A (random.rs). Only the qualifiers need to go:

```rust
#[inline]
unsafe extern "C" fn rotl_u64(x: uint64_t, k: ::core::ffi::c_int) -> uint64_t {
    return x << k | x >> 64 as ::core::ffi::c_int - k;
}
```

Mechanical, class B (random.rs, `mp_rand_next`). A pointer into a fixed array is used with constant offsets only. It becomes `s.v[1]` with `s: &mut mp_rand_state`:

```rust
pub unsafe extern "C" fn mp_rand_next(mut s: *mut mp_rand_state) -> uint64_t {
    let mut state: *mut uint64_t = &raw mut (*s).v as *mut uint64_t;
    result = rotl_u64(
        (*state.offset(1 as ::core::ffi::c_int as isize)).wrapping_mul(5 as uint64_t),
        7 as ::core::ffi::c_int,
    )
    .wrapping_mul(9 as uint64_t);
    t = *state.offset(1 as ::core::ffi::c_int as isize) << 17 as ::core::ffi::c_int;
    *state.offset(2 as ::core::ffi::c_int as isize) ^= *state.offset(0 as ::core::ffi::c_int as isize);
    // ...
```

Hard, class C (bstr.rs, `bstrchr`). FFI `memchr`, `void*` casts and pointer subtraction. The C is three lines:

```rust
pub unsafe extern "C" fn bstrchr(mut str: bstr, mut c: ::core::ffi::c_int) -> ::core::ffi::c_int {
    if str.len == 0 {
        return -(1 as ::core::ffi::c_int);
    }
    let mut pos: *mut ::core::ffi::c_uchar =
        memchr(str.start as *const ::core::ffi::c_void, c, str.len) as *mut ::core::ffi::c_uchar;
    return (if !pos.is_null() {
        pos.offset_from(str.start) as ::core::ffi::c_long
    } else {
        -(1 as ::core::ffi::c_int) as ::core::ffi::c_long
    }) as ::core::ffi::c_int;
}
```

`mp_natural_sort_cmp` is class C for the same reason. It walks two `*const c_char` pointers (`name1 = name1.offset(1)`) and measures digit runs with `offset_from`.

### c2rust-analyze and c2rust-refactor

Both exist in v0.22.1 when built from git. Neither is in the crates.io install. Both need `nightly-2022-08-08` with `rustc-dev`. I tried them on random.rs, packaged as a one-file crate at `/home/user/spike-c2rust/analyze-try/random`.

`c2rust-analyze --rewrite-mode alongside build` (ownership and pointer-permission inference):

- It ran without crashing and wrote 10,870 lines of debug log. It reported "saw errors in 3 / 6 functions":
  - `mp_rand_seed`: DATAFLOW_INVALID, "TODO: visit Callee::UnknownDef" on the extern `av_random_bytes`;
  - `mp_rand_in_range32`: DATAFLOW_INVALID, on the extern call;
  - `mp_rand_next`: REWRITE_INVALID, in the cast builder.
- What it rewrote: `splitmix64(x: *mut u64)` became `splitmix64<'h0>(x: &'h0 mut u64)`, with an unsafe `splitmix64_shim` for raw-pointer callers. `mp_rand_next_double(s: *mut mp_rand_state)` became `&'h0 mut mp_rand_state`, and it calls `mp_rand_next(core::ptr::addr_of_mut!(*s))`.
- The rewritten file (`lib.new.rs`, used unchanged as `lib.rs` in `analyze-try/random-rewritten`) compiles. Every function is still `unsafe extern "C"`.
- The only function that holds the real logic (`mp_rand_next`) kept its raw pointer and `.offset()` calls. The tool turned 2 pointer parameters into references and nothing else.

`c2rust-refactor`, run with `--cargo --lib -r inplace`:

- Each of `remove_redundant_casts` (78 changed lines), `remove_literal_suffixes` (52), `fix_unused_unsafe` (0), `sink_unsafe` (0), `remove_unnecessary_refs` (0) and `reconstruct_while` (0) ran alone and the result compiles.
- It removes cast noise such as `0 as ::core::ffi::c_int`. Pointers, `unsafe` and the function signatures do not change.
- Chaining transforms in one call (`a \; b \; c`) crashed rustc with an internal compiler error: "index out of bounds" in `rustc_metadata/src/creader.rs:141`.
- I did not try the ownership transforms (`ownership_annotate`, `ownership_split_variants`). They need manual marks.

## What did not work

- `c2rust refactor` and `c2rust analyze` from the crates.io install: "subcommand not found". They work only from a git build, on a 2022 nightly.
- Relative `-o` for `c2rust transpile` (rustfmt step).
- Building the transpiled crate on stable Rust.
- `atomic_bool` translation (fixed by hand, see above).
- Faithful translation of glibc redirected symbols (`strtoll`, `vsscanf`). This produced a measured behaviour difference.
- c2rust-analyze on functions that call externs or do pointer casts (3 of 6 functions in random.rs).
- c2rust-refactor with several transforms chained in one invocation (rustc ICE).

## Not verified

- Whether Charon/Aeneas accept any of this output, including the class A functions as emitted. Another agent is installing Aeneas. All Aeneas-readiness numbers are rule-based estimates, not tool results.
- The behaviour of the 12 files outside the differential test, including the manual atomic edit.
- Whether other redirected glibc symbols (beyond `strtoll` and `vsscanf`) appear in `misc/`.
- Behavioural equivalence of the c2rust-refactor and c2rust-analyze rewrites. They compile, but I did not test them.
- Newer c2rust revisions after v0.22.1.

## Files

- `/home/user/spike-c2rust/misc-c2rust`: transpiled crate (with `README.md`). Pristine output: `misc-c2rust.pristine`.
- `/home/user/spike-c2rust/cc/compile_commands.json`: filtered compile commands.
- `/home/user/spike-c2rust/difftest`: differential test. Results: `difftest-seed{1,2,3}.txt`.
- `/home/user/spike-c2rust/tools/{rsmetrics,cmetrics.py,analyze.py}`: measurement scripts. Outputs: `metrics_rs.json`, `metrics_c.json`, `classification.json`, `analysis.txt`.
- `/home/user/spike-c2rust/analyze-try`: c2rust-analyze and c2rust-refactor trials and logs.
- Logs: `install.log`, `transpile.log`, `build1.log`, `build-tools.log`.
