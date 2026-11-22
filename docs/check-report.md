# Check report: emitted Lean against compiled mpv

`achates check` runs each emitted Lean definition and the C function it was
emitted from on the same generated inputs and compares what they leave
behind. Nothing in it is written per function: what inputs to make and what
to observe is decided from the C signature, the types, and how the body uses
each pointer parameter. Then bugs are planted in a copy of the C to show
that the comparison notices a change in behaviour.

This report says how the check works, what it found on mpv's `misc/`, and
what "checked" does and does not mean.

## How it works

1. **Emit.** The selection is emitted into `WORK/emitted`, as `achates emit`
   would.
2. **Plan.** For each emitted function, every parameter and the result get a
   *shape* (`src/check/shape.rs`), or the function is *not checkable* with
   the reason. A function that needs an external function the check has no
   model for is not checkable ("needs external X").
3. **Generate.** A generator seeded with `--seed` and the function's key
   (SplitMix64; adding a function does not change another's inputs) writes
   `--count` input lines (default 10,000). Integers are drawn from small
   values, the function's own constants (and those of what it calls) plus or
   minus one, the type's edges, powers of two, and uniform bits. Byte buffers
   are drawn from random bytes, printable bytes, special bytes, UTF-8
   sequences (valid, truncated, overlong, surrogate, out of range), the
   function's string constants, and copies, prefixes, suffixes and one-byte
   changes of earlier buffers of the same call; lengths cover 0, 1 to 8, and
   15/16/17, 31/32/33, ..., 127/128/129.
4. **Run the model.** A Lean driver (`WORK/driver`, built by Lake against
   the runtime and the emitted project) reads the same tokens, builds the
   input objects in the model's memory, calls the definition with fuel
   100,000 per loop, and prints one line per input.
5. **Run the C.** A C file includes the function's `.c` file (so static
   functions are reachable) and, for a header function, the unit's main
   file; it is compiled with the real build's flags (`harness.rsp`) and
   linked against `libmpv.a` (`harness-link.rsp`). It reads the same tokens,
   builds the same objects with `malloc` or talloc, calls the function, and
   prints a line in the same form.
6. **Compare** line by line (`src/check/compare.rs`).
7. **Plant bugs** (`src/check/mutate.rs`) and repeat step 5 and 6 for each
   mutant, with the Lean results of the original.

### Input kinds

| Shape | C type | Generated as | Observed after the call |
| --- | --- | --- | --- |
| integer, enum, `bool` | any integer type | see above, wrapped to the type | the value |
| float | `float`, `double` | specials (0, -0, inf, NaN, max, denormal, 2^32, 2^63, ...), random bits of the type, decimals | the bit pattern |
| `bstr` | `struct bstr` by value | null (1 in 24) or a buffer of exactly `len` bytes, embedded NUL allowed; when it sits in an in/out object (a talloc buffer the function may grow), half the time with 1 to 40 bytes of room after it | where `start` points relative to the inputs, and `len`; the bytes if it points elsewhere |
| C string | `char *`, `const char *` | null (1 in 48) or a buffer without NUL plus a terminator | as for `bstr`, or the string's bytes |
| talloc context | `void *` used only as a talloc parent (found by a fixed point over the call graph) | null or a fresh `ta_new_context` | where it points |
| out slot | `T **` that the function only writes | null slot | where the written pointer points |
| in/out object | pointer to a scalar or to a struct of scalars, fixed arrays, `bstr`s and such structs | null (1 in 12) or a heap object; a `bstr` inside one is talloc-allocated, as mpv's are | the object's bytes, member by member |

Every input buffer that is not talloc-allocated is also reported after the
call, byte by byte, so a write through any pointer into the inputs is
compared. A pointer is never printed as an address: it is `null`,
`in<k>+<offset>` into the `k`-th input object, or the bytes it points to
when it points elsewhere (a new allocation). The start of a talloc input
buffer counts as "elsewhere", because `realloc` may or may not move it and
the model always moves it.

A function is not checkable when any of its parameters or its result has no
shape. The reasons the check gives are listed in the results below; the
common ones are unions, function pointers, `void *` used as something other
than a talloc parent, pointers to pointers that are read, pointers used as
arrays with no evident length, and structs with pointer members.

### What each Lean outcome means

| Lean outcome | C run? | Counts as |
| --- | --- | --- |
| `ok` | yes | compared: every word of the two lines must agree |
| `ub` (undefined behaviour) | no | out of contract; counted per function |
| `assert` or `abort` | yes, in a child process | the C must die from `SIGABRT`; counted as out of contract and as "aborts confirmed" |
| `unsupported` (defined C the model does not cover) | no | counted per function; not compared |
| `fuel` (a loop ran 100,000 rounds) | no | **failed check** |
| driver crash, stall (30 s without output), or memory over 4 GiB | no | **failed check** |

The C harness also fails the input when the call crashes, runs past 10 s
(`alarm`), or exceeds its CPU or memory limit; each of those differs from
any Lean line and so is a disagreement.

A function whose inputs are nearly all out of contract would pass without
showing anything, so the share is printed per function and kept in the JSON.

Floats agree when their bit patterns are equal, except that any NaN agrees
with any NaN (C fixes neither payload nor sign of a NaN result), and a zero
agrees with a zero of either sign (mpv is built with `-fno-signed-zeros`,
which lets the compiler choose). A byte the model holds as indeterminate
(`??`) agrees with any byte. Nothing else is relaxed.

### Status per function

- **checked and sensitive**: the two agreed on every compared input, and at
  least one planted bug made them differ.
- **checked, agreement not shown to be sensitive**: they agreed, but no
  planted bug was caught (often because the function's text gives no
  mutation point, as in a one-line wrapper).
- **disagrees**: at least one input gave different results, or the model
  failed (out of fuel, stall). The first such input is reported with its
  tokens and both lines.
- **not checkable**: with the reason.
- **not emitted**: with the emitter's reason.

### Planted bugs

The mutation operators work on the tokens of the function's text and of its
direct callees defined in the same files the harness compiles (a callee in
another file is linked from `libmpv.a`, and a changed copy of its file would
define its neighbours twice). Comments, preprocessor lines and literals are
never changed. Operators: comparison (`<` and `<=`, `>` and `>=`, `==` and
`!=`), logical (`&&` and `||`), arithmetic (`+` and `-` where binary, `+=`
and `-=`, `++` and `--`, `<<` and `>>`, `/` to `*`, `%` to `/`), constant
(an integer literal plus one, in its own notation), statement (an
expression statement on a line of its own replaced by `;`). At most 24 per
function, picked by a seeded shuffle; the callees fill only what the
function's own text leaves.

A mutant is **caught** when some input's C line differs from the model's
line for the original. A mutant whose only differences are calls that ran
past the 10 s limit counts as caught only if the original's slowest call
took less than a quarter of the limit; the summary says how many were caught
that way. Mutants that do not compile are counted and not run. Survivors are
listed with file, line, operator and text.

### Resources and isolation

Each harness and driver runs in its own process group under `ulimit -v`
(4 GiB) and `ulimit -t`; the group is killed when the run ends or stalls, so
a child forked for an abort-expecting call cannot outlive it.

### Models of external functions

A function that calls something outside the selection needs a model of it
in Lean. The runtime's own models (`memcpy`, `memcmp`, `strlen`, `strchr`,
talloc, `__assert_fail`, `abort`, ...; see the back end report) are used as
they are. The check adds executable models for externals that are fully
specified and cheap (`lean/AchatesCheck/Models.lean`), supplied as
instances of the `Ext` classes, and only where the C declaration maps to
the model's Lean type. They are not part of the runtime and no emitted
definition refers to them, so agreement is evidence about the emitted
definition *and* the model together.

| External | Model |
| --- | --- |
| `strncasecmp`, `strcasecmp` | C locale; glibc's result, the difference of the lower-cased bytes |
| `memrchr` | GNU `memrchr` |
| `mp_log2`, `mp_round_next_power_of_2` | mpv's `common/common.c` |
| `ta_xstrdup`, `ta_xstrndup` | talloc's `ta/ta_utils.c`; allocation does not fail |
| `strtoll` | glibc's `__isoc23_strtoll`, which the compiled C calls (`0b` prefix accepted); `errno` not modelled; a base outside 0 and 2 to 36 is `unsupported` |

Any other external makes the function "not checkable: needs external X".

## Running it

```sh
make check-misc        # all of misc/, writes pilot/misc/check.json and check.txt
make check-misc-fast   # six functions, 2,000 inputs, 8 mutants each; part of make ci
```

`achates check --help` lists the options: `--count` (default 10,000),
`--seed` (default 1), `--mutants` (default 24, 0 skips them), `--function`
(repeatable), `--jobs`, `--cflags-file`, `--link-file`, `--json`, `--work`.
`make check-misc-fast` takes about 1.5 minutes (half of it building the
Lean driver); `make ci` runs it whenever the mpv build is present, and
passes with Lean's bundled `clang` first or last on `PATH` (Achates
resolves `clang` and `cc` to absolute paths and tries each on a small
program; `ACHATES_CLANG` and `ACHATES_CC` override the choice). The
command exits non-zero when any function disagrees. The JSON has no
times in it, so two runs with the same seed and inputs give the same file.

## Results on `misc/`

Run: `make check-misc`, seed 1, 10,000 inputs per function, at most 24
mutants per function, 4 jobs on 4 cores, 15 GiB of memory. Wall time
26 min 35 s (1,642 s in the check itself; building the Lean driver from
cold adds about 70 s). Result: `pilot/misc/check.json`, summary in
`pilot/misc/check.txt`.

### Counts by status

Of the **135** functions of `misc/` that Achates emits (141 selected, 6 not
emitted):

| Status | Functions |
| --- | ---: |
| checked and sensitive | 54 |
| checked, agreement not shown to be sensitive | 0 |
| disagrees | 1 (`add_indent`: out of fuel, see below) |
| not checkable | 80 |

and the 6 not emitted (`bstr_sscanf`, `bstr_xappend_asprintf`,
`bstr_xappend_vasprintf`: variadic; `mp_match_lang`, `node_array_add`,
`node_map_badd`: unsequenced operands that may interfere).

Of the **33** header functions they reach: 18 checked and sensitive, 4
checked but not shown sensitive (`bstrdup0` and `bstrto0` have no mutation
point in their own text and call only modelled talloc functions;
`bstr_eatstart0` and `bstr_find0` each have one mutant, a callee's, that
survived), 0 disagree, 11 not checkable.

**Inputs:** 770,000 run through the model for 77 functions; 713,517 compared
with the compiled C and equal; 7,476 failed assertions or aborts in the
model confirmed as `SIGABRT` in C; 39,484 undefined in the model (not run in
C); 8,056 unsupported by the model (not run in C); 1,467 failed checks, all
`fuel` in `add_indent`.

### Why functions are not checkable

A function can have several reasons. By number of functions (of the 91
not-checkable selected and header functions):

| Functions | Reason |
| ---: | --- |
| 30 | needs external `pthread_mutex_lock` (and 30 `pthread_mutex_unlock`, 20 `pthread_cond_broadcast`, 19 `pthread_cond_destroy`, 18 `pthread_mutex_destroy`, 10 `pthread_cond_wait`, 9 `pthread_join`, ...) |
| 26 | a `void *` parameter that is not only handed to talloc as a parent |
| 18 | a pointer to `struct mpv_node`, whose member `u` is a union |
| 13 | a pointer to `struct mp_dispatch_queue`, which has pointer members |
| 12 | a function pointer parameter |
| 12 | `char **` that the function reads or passes on |
| 9 | a pointer to `struct mp_cancel`, whose `lock` is a `pthread_mutex_t` (a union) |
| 8 | needs `cancel_destroy` (a function of the selection that is not checkable itself) |
| 8, 7, 7 | needs `close`, `write`, `__errno_location` (errno) |
| 7 | needs `thread_pool_dtor` |
| 6, 6 | needs `bstr_xappend_asprintf`, `node_map_badd` (not emitted) |
| 5 each | needs `clock_gettime`, `pthread_create`, `pthread_self`, `stat`, ... |
| 3 | needs `strtod` |
| 1 or 2 | file system and process calls (`open`, `getcwd`, `getenv`, `mkdir`, `realpath`, `rename`, `unlink`, `fdopen`, `fwrite`, ...), libavutil hashing and random bytes, `mp_msg`, `strncpy`, pointers to bytes without an evident length (`write_json_str`, 2 functions), pointers used as arrays without an evident length (2) |

The full list, with every reason, is in `pilot/misc/check.txt`. The
threading half of `misc/` (`dispatch.c`, `thread_pool.c`, `thread_tools.c`,
`rendezvous.c`, `jsonrpc.c` and the like) is out of reach until there are
models of mutexes and condition variables, which the back end deliberately
does not assume away.

### Per function

Out of contract is undefined plus aborts confirmed, as a share of inputs.
Mutants: caught / compiled (generated, set aside as equivalent).

| Function | Where | Status | Inputs | Compared | Aborts confirmed | UB | Unsupported | Out of contract | Mutants caught / compiled (generated, equivalent) | Survivors |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| `bstrcmp` | misc/bstr.c:30 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 6 / 8 (8, 0) | 2 |
| `bstrcasecmp` | misc/bstr.c:47 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 6 / 8 (8, 0) | 2 |
| `bstrchr` | misc/bstr.c:64 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 2 / 2 (3, 0) | 0 |
| `bstrrchr` | misc/bstr.c:72 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 2 / 2 (10, 7) | 0 |
| `bstrcspn` | misc/bstr.c:87 | sensitive | 10000 | 9809 | 0 | 191 | 0 | 1.9% | 4 / 4 (4, 0) | 0 |
| `bstrspn` | misc/bstr.c:96 | sensitive | 10000 | 9823 | 0 | 177 | 0 | 1.8% | 4 / 4 (4, 0) | 0 |
| `bstr_find` | misc/bstr.c:105 | sensitive | 10000 | 9655 | 0 | 345 | 0 | 3.5% | 9 / 20 (20, 0) | 11 |
| `bstr_lstrip` | misc/bstr.c:113 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 5 / 5 (5, 0) | 0 |
| `bstr_strip` | misc/bstr.c:122 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 11 / 11 (11, 0) | 0 |
| `bstr_split` | misc/bstr.c:130 | sensitive | 10000 | 9440 | 0 | 560 | 0 | 5.6% | 12 / 24 (24, 0) | 12 |
| `bstr_split_tok` | misc/bstr.c:147 | sensitive | 10000 | 7923 | 0 | 2077 | 0 | 20.8% | 17 / 24 (24, 0) | 7 |
| `bstr_splice` | misc/bstr.c:158 | sensitive | 10000 | 5816 | 0 | 4184 | 0 | 41.8% | 16 / 16 (16, 0) | 0 |
| `bstrtoll` | misc/bstr.c:175 | sensitive | 10000 | 3578 | 0 | 397 | 6025 | 4.0% | 9 / 12 (13, 0) | 3 |
| `bstr_splitchar` | misc/bstr.c:203 | sensitive | 10000 | 9633 | 0 | 367 | 0 | 3.7% | 13 / 24 (24, 0) | 11 |
| `bstr_strip_linebreaks` | misc/bstr.c:213 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 14 / 24 (24, 0) | 10 |
| `bstr_eatstart` | misc/bstr.c:223 | sensitive | 10000 | 8746 | 0 | 1254 | 0 | 12.5% | 1 / 1 (1, 0) | 0 |
| `bstr_eatend` | misc/bstr.c:231 | sensitive | 10000 | 8733 | 0 | 1267 | 0 | 12.7% | 2 / 2 (2, 0) | 0 |
| `bstr_lower` | misc/bstr.c:239 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 4 / 4 (4, 0) | 0 |
| `bstr_parse_utf8_code_length` | misc/bstr.c:256 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 12 / 12 (12, 0) | 0 |
| `bstr_decode_partial_utf8` | misc/bstr.c:264 | sensitive | 10000 | 9154 | 0 | 846 | 0 | 8.5% | 22 / 24 (24, 0) | 2 |
| `bstr_decode_utf8` | misc/bstr.c:295 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 22 / 24 (24, 0) | 2 |
| `bstr_split_utf8` | misc/bstr.c:303 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 13 / 24 (24, 0) | 11 |
| `bstr_validate_utf8` | misc/bstr.c:314 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 20 / 24 (24, 0) | 4 |
| `resize_append` | misc/bstr.c:361 | sensitive | 10000 | 5619 | 2111 | 835 | 1435 | 29.5% | 7 / 16 (16, 0) | 9 |
| `bstr_xappend` | misc/bstr.c:374 | sensitive | 10000 | 9218 | 0 | 782 | 0 | 7.8% | 10 / 24 (24, 0) | 14 |
| `bstr_case_startswith` | misc/bstr.c:415 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 15 / 24 (24, 0) | 9 |
| `bstr_case_endswith` | misc/bstr.c:421 | sensitive | 10000 | 9581 | 0 | 419 | 0 | 4.2% | 8 / 12 (12, 0) | 4 |
| `h_to_i` | misc/bstr.c:427 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 17 / 17 (17, 0) | 0 |
| `bstr_decode_hex` | misc/bstr.c:439 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 22 / 24 (24, 0) | 2 |
| `bstr0` | misc/bstr.h:61 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 1 / 1 (1, 0) | 0 |
| `bstr_cut` | misc/bstr.h:226 | sensitive | 10000 | 9587 | 0 | 413 | 0 | 4.1% | 9 / 12 (12, 0) | 3 |
| `bstr_endswith` | misc/bstr.h:250 | sensitive | 10000 | 9525 | 0 | 475 | 0 | 4.8% | 3 / 3 (3, 0) | 0 |
| `bstr_endswith0` | misc/bstr.h:257 | sensitive | 10000 | 9725 | 0 | 275 | 0 | 2.8% | 3 / 4 (4, 0) | 1 |
| `bstr_startswith` | misc/bstr.h:238 | sensitive | 10000 | 9517 | 0 | 483 | 0 | 4.8% | 1 / 1 (1, 0) | 0 |
| `bstrcasecmp0` | misc/bstr.h:280 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 7 / 9 (9, 0) | 2 |
| `bstrcmp0` | misc/bstr.h:262 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 7 / 9 (9, 0) | 2 |
| `bstrdup0` | misc/bstr.h:39 | not shown sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 0 / 0 (0, 0) | 0 |
| `mp_isspace` | misc/ctype.h:8 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 11 / 11 (11, 0) | 0 |
| `mp_tolower` | misc/ctype.h:16 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 5 / 5 (5, 0) | 0 |
| `mp_isupper` | misc/ctype.h:10 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 3 / 3 (3, 0) | 0 |
| `mp_charset_is_utf8` | misc/charset_conv.c:41 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 6 / 6 (6, 0) | 0 |
| `mp_charset_is_utf16` | misc/charset_conv.c:47 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 1 / 1 (1, 0) | 0 |
| `ms_bom_guess` | misc/charset_conv.c:57 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 2 / 4 (4, 0) | 2 |
| `bstr_startswith0` | misc/bstr.h:245 | sensitive | 10000 | 9761 | 0 | 239 | 0 | 2.4% | 1 / 2 (2, 0) | 1 |
| `ucdLookup` | misc/codepoint_width.c:617 | sensitive | 10000 | 6733 | 0 | 3267 | 0 | 32.7% | 13 / 14 (14, 0) | 1 |
| `ucdGraphemeJoins` | misc/codepoint_width.c:625 | sensitive | 10000 | 748 | 0 | 9252 | 0 | 92.5% | 5 / 5 (5, 0) | 0 |
| `ucdGraphemeDone` | misc/codepoint_width.c:631 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 2 / 2 (2, 0) | 0 |
| `ucdToCharacterWidth` | misc/codepoint_width.c:635 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 2 / 2 (2, 0) | 0 |
| `is_valid_partial_sequence` | misc/codepoint_width.c:664 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 19 / 24 (24, 0) | 5 |
| `term_disp_width` | misc/codepoint_width.c:680 | sensitive | 10000 | 9743 | 0 | 257 | 0 | 2.6% | 21 / 24 (24, 0) | 3 |
| `bstr_eatstart0` | misc/bstr.h:290 | not shown sensitive | 10000 | 8951 | 0 | 1049 | 0 | 10.5% | 0 / 1 (1, 0) | 1 |
| `ta_oom_s` | ta/ta.h:174 | sensitive | 10000 | 9778 | 222 | 0 | 0 | 2.2% | 1 / 1 (1, 0) | 0 |
| `add_indent` | misc/json.c:285 | **disagrees** | 10000 | 7875 | 0 | 658 | 0 | 6.6% | not run | - |
| `mp_isalnum` | misc/ctype.h:14 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 5 / 5 (5, 0) | 0 |
| `mp_isalpha` | misc/ctype.h:13 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 7 / 7 (7, 0) | 0 |
| `mp_isdigit` | misc/ctype.h:12 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 3 / 3 (3, 0) | 0 |
| `mp_islower` | misc/ctype.h:11 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 3 / 3 (3, 0) | 0 |
| `mp_natural_sort_cmp` | misc/natural_sort.c:26 | sensitive | 10000 | 9583 | 0 | 417 | 0 | 4.2% | 20 / 21 (24, 0) | 1 |
| `bstr_equals0` | misc/bstr.h:275 | sensitive | 10000 | 9704 | 0 | 0 | 296 | 0.0% | 6 / 6 (6, 0) | 0 |
| `bstr_equals` | misc/bstr.h:267 | sensitive | 10000 | 9700 | 0 | 0 | 300 | 0.0% | 5 / 5 (5, 0) | 0 |
| `bstrto0` | misc/bstr.h:45 | not shown sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 0 / 0 (0, 0) | 0 |
| `mp_basename_bstr` | misc/path_utils.c:42 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 5 / 5 (17, 12) | 0 |
| `mp_basename` | misc/path_utils.c:62 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 5 / 5 (17, 12) | 0 |
| `mp_dirname` | misc/path_utils.c:67 | sensitive | 10000 | 9803 | 0 | 197 | 0 | 2.0% | 2 / 2 (3, 0) | 0 |
| `mp_path_strip_trailing_separator` | misc/path_utils.c:85 | sensitive | 10000 | 9778 | 0 | 222 | 0 | 2.2% | 7 / 8 (8, 0) | 1 |
| `split_ext` | misc/path_utils.c:96 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 13 / 15 (24, 8) | 2 |
| `mp_strip_ext` | misc/path_utils.c:113 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 10 / 14 (15, 0) | 4 |
| `mp_get_ext` | misc/path_utils.c:120 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 8 / 12 (13, 0) | 4 |
| `mp_path_is_absolute` | misc/path_utils.c:125 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 2 / 2 (9, 7) | 0 |
| `mp_is_url` | misc/path_utils.c:289 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 15 / 15 (15, 0) | 0 |
| `mp_split_proto` | misc/path_utils.c:309 | sensitive | 10000 | 10000 | 0 | 0 | 0 | 0.0% | 16 / 17 (17, 0) | 1 |
| `bstr_find0` | misc/bstr.h:285 | not shown sensitive | 10000 | 9844 | 0 | 156 | 0 | 1.6% | 0 / 1 (1, 0) | 1 |
| `rotl_u64` | misc/random.c:31 | sensitive | 10000 | 4494 | 0 | 5506 | 0 | 55.1% | 4 / 4 (4, 0) | 0 |
| `splitmix64` | misc/random.c:36 | sensitive | 10000 | 9164 | 0 | 836 | 0 | 8.4% | 12 / 12 (12, 0) | 0 |
| `mp_rand_next` | misc/random.c:67 | sensitive | 10000 | 9181 | 0 | 819 | 0 | 8.2% | 23 / 23 (24, 0) | 0 |
| `mp_rand_next_double` | misc/random.c:85 | sensitive | 10000 | 9158 | 0 | 842 | 0 | 8.4% | 24 / 24 (24, 0) | 0 |
| `mp_rand_in_range32` | misc/random.c:92 | sensitive | 10000 | 4437 | 5143 | 420 | 0 | 55.6% | 24 / 24 (24, 0) | 0 |


The high out-of-contract shares have one cause each, read from the model's
reasons: `ucdGraphemeJoins` (92.5%) indexes `s_joinRules[state]` with any `int`
`state`, while its caller passes only the 0 to 3 its own tables give;
`ucdLookup` (32.7%) indexes its first table with `cp >> 11` for code points
above U+10FFFF, which its callers never pass;
`rotl_u64` (55%) shifts by 64 for `k = 0` and by more for `k > 64`;
`mp_rand_in_range32` (55%) has `min >= max`, an assertion; `bstr_splice`
(43%) moves `start` past the end; `resize_append` (30%) aborts on sizes
near `SIZE_MAX`; `bstr_split_tok` (21%) gets null out-pointers. The rest
are mostly null `bstr`s passed to `memcmp` or pointer arithmetic, which C
leaves undefined even with length 0.

## Every disagreement and failure, with its root cause

The final run has no input on which the model and the compiled C give
different results. Everything below was found by the check on the way
there, on `misc/` or on its fixtures, and is fixed or classified.

| # | Where | Input | Model | C | Root cause | Change |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `resize_append` | one of the first 20 inputs of the first run, `C P H<bytes> <append_min>`; the first six were run one by one and were fine, so it was one whose `size + append_min` fell between the machine's memory and 2^47 | the driver was killed by the kernel for lack of memory | not run then; for such a request `talloc_realloc_size` fails and mpv's `ta_xrealloc` aborts, unless the machine has that much memory | **Achates runtime**: `Mem.alloc` held any request below 2^47 bytes as an array of that many bytes. The named assumption `alloc-succeeds` is false for such a request on this machine | The model now makes no allocation of 2^26 bytes or more; such a request is `unsupported`. Not made exact: whether a large request succeeds depends on the machine's memory, which C does not fix |
| 2 | `add_indent` | `P H 100000` (and every large `indent`) | correct result after 2 minutes; 10,000 inputs did not finish in 15 minutes | correct result in microseconds | **Achates runtime**: `Mem.alloc` read the block count after pushing the new block, which kept the old array alive across the push and copied all blocks on every allocation, so a loop of calls with locals was quadratic | Read the count first. Regression test `many_calls_do_not_make_the_model_quadratic` |
| 3 | `add_indent` | `P H0a344234 1637373116` (1,467 inputs with `indent` above 100,000) | `fuel` | not run | **Limit of the check**: `add_indent` appends `indent` spaces one call at a time; an `int` near 2^31 needs that many rounds, and the model's fuel is 100,000 rounds per loop | None. By the rule, out of fuel is a failed check, so `add_indent` is reported as **disagrees**. On the 7,875 inputs that finished, model and C agree |
| 4 | all functions | any | | `cc1: fatal error: target/check/run/.../harness.c: No such file` | **Harness**: the harness is compiled in the unit's directory, and the work directory was relative | Paths made absolute |
| 5 | `mp_rand_in_range32` mutants | inputs with `min >= max` | `assert` | the forked child kept running after its parent was killed (two processes found at 100% CPU for 22 minutes by the coordinator) | **Harness**: a call expected to abort runs in a forked child; killing the harness at its time limit left the child running | Every run is in its own process group, killed as a whole at the end; `ulimit -t` and `ulimit -v` apply to every process it forks; `alarm` ends each call after 10 s, in parent and child |
| 6 | all with talloc inputs | mutants | | | **Harness**: the equivalence test (below) compared preprocessed text, which contains the harness's own path through talloc's debugging macros, and then compared against a stale file from an earlier run | Path normalised; a function's run directory is cleared before it is checked |
| 7 | fixture tests | | | `CLOCK_MONOTONIC undeclared` | **Harness**: with `-std=c11` the C library hides POSIX | The harness defines `_POSIX_C_SOURCE` before its first include unless the build defines `_GNU_SOURCE` |

No disagreement was traced to a wrong external model or to real mpv
misbehaviour.

### Achates bugs fixed

| Bug | Fix | Test that would have caught it |
| --- | --- | --- |
| `Mem.alloc` copied the whole block array on each allocation (quadratic run time for loops that call functions with locals) | `lean/Achates/Memory.lean`: read the block count before the push | `check::tests::many_calls_do_not_make_the_model_quadratic` (fixture `many_calls`, 90,000 calls): 45 s and a stalled driver with the old code, under 1 s with the fix |
| The model tried to hold allocations up to 2^47 bytes, exhausting the machine's memory | `Mem.allocLimit = 2^26`, used by `Mem.alloc` and `ta_realloc_size`; the `alloc-succeeds` assumption text in every emitted definition says so (`pilot/misc` re-emitted) | `resize_append` on `misc/` in `make check-misc`; no small fixture, because the old failure is the machine running out of memory |

Neither changes an emitted definition's text other than its assumption
comment; both change what the runtime does.

## Sensitivity

| | Mutants |
| --- | ---: |
| candidates (every change the operators can make in the checked functions and their same-file callees) | 1,043 |
| generated (at most 24 per function) | 854 |
| set aside as equivalent (preprocessed text unchanged) | 46 |
| compiled | 797 |
| did not compile | 11 |
| **caught** | **647** (81% of compiled) |
| caught only by running past the time limit | 0 |
| survived | 150 |

The 46 equivalent mutants are all in `#if` branches this build does not
compile: `HAVE_DOS_PATHS` in `mp_basename_bstr` (32, counted once per
function whose run planted them) and `mp_path_is_absolute` (7), and the
`#else` of `HAVE_MEMRCHR` in `bstrrchr` (7). The argument is mechanical: the
preprocessor's output, with the copy's path read as the original's, equals
the original's, so the compiler sees the same program.

Of the 150 survivors, 104 are in a callee, planted while checking a caller:
68 in `bstr_splice` (callers pass it only non-negative, in-range bounds, so
its negative-index and clamping code is never reached from them; checked on
its own, `bstr_splice` caught all 16 of its mutants), 12 in
`resize_append`, 7 in `split_ext`, 6 in `bstrcasecmp`, 4 in `bstr0`, and
11 more. They are not examined one by one and should be read as
**unexplained** beyond that.

The 46 survivors in the checked function's own text, each examined:

| Function | Line | Change | Why it survives |
| --- | --- | --- | --- |
| `bstrcmp` | bstr.c:33 | `&&` → `\|\|` | Equivalent on glibc: with one length 0, `memcmp` is called with length 0 and returns 0, as not calling it does |
| `bstrcmp` | bstr.c:39 | `>` → `>=` | Equivalent: equal lengths returned 0 on line 37 |
| `bstrcasecmp` | bstr.c:50, 56 | same two | Same arguments, with `strncasecmp` |
| `bstrtoll` | bstr.c:178 | `51` → `52` | Equivalent: a larger buffer, of which at most 51 bytes are used |
| `bstrtoll` | bstr.c:179 | `50` → `51` | Not equivalent (and writes `buf[51]`, out of bounds): differs only for a string with more than 50 bytes of number after leading blanks. **Generator gap**: number text is at most 29 bytes |
| `bstrtoll` | bstr.c:181 | `0` → `1` | Equivalent: `strtoll` stops at the byte 1 as at the byte 0, and nothing reads past it |
| `bstr_decode_partial_utf8` | bstr.c:272, 288 | constants | unexplained |
| `bstr_validate_utf8` | bstr.c:321 (4) | the guess for a cut-off sequence, `bytes > 1 && s.len < 6` | unexplained; the guess only changes which of two negative codes is returned for some invalid tails |
| `resize_append` | bstr.c:364 | assertion dropped | Unreachable from inputs the harness can build: a `bstr` it makes never has `len` above its allocation's size |
| `resize_append` | bstr.c:365–368 (8) | growth amount and the `SIZE_MAX / 2` limit | **Observation gap**: they change only how much room is allocated, which the check does not observe (a talloc buffer's start is "elsewhere" and its size is not printed), or the limit above 2^63, where the model is `unsupported` and C aborts either way |
| `bstr_xappend` | bstr.c:378 | `+ 1` → `+ 2` | Observation gap: one more byte of room |
| `bstr_xappend` | bstr.c:381 | terminator dropped | **Observation gap**: the byte after `len` of a talloc buffer is not observed. A real difference to callers that use the buffer as a C string |
| `bstr_decode_hex` | bstr.c:444 | `/` → `*` (initial capacity) | Observation gap: room only |
| `bstr_decode_hex` | bstr.c:453 | `talloc_free(arr)` dropped | Equivalent in what can be observed: a leak |
| `bstr_cut` | bstr.h:230 (2), 233 | `<` → `<=`, `0` → `1`, `>` → `>=` | Equivalent: at the boundary both branches set `n` to the value it has |
| `ms_bom_guess` | charset_conv.c:59 (2) | loop bound 3 → 4 | Reads `utf_bom[3]`, out of bounds (undefined); survives because the neighbouring memory is not a prefix of any input |
| `ucdLookup` | codepoint_width.c:622 | `cp >> 0` → `cp << 0` | Equivalent: a shift by 0 |
| `is_valid_partial_sequence` | codepoint_width.c:670–676 (5) | range bounds of UTF-8 continuation checks | unexplained; probably inputs that hit exactly the bounds (0x80, 0x90, 0x9F, 0xBF) in that position are too rare |
| `term_disp_width` | codepoint_width.c:737, 750, 761 | constants, `w = 2` dropped | unexplained |
| `mp_natural_sort_cmp` | natural_sort.c:28 | `&&` → `\|\|` | probably equivalent (when one string ends, the next comparison in the loop returns the same result as the code after it); not proven |
| `mp_path_strip_trailing_separator` | path_utils.c:88 | `len > 0` → `len >= 0` | Reads `path[-1]`, out of bounds (undefined); survives because that byte is not `/` |
| `split_ext` | path_utils.c:105 (2) | `dot_pos < 0` → `<= 0` / `< 1` | Equivalent: leading dots were removed, so a dot is never at 0 |
| `mp_strip_ext` | path_utils.c:115 | `{0}` → `{1}` | Equivalent: `root.start` is not used when `root.len` is 0 |
| `mp_split_proto` | path_utils.c:314 | `&(bstr){0}` → `{1}` | Equivalent: a dummy target that is written and dropped |

Not one survivor was deleted or hidden; all are in `check.json` with file,
line, column and text.

## Named assumptions

| Assumption | Exercised? | Outcome |
| --- | --- | --- |
| `cmp-byte-difference` (`memcmp`, `strcmp`, `strncmp` return the byte difference; C fixes only the sign) | yes: 24 checked functions carry it; `bstrcmp` and `bstrcmp0` return `memcmp`'s result directly, with results such as 135 and -160 on 10,000 inputs each | **confirmed** for glibc on x86-64 as compiled here. The model was kept exact for this platform rather than the comparison relaxed to signs, because the Rust side will be compared against this C, not against every C |
| `talloc-model` | yes: `resize_append`, `bstr_xappend`, `bstr_decode_hex`, `add_indent` carry it; `bstrdup0` and `bstrto0` use the check's `ta_xstrndup` model | consistent on every compared input (allocation, reallocation, parent ownership; destructors were not reached) |
| `alloc-succeeds` | yes | **refuted** for requests of terabytes (row 1 above); the model now covers only requests below 2^26 bytes and calls larger ones `unsupported` |
| `signed-zeros` (`-fno-signed-zeros`) | yes: `mp_rand_next_double`, 9,158 compared | consistent; no zero results of either sign arose, so the relaxation was not needed |
| `sequential-atomics` | no | the 11 functions are not checkable (mutexes, threads) |
| `external-order` | no | the 3 functions are not checkable |
| glibc's C23 `strtoll` (`0b` accepted; `docs/research/c2rust.md`) | yes: 9 of `bstrtoll`'s inputs start with `0b` or `0B`, a binary digit, and base 0 or 2 | **confirmed**: the C23 model agrees on all; with the C17 model (`AchatesCheck.Models.strtollC17`) put in its place by hand, the check reports 9 disagreements, the first `"\t 0B0012..."` base 0, where C17 reads 0 and C23 reads 1 |

## Suspected mpv misbehaviour

None found by the check. Recorded for completeness, already known and
visible here as undefined inputs, not as disagreements: `rotl_u64(x, 0)`
shifts right by 64 (`misc/random.c:33`), undefined in C; the model reports
it on every input with `k = 0`.

## What "checked" means

A function reported **checked and sensitive** ran on 10,000 generated
inputs; on every input the model gave a defined result for, the compiled
mpv C (built with mpv's own flags, linked against `libmpv.a`) returned the
same value and left every observed object the same; every assertion
failure in the model was an abort in C; and at least one planted bug in the
C changed what the check saw.

It does **not** mean:

- that the two agree on all inputs: only on these, from one generator, with
  its gaps (lengths up to 129 bytes, number text up to 29 bytes, talloc
  room up to 40 bytes, one input object per pointer, never aliasing between
  parameters);
- anything about inputs the model calls undefined or unsupported: those are
  not run in C at all, and for some functions they are most inputs;
- that what is not observed agrees: the room in a talloc buffer, the byte
  after a `bstr`'s length, `errno`, timing, and output through anything
  other than parameters and the result;
- that the external models are right beyond what the inputs reached;
- anything about the 80 not-checkable functions, which include all of the
  threading code.

A survivor in the table above is a place where a bug could hide from this
check; an unexplained one is a place nobody has shown it cannot.

## What to build next

1. Observe a talloc buffer's size and the byte after a `bstr`'s length, so
   that the capacity and terminator survivors become catchable (or are
   shown equivalent for callers).
2. Models of `pthread_mutex_*` and `pthread_cond_*` for one thread (lock
   and unlock as no-ops that check the protocol), which alone would bring
   about 30 functions into reach; then structs with pointer members, built
   from the same shapes.
3. Inputs with aliasing between pointer parameters, and lengths beyond 129
   bytes for functions with fixed buffers (`bstrtoll`'s 51 bytes).
4. A cheaper loop model in the runtime, so that `add_indent`-style inputs
   can run further than 100,000 rounds; and a generator that bounds count
   parameters it can see are loop bounds, recorded per function, instead
   of a blanket limit.
5. Make the 104 unexamined callee survivors and the unexplained own ones
   either caught (targeted inputs) or argued equivalent.
