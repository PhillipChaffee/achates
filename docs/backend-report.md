# Back end report

The back half of Achates turns the typed intermediate representation (IR)
of the front end into Lean 4 definitions, and provides the Lean runtime
those definitions run on. This report gives the design, what a reader must
trust, the result on mpv's `misc/`, the tests, how the output relates to
Aeneas output, and the known gaps.

```sh
achates emit --compile-commands PATH --select misc/ --out DIR --name Misc
make ci      # lint, cargo test, build lean/, re-emit and build pilot/misc
```

Where things are:

| Path | Content |
| --- | --- |
| `lean/Achates/` | The runtime, a Lake project on Lean 4.36.0 with no dependencies (no Mathlib, no Aeneas library). 859 lines. |
| `src/emit/` | The emitter. |
| `pilot/misc/` | The emitted project for mpv's `misc/`, with `status.json` and `summary.txt`. |
| `pilot/misc-checks/` | Hand-written Lean checks on the emitted `misc/` definitions. |
| `tests/fixtures/fidelity.c` | The C fixture of the fidelity tests. |

## Result in one paragraph

Of the 141 functions of `misc/`, **135 are emitted**; of the 33 header
functions they reach, **33 are emitted**. The emitted project (168
definitions, 9,900 lines of Lean) builds with `lake build --wfail` in 20 s
from clean on 4 cores, with no `sorry`, `axiom`, `partial`, `unsafe`,
`implemented_by` or `native_decide` in it or in the runtime. 6 functions are
refused, each with its reasons. 94 fidelity cases run the same C function as
compiled C and as emitted Lean; all 94 agree or report the expected
undefined behaviour. Nothing was checked against real mpv except
`mp_natural_sort_cmp` on 196 input pairs and `splitmix64` on one seed (see
"Checks on `misc/`"); checking the rest is the next task.

## Design

### Shape of an emitted definition

One C function becomes one Lean definition in the monad `M`, in a `do`
block. Two verbatim examples from `pilot/misc/Misc/Misc/Random_c.lean`, the
first scalar, the second using memory:

```lean
/-- C function `rotl_u64`, ../.mpv/misc/random.c:31.
-/
def rotl_u64 (fuel : Nat) (x : U64) (k : I32) : M U64 := do
  let mut x_v : U64 := x
  let mut k_v : I32 := k
  let t1 : U64 ← UInt.shl x_v (SInt.toInt k_v)
  let t2 : I32 ← SInt.sub (64 : I32) k_v
  let t3 : U64 ← UInt.shr x_v (SInt.toInt t2)
  return (UInt.bor t1 t3)

/-- C function `splitmix64`, ../.mpv/misc/random.c:36.
-/
def splitmix64 (fuel : Nat) (x : Ptr) : M U64 := do
  let mut x_v : Ptr := x
  let t1 : U64 ← Mem.load U64 x_v
  let t2 : U64 := (t1 + (11400714819323198485 : U64))
  Mem.store x_v t2
  let mut z_1 : U64 := t2
  let t3 : U64 ← UInt.shr z_1 (SInt.toInt (30 : I32))
  let t4 : U64 := ((UInt.bxor z_1 t3) * (13787848793156543929 : U64))
  z_1 := t4
  ...
  return (UInt.bxor z_1 t7)
```

Every operation that can fail or touches memory has a line of its own, so
the order of effects is the order of the lines. Operations that cannot fail
(unsigned `+ - *`, bit operations, integer conversions, comparisons) are
plain terms.

### The monad

`abbrev M := StateT Mem (Except Err)` (`lean/Achates/Basic.lean`). The state
is the memory. `Err` has five cases:

| Case | Meaning |
| --- | --- |
| `ub reason` | The C standard gives the execution no meaning from here. |
| `assertFail expr file line func` | `__assert_fail` was called. |
| `abort` | `abort` was called. |
| `unsupported what` | Defined (or unspecified) C that the model does not cover, reached at run time. |
| `outOfFuel` | A loop or a recursion used up the fuel. Says nothing about the C. |

Failure is final: no emitted code catches it, and the memory at the point
of failure is dropped.

Decision: one monad for every function, instead of the weakest monad per
function (AutoCorres's type strengthening). A uniform literal layer is
simpler to trust; `rotl_u64` above does not use the memory, and proving
that is a one-line lemma for a later layer.

### Integers

`UInt w` and `SInt w` are structures around `BitVec w`
(`lean/Achates/Int.lean`), with `U8` ... `U128` and `I8` ... `I128` as
abbreviations. Signedness is in the type, not only in the operation, so
Lean rejects an emitted operation applied at the wrong C type: the type
checker re-checks the emitter. Widths come from the IR, which has them from
clang's predefined macros.

- Unsigned `+ - *`, negation and bit operations wrap and are pure.
- Signed `+ - *`, negation, `/`: the exact integer result is computed and
  checked against the type's range; out of range is `ub`. This covers
  `INT_MIN / -1`.
- `/` and `%` by zero are `ub` for both signs. `INT_MIN % -1` is `ub`
  (C11 6.5.5p6); Aeneas's model returns 0 here (`docs/research/aeneas.md`,
  section 7).
- Shifts take the count as the right operand's own value. A count below 0
  or at least the width is `ub`. Signed left shift is `ub` for a negative
  left operand or a result that does not fit (C11 6.5.7p4). Signed right
  shift is arithmetic.
- Conversions follow the IR's cast nodes: `toU`/`toS` reduce modulo 2^w or
  sign-extend. Nothing is promoted by the emitter, with one exception:
  `++` and `--` on a type narrower than `int` are computed in `int` and
  converted back, as C defines them, because clang's node for them carries
  no cast.
- Comparisons and `&& || !` are Lean `Bool` where C uses them as conditions,
  and are converted to the C result type (`int`) with `ofBool` where C uses
  the value.
- `_Bool` is Lean `Bool`. Reading a `_Bool` object that holds neither 0 nor
  1 is `ub`.
- An enum is its integer type as clang chose it.

`float` is `Float32` and `double` is `Float` (`lean/Achates/Float.lean`).
Float-to-integer conversion truncates and is `ub` when the truncated value
does not fit, NaN and infinities included; integer-to-float uses the
host's correctly rounded conversion. Lean proves nothing about `Float`, so
these definitions run but give proofs no arithmetic facts.

### Memory

CompCert-style, as the brief suggested (`lean/Achates/Memory.lean`):

- Memory is an array of blocks. A block has bytes, an alignment, a liveness
  flag, a read-only flag, a kind (static, stack, malloc, talloc) and, for
  talloc, a parent and a destructor. Block numbers are never reused.
- A pointer is `null`, `obj block offset`, `fn name` (the address of a
  function, by its key) or `addr n` (a nonzero integer converted to a
  pointer, which designates no object).
- A byte is `undef`, `byte b`, or `frag p i` (byte `i` of stored pointer
  `p`).
- Typed access goes through `class CVal` (size, alignment, encode, decode),
  little-endian. Every access checks: pointer kind, liveness, bounds,
  read-only on write, and alignment (offset and block alignment).
- Reading `undef` bytes as a scalar is `ub`; through a character type it is
  `unsupported` (C makes the value unspecified, not undefined, and no value
  would be faithful). Reading pointer fragments as an integer is
  `unsupported`. Eight zero bytes read as a pointer give `null`.
- Struct, union and array values are `Agg`: their bytes, which may include
  `undef`. Copying a partly initialised struct is therefore allowed, as in
  C.
- Pointer arithmetic is defined only within the object or one past its end,
  and is `ub` on `null` even for offset 0 (C17; C2y defines that case).
  Subtraction and ordering need the same block. Equality of pointers into
  different blocks is `false`, except that comparing a one-past-the-end
  pointer with a pointer into another block is `unsupported`.
- A pointer converted to an integer is `unsupported` unless it is `null` or
  an `addr`: the model gives objects no addresses.

Which variables live in memory: a parameter or local that is a scalar,
never has its address taken, and (for a local) is initialised where it is
declared is a Lean `let mut` value. Everything else is a block: aggregates,
addressed variables, locals declared without an initialiser (so that a read
before a write is caught as uninitialised), and locals declared directly in
a block that contains labels. Memory locals are allocated at function entry
and freed at return; reaching a declaration without an initialiser makes the
object indeterminate again. This is CompCert's Clight scheme, with one
difference: Clight puts every variable in memory first and promotes later
(`SimplLocals`), with a proof; Achates decides at emission, without a proof.

Layout comes from clang only (`src/emit/layout.rs`). For every record the
emitter asks clang `sizeof`, `_Alignof` and `__builtin_offsetof` of each
member through the front end's probe mechanism; anonymous records are
reached by designator paths from a named record. A bit-field has no offset
and a function that accesses one is refused. The runtime takes scalar
alignment to equal size, and the emitter stops with an error unless clang
confirms it for each scalar type.

Objects with static storage (`Misc/Statics.lean`): every string literal and
every file-scope or `static` local variable the selection defines has a
fixed block number. `Statics.init` allocates them in order (zero-filled, as
C requires), runs their initialisers, and marks string literals and `const`
objects read-only. It must run before any emitted function.

### Control flow

Lean's `do` notation supplies mutable variables, `return`, and `break` and
`continue` for the innermost `for`. Two `ForIn` instances are all the
runtime adds:

- `for _ in Fuel.mk fuel do` runs its body until it breaks and fails with
  `outOfFuel` after `fuel` rounds. Every C loop is one.
- `for _ in Once.mk do` runs its body once. It is a place to `break` out
  of: a `switch`, the part of a block before a label, and a loop body whose
  `continue` must still run the increment.

A C jump that leaves more than one Lean loop sets a flag, breaks, and is
passed on by `if flag then break` after each loop on the way.

- `switch`: the matching section's index is computed first; the sections
  are consecutive `if sel ≤ i then ..`, so falling through is falling into
  the next `if`. Case labels must be directly in the switch's block.
- `goto`: only a forward jump to a label of an enclosing block. Anything
  else is refused.
- A statement after one that cannot fall through is not emitted.

Proof obligation the fuel leaves: for each call of interest, a fuel bound
`n` such that the result is not `outOfFuel` at `n`. `Fuel.loop` is
monotone: more fuel never changes a result that is not `outOfFuel`. That
lemma is not proved in the runtime yet. Recursive and mutually recursive
functions match on `fuel` and are structurally recursive
(`termination_by structural fuel`), so Lean checks their totality itself.

AutoCorres2 encodes `break`, `continue`, `return` and `goto` as exceptions
in its monad; Achates leaves that to Lean's `do` elaborator, whose output
is ordinary terms over `forIn`, and adds no exception case for control.
Aeneas uses a `loop` combinator defined by `partial_fixpoint` with no fuel;
its Lean back end rejects `-use-fuel`.

### Evaluation order

C leaves the order of most operands open. The emitted Lean evaluates left
to right. To keep that from being a silent choice, the emitter analyses
every full expression (`src/emit/order.rs`): for each pair of operands C
does not sequence it computes what each reads and writes (variables held as
values, exactly; memory, as one unit; calls, by a summary of the callee) and
refuses the function if one operand writes what the other reads or writes.
`i + i++` and `f() - g()` with `f` and `g` writing memory are refused. The
analysis is conservative: it refuses `&list->values[list->num++]` because
it does not tell two members of one struct apart.

### External functions

A function that is called but not defined in the selection is one Lean type
class with one method (`Misc/Externals.lean`):

```lean
/-- C function `strtoll`. -/
class Ext.strtoll where
  call : Ptr → Ptr → I32 → M I64
```

A definition lists, as instance arguments, exactly the externals it needs,
directly or through its callees:

```lean
def bstrcasecmp [Ext.strncasecmp] (fuel : Nat) (str1 : Agg) (str2 : Agg) : M I32 := do
```

A variadic external takes its fixed arguments and a `List VArg` of the
promoted extra arguments. Decision: type classes instead of one structure
of all externals, so that the signature states the dependency and Lean
passes it along.

Modelled in the runtime (`lean/Achates/Libc.lean`, `Talloc.lean`), and used
only when the C declaration maps to the model's Lean type:

`__assert_fail`, `abort`, `memcpy`, `memmove`, `memset`, `memcmp`,
`memchr`, `strlen`, `strcmp`, `strncmp`, `strchr`, `malloc`, `calloc`,
`free`, `ta_alloc_size`, `ta_zalloc_size`, `ta_new_context`,
`ta_realloc_size`, `ta_xrealloc_size`, `ta_free`, `ta_free_children`,
`ta_get_size`, `ta_set_destructor`, `ta_set_parent`, `ta_steal_`,
`ta_dbg_set_loc`, `ta_calc_array_size`, `ta_calc_prealloc_elems`.

What the talloc model omits: destructors are recorded but never run, and
freeing an allocation that has one (directly or through a parent) fails as
`unsupported`; allocation never fails (2^26 bytes or more fails as
`unsupported`; this was 2^47 until `achates check` ran out of memory on a
request the model tried to hold, see `docs/check-report.md`); the leak report and the canaries do not exist;
`ta_realloc_size` always moves the block. Parent ownership is modelled.

A function of the selection that is not emitted is also taken as a
parameter by its callers, under its key, and the summary says so.

### Function pointers

The address of a function is `Ptr.fn key`. A call through a pointer is a
`match` over every function whose address is taken anywhere in the
selection and whose Lean type equals the call's: an emitted function is
called directly, any other goes to its `Ext` class. A null pointer is `ub`;
any other pointer is `unsupported`.

### Named assumptions

Recorded per function in `status.json` and in the definition's comment, and
inherited by callers:

| Tag | Assumption | Functions |
| --- | --- | ---: |
| `talloc-model` | talloc as described above | 32 |
| `cmp-byte-difference` | `memcmp`, `strcmp`, `strncmp` return the difference of the first differing bytes; C fixes only the sign | 31 |
| `alloc-succeeds` | allocation never returns null | 26 |
| `sequential-atomics` | an atomic load or store is a plain one; no other thread runs | 11 |
| `external-order` | where an external call and a memory read are unsequenced, the external does not write what is read | 3 |
| `signed-zeros` | the unit is compiled with `-fno-signed-zeros`, so the compiled C may differ in the sign of a zero | 1 |

Any other flag that changes floating-point results (`-ffast-math`,
`-ffinite-math-only`, `-march=`, ...) makes a function with floating
arithmetic not emitted. Mutexes and condition variables are not modelled
and not assumed away: `pthread_*` are parameters.

### Names and files

- A C file is a Lean module named after its path below the directory the
  project's files share: `misc/bstr.c` is `Misc.Bstr_c`, `ta/ta.h` is
  `Ta.Ta_h`; a system header is `Sys.<file>`. All are under the root
  namespace given by `--name`.
- A function keeps its C name inside its module's namespace:
  `Misc.Misc.Bstr_c.bstrcmp`. A name that is a Lean keyword is written
  `«name»`.
- A local is `name_N` with the IR's number, a parameter held as a value is
  `name_v`, a memory object's address is `name_p` or `name_N`, a temporary
  is `tN`.
- A header function is emitted once, in its header's module.
- Lean imports cannot be circular, and `bstr.c` and `bstr.h` call each
  other. A file in such a cycle continues in numbered parts
  (`Misc/Bstr_c/Part2.lean`), each holding the functions one layer further
  up the call chain; the namespace does not change. In `misc/` only
  `bstr.c` (3 parts) and `bstr.h` (3 parts) are split. So "one Lean file per
  C file" holds for 14 of the 15 C files and 4 of the 5 headers.

### From AutoCorres, CompCert and Aeneas

Taken: undefined behaviour as explicit failing guards (AutoCorres, CompCert);
a literal layer first, to be abstracted later with proofs (AutoCorres);
address-taken locals in memory (both); blocks, offsets, provenance, `undef`
bytes and pointer fragments (CompCert); bounded integer types over `BitVec`
and a failure monad with `ok`/`fail` (Aeneas); clang as the front end and
target facts from the compile command (`docs/research/autocorres.md`,
section 6).

Different on purpose: fuel instead of `partial_fixpoint` or a
nondeterministic `whileLoop`; floats, variadic calls to externals, string
literals and open-world function pointers are modelled, which AutoCorres2
does not do; the heap is not split by type and nothing is lifted to values
yet; Aeneas's own types are not used at this layer, because C's wrapping
unsigned arithmetic, undefined signed overflow and byte-level memory do not
fit them. The section "Relation to Aeneas output" says how the two are
connected.

## What the definitions' trust rests on

For an emitted definition to mean what the compiled C does, a reader must
believe:

1. **clang's reading of the source**, with the build's flags, as the front
   end's IR records it (`docs/frontend-report.md`): every implicit
   conversion, the resolved types, the callee of each call. The IR is of
   the clang build; mpv is built with gcc.
2. **ABI facts**: integer widths from clang's macros; record sizes,
   alignments and member offsets from clang's `sizeof`, `_Alignof` and
   `offsetof`; scalar alignment equal to size (checked with clang);
   little-endian two's complement; null is all-bits-zero; arithmetic right
   shift of negative values; out-of-range conversion to a signed type
   reduces modulo 2^w; `char` signedness from clang.
3. **The runtime's semantics** for each operation: `Int.lean` (141 lines),
   `Float.lean` (63), `Memory.lean` (291), `Basic.lean` (104). `Float` and
   `Float32` operations are the host's, in round-to-nearest.
4. **Each modelled external** (`Libc.lean`, 131 lines; `Talloc.lean`, 129
   lines), written from the C standard and from reading `ta/ta.c`. Only
   `memcpy`, `memmove`, `memset`, `memcmp`, `memchr`, `strlen`, `strcmp`,
   `strncmp`, `strchr`, `malloc` and `free` are compared with the system's
   libc by the tests, and `__assert_fail` and `abort` are exercised. The
   talloc models and `calloc` were not run against the real functions.
5. **Each named assumption** a definition lists.
6. **The emitter**: the mapping from IR nodes to runtime calls
   (`src/emit/expr.rs`, `func.rs`), the classification of variables, the
   evaluation-order analysis, and the constant folding it does, which is
   exactly two things: `-` applied to an integer literal, and clang's
   unsigned printing of character constants (`'\xff'` arrives as
   4294967295 and is read as -1).
7. **Lean's `do` elaboration** of `let mut`, `for`, `break`, `continue` and
   `return`.
8. **Sequential execution**: no other thread changes the memory.
9. **For an external taken as a parameter**: that whoever supplies the
   instance models the symbol the object file really calls. glibc redirects
   `strtoll` to `__isoc23_strtoll` under `_GNU_SOURCE`
   (`docs/research/c2rust.md`); the class is named `Ext.strtoll` and the
   emitter does not read the redirection.

## Results on `misc/`

`achates emit --compile-commands /home/user/rmpv/formal/.mpv-build/compile_commands.json --select misc/ --out pilot/misc --name Misc`
takes 11 s with a debug build. The full output is `pilot/misc/summary.txt`.

| File | Functions | Emitted |
| --- | ---: | ---: |
| bstr.c | 36 | 33 |
| charset_conv.c | 5 | 5 |
| codepoint_width.c | 6 | 6 |
| dispatch.c | 15 | 15 |
| hash.c | 1 | 1 |
| io_utils.c | 2 | 2 |
| json.c | 13 | 13 |
| language.c | 4 | 3 |
| natural_sort.c | 1 | 1 |
| node.c | 13 | 11 |
| path_utils.c | 17 | 17 |
| random.c | 6 | 6 |
| rendezvous.c | 1 | 1 |
| thread_pool.c | 7 | 7 |
| thread_tools.c | 14 | 14 |
| **Selected** | **141** | **135** |
| bstr.h | 14 | 14 |
| ctype.h | 7 | 7 |
| threads-posix.h | 9 | 9 |
| ta.h | 2 | 2 |
| glibc stdlib-bsearch.h | 1 | 1 |
| **Header** | **33** | **33** |

"Emitted" covers different degrees of self-containment. Of the 135 emitted
selected functions:

- 46 need no external function at all, so they can be run as they are; 26
  of those also rest on no named assumption.
- 89 take at least one function as a parameter.
- Of all 168 emitted functions, 22 take as a parameter a function that is
  in the selection: one that was refused (`bstr_xappend_asprintf`,
  `node_map_badd`), or a function reached only through a function pointer
  from a file that cannot import its file (`cancel_destroy`,
  `thread_pool_dtor`, `lang_compare`).

Functions not emitted (6), and why:

| Functions | Reason | Which |
| ---: | --- | --- |
| 3 | an expression whose operands C does not sequence may interfere | `mp_match_lang`, `node_array_add`, `node_map_badd` |
| 3 | variadic argument handling (`va_start` and friends, `va_list`) is not modelled | `bstr_sscanf`, `bstr_xappend_asprintf`, `bstr_xappend_vasprintf` |
| 2 | variadic function definition | `bstr_sscanf`, `bstr_xappend_asprintf` (also counted above) |

The three order refusals are conservative, not found bugs:
`bstrcasecmp(canonicalize(a), canonicalize(b))` (two calls that reach an
indirect call), `list->keys[list->num] = bstrdup0(list, key)` (a memory
read beside a call that allocates) and `&list->values[list->num++]`.

Modelled functions, with the number of emitted functions that depend on
each: `__assert_fail` 61, `strlen` 44, `abort` 30, `memcmp` 27,
`ta_dbg_set_loc` 26, `ta_get_size` 19, `ta_xrealloc_size` 19, `strchr` 14,
`memmove` 13, `ta_free` 13, `ta_calc_array_size` 10, `ta_alloc_size` 8,
`ta_calc_prealloc_elems` 7, `memcpy` 4, `strcmp` 4, `strncmp` 4,
`ta_zalloc_size` 4, `memchr` 3, `ta_set_destructor` 3, `ta_steal_` 2,
`free` 1, `memset` 1, `ta_new_context` 1.

Functions left as parameters: 70 classes, 65 of them outside the
selection. With the number of emitted functions that depend on each:
`pthread_mutex_lock` 30, `pthread_mutex_unlock` 30,
`pthread_cond_broadcast` 20, `pthread_cond_destroy` 19,
`pthread_mutex_destroy` 18, `pthread_cond_wait` 10, `mp_log2` 9,
`pthread_join` 9, `strncasecmp` 9, `ta_xstrndup` 9, `close` 8, `memrchr` 8,
`__errno_location` 7, `write` 7, `ta_xstrdup` 6, `clock_gettime` 5,
`pthread_cond_signal` 5, `pthread_cond_timedwait` 5, `pthread_create` 5,
`pthread_self` 5, `stat` 5, `mp_time_ns` 4, `pthread_cond_init` 4,
`pthread_condattr_destroy` 4, `pthread_condattr_init` 4,
`pthread_condattr_setclock` 4, `pthread_mutex_init` 4,
`pthread_mutexattr_destroy` 4, `pthread_mutexattr_init` 4,
`pthread_mutexattr_settype` 4, `ta_asprintf` 4, `av_random_bytes` 3,
`mp_append_escaped_string` 3, `mp_raw_time_ns` 3, `strtod` 3, `strtoll` 3,
`getcwd` 2, `getenv` 2, `mp_append_utf8_bstr` 2, `mp_time_ns_add` 2,
`mp_tprintf_buf` 2, `open` 2, `pthread_setname_np` 2, `strcasecmp` 2,
`strncpy` 2, and with 1 each: `av_hash_alloc`, `av_hash_final`,
`av_hash_freep`, `av_hash_get_size`, `av_hash_init`, `av_hash_update`,
`fclose`, `fdopen`, `fwrite`, `mkdir`, `mp_make_wakeup_pipe`, `mp_msg`,
`mp_round_next_power_of_2`, `pthread_detach`, `read`, `realpath`, `rename`,
`ta_talloc_strdup_append_buffer`, `ta_talloc_strndup_append_buffer`,
`unlink`. In the selection: `cancel_destroy` 8, `thread_pool_dtor` 7,
`bstr_xappend_asprintf` 6, `node_map_badd` 6, `lang_compare` 2.

Of the 90 externals the front end names, 23 are modelled, 65 are
parameters, and 2 (`vsnprintf`, `vsscanf`) are called only by functions
that are not emitted.

Build time of `pilot/misc` from clean, `lake build --wfail`, 4 cores: 20 s
wall (33 s user). `Statics.lean` is the slowest module: `langmap` and the
Unicode tables are initialised by about 2,700 lines.

### Checks on `misc/`

`pilot/misc-checks/MiscChecks.lean`, built by `make ci`:

- `mp_natural_sort_cmp` on all 196 pairs of 14 strings equals what mpv's
  `misc/natural_sort.c`, compiled by gcc, returns (the expected values were
  produced by that program and are written in the file).
- `splitmix64` on seed 0 returns `0xe220a8397b1dcdaf`, the published value.
- `rotl_u64 f x k = rotl_u64 g x k` for all fuels, by `rfl`.
- `rotl_u64 0 1 1` evaluates to `ok 2` and `rotl_u64 0 1 0` to
  `ub "shift by 64 of a 64-bit value"`, both by `rfl`. The second is real:
  mpv's `rotl_u64(x, 0)` shifts right by 64.

`#print axioms` on the fuel theorem lists `propext` and `Quot.sound` only.

## Fixture tests

`cargo test` runs 125 tests; 98 are the back end's (`src/emit/tests.rs`).
One emission and one `lake build --wfail` serve all cases; the back-end
tests take 5 s.

**94 fidelity cases, 94 pass.** Each is a C function `t_*` in
`tests/fixtures/fidelity.c`. The file is compiled by `cc -O1` and run; the
same file is emitted, built, and run by `lake env lean --run`.

- 68 cases compare the Lean result with the compiled C's result: `char`
  promotion; wraparound at 8, 16, 32 and 64 bits; `-1 < 1u`; shifts;
  `&&`/`||`/`?:`/comma with side effects; `for` with `break` and
  `continue`, `do`-`while` with `continue`, nested loops; `switch` with
  fall-through, default in the middle, and inside a loop; `goto` cleanup;
  structs through pointers and by value, nested and anonymous members,
  unions, compound literals; arrays through pointer arithmetic, 2-D
  arrays, pointer difference; an out parameter; a string literal walked by
  `while (*p)`; bytes of an `unsigned` and of a struct read through a cast;
  recursion and mutual recursion; calls through a function pointer and
  through a table of them; globals, static tables, a static local, a table
  of string pointers; `memcpy`, overlapping `memmove`, `memset`, the sign
  of `memcmp`/`strcmp`/`strncmp`, `strchr`, `memchr`, `strlen`;
  float-to-int, int-to-float, `double` and `float` arithmetic compared bit
  for bit, NaN comparisons.
- 21 cases expect `ub` with a given reason and are not run as C: signed
  overflow in `+`, `*` (through `unsigned short` promotion), `/`, `%`,
  negation, shift; division by zero; shift by the width and by a negative
  count; reading one past an array; a pointer two past an array; an
  uninitialised local; use after free; double free; null dereference;
  writing a string literal; a null function pointer; overlapping `memcpy`;
  `double` to `int` out of range; a misaligned access.
- 5 cases expect another stop: `assert` failure, `abort`, an infinite loop
  (`outOfFuel`), an uninitialised `unsigned char` read (`unsupported`), an
  object address converted to an integer (`unsupported`).

**4 emission tests, 4 pass**: a variadic definition, `f() - g()` and
`i + i++`, and a backward `goto` are refused with the right reason; a
caller of a refused function and of an undeclared-body function gets
`[Ext.puts]` in its signature and the class has the right type.

One real defect was found by these tests and fixed: character constants
with the high bit set (see trust item 6).

## Relation to Aeneas output

Aeneas gives a Rust function as a Lean function over values in its
`Result` monad: `&[u8]` is `Slice U8`, `&mut T` is a `T` in and a `T` out.
Achates gives the C function over pointers into `Mem`. They are not equal
as Lean terms and are not meant to be; they are related by a
representation predicate and a simulation theorem. Nothing in this section
is proved yet; it is the design the current output was shaped for.

**Scalars.** `SInt w`, `UInt w`, Aeneas's `IScalar` and `UScalar` all wrap
`BitVec`. A bridge `toAeneas (x : SInt 32) : Std.I32 := ⟨x.bv⟩` is a
bijection, and each operation needs one lemma:

- `SInt.add a b = .ok c ↔ toAeneas a + toAeneas b = ok (toAeneas c)`, and
  `SInt.add a b = .error (.ub _) ↔ ... = fail .integerOverflow`. C's
  undefined behaviour and Rust's debug-build panic coincide for `+ - *`.
- `a + b` on `UInt` equals `core.num.U32.wrapping_add`.
- `SInt.rem` disagrees with Aeneas's `%` at `MIN % -1`, where Aeneas is
  wrong about Rust; a theorem must exclude that input.

**Memory.** For `bstrcmp`, emitted as

```lean
def bstrcmp (fuel : Nat) (str1 : Agg) (str2 : Agg) : M I32
```

where a `struct bstr` is 16 bytes (`start : Ptr` at 0, `len : U64` at 8),
and a Rust port `fn bstrcmp(a: &[u8], b: &[u8]) -> i32` that Aeneas gives
as `bstrcmp (a b : Slice U8) : Result I32`, the predicate is

```lean
/-- In memory `m`, the bstr value `v` denotes the byte slice `s`. -/
def IsBstr (m : Mem) (v : Agg) (s : Slice U8) : Prop :=
  ∃ p, Agg.get Ptr v 0 = .ok p ∧ Agg.get U64 v 8 = .ok (UInt.ofNat 64 s.length) ∧
    (s.length = 0 ∨ ((Mem.loadBytes p s.length).run m).map (·.1) = .ok (s.val.map byteOf).toArray)
```

and the theorem is

```lean
theorem bstrcmp_refines (m : Mem) (x y : Agg) (a b : Slice U8)
    (hx : IsBstr m x a) (hy : IsBstr m y b) :
    ∃ n, ∀ fuel ≥ n, ∃ r m',
      (C.bstrcmp fuel x y).run m = .ok (r, m') ∧ Unchanged m m' ∧
      ∃ r', Rust.bstrcmp a b = ok r' ∧ sign r.toInt = sign r'.val
```

Four things in it are general:

1. The fuel is quantified away: some bound exists and the result holds
   above it.
2. `Unchanged m m'` is a frame condition: every block live in `m` has the
   same bytes in `m'` (the function's own locals were added and freed).
3. The result is compared up to what C leaves open: here the sign, because
   `bstrcmp` returns `memcmp`'s value and the definition rests on the
   `cmp-byte-difference` assumption. A Rust port that returns -1, 0, 1 is
   equal in sign, not in value.
4. C's undefined behaviour appears as a precondition. `bstrcmp` on two
   empty strings with null `start` never calls `memcmp`, so it needs none;
   `bstr_xappend`, which calls `memmove(s->start + s->len, ...)`, would
   need `start ≠ null`, because pointer arithmetic on null is `ub`.

**Writes through pointers.** For `mp_rand_next(mp_rand_state *s)`, Aeneas
gives `next (s : State) : Result (U64 × State)`. The C side is stated with
the same predicate before and after:

```lean
IsState m p s → ∃ r m', (C.mp_rand_next fuel p).run m = .ok (r, m') ∧
  ∃ s', Rust.next s = ok (toAeneas r, s') ∧ IsState m' p s' ∧ UnchangedExcept p m m'
```

The updated value Aeneas returns is what the memory holds at `p` afterwards.

**Loops.** An emitted loop is `Fuel.loop body n s`; Aeneas's is
`loop body' s'`. With a relation `R` between the two loop states, a shared
invariant, and a measure, one lemma turns "the bodies are related step by
step" into "the loops are related" and produces the fuel bound from the
measure. This is the same shape as Aeneas's `loop.spec_decr_nat`.

**The planned middle layer.** Stating these theorems directly against
`Mem` for every function would repeat the same reasoning. The next step is
the one AutoCorres takes: for each emitted function, a value-level
definition (structs as Lean structures, in/out pointers as values in and
out) with a generated proof that the memory-level definition refines it
under a separation precondition. The Aeneas comparison then happens between
two value-level functions. The emitter already has what that step needs:
the record layouts from clang, which variables are values, and the
`status.json` assumptions.

**Functions Aeneas cannot take as written.** `mp_natural_sort_cmp` returns
from inside nested loops, which Aeneas rejects
(`docs/research/aeneas.md`, section 6); the Rust port needs the inner loops
as functions. Achates emits the C as written.

## Known gaps, and what was not verified

Undefined behaviour the model does not detect (it gives such an execution a
result):

- Use of a pointer to a block-scoped local after its block ends but before
  the function returns; such a local also keeps its value when its block is
  entered again without passing its declaration.
- Two unsequenced writes to the same object through pointers, such as
  `*p = *q = 0` with `p == q`.
- Violations of strict aliasing (effective types) and of `restrict`.
- Comparing a dangling pointer with null.
- Data races.

Choices where C leaves the behaviour open:

- Identical string literals share one object; padding of a zero-initialised
  aggregate is zero.
- Left-to-right evaluation, wherever the order analysis finds no
  interference.
- `void *` arithmetic counts in bytes (the GNU rule mpv relies on).

Limits of the emitter:

- No reading of variadic arguments, no bit-field access, no backward
  `goto`, no case label inside a nested statement, no `_Atomic` aggregates,
  no `long double`.
- The order analysis treats memory as one unit and unknown calls as
  writers; three `misc/` functions are refused by it.
- A selection function refused or out of import reach is a parameter of
  its callers, which lowers what "emitted" means for 22 functions.
- An object defined outside the selection makes its users not emitted
  (none in `misc/`).
- Symbol redirection (`strtoll`) is not read; see trust item 9.
- The IR is clang's; mpv is built by gcc.

Not verified:

- The emitted `misc/` definitions against real mpv, beyond the two checks
  above. In particular none of the 89 functions that take externals was
  run.
- The talloc models against talloc; `calloc`, `ta_*` have no test.
- That glibc's `memcmp`, `strcmp` and `strncmp` on this machine return the
  byte difference; the tests compare signs only.
- Monotonicity of `Fuel.loop` in the fuel, and every other lemma named in
  "Relation to Aeneas output". No theorem relating Achates and Aeneas
  output has been stated in Lean or proved.
- The alignment and `sizeof` of `_Atomic` types are taken to be those of
  the underlying type; true for the `atomic_bool` in `misc/`, not checked
  with clang.
- Build and run times on machines other than this one.
