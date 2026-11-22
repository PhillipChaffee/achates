# Equality theorems between mpv's C and the rmpv port: generator and results

This is the last step of the pilot (`docs/pilot.md`, question 4): from a C
function of mpv's `misc/` as Achates emits it and its Rust counterpart as
Aeneas translates it, state the theorem that the two are equal, try to prove
it without a person, and count.

```sh
make equiv         # regenerate the statements, run the tiers, build (about 40 min)
make equiv-build   # only check the committed proofs (about 1 min once built)
```

| Path | Content |
| --- | --- |
| `src/equiv/` | `achates equiv`: name mapping, templates, the tier runner |
| `equiv/` | The bridge Lake project (`equiv/README.md`): both sides, the correspondence library, the tier scripts and lemmas |
| `equiv/Equiv/Proved.lean` | Generated: the theorems some tier proved, with that tier's script. Built by `make equiv-build`. |
| `equiv/open/Open.lean` | Generated, not built: every open theorem, stated, with the generic script and its first error |
| `equiv/results.json`, `equiv/summary.txt` | Generated: what happened to each of the 174 C functions |

## Result in one paragraph

Of the 174 C functions of the emitted project (141 of `misc/`, 33 header
helpers), **120 pair** by the naming rule with a function that has a body in
the Aeneas output, with no mismatch of the rule. **36 theorems are
generated**, in four shapes; 84 paired functions are not, each with its
reason (57 because the C side takes an external function as a parameter,
24 because no template covers their shape, 3 because the C side is not
emitted). **11 of the 36 are proved without a person**: 1 at tier 0, 8 at
tier 1, 2 at tier 2 (`bstrcmp` and `bstr_startswith`, by general memory and
`memcmp` lemmas), none by hand. Every proof is kernel-checked: `#print
axioms` gives `propext`, `Classical.choice` and `Quot.sound` only. **25
are open**: 13 for a loop (8 C loops, 5 Rust recursions), 3 for static
tables, 9 for memory forms the lemmas do not yet cover or the heartbeat
budget. **No port bug was found.** One theorem, `bstr_equals`, is false on
a corner the C model refuses (`unsupported`) though C and Rust agree there:
a limit of the model, not a mismatch of the two programs. The rate is 11
of 36 generated (31%), 11 of 120 paired (9%); the proved functions are the
character tests, two Unicode table helpers that compute without the table,
and the two `memcmp`-based comparisons.

## What "proved equal" means

Every generated theorem has the same form:

```lean
theorem f (m : Achates.Mem) <arguments and their hypotheses> :
    Equiv.Equal (fun r m' y => Equiv.Unchanged m m' ∧ <r and y correspond>)
      (fun fuel => <C f> fuel <C arguments>) m
      (<Rust f> <Rust arguments>)
```

`Equal R c m r` (in `equiv/Equiv/Basic.lean`) says: there is a fuel bound
`n` such that for every fuel `≥ n`, running the C side from memory `m`
*agrees* with the Rust result. Agreement is one of two things:

* the C side returns a value `a` and memory `m'`, the Rust side returns
  `ok b`, and `R a m' b`; or
* the C side stops with undefined behaviour, a failed `assert` or `abort`,
  and the Rust side fails (`fail e`, any `e`).

Nothing else agrees. In particular a C run that reaches `unsupported` (the
model does not know what the C does there) or runs out of fuel, and a Rust
run that diverges, never agree with anything. So the theorem says, in both
directions: on the inputs it covers, the C succeeds exactly when the Rust
returns `ok`, with corresponding results, and C's undefined behaviour is
exactly where the Rust panics. It is not a refinement in one direction.

The conventions, one by one:

* **Integers.** A C integer and an Aeneas integer correspond when they have
  the same bits (`Equiv.i32` and friends are `⟨x.bv⟩`). A C `char` passed
  where the port takes `u8` is the same byte (`Equiv.charU8`). A C `int`
  truth value corresponds to a Rust `bool` only when it is exactly 0 or 1
  (`r = Equiv.ofBool y`), not merely nonzero.
* **Failure.** C undefined behaviour, assertion failure and `abort` all
  correspond to any Rust failure; the kinds are not matched (C's undefined
  behaviour has no defined kind, and the port's convention is that each
  such case panics). C `unsupported` and out-of-fuel are not failures that
  can agree with anything.
* **Fuel.** The bound is existential and must hold for all larger fuel, so a
  result that appears only for some fuels does not count. Every proof so far
  takes the bound 0: no proved function has a loop on the C side.
* **Memory, unchanged.** `Unchanged m m'`: every block that existed before
  the call is identical after it, and every block the call added is dead
  (its locals were freed and it kept no allocation). This is the frame
  condition for functions with no output through memory, which are all the
  generated ones.
* **A byte slice and memory.** `Region m p bs`: `p` is an object pointer
  (never NULL, never an integer cast to a pointer) into a live block of `m`
  that holds the bytes `bs` from `p` on.
* **A `bstr` argument.** `IsBstr m v s`: the 16-byte aggregate `v` (`struct
  bstr { unsigned char *start; size_t len; }`), read as the C model reads
  its members, has `start = p`, `len = |s|`, and `Region m p s`. This
  excludes a `bstr` with a NULL start. The port maps a NULL `bstr` to the
  empty slice, but in the C model `NULL + 0` is undefined (C17), so for
  every function that computes `start + i` the theorem would be false on a
  NULL empty `bstr`; such a `bstr` is outside every generated theorem.
* **A `const char *` argument.** `IsCStr m p s`: `Region m p (s ++ [0])`.
  The slice may itself contain a NUL; both sides then stop at the first one,
  which is the port's documented convention ("content ends at the first NUL
  or the end").
* **A `bstr` result** (a view into an argument): `IsBstr m' r y`, the C
  view denotes the bytes of the Rust slice. Aeneas slices have no position,
  so the position of the view inside its argument is not compared, although
  the differential tests compare it.
* **Static objects.** A C function that reads string literals or tables gets
  the hypothesis `StaticsReady m`: the memory starts with the blocks
  `Statics.init` builds.

What "proved equal" does **not** cover:

* **Externals.** No generated theorem has an external C function (one the
  emitted code takes as a type-class parameter): 57 functions were not
  generated for that reason. A theorem for them would have to assume a
  correspondence between the external and the port's version of it.
* **The C model's named assumptions.** `bstrcmp` and `bstr_startswith`
  call the runtime's `memcmp`, which returns the difference of the first
  differing bytes (`cmp-byte-difference` in `pilot/misc/status.json`).
  The port's `clib::memcmp` returns the same difference, so the theorems
  compare the exact value. Against real glibc, whose magnitude varies, only
  the sign is meaningful, and the theorem is about the model.
* **Aeneas's library and axioms.** The Rust side is Aeneas's Lean, trusted
  as a model of the Rust. No proved theorem reaches an Aeneas axiom.
* **Everything the backend report lists under trust** (clang's reading of
  the source, the ABI facts, the runtime's semantics, sequential
  execution) holds for the C side here too.
* **`usize` width.** The theorems never fix `System.Platform.numBits`; they
  use only that a slice is shorter than 2^64.

Preconditions are all of the three kinds above (`IsBstr`, `IsCStr`,
`StaticsReady`), generated from the C prototype. None is hand-written, and
no theorem excludes an input value (a range of an integer, say): C's
undefined behaviour on values is related to Rust failure instead of being
assumed away.

## The bridge project

`equiv/lakefile.toml` requires the runtime (`../lean`) and the Aeneas
library, and builds both generated sides as libraries of its own:
`pilot/misc` as `Misc` and `rmpv/pilot/misc-lean/MiscRec` as `MiscRec`.
Both of their Lake packages are named `misc`, which Lake cannot require
twice; building them as libraries of the bridge solves that without editing
either. No other clash came up: neither side's namespace is opened in the
bridge, and every name is written qualified (both have `U8`, `I32` and a
`Result`-like monad). The runtime still uses no Mathlib; only the bridge
does.

From clean, with the rmpv pilot's Mathlib reused through a symlink (see
`equiv/README.md`), `lake build` takes about 4 minutes on 4 cores, 3.5 of
them for `MiscRec.RmpvMisc`.

## The generator

`achates equiv --compile-commands … --select misc/ --c-project pilot/misc
--rust-lean …/MiscRec/RmpvMisc.lean --lake-dir equiv [--prove]`.

**Name mapping.** For each function in `pilot/misc/status.json` (141 of
`misc/` and 33 header helpers), the Rust name is
`rmpv_misc.<file stem>.<snake case of the C name>`: `misc/bstr.c` and
`misc/bstr.h` give module `bstr`, `ucdLookup` gives `ucd_lookup`. If that
name is missing, the generator looks for the snake-case name in any module
and reports it as a mismatch of the naming rule. The rule finds all 120 pairs it can: every C function that has a Rust
function with a body in the Aeneas output is found under the predicted
name, and the fuzzy search finds no Rust function under another module.
The 54 not paired are: the 33 threaded functions of `dispatch.c`,
`thread_pool.c`, `thread_tools.c` and `rendezvous.c` and the 9 inline
helpers of `threads-posix.h` (not ported, or `Mutex`/`Condvar` rejected by
Aeneas); `bstr_sscanf`, `bstr_xappend_asprintf`, `bstr_xappend_vasprintf`
(variadic, not ported); `bstrtod` and `mp_rand_next_double` (an `f64`, left
out of Aeneas); `ta_oom_p`, `ta_oom_s` and glibc's `bsearch` (header
helpers the port has no counterpart for). The port's `-loops-to-rec`
output has no axiom for a function of `misc/`, so "an Aeneas declaration
without a body" never occurs.

**Templates.** The C side's Lean signature says `Agg` or `Ptr` but not what
they are, so the generator also reads the C prototype through the front end
(`frontend::load`). An argument pair is one of: an integer or `_Bool` with
the same width (and the `char`/`u8` case); a `struct bstr` and a `&[u8]`; a
`char *` and a `&[u8]`. A result pair is: integers of the same width; an
`int` and a `bool`; a `struct bstr` and a `&[u8]`. Anything else, and any
pair whose parameter lists differ in length, is reported as "no template
yet" with the pair that failed. A Rust tuple result (the port returns
updated `&mut` values in a tuple) is the shape "output through a pointer",
for which no template is written yet. A C function that takes a talloc
parent or a logger is "allocation", also not covered.

Generated, by shape (an argument kind appears once however many arguments
have it):

| Shape | Theorems |
| --- | ---: |
| bstr arguments, scalar result | 8 |
| C string and bstr arguments, scalar result | 7 |
| scalar arguments, scalar result | 7 |
| scalar arguments, truth value result | 6 |
| bstr arguments, bstr view result | 3 |
| bstr and scalar arguments, bstr view result | 2 |
| bstr and scalar arguments, scalar result | 1 |
| C string arguments, scalar result | 1 |
| C string arguments, bstr view result | 1 |
| **Generated** | **36** |

Not generated, by reason:

| Reason | Functions |
| --- | ---: |
| The C side takes external functions as parameters | 57 |
| No template: output through a pointer (`bstr *` in/out, a `void` C function that writes its argument, a pointer to `uint64_t` or `mp_rand_state`, the JSON writer's output `bstr`; the Rust side returns the new value) | 9 |
| No template: `mpv_node` trees (`node_init`, `node_map_get`, `node_map_bget`, `equal_mpv_value`, `equal_mpv_node`) | 5 |
| No template: parameter lists differ (the JSON reader's `char **` cursor is a slice and an offset in Rust, so 1 C parameter is 2 Rust ones; `bstr_split*` return the rest through a pointer) | 6 |
| No template: allocation (a talloc parent: `resize_append`, `bstr_xappend`, `bstr_decode_hex`) | 3 |
| No template: `ms_bom_guess` returns a pointer to a static string, Rust an `Option` of a slice | 1 |
| The C side is not emitted (`mp_match_lang`, `node_array_add`, `node_map_badd`) | 3 |
| **Paired, not generated** | **84** |

Of the 57 with externals, 25 need only one of six pure functions the port
has its own version of: `strncasecmp` (9), `memrchr` (8, one with
`strncasecmp` too), `mp_log2` (6), `strtoll`, `strcasecmp`,
`mp_round_next_power_of_2`. The rest need talloc string functions
(`ta_xstrndup`, `ta_xstrdup`, `ta_asprintf`), `errno`, the file system, the
clock or the random source.

## The proof tiers

Each tier is one fixed script, written by the generator as the proof of
every theorem still open, with the list of definitions to unfold (both
functions and every non-recursive definition they reach). The runner
writes one Lean file per tier and job, runs `lake env lean --json`, and
counts a theorem as proved only when Lean reports no error inside it **and**
`#print axioms` for it lists only `propext`, `Classical.choice` and
`Quot.sound`.

* **Tier 0** (`equiv_tier0`): unfold, simplify with the rewriting lemmas,
  one closer.
* **Tier 1** (`equiv_tier1`): the same rewriting (`equiv/Equiv/Simp.lean`)
  turns every primitive of both sides into an `if` over bit-vectors (a C
  signed overflow check and an Aeneas `tryMk` both become
  `BitVec.saddOverflow`, C and Rust comparisons both become `BitVec.sle` or
  `≤`), then `split`s every `if` on either side, drops each branch whose
  path condition is contradictory, and closes each leaf. The closer `bvk`
  turns bit-vectors into natural numbers and calls `omega`.
* **Tier 2**, in two entries so that the report can say which lemmas
  closed what:
  * *memory lemmas* (`equiv_tier2_mem`): takes the representation
    hypotheses apart and symbolically executes the C side's memory on the
    caller's memory extended by the call's locals: `s_alloca`,
    `s_storeBytes`, `s_load`, `s_add` (each with a side condition the
    simplifier computes from the block the pointer designates),
    `write_fresh'` (a struct stored into a fresh local reads back as
    itself), `region_frame` (a caller's region survives the call's pushes
    and stores), `s_popFrame` and the `unchanged` script for the frame
    condition. All in `equiv/Equiv/Mem.lean`.
  * *memory and `memcmp` lemmas* (`equiv_tier2_memcmp`): adds `run_memcmp`
    (the runtime's `memcmp` over two regions of `n` bytes returns the first
    byte difference of the two prefixes; proved with `run_bytesAt` and
    `run_checkRange` in `equiv/Equiv/Libc.lean`) and `memcmp_ok` (the
    port's `clib.memcmp_loop`, an Aeneas `partial_fixpoint` recursion,
    returns the same value; proved by induction in `equiv/Equiv/Port.lean`).
* **Tier 3** (hand-written per theorem): none. Nothing in the counts below
  was written for one function.

## Results

| | Count |
| --- | ---: |
| C functions (141 of `misc/` and 33 header helpers) | 174 |
| Paired with a Rust function with a body | 120 |
| Theorems generated | 36 |
| Proved at tier 0 | 1 |
| Proved at tier 1 | 8 |
| Proved at tier 2, memory lemmas only | 0 |
| Proved at tier 2, memory and `memcmp` lemmas | 2 |
| Proved at tier 3 (by hand) | 0 |
| **Proved** | **11** |
| Open | 25 |

Open, by what blocks them (the generator's first sorting, checked by
reading each first error):

| Category | Count | Functions |
| --- | ---: | --- |
| Loop: a C loop needs a fuel bound and an invariant | 8 | `bstrcspn`, `bstrspn`, `bstr_find`, `bstr_lstrip`, `bstr_strip`, `mp_natural_sort_cmp`, `mp_is_url`, `bstr_find0` |
| Loop: a Rust recursion needs an induction (the C side has none or calls a model) | 5 | `bstrchr` (`memchr`), `bstr_endswith`, `bstr_endswith0`, `bstr_startswith0`, `mp_path_is_absolute` |
| Memory: static tables against Aeneas array constants | 3 | `ucdLookup`, `ucdGraphemeJoins`, `bstr_strip_linebreaks` |
| Memory: a C string argument (`strlen` has no lemma yet; tier 2 does not take `IsCStr` apart) | 2 | `bstr0`, `bstr_equals0` |
| Memory: a `bstr` result built in a local and read back as an aggregate (needs `decode ∘ encode` for pointers and `size_t`) | 1 | `bstr_cut` |
| Heartbeat budget: the symbolic execution or the `omega` closer ran out of 4 million heartbeats | 5 | `h_to_i`, `bstr_splice`, `bstrcmp0`, `is_valid_partial_sequence`, `bstr_equals` |
| Arithmetic: a shift by a variable amount (the bind over the C shift's `if` is not lifted) | 1 | `rotl_u64` |

Time: the whole run (`make equiv`) takes about 37 minutes on 4 cores, most
of it failing attempts that use their whole budget. The 11 proofs check in
under a minute (`Equiv.Proved`, 52 s), once the project is built.

Per function (the generated 36):

| C | Rust | Shape | Result |
| --- | --- | --- | --- |
| `bstrcmp` | `bstr.bstrcmp` | bstr arguments, scalar result | tier 2: memory and memcmp lemmas |
| `bstrchr` | `bstr.bstrchr` | bstr and scalar arguments, scalar result | open: loop: a Rust recursion needs an induction |
| `bstrcspn` | `bstr.bstrcspn` | C string and bstr arguments, scalar result | open: loop: a C loop needs a fuel bound and an invariant |
| `bstrspn` | `bstr.bstrspn` | C string and bstr arguments, scalar result | open: loop: a C loop needs a fuel bound and an invariant |
| `bstr_find` | `bstr.bstr_find` | bstr arguments, scalar result | open: loop: a C loop needs a fuel bound and an invariant |
| `bstr_lstrip` | `bstr.bstr_lstrip` | bstr arguments, bstr view result | open: loop: a C loop needs a fuel bound and an invariant |
| `bstr_strip` | `bstr.bstr_strip` | bstr arguments, bstr view result | open: loop: a C loop needs a fuel bound and an invariant |
| `bstr_splice` | `bstr.bstr_splice` | bstr and scalar arguments, bstr view result | open: arithmetic or unfolding |
| `bstr_strip_linebreaks` | `bstr.bstr_strip_linebreaks` | bstr arguments, bstr view result | open: memory: static tables against Aeneas constants |
| `h_to_i` | `bstr.h_to_i` | scalar arguments, scalar result | open: arithmetic or unfolding |
| `bstr0` | `bstr.bstr0` | C string arguments, bstr view result | open: arithmetic or unfolding |
| `bstr_cut` | `bstr.bstr_cut` | bstr and scalar arguments, bstr view result | open: memory correspondence |
| `bstr_endswith` | `bstr.bstr_endswith` | bstr arguments, scalar result | open: loop: a Rust recursion needs an induction |
| `bstr_endswith0` | `bstr.bstr_endswith0` | C string and bstr arguments, scalar result | open: loop: a Rust recursion needs an induction |
| `bstr_startswith` | `bstr.bstr_startswith` | bstr arguments, scalar result | tier 2: memory and memcmp lemmas |
| `bstrcmp0` | `bstr.bstrcmp0` | C string and bstr arguments, scalar result | open: arithmetic or unfolding |
| `mp_isspace` | `ctype.mp_isspace` | scalar arguments, truth value result | tier 1 |
| `mp_tolower` | `ctype.mp_tolower` | scalar arguments, scalar result | tier 1 |
| `mp_isupper` | `ctype.mp_isupper` | scalar arguments, truth value result | tier 1 |
| `bstr_startswith0` | `bstr.bstr_startswith0` | C string and bstr arguments, scalar result | open: loop: a Rust recursion needs an induction |
| `ucdLookup` | `codepoint_width.ucd_lookup` | scalar arguments, scalar result | open: memory: static tables against Aeneas constants |
| `ucdGraphemeJoins` | `codepoint_width.ucd_grapheme_joins` | scalar arguments, scalar result | open: memory: static tables against Aeneas constants |
| `ucdGraphemeDone` | `codepoint_width.ucd_grapheme_done` | scalar arguments, scalar result | tier 0 |
| `ucdToCharacterWidth` | `codepoint_width.ucd_to_character_width` | scalar arguments, scalar result | tier 1 |
| `is_valid_partial_sequence` | `codepoint_width.is_valid_partial_sequence` | bstr arguments, scalar result | open: arithmetic or unfolding |
| `mp_isalnum` | `ctype.mp_isalnum` | scalar arguments, truth value result | tier 1 |
| `mp_isalpha` | `ctype.mp_isalpha` | scalar arguments, truth value result | tier 1 |
| `mp_isdigit` | `ctype.mp_isdigit` | scalar arguments, truth value result | tier 1 |
| `mp_islower` | `ctype.mp_islower` | scalar arguments, truth value result | tier 1 |
| `mp_natural_sort_cmp` | `natural_sort.mp_natural_sort_cmp` | C string arguments, scalar result | open: loop: a C loop needs a fuel bound and an invariant |
| `bstr_equals0` | `bstr.bstr_equals0` | C string and bstr arguments, scalar result | open: arithmetic or unfolding |
| `bstr_equals` | `bstr.bstr_equals` | bstr arguments, scalar result | open: arithmetic or unfolding |
| `mp_path_is_absolute` | `path_utils.mp_path_is_absolute` | bstr arguments, scalar result | open: loop: a Rust recursion needs an induction |
| `mp_is_url` | `path_utils.mp_is_url` | bstr arguments, scalar result | open: loop: a C loop needs a fuel bound and an invariant |
| `bstr_find0` | `bstr.bstr_find0` | C string and bstr arguments, scalar result | open: loop: a C loop needs a fuel bound and an invariant |
| `rotl_u64` | `random.rotl_u64` | scalar arguments, scalar result | open: arithmetic or unfolding |

## Worked example: `bstrcmp`

The statement, as generated (`equiv/Equiv/Proved.lean`):

```lean
theorem bstrcmp (m : Achates.Mem) (str1 : Achates.Agg) (s_str1 : Aeneas.Std.Slice Aeneas.Std.U8)
    (h_str1 : Equiv.IsBstr m str1 s_str1) (str2 : Achates.Agg)
    (s_str2 : Aeneas.Std.Slice Aeneas.Std.U8) (h_str2 : Equiv.IsBstr m str2 s_str2) :
    Equiv.Equal (fun r m' y => Equiv.Unchanged m m' ∧ y = (Equiv.i32 r))
      (fun fuel => Misc.Misc.Bstr_c.bstrcmp fuel str1 str2) m
      (rmpv_misc.bstr.bstrcmp s_str1 s_str2) := by
  equiv_tier2_memcmp [Misc.Misc.Bstr_c.bstrcmp, rmpv_misc.bstr.bstrcmp, rmpv_misc.clib.memcmp]
```

In words: for any memory and any two `bstr` values that are views of two
byte slices (non-NULL starts, live memory holding the bytes), mpv's
`bstrcmp` as Achates emits it returns exactly the `i32` the port's
`bstrcmp` returns, never stops, and leaves the caller's memory as it was.
`#print axioms` gives `propext, Classical.choice, Quot.sound`.

What the script does, on this function:

1. Takes `IsBstr` apart: each `bstr` gives its start pointer `p`, the fact
   that its `len` member reads as the slice length, and `Region m p s`;
   adds `|s| < 2^64` for each slice.
2. Unfolds both functions and the port's `clib.memcmp` (which is the loop
   applied to 0).
3. Executes the C side: two 16-byte locals are allocated at block numbers
   `|m|` and `|m|+1`; `str1` and `str2` are stored into them
   (`s_storeBytes`, `write_fresh'`); each `str.len` load reads the length
   back (`s_load` and `decode_bstr_len`); each `if` on lengths is split, on
   both sides, and a branch whose conditions contradict (the C side says
   `len1 ≠ 0`, the Rust side says `str1.is_empty()`) is dropped by `omega`.
4. At the C `memcmp` call, `run_memcmp` applies: the two regions are still
   there in the memory with the locals (`region_frame`, by the `frame`
   script), and the count is `min(len1, len2)`, at most each length. On the
   Rust side `memcmp_ok` applies with the `min` the port computes. Both
   give `firstDiff` of the same two prefixes; this is where the loop is,
   inside `memcmp`, on both sides.
5. The remaining `if`s compare the `memcmp` result with 0 and the lengths;
   each leaf is `Unchanged m m'` (the two locals are dead after
   `popFrame`; the `unchanged` script) and an equality of two `i32`s that
   simplification closes.

The general lemmas, proved once: `run_bytesAt` (induction over the byte
indices: each `p + i` stays in the block and each byte read is the slice's
byte), `run_checkRange`, `run_memcmp`, `memcmp_loop_ok` (induction on the
bytes left: equal bytes step to `i + 1`, the first different pair returns
`a - b`, which cannot overflow `i32` for two bytes), and the memory lemmas
above. The same script, unchanged, proves `bstr_startswith`.

## Mismatches

None of the 25 open theorems has a counterexample, and none of them was
found false by the tiers, except one case where the statement is false for
a reason that is not a difference between the programs:

**`bstr_equals`, two empty views whose starts are the ends of two
different blocks.** mpv's

```c
static inline bool bstr_equals(struct bstr str1, struct bstr str2)
{
    if (str1.len != str2.len)
        return false;
    return str1.start == str2.start || bstrcmp(str1, str2) == 0;
}
```

compares the two start pointers. When one points one past the end of its
object and the other into a different object, C11 6.5.9p6 leaves the
result open, and the Achates model refuses to choose: `Ptr.eq` stops with
`unsupported`. Both answers lead to `true` here (two empty strings compare
equal), and the port returns `ok true`. Since `unsupported` agrees with
nothing, the generated theorem is false on this input. Evaluated in the
model (memory with two 4-byte blocks, `bstr`s at offset 4 of each, length
0): `bstr_equals` gives `unsupported "comparison of a one-past-the-end
pointer with a pointer to another object"`. Verdict: neither a port bug nor
a translator bug; a choice of the C model that makes a correct C function
unprovable. Two ways out: give pointer equality in that case a
nondeterministic result and prove the theorem for both, or add the
precondition "the starts are not one past the end of different blocks" (a
hand-written precondition, to be flagged). `bstr_equals0` calls
`bstr_equals` and has the same corner.

Real counterexamples could not have been produced the other way, by
evaluating both sides: the Aeneas output is `noncomputable` (its loops are
`partial_fixpoint`s over an interaction tree), so `#eval` runs only the C
side. The differential tests of the port (12.8 M inputs) remain the
evidence for the 25 open ones.

## What blocked the open theorems

Each category with what would unblock it, and the estimated share of
`misc/` it would add (counts of generated theorems, then of paired
functions it would make generatable):

1. **Loops, 13 of the 25 open.** The missing lemma is a simulation rule
   between the runtime's `Fuel.loop` and an Aeneas recursion: given a
   relation between the two loop states, an invariant and a measure that
   decreases, the loops agree with fuel at least the measure. It has to be
   proved once (by induction on the measure) and then instantiated; the
   invariant is the part a tier cannot guess. For the `bstr` loops here the
   invariant is "the index is the same on both sides and at most the
   length", which a template per loop shape (index walk over a slice,
   `while (*p)` over a string) could state mechanically. The Rust-only
   recursions (`memchr`, the slicing in `bstr_endswith`) need a lemma per
   library function, like `memcmp_ok`. Estimate: 10 to 13 more theorems.
2. **Memory forms, 6.** A lemma that `decode` inverts `encode` for pointers
   and `size_t` (for `bstr` results built in locals: `bstr_cut`, and
   through it `bstr_splice`, `bstr_lstrip`, `bstr_strip`); `run_strlen`
   with a Rust `strlen_loop` lemma for C string arguments (`bstr0`,
   `bstr_equals0`, `bstrcmp0`, `bstr_startswith0`, `bstr_endswith0`,
   `bstr_find0`); pointer arithmetic on a caller's region with
   `region_drop` (for `bstr_endswith`). Estimate: 6 to 9.
3. **Static tables, 3.** The C tables are blocks that `Statics.init`
   fills; the Rust tables are Aeneas `Array` constants. One lemma per
   table, proved by evaluation (`decide` over a few thousand entries),
   would relate them. Estimate: 3.
4. **Budget, 5.** `bvk` (natural numbers and `omega`) is much slower than
   `bv_decide`; `h_to_i` was proved in 30 seconds with `bv_decide`. A
   kernel-checked bit-vector decision procedure, or `decide` over the 256
   values of a byte argument, would close the character-sized ones.
   Estimate: 2 to 5.
5. **Not generated, 84 paired functions.** Templates for output through a
   pointer (9, and 3 more with `bstr_split*`) and correspondence assumptions for six pure externals (25)
   are the two largest; both are mechanical. With them, about 70 of the
   120 paired functions would be stated instead of 36.

## Can these proofs be generated rather than written?

**Statements: yes, mechanically, for the shapes covered.** The 36
statements come from the C prototype, the two Lean signatures and a fixed
template per argument and result kind; nothing in them was written for one
function, and they elaborate against both sides without change. The
conventions they encode (bit-for-bit integers, UB ↔ panic, unchanged
caller memory, `bstr`/C string as regions) were enough for every
`misc/` function whose arguments are scalars, `bstr`s and C strings. The
limits are the shapes, not the method: output through pointers, trees of
`mpv_node`, allocation and externals need templates or assumptions that
are just as mechanical but not written yet.

**Proofs: at a low rate today, 11 of 36 (31%), and only for loop-free
functions.** Scalar functions with branches and arithmetic go through a
fixed script (tier 1, 9 of the 13 scalar ones). Loop-free functions over
`bstr`s go through once the memory lemmas exist (tier 2), and those lemmas
are general: the same script proved `bstrcmp` and `bstr_startswith`, and
it would prove any function whose C side only stores its arguments,
loads members and calls `memcmp`. Nothing with a C loop is proved.

**What would raise the rate**, in order of yield: (1) a loop simulation
lemma and invariant templates for the two loop shapes of `misc/` (index
walk, NUL walk), the largest single gain; (2) the three memory lemmas
named above; (3) a kernel-checked bit-vector decision procedure, since the
fastest one (`bv_decide`) is not kernel-checked and was not counted; (4)
the output-through-pointer template and external correspondences, which
add statements rather than proofs. With (1) and (2) the generated rate
would plausibly reach 25 to 30 of 36; a person would still be needed for
the invariants of the irregular loops (`mp_natural_sort_cmp`,
`bstr_decode_partial_utf8`).

The cost of the attempt is worth stating: about 37 minutes of machine
time per run, most of it in failing attempts, and the tier 2 lemmas took
the largest part of the work (the symbolic memory steps, the frame
conditions and the `memcmp` inductions on both sides).

## Problems met on the way, for whoever continues

* **`bv_decide` is not a kernel proof.** Tier 1 first used `bv_decide` and
  closed 10 of the 13 scalar theorems. `#print axioms` then showed
  `….bv_decide.ax_…` axioms on every one: `bv_decide` checks its LRAT
  certificate with compiled code, which is the trust `native_decide` asks
  for. Those proofs are not counted; the closer is now `bvk`
  (bit-vectors to naturals, then `omega`), which is kernel-checked and much
  slower.
* **A Lean run stops at 100 errors.** Lean's `maxErrors` default ends the
  elaboration of a file after the 100th error and reports nothing about
  the theorems after it. An early version of the runner counted those
  theorems as proved (no error in their span); seven false "proofs" came
  from it before the per-theorem `#print axioms` check was added. Every
  attempt file now raises `maxErrors` and the runner requires the axiom
  report.
* **Error recovery hides failures.** A failing `by` block inside a `rw`
  argument is logged and replaced by `sorry`, so `first | rw [h (by tac)] |
  …` takes the first branch even when `tac` fails. The tier scripts state
  side conditions as goals of the rewrite and close them with `case`,
  which fails properly.
* **The merge of the main branch** (runtime `ff754db`: `Mem.alloc` takes
  the block number before the push and refuses allocations of 2^26 bytes
  or more) changed one lemma, `run_alloc`, whose hypothesis is now
  `size < Mem.allocLimit`, and the `s_alloca` step of tier 2. No generated proof needed a change: the
proved set before the merge, counting only kernel-checked proofs, was
`bstrcmp`, `bstr_startswith`, `ucdGraphemeDone` and `ucdToCharacterWidth`,
and all four are proved after it. The run after the merge, with the
kernel-only closer, adds the seven `ctype.h` functions.
* **No Achates bug was found.** No change to the emitter or the runtime was
  made in this worktree.
