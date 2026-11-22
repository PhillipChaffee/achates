# Equality theorems between mpv's C and the rmpv port: generator and results

This is the last step of the pilot (`docs/pilot.md`, question 4): from a C
function of mpv's `misc/` as Achates emits it and its Rust counterpart as
Aeneas translates it, state the theorem that the two are equal, try to prove
it without a person, and count.

```sh
make equiv         # regenerate the statements, search, build (about 20 min from an empty cache, 20 s with nothing changed)
make equiv-build   # only check the committed proofs and their axioms (about 6 min when Proved.lean changed)
```

| Path | Content |
| --- | --- |
| `src/equiv/` | `achates equiv`: name mapping, templates, the search (`search.rs`), the worker pool (`prove.rs`), the cache (`cache.rs`) |
| `equiv/` | The bridge Lake project (`equiv/README.md`): both sides, the correspondence library, the tier scripts and lemmas |
| `equiv/Equiv/Proved.lean` | Generated: the theorems some tier proved, each with that tier's script and budget, then a check of each proof's axioms. Built by `make equiv-build`. |
| `equiv/open/Open.lean` | Generated, not built: every open theorem, stated, with the script of its last try and that try's first error |
| `equiv/results.json`, `equiv/summary.txt` | Generated: what happened to each of the 174 C functions, with each theorem's tries |
| `equiv/tiers.json` | Generated: the search cache, per theorem the outcome, tries, budgets and times under a key of what they depend on |

## Result in one paragraph

Of the 174 C functions of the emitted project (141 of `misc/`, 33 header
helpers), **120 pair** by the naming rule with a function that has a body in
the Aeneas output (in the first run; 122 now that all of `misc/` is
emitted), with no mismatch of the rule. **36 theorems are
generated**, in four shapes; 84 paired functions are not, each with its
reason (57 because the C side takes an external function as a parameter,
24 because no template covers their shape, 3 because the C side is not
emitted). **12 of the 36 are proved without a person**: 1 at tier 0, 9 at
tier 1, 2 at tier 2 (`bstrcmp` and `bstr_startswith`, by general memory and
`memcmp` lemmas), none by hand. Every proof is kernel-checked: `#print
axioms` gives `propext`, `Classical.choice` and `Quot.sound` only. The
twelfth, `h_to_i`, needs 4.2 million heartbeats and came with the larger
tier 1 budget. **24 are open**: 10 for a loop (8 C loops, 2 Rust
recursions), 3 for static tables, 3 for a C string argument, 2 for memory
forms tier 2 does not cover, 5 for the tier 2 budget, 1 for arithmetic.
Each theorem is tried at the tier predicted from its shape, at most twice,
in a pool of four Lean processes, and the outcome is cached: a run from an
empty cache takes 1,173 s (it took 2,550 s before), and with nothing
changed 19 s. **No port bug was found.** One theorem, `bstr_equals`, is false on
a corner the C model refuses (`unsupported`) though C and Rust agree there:
a limit of the model, not a mismatch of the two programs. The rate is 12
of 36 generated (33%), 12 of 122 paired (10%); the proved functions are the
character tests, `h_to_i`, two Unicode table helpers that compute without
the table, and the two `memcmp`-based comparisons.

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

These counts are of the first run (commit 2c72b0d). Since then the three
functions are emitted, and `ta_xstrndup` and `ta_xstrdup` are runtime
models instead of parameters (`docs/backend-report.md`): the run recorded in
`equiv/results.json` pairs 122 functions and does not generate 86, with
their reasons in `equiv/summary.txt`. The 36 generated theorems are the
same.

Of the 57 with externals, 25 need only one of six pure functions the port
has its own version of: `strncasecmp` (9), `memrchr` (8, one with
`strncasecmp` too), `mp_log2` (6), `strtoll`, `strcasecmp`,
`mp_round_next_power_of_2`. The rest need talloc string functions
(`ta_xstrndup`, `ta_xstrdup`, `ta_asprintf`), `errno`, the file system, the
clock or the random source.

## The proof tiers

Each tier is one fixed script, written by the generator as the proof of a
theorem, with the list of definitions to unfold (both functions and every
non-recursive definition they reach), and a heartbeat budget of its own
(see "Budgets"). A theorem counts as proved only when Lean reports no
error inside it **and** `#print axioms` for it lists only `propext`,
`Classical.choice` and `Quot.sound`.

* **Tier 0** (`equiv_tier0`): unfold, simplify with the rewriting lemmas,
  one closer.
* **Tier 1** (`equiv_tier1`): the same rewriting (`equiv/Equiv/Simp.lean`)
  turns every primitive of both sides into an `if` over bit-vectors (a C
  signed overflow check and an Aeneas `tryMk` both become
  `BitVec.saddOverflow`, C and Rust comparisons both become `BitVec.sle` or
  `≤`), then `split`s every `if` on either side, drops each branch whose
  path condition is contradictory, and closes each leaf. The closer `bvk`
  turns bit-vectors into natural numbers and calls `omega`.
* **Tier 2** (`equiv_tier2`): takes the representation hypotheses apart and
  symbolically executes the C side's memory on the caller's memory extended
  by the call's locals: `s_alloca`, `s_storeBytes`, `s_load`, `s_add` (each
  with a side condition the simplifier computes from the block the pointer
  designates), `write_fresh'` (a struct stored into a fresh local reads
  back as itself), `region_frame` (a caller's region survives the call's
  pushes and stores), `s_popFrame` and the `unchanged` script for the frame
  condition, all in `equiv/Equiv/Mem.lean`; and `memcmp` on both sides:
  `run_memcmp` (the runtime's `memcmp` over two regions of `n` bytes
  returns the first byte difference of the two prefixes; proved with
  `run_bytesAt` and `run_checkRange` in `equiv/Equiv/Libc.lean`) and
  `memcmp_ok` (the port's `clib.memcmp_loop`, an Aeneas `partial_fixpoint`
  recursion, returns the same value; proved by induction in
  `equiv/Equiv/Port.lean`).

  Tier 2 used to have a first entry with the memory lemmas only
  (`equiv_tier2_mem`), so that the report could say which lemmas closed
  what. On the measured run it proved nothing (the memory-and-`memcmp`
  entry closes everything it could) and took 717 s of wall time, five of
  its tries running out of budget; it is gone.
* **Tier 3** (hand-written per theorem): none. Nothing in the counts below
  was written for one function.

## The search

A run used to try every tier in turn on every theorem still open, all of
a tier's theorems in four files, each tier waiting for its slowest file
before the next began. The measured run (before this change) took 2,550 s:
the four tiers took 631, 453, 717 and 705 s of wall time, the four cores
were busy only 50–64% of each, and 73% of the 5,829 Lean-seconds went to
14 tries that used their whole budget on 8 theorems. The first tier-2
entry (memory lemmas only) proved nothing.

Now each theorem gets at most two **tries**. A try is one theorem, one
tier's script and that tier's budget, in a Lean file of its own
(`equiv/attempts/<theorem>_T<tier>.lean`, about 2–5 s of import before the
proof). A pool of `--jobs` workers (4) takes tries from one queue, so no
try waits for another: a theorem's second try is queued, at the front, as
soon as its first ends. The first tries are queued longest first by the
time the cache last recorded for each theorem; a theorem the cache has
never seen goes first, as possibly the longest.

### Which tier first

The generator knows, before any Lean runs, how the statement passes memory
and what both sides reach. The first try's tier:

| What the generator knows | First tier | Why |
| --- | --- | --- |
| A `bstr` argument | 2 | The only script that takes `IsBstr` apart and executes the C side's memory |
| Scalars only, and no `if`, `match` or bind (`←`) in any definition either side reaches | 0 | Nothing to split |
| Anything else: scalars with a branch or a step that can fail; C strings without a `bstr` | 1 | Tier 1 splits; tier 2's script cannot start without a `bstr` hypothesis, and tier 1 gets furthest on the rest |

A bind counts as a branch because the rewriting turns every step that can
fail (a C shift's undefined case, an Aeneas `tryMk`) into an `if`:
`ucdToCharacterWidth` has no `if` in its source, but its shift has one
after rewriting, and tier 0 fails on it.

Against the measured run, the rule picks the tier that proved each of the
11: `ucdGraphemeDone` (one comparison, no bind) at tier 0; the seven
`ctype.h` tests and `ucdToCharacterWidth` at tier 1; `bstrcmp` and
`bstr_startswith` at tier 2. It also moves `mp_isalnum` straight to tier
1, where the old run reached it only after 303 s out of budget at tier 0,
and keeps `ucdLookup` (out of budget at tier 0 in 213 s, an unsolved
static-table goal at tier 1 in 24 s) off tier 0.

Loops, static tables and Aeneas axioms do not change the first tier: the
first try is what tells whether a tier gets anywhere, and it costs at most
the tier's budget.

### What a failure says about the second

The runner reads the theorem's errors from `lean --json`: whether one is
out of heartbeats, whether the first is `unsolved goals`, and what the goals
left mention. Then (`src/equiv/search.rs`, `decide`):

First, what no tier has, whatever the failure — no second try:

| Found | Reason recorded |
| --- | --- |
| The Rust side reaches an Aeneas axiom | Aeneas axiom reached |
| The C side reaches a loop (a recursive or fuelled definition) | loop: a C loop needs a fuel bound and an invariant |
| The goals name a Rust recursion other than `clib.memcmp_loop` (tier 2's lemma) and `clib.strlen_loop` (counted as a C string) | loop: a Rust recursion needs an induction |
| The C side reads static objects, or the goals name `Statics.` | memory: static tables against Aeneas constants |

Then the failure itself:

| Failure | At | Second try |
| --- | --- | --- |
| Out of heartbeats | tier 0 | tier 1 (tier 2 with a `bstr` argument): tier 0 does not split, tier 1's leaves are smaller |
| Out of heartbeats | tier 1, `bstr` argument | tier 2 |
| Out of heartbeats | tier 1 without a `bstr`, or tier 2 | none: budget at the top tier for its shape |
| Goals left mention memory (`StateT.run`, `Mem.`, `Region`, `IsBstr`, `memcmp`) or a C string (`IsCStr`, `strlen`) | tier 0 or 1, `bstr` argument | tier 2 |
| The same | tier 2, or no `bstr` argument | none: a C string, or a memory form tier 2 does not cover |
| Goals left with an `if` or `match` | tier 0 | tier 1 |
| A script step fails before the end (`unfold`, `casesm`) | below tier 2, `bstr` argument | tier 2 |
| Anything else | | none: arithmetic or unfolding the closer does not finish, or a script that does not apply |

A tier is never repeated and never lower than the one that failed, and no
theorem gets a third try: if the second try's failure points to a tier not
yet tried, the theorem stays open with "2 tries made; tier N would be
next". A genuinely false statement cannot be told from a closer that gives
up (no tier uses `bv_decide`, whose counterexamples said so), so it falls
under the last row. The unit tests check this mapping on twelve first
errors of the measured run (`src/equiv/testdata/failures.json`).

## Budgets

Each tier has its own `maxHeartbeats`, set per theorem (`equiv_budget N
in`, in `Equiv/Tactic.lean`, which also logs the heartbeats the theorem
used; `Proved.lean` has `set_option maxHeartbeats N in`). The numbers come
from two measurements.

**What the proofs use.** The 11 proofs of the measured run, each under
Mathlib's `#count_heartbeats` (four Lean processes at once on 4 cores):

| Theorem | Tier | Heartbeats | Seconds |
| --- | --- | ---: | ---: |
| `ucdGraphemeDone` | 0 | 316 | 0.0 |
| `ucdToCharacterWidth` | 1 | 1,529 | 0.3 |
| `mp_isspace` | 1 | 24,314 | 2.2 |
| `mp_isupper` | 1 | 28,618 | 3.7 |
| `mp_isdigit` | 1 | 29,324 | 2.5 |
| `mp_islower` | 1 | 29,327 | 3.3 |
| `mp_tolower` | 1 | 263,432 | 25.4 |
| `mp_isalpha` | 1 | 406,258 | 57.9 |
| `mp_isalnum` | 1 | 3,069,294 | 251.9 |
| `bstr_startswith` | 2 | 34,944 | 3.0 |
| `bstrcmp` | 2 | 261,936 | (first in its file, with the import) |

**What more budget buys.** The 8 theorems that ran out of the old 4
million, each once in its own file with no heartbeat limit
(`#count_heartbeats` sets none), four at a time, stopped by wall time:

| Theorem | Tier | Result | At |
| --- | --- | --- | --- |
| `h_to_i` | 1 | **proved**, 4,184,577 heartbeats | 384 s, 2.0 GB |
| `is_valid_partial_sequence` | 2 | ran to its end, **unsolved goals** (a memory goal), 9,077,521 heartbeats | 677 s |
| `bstr_splice` | 2 | not finished | stopped at 1,800 s (about 22 million), 3.2 GB |
| `bstrcmp0` | 2 | not finished | stopped by hand at 672 s with 8.9 GB, growing |
| `bstr_equals` | 2 | not finished | killed by the kernel for memory at 721 s (about 6 GB) |
| `bstr_equals0` | 2 | not finished | killed by the kernel for memory at 501 s |
| `mp_isalnum` | 0 | not finished | stopped at 1,206 s (about 14 million), 2.5 GB |
| `ucdLookup` | 0 | not finished | stopped at 1,205 s (about 14 million), 2.8 GB |

**The rate.** Heartbeats per second per Lean process, four processes on
the 4 cores: 12,200 (`mp_isalnum`, 3.07 million in 252 s), 13,400
(`is_valid_partial_sequence`, 9.08 million in 677 s), 10,900 (`h_to_i`,
under memory pressure); the old run's budget-outs, 4 million in 210–345
s, give 11,600–19,000. The cold run below logs both for every try; over
its 17 tries of 20 s or more, less 3 s of import each, the rate is 9,300 to
15,200 and 12,000 on average, the figure the budgets are converted with.

**The budgets**, the most a try at each tier is allowed:

| Tier | Old | New | About | Basis |
| --- | ---: | ---: | ---: | --- |
| 0 | 4,000,000 | 400,000 | 30 s | Its one proof uses 316. A theorem it runs out on goes to tier 1, which splits and is cheaper on it: `mp_isalnum` is proved at tier 1 with 3.07 million, while at tier 0 it had not closed after 1,206 s (about 14 million), and `ucdLookup` had not either (tier 1 fails on it at once, on its static tables). |
| 1 | 4,000,000 | 8,000,000 | 11 min | The largest proof, `h_to_i`, needs 4.18 million (about 5.5 min); 8 million admits proofs up to about twice that, and 11 minutes is the most one try may take in a run that should end in about a quarter of an hour. `h_to_i` uses 2.0 GB, so four such tries fit. |
| 2 | 4,000,000 | 4,000,000 | 5 min | Its proofs use at most 262 thousand. Of the five that ran out, none closed with 1.5 to 5 times more; `is_valid_partial_sequence` reached the end of the script and left a goal, and three grew past 5 GB within about twice the budget's time, which four tries at once on 16 GB do not survive. Raising it buys nothing measured and risks the run; 4 million is the most four tries at once can afford. |

No tier uses `bv_decide` or `native_decide`; the kernel-only rule is
unchanged.

## The cache

`equiv/tiers.json` (committed) holds, per theorem, what its last search
found: the key, the tier that proved it or the reason it is open, every
try (tier, budget, heartbeats used, seconds, result, first error) and, for
a proof, its `#print axioms` message. The run reads it at the start and
writes it at the end; `--no-cache` skips the reading, so every theorem is
searched, and the file is still written.

**The key** is a SHA-256 (`src/equiv/sha256.rs`; no crate in the lock file
has one, and the function is short and fixed, checked against the FIPS
180-4 examples) over:

* the search's version (a constant bumped when the prediction, the
  failure mapping or the try limit changes), the attempt header, and every
  tier's label, script and budget;
* `lake env lean --version`, and the Lake project's `lean-toolchain`,
  `lakefile.toml` and `lake-manifest.json` (which pins Mathlib);
* every Lean file of the path packages the manifest names (the Achates
  runtime in `lean/`, the Aeneas library) and of `equiv/Equiv/` except the
  generated `Proved.lean`;
* the theorem's statement, its unfold list, and the text (header and body)
  of every C and Rust definition it reaches, transitively, as the
  generator's `reach` finds them; for a theorem that assumes
  `StaticsReady`, also everything `Misc.Statics.init` reaches.

So a change to a callee's body, even a comment, changes the key of every
theorem that reaches it and of no other; a change to a tier script, a
budget, the runtime or the toolchain changes every key. The two generated
sides enter only through the definitions reached, so an unrelated change
to `pilot/misc` or to the Aeneas output searches nothing again. Before the
search the run builds the modules the attempts import (`lake build
Equiv.Tactic Equiv.Lemmas Misc MiscRec`): `lake env lean` loads whatever
`.olean` files exist, and the key hashes sources, so the two must agree.

**On a hit** (the entry's key is the theorem's key now):

* **Open**: the theorem is not run; it is reported open with the cached
  reason and tries, marked "cached". An open entry always means that two
  tries were spent or no tier would help, and the search does not depend
  on wall time: budgets are in heartbeats, which vary by a few in a million
  between runs of the same try (`h_to_i`: 4,185,098 and 4,185,101), so a
  rerun with the same key gives the same result unless a theorem needs
  within that margin of its budget. A try whose Lean process stopped without a report
  (killed, out of memory) is never cached.
* **Proved**: the theorem is not run either. Its proof is written into
  `Proved.lean` with the cached tier's script and budget, followed by

  ```lean
  /-- info: 'Equiv.Gen.bstrcmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
  #guard_msgs (whitespace := lax) in
  #print axioms Equiv.Gen.bstrcmp
  ```

  with the message the run accepted, and `make equiv` always ends with
  `make equiv-build`, which builds `Proved.lean`. A proof that no longer
  checks is an error there, and so is a change of its axioms. So the build
  checks every cached proof with the same two conditions the run applies
  (no error, only Lean's own axioms), and running it again in the search
  would only check it twice. `achates equiv --prove` alone, without the
  build, does not check cached proofs.

On a miss the theorem is searched from its predicted tier; the stale
entry's time still orders the queue.

## Timings

All on the same 4 cores, `make equiv` with `--jobs 4`, timed through a
`lake` wrapper that stamps every message of every Lean run:

| Run | Total | Search | Build of `Proved.lean` | Tries | Lean-seconds | Workers busy |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Before (four tiers in turn, four files each) | 2,550 s | 2,520 s | not rebuilt | 125 | 5,829 | 50–64% per tier |
| Cold: empty cache | 1,173 s | 814 s | 357 s | 36 | 2,696 | 85% |
| Warm: cache present, nothing changed | 19 s | no try | not rebuilt | 0 | 0 | |
| One reached definition changed (search only) | 285 s | 285 s | see below | 6 | 381 | |

**Cold.** Every theorem took one try at its predicted tier, and the
prediction was the tier that proved it for all 12. The longest tries are
the five tier-2 budget-outs (`bstr_splice`, `bstrcmp0`,
`is_valid_partial_sequence`, `bstr_equals`, `bstr_equals0`, 278–365 s each),
`h_to_i` (347 s) and `mp_isalnum` (253 s): together 2,300 of the 2,696
Lean-seconds. With no cache there is no cost estimate, so tries start in the
generator's order; `bstr_equals0` and `bstr_equals` start last, at 436 and
456 s, and end the search at 814 s. The 12 proofs pass the same axiom check
as before. Two runs from an empty cache gave the same outcomes and keys;
the heartbeats of a try differ by a few in a million between them
(`h_to_i`: 4,185,098 and 4,185,101).

`Proved.lean` now takes 357 s to build, most of it `h_to_i` (the theorems of
the file are checked in parallel, the longest sets the time). The axiom
checks are at the end of the file: placed after each theorem, `#print
axioms` waited for each proof in turn and the build took 722 s. `make
equiv-build` rebuilds it only when it or an import changed.

**Warm.** All 36 entries hold. The run parses the C, computes the keys,
runs no Lean on a theorem, writes the same `Proved.lean` (so the build has
nothing to do) and leaves `tiers.json` unchanged.

**One definition changed.** A comment added to the body of the C side's
`mp_isupper` (in `pilot/misc/Misc/Misc/Ctype_h.lean`) changed the keys of
the six theorems that reach it: `mp_isupper`, and through it `mp_tolower`,
`mp_isalpha`, `mp_isalnum` (via `mp_isalpha`), `mp_natural_sort_cmp` and
`mp_is_url`. Only those were searched, `mp_isalnum` first (its cached 253
s, the longest), with the same outcomes as before; the search took 285 s,
`mp_isalnum` alone 260 of them. The comment was then reverted (and the
cache with it). In a real change the build afterwards also rebuilds the
changed module and `Proved.lean`, about 6 more minutes.

## Results

| | Count |
| --- | ---: |
| C functions (141 of `misc/` and 33 header helpers) | 174 |
| Paired with a Rust function with a body | 122 |
| Theorems generated | 36 |
| Proved at tier 0 | 1 |
| Proved at tier 1 | 9 |
| Proved at tier 2 | 2 |
| Proved at tier 3 (by hand) | 0 |
| **Proved** | **12** |
| Open | 24 |

Compared with the run before this search, `h_to_i` is proved (tier 1, with
the larger budget) and nothing proved before is lost; the eleven others are
proved at the tier they were proved at before.

Open, by what blocks them (the reason the search recorded, from the first
try's error and what both sides reach; checked by reading each first
error):

| Category | Count | Functions |
| --- | ---: | --- |
| Loop: a C loop needs a fuel bound and an invariant | 8 | `bstrcspn`, `bstrspn`, `bstr_find`, `bstr_lstrip`, `bstr_strip`, `mp_natural_sort_cmp`, `mp_is_url`, `bstr_find0` |
| Loop: a Rust recursion needs an induction (`memchr_loop`, `strchr_loop`; the C side calls a model) | 2 | `bstrchr`, `mp_path_is_absolute` |
| Memory: static tables against Aeneas array constants | 3 | `bstr_strip_linebreaks`, `ucdLookup`, `ucdGraphemeJoins` |
| Memory: a C string argument (`strlen` has no lemma; no script takes `IsCStr` apart) | 3 | `bstr0`, `bstr_endswith0`, `bstr_startswith0` |
| Memory: a form tier 2 does not cover (`bstr_cut`: a `bstr` result built in a local and read back, which needs `decode ∘ encode` for pointers and `size_t`; `bstr_endswith`: pointer arithmetic on a caller's region) | 2 | `bstr_cut`, `bstr_endswith` |
| Budget: out of tier 2's 4 million heartbeats (with more, `is_valid_partial_sequence` leaves a memory goal; the others do not finish or exhaust memory, see "Budgets") | 5 | `bstr_splice`, `bstrcmp0`, `is_valid_partial_sequence`, `bstr_equals0`, `bstr_equals` |
| Arithmetic: a shift by a variable amount (the bind over the C shift's `if` is not lifted) | 1 | `rotl_u64` |

`bstr_endswith0` and `bstr_startswith0` were sorted under Rust recursions
before: their goals name `clib.strlen_loop`, which is the C string's
`strlen`, and `bstr_endswith`'s only loop is `clib.memcmp_loop`, which tier
2 has a lemma for.

Time: see "Timings". The 12 proofs check in 357 s (`Equiv.Proved`), most of
it `h_to_i`, once the project is built.

Per function (the generated 36), from the cold run:

| C | Rust | Shape | Result |
| --- | --- | --- | --- |
| `bstrcmp` | `bstr.bstrcmp` | bstr arguments, scalar result | tier 2 (1 try, 27 s) |
| `bstrchr` | `bstr.bstrchr` | bstr and scalar arguments, scalar result | open after tier 2 (1 try, 4 s): loop: a Rust recursion needs an induction |
| `bstrcspn` | `bstr.bstrcspn` | C string and bstr arguments, scalar result | open after tier 2 (1 try, 6 s): loop: a C loop needs a fuel bound and an invariant |
| `bstrspn` | `bstr.bstrspn` | C string and bstr arguments, scalar result | open after tier 2 (1 try, 6 s): loop: a C loop needs a fuel bound and an invariant |
| `bstr_find` | `bstr.bstr_find` | bstr arguments, scalar result | open after tier 2 (1 try, 19 s): loop: a C loop needs a fuel bound and an invariant |
| `bstr_lstrip` | `bstr.bstr_lstrip` | bstr arguments, bstr view result | open after tier 2 (1 try, 3 s): loop: a C loop needs a fuel bound and an invariant |
| `bstr_strip` | `bstr.bstr_strip` | bstr arguments, bstr view result | open after tier 2 (1 try, 8 s): loop: a C loop needs a fuel bound and an invariant |
| `bstr_splice` | `bstr.bstr_splice` | bstr and scalar arguments, bstr view result | open after tier 2 (1 try, 352 s): budget: out of heartbeats at the top tier for its shape |
| `bstr_strip_linebreaks` | `bstr.bstr_strip_linebreaks` | bstr arguments, bstr view result | open after tier 2 (1 try, 31 s): memory: static tables against Aeneas constants |
| `h_to_i` | `bstr.h_to_i` | scalar arguments, scalar result | tier 1 (1 try, 347 s) |
| `bstr0` | `bstr.bstr0` | C string arguments, bstr view result | open after tier 1 (1 try, 3 s): memory: a C string argument (no script takes `IsCStr` apart; `strlen` has no lemma) |
| `bstr_cut` | `bstr.bstr_cut` | bstr and scalar arguments, bstr view result | open after tier 2 (1 try, 30 s): memory correspondence |
| `bstr_endswith` | `bstr.bstr_endswith` | bstr arguments, scalar result | open after tier 2 (1 try, 5 s): memory correspondence |
| `bstr_endswith0` | `bstr.bstr_endswith0` | C string and bstr arguments, scalar result | open after tier 2 (1 try, 22 s): memory: a C string argument (no script takes `IsCStr` apart; `strlen` has no lemma) |
| `bstr_startswith` | `bstr.bstr_startswith` | bstr arguments, scalar result | tier 2 (1 try, 6 s) |
| `bstrcmp0` | `bstr.bstrcmp0` | C string and bstr arguments, scalar result | open after tier 2 (1 try, 352 s): budget: out of heartbeats at the top tier for its shape |
| `mp_isspace` | `ctype.mp_isspace` | scalar arguments, truth value result | tier 1 (1 try, 5 s) |
| `mp_tolower` | `ctype.mp_tolower` | scalar arguments, scalar result | tier 1 (1 try, 26 s) |
| `mp_isupper` | `ctype.mp_isupper` | scalar arguments, truth value result | tier 1 (1 try, 5 s) |
| `bstr_startswith0` | `bstr.bstr_startswith0` | C string and bstr arguments, scalar result | open after tier 2 (1 try, 18 s): memory: a C string argument (no script takes `IsCStr` apart; `strlen` has no lemma) |
| `ucdLookup` | `codepoint_width.ucd_lookup` | scalar arguments, scalar result | open after tier 1 (1 try, 21 s): memory: static tables against Aeneas constants |
| `ucdGraphemeJoins` | `codepoint_width.ucd_grapheme_joins` | scalar arguments, scalar result | open after tier 1 (1 try, 8 s): memory: static tables against Aeneas constants |
| `ucdGraphemeDone` | `codepoint_width.ucd_grapheme_done` | scalar arguments, scalar result | tier 0 (1 try, 3 s) |
| `ucdToCharacterWidth` | `codepoint_width.ucd_to_character_width` | scalar arguments, scalar result | tier 1 (1 try, 2 s) |
| `is_valid_partial_sequence` | `codepoint_width.is_valid_partial_sequence` | bstr arguments, scalar result | open after tier 2 (1 try, 278 s): budget: out of heartbeats at the top tier for its shape |
| `mp_isalnum` | `ctype.mp_isalnum` | scalar arguments, truth value result | tier 1 (1 try, 253 s) |
| `mp_isalpha` | `ctype.mp_isalpha` | scalar arguments, truth value result | tier 1 (1 try, 38 s) |
| `mp_isdigit` | `ctype.mp_isdigit` | scalar arguments, truth value result | tier 1 (1 try, 6 s) |
| `mp_islower` | `ctype.mp_islower` | scalar arguments, truth value result | tier 1 (1 try, 5 s) |
| `mp_natural_sort_cmp` | `natural_sort.mp_natural_sort_cmp` | C string arguments, scalar result | open after tier 1 (1 try, 22 s): loop: a C loop needs a fuel bound and an invariant |
| `bstr_equals0` | `bstr.bstr_equals0` | C string and bstr arguments, scalar result | open after tier 2 (1 try, 365 s): budget: out of heartbeats at the top tier for its shape |
| `bstr_equals` | `bstr.bstr_equals` | bstr arguments, scalar result | open after tier 2 (1 try, 358 s): budget: out of heartbeats at the top tier for its shape |
| `mp_path_is_absolute` | `path_utils.mp_path_is_absolute` | bstr arguments, scalar result | open after tier 2 (1 try, 4 s): loop: a Rust recursion needs an induction |
| `mp_is_url` | `path_utils.mp_is_url` | bstr arguments, scalar result | open after tier 2 (1 try, 25 s): loop: a C loop needs a fuel bound and an invariant |
| `bstr_find0` | `bstr.bstr_find0` | C string and bstr arguments, scalar result | open after tier 2 (1 try, 23 s): loop: a C loop needs a fuel bound and an invariant |
| `rotl_u64` | `random.rotl_u64` | scalar arguments, scalar result | open after tier 1 (1 try, 11 s): arithmetic or unfolding |

## Worked example: `bstrcmp`

The statement, as generated (`equiv/Equiv/Proved.lean`):

```lean
set_option maxHeartbeats 4000000 in
theorem bstrcmp (m : Achates.Mem) (str1 : Achates.Agg) (s_str1 : Aeneas.Std.Slice Aeneas.Std.U8)
    (h_str1 : Equiv.IsBstr m str1 s_str1) (str2 : Achates.Agg)
    (s_str2 : Aeneas.Std.Slice Aeneas.Std.U8) (h_str2 : Equiv.IsBstr m str2 s_str2) :
    Equiv.Equal (fun r m' y => Equiv.Unchanged m m' ∧ y = (Equiv.i32 r))
      (fun fuel => Misc.Misc.Bstr_c.bstrcmp fuel str1 str2) m
      (rmpv_misc.bstr.bstrcmp s_str1 s_str2) := by
  equiv_tier2 [Misc.Misc.Bstr_c.bstrcmp, rmpv_misc.bstr.bstrcmp, rmpv_misc.clib.memcmp]
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

None of the 24 open theorems has a counterexample, and none of them was
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
evidence for the 24 open ones.

## What blocked the open theorems

Each category with what would unblock it, and the estimated share of
`misc/` it would add (counts of generated theorems, then of paired
functions it would make generatable):

1. **Loops, 10 of the 24 open** (and the C-string ones of item 2 also need
   the Rust `strlen_loop`). The missing lemma is a simulation rule
   between the runtime's `Fuel.loop` and an Aeneas recursion: given a
   relation between the two loop states, an invariant and a measure that
   decreases, the loops agree with fuel at least the measure. It has to be
   proved once (by induction on the measure) and then instantiated; the
   invariant is the part a tier cannot guess. For the `bstr` loops here the
   invariant is "the index is the same on both sides and at most the
   length", which a template per loop shape (index walk over a slice,
   `while (*p)` over a string) could state mechanically. The Rust-only
   recursions (`memchr`, `strchr`) need a lemma per library function, like
   `memcmp_ok`. Estimate: 8 to 10 more theorems.
2. **Memory forms, 5** (3 C strings, `bstr_cut`, `bstr_endswith`), and
   behind the budget, `bstr_splice` and the `0` variants. A lemma that `decode` inverts `encode` for pointers
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
4. **Budget, 5, all at tier 2.** `bvk` (natural numbers and `omega`) is
   much slower than `bv_decide`: `h_to_i` was proved in 30 seconds with
   `bv_decide`, and now takes 4.2 million heartbeats (347 s) with `bvk`
   under tier 1's larger budget. The five tier-2 ones do not close with
   more budget ("Budgets"): `is_valid_partial_sequence` then reaches the end
   of the script with a memory goal, and the others grow in memory faster
   than they progress. They need the memory lemmas of item 2 (`bstrcmp0`,
   `bstr_equals0`: `strlen`; `bstr_splice`: `decode ∘ encode`) or a
   smaller symbolic state, not heartbeats. Estimate: 0 to 3 by budget
   alone, none measured.
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

**Proofs: at a low rate today, 12 of 36 (33%), and only for loop-free
functions.** Scalar functions with branches and arithmetic go through a
fixed script (tier 1, 9 of the 13 scalar ones; tier 0 the tenth). Loop-free functions over
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

The cost of the attempt is worth stating: about 20 minutes of machine
time for a run from an empty cache (it was 42 before the search was
changed), most of it seven tries that use or nearly use their whole
budget and the build of `h_to_i`; a run with nothing changed takes 20
seconds. The tier 2 lemmas took the largest part of the work (the symbolic
memory steps, the frame conditions and the `memcmp` inductions on both
sides).

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
* **More budget can cost memory before it buys time.** Run without a
  heartbeat limit, three tier-2 theorems grew past 5 GB (one to 8.9 GB) in
  about twice the old budget's time, and the kernel killed two of them
  while four ran at once on 16 GB. A budget is also a memory bound.
* **`#print axioms` serialises a file.** Lean checks the theorems of a file
  in parallel, but `#print axioms` waits for the proof it names; one after
  each theorem made `Proved.lean` build in 722 s instead of 357 s. The
  axiom checks are at the end of the file.
* **No Achates bug was found.** No change to the emitter or the runtime was
  made in this worktree.
