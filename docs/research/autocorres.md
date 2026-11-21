# AutoCorres and AutoCorres2 on mpv's C

Research and hands-on spike, 2026-11-21. Lines marked "observed" come from
running AutoCorres2 in `/home/user/spike-autocorres`. Lines marked
"documented" come from a source I read; the source is named in the row.
Raw logs and summaries are in `/home/user/spike-autocorres/results/` and in
the `run_*.log` files under `probe/` and `mpv/`.

## Verdict

Not usable out of the box, and not usable with a small, defined set of
changes either. AutoCorres2 (the maintained fork, AFP release for
Isabelle2026) installs and runs. It produced a correct-looking monadic model
of `mp_natural_sort_cmp` and of most of `misc/random.c` with no hand-writing
of semantics. But it rejects every real mpv translation unit, because the
system headers alone contain `double`, variadic prototypes and GNU spellings
such as `__restrict`. It also rejects or cannot finish constructs that mpv
uses all the time: floating point, string literals in expressions, variadic
functions, function-pointer calls through struct fields unless each call is
annotated, bitfields, static locals, GNU statement expressions and side
effects through pointers inside expressions. Library calls such as `memcmp`
need a hand-written specification or become opaque constants. Even if all of
that were fixed, the output lives in Isabelle/HOL, and no maintained route
connects it to Aeneas's Lean output. Achates should borrow AutoCorres's
design, not its code.

## 1. What AutoCorres and AutoCorres2 are

- AutoCorres takes C that Norrish's C parser has translated into Schirmer's
  Simpl language and abstracts it into a shallow monadic embedding, with an
  Isabelle proof that the abstraction is correct (documented: Greenaway et
  al., PLDI 2014, "Don't sweat the small stuff",
  <https://www.trustworthy.systems/publications/nicta_full_text/7629.pdf>).
- Because it uses the C parser's output, AutoCorres "supports the same C
  subset as the parser" (same paper, section 2).
- The original AutoCorres lives in the seL4 `l4v` repository under
  `tools/autocorres`, "packaged as a theory for Isabelle2025", for ARM, X64
  and RISCV64. Its README tells users to consider AutoCorres2 first
  (documented: <https://github.com/seL4/l4v/blob/master/tools/autocorres/README.md>).
- AutoCorres2 is a fork in the Archive of Formal Proofs. The entry was
  published 2024-04-17. The AFP has releases of it for Isabelle2024,
  Isabelle2025, Isabelle2025-1, Isabelle2025-2 and Isabelle2026
  (2026-10-26) (documented: <https://www.isa-afp.org/entries/AutoCorres2.html>).
  Its theory files carry Apple Inc. copyright notices (observed in the
  source). Its README lists Hölzl, Immler, Schirmer, Sickert-Zehnter and
  Wimmer as authors of the new material.
- Maintenance: active. A new AFP release follows each Isabelle release. The
  `NEWS` file in the AFP source has sections for Isabelle2024, 2025 and
  2025-1. The 2025-2 and 2026 releases add no NEWS section (observed in
  `afp-2026-11-19/thys/AutoCorres2/NEWS`).

### What AutoCorres2 added over AutoCorres

From `AutoCorres2/NEWS` in the AFP 2026-11-19 snapshot (documented):

| Version | Addition |
| --- | --- |
| Isabelle2024 | New `spec_monad` replaces `nondet_monad`; single-variant unions and same-size packed multi-variant unions; pointers to local variables (the local is moved to the heap); in-out parameter abstraction; heap lifting with pointers into structures; "well-behaved" forward `goto`; `exit()`; function pointers (constant parameters, global dispatch tables, struct fields of "C-style objects"); `typeof`, `offsetof`, `aligned` attribute; parallel processing; the C parser no longer needs MLton (ML-Lex/ML-Yacc run inside Isabelle/ML) |
| Isabelle2025 | Post-increment/decrement on locals in assignments and loop conditions; anonymous structs and unions; function and array decay; flexible array members |
| Isabelle2025-1 | Some GNU statement expressions; `++`/`--`/chained assignment in expressions, for local variables only; struct layout cross-check against clang; C23 `_BitInt`; a "closed-world" model of function pointers, where unknown targets need prototypes with user specifications |

The C parser manual shipped in the same snapshot
(`c-parser/doc/ctranslation_body.tex`, section "StrictC Subset Summary")
still says "No goto", "No unions" and "No fall-through cases". NEWS
supersedes it for `goto` and unions.

## 2. C constructs

"Observed" rows come from a one-construct C file in
`/home/user/spike-autocorres/probe/c/` run through `install_C_file` and then
`autocorres` (theories `probe/P*.thy`). The error text is copied from the
log, shortened only where marked "...".

| Construct | Result | Kind | Source or error |
| --- | --- | --- | --- |
| `double` | Rejected by parser | observed, documented | `syntax error: replacing ID with YENUM ... double` (P01). l4v C parser README lists "Floating-point types" as unsupported. Lexer has no `float`/`double` token; `Absyn-CType.ML` line 271: `arithmetic_type = integer_type (* in the absence of floating types *)` |
| `float` | Rejected by parser | observed | `syntax error: replacing ID with YENUM ... float` (P02) |
| `long double` | Rejected by parser | observed | `Two type-specifiers ... double` (P03) |
| Floating literal (`0x1.0p-53`) | Rejected by parser | observed | `syntax error: deleting NUMERIC_CONSTANT` (P27, H_random_v) |
| Function pointer parameter, called directly | Accepted | observed | P04. Output `apply' f a b ≡ 𝒫 f a b` |
| Function pointer in a global `const` table | Accepted | observed, documented | P30. NEWS 2024: "Dispatching of function pointers via global static variable" |
| Function pointer in a struct field (`o->get(o->ctx)`) | Rejected unless each call is annotated | observed | `Could not infer any potential function pointer callees in call_ops. Maybe annotate call with '__attribute__((calls(...)))'` (P05). With `__attribute__((calls(get_a)))` before the statement it is accepted (P43) |
| Function pointer whose parameter is a function pointer | Not supported | documented | NEWS 2024: "higher-order function pointer parameters unsupported" |
| Union, same-size variants | Accepted | observed | P06 |
| Union, different-size variants inside a struct | Accepted | observed | P07 (`long long`/`void *`/`char`). NEWS 2024 says only "packed variants with the same size" are supported; I did not check whether the model of this case is sound |
| Forward `goto` to a cleanup label | Accepted | observed, documented | P08. NEWS 2024: "wellbehaved goto statements" |
| Backward `goto` | Rejected | observed | `invalid goto label 'again'. Only block-structured nested gotos are supported` (P09) |
| `switch` fall-through | Rejected | observed, documented | `Switch case beginning here does not end with a break or return or a nested switch statement` (P10). l4v C parser README |
| Variadic function definition (`...`, `va_list`) | Rejected | observed, documented | `syntax error: deleting YDOT YDOT YDOT` and errors inside gcc's `stdarg.h` (P11). l4v C parser README: "Variadic argument lists" |
| Variadic prototype (`printf`) | Rejected | observed | `syntax error: deleting YDOT YDOT YDOT` (P12). This is what breaks every glibc header |
| Address of a local variable | Accepted | observed, documented | P13. Local moved to a fresh stack heap cell (`assume_with_fresh_stack_ptr`). NEWS 2024 |
| Bitfield, read of a field | Rejected | observed | `exception Fail ... program_analysis.ML: Type of returned expression (unsigned:3) incompatible` (P14). With the read copied to a local first: `exception Fail raised (line 193 of ".../calculate_state.ML"): Can't cope with bitfields` (P46) |
| Struct passed and returned by value | Accepted | observed | P15. `mk' s n ≡ bstr_C s n` |
| Compound literal | Accepted | observed | P15, P16 |
| Designated initializer | Accepted | observed | P29 |
| GNU statement expression (mpv `MPMAX` style) | Rejected here | observed, documented | `You may not use "StrictC'_a" as a variable name; you might try turning on the "allow_underscore_idents" config variable` (P17). NEWS 2025-1 says "some forms" are supported. I did not retry with that option |
| `__typeof__` | Rejected | observed | `syntax error: inserting YSEMI` (P18). Plain `typeof` is a keyword in the lexer (documented in NEWS 2024); the GNU spelling is not |
| `_Atomic` | Rejected | observed | `Bad combination with 'int' ... _Atomic` (P19) |
| `_Thread_local` | Accepted, modelled as an ordinary global | observed | P36: `gettl' ≡ sint tl`. The model is sequential (PLDI 2014: input is "sequential C") |
| Inline assembly (`__asm__ volatile`) | Parsed; AutoCorres crashed | observed | `exception MATCH raised (line 351 of "pattern.ML") At command "autocorres"` (P20) |
| `++`/`+=` through a pointer inside an expression | Parsed with an internal proof failure | observed, documented | P21 and `splitmix64` in random.c: `Proof failed ... Call ...splitmix64 {t. t may_not_modify_globals σ}`. The theory is then marked failed. NEWS 2025-1: such side effects are allowed "only for local variables" |
| Two calls that write the same global in one expression | Rejected | observed | `expecting local variable` (P45, `next() + next()`) |
| `static` local variable | Rejected | observed, documented | `expecting local variable` (P23). l4v C parser README |
| Function call inside `?:` and `&&` | Accepted | observed | P24, P25 |
| `while (*s++)` | Accepted | observed | P38 |
| Pointer difference | Accepted | observed | P22. `d' a b ≡ sint (b -p a)` |
| Flexible array member | Accepted | observed | P28 |
| `void *` to struct pointer | Accepted | observed | P31 |
| `do`/`while` with `break` | Accepted | observed | P32 |
| Local `char` array | Accepted | observed | P33 |
| Local `char s[] = "abc"` | Rejected | observed | `exception Fail ... Array s initialised with non-constant expression` (P42) |
| String literal as an expression (`puts("hello")`) | Rejected | observed | `Don't want to handle string literals!` (P41, and the `assert` call in random.c) |
| `unsigned __int128` | Accepted | observed | P34 |
| `__builtin_expect` | Accepted | observed | P35. Output drops it: `be' x ≡ if 0 < x then 1 else 0` |
| `_Generic` | Rejected | observed | `syntax error: deleting INT YCOLON ... int:` (P37) |
| `_Static_assert` | Rejected | observed | `syntax error: replacing ID with YTYPEOF ... _Static_assert`, then `exception Match raised (line 303 of ".../StrictC.grm.sml")` (P39) |
| `enum` and `switch` with `default` | Accepted | observed | P40 |
| GNU `__restrict`, `__extension__`, `__attribute__((__malloc__(f,1)))`, `__alignof__` in glibc headers | Rejected | observed | `syntax error: replacing ID with YSTAR ... __restrict` and similar; 4 732 of the error regions in the whole-file runs were `*__restrict` |
| glibc `assert()` expansion (`(c) ? (void)0 : __assert_fail(..., __extension__ __PRETTY_FUNCTION__)`) | Rejected | observed | `syntax error: inserting YSTAR` (H_random_b) |
| Identifiers starting with `__` | Rejected by default | observed | `__assert_fail is an illegal name for a function`. Accepted after `declare [[allow_underscore_idents]]` |
| `pthread.h` | Rejected (headers contain `double`) | observed | Errors in `/usr/include/time.h` (P44) |
| Function with a prototype but no body (libc) | Translation stops | observed, documented | `No implementation or specification for function prototype: free. Use option 'no_body' or provide a specification by overloaded definition of: free_body` (P26). With `[no_body = ...]` the call becomes an opaque constant (P47, H_bstr_nb). `tests/proof-tests/fnptr_proto.thy` documents the specification route (`declare_prototype`) |
| `exit()` | Supported | documented | NEWS 2024 |
| 64-bit target | Supported (X64, ARM64, RISCV64) | documented, observed | `c-parser/Target_Architecture.thy`; selected by the `L4V_ARCH` environment variable. The default is 32-bit ARM. I built for X64 and the output uses `64 word` for `uint64_t` and pointers |

### Other points about the parser

- Unsigned and signed arithmetic are modelled at the bit level, with guards
  for undefined behaviour. Examples observed: `rotl_u64'` begins with
  `oguard (λ_. k ≤ 64 ∧ 0 < k ∧ k < 64)` for the shift; signed `n + 1` gets
  `guard (λs. i < INT_MAX)`; every heap read gets `IS_VALID(...)`.
- The parser runs `/usr/bin/cpp` itself. When clang is installed it also
  compiles the file with clang to cross-check struct layouts (NEWS 2025-1).
  On gcc-preprocessed glibc headers this check fails first
  (`clang error: unknown type name '_Float32'`). Turn it off with
  `declare [[clang_path=""]]`.

## 3. Installation and runs

Machine: Ubuntu 24.04, 4 cores, 15 GB RAM. The session's memory cgroup limit
is 14.3 GB (seen in `dmesg`).

| Step | Command | Time | Result |
| --- | --- | --- | --- |
| Download Isabelle | `curl -sS -o Isabelle2026_linux.tar.gz "https://dists.isabelle.cit.tum.de/dist/Isabelle2026_linux.tar.gz?token=Isabelle"` | ~2 min, 1.41 GB | The link on `isabelle.in.tum.de/installation.html` redirects to plain `http://`, which the proxy refused (`503`); the `https://` form of the redirect target works |
| Download AFP | `curl -sSL -o afp-current.tar.gz https://www.isa-afp.org/release/afp-current.tar.gz` | seconds, 106 MB | Snapshot `afp-2026-11-19` |
| Unpack | `tar -xzf ...` for both | 21 s | Isabelle2026 ships Poly/ML 5.9.2 (`x86_64_32`), with `Pure` and `HOL` heaps prebuilt |
| Register AFP | `Isabelle2026/bin/isabelle components -u $PWD/afp/afp-2026-11-19/thys` | instant | |
| Build, attempt 1 | `isabelle build -b -v -j 2 -o threads=2 AutoCorres2` | stopped by me | `L4V_ARCH` was unset, so it would have built for 32-bit ARM |
| Build, attempt 2 | `L4V_ARCH=X64 isabelle build -b -v -j 2 -o threads=3 AutoCorres2` | 10.5 min | `Simpl` built (2 min 46 s). `AutoCorres2` killed by the kernel OOM killer (`poly` at 8.3 GB RSS, exit 137) |
| Settings | `~/.isabelle/Isabelle2026/etc/settings`: `ML_OPTIONS="--minheap 1000 --maxheap 10000 --enablegcsharing"`, `ISABELLE_TOOL_JAVA_OPTIONS="... -Xmx1500m ..."`, `L4V_ARCH=X64` | | |
| Build, attempt 3 | `isabelle build -b -v -j 1 -o threads=4 AutoCorres2` | 21 min 25 s wall, 43 min CPU | Success. `AutoCorres2` session alone: 20 min 44 s |
| Probes | `cd probe; isabelle process_theories -l AutoCorres2 -O -D . P01_double ... P40_enum_switch` | 1 min 35 s for 40 theories | See section 2 |
| mpv whole files | `cd mpv; isabelle process_theories -l AutoCorres2 -O -D . M_bstr ... M_thread_tools` | 1 min 47 s for 15 theories | See section 4 |

Total machine time from first download to a working heap: about 40 minutes.
Each theory is `install_C_file "c/x.c"`, then `autocorres "x.c"`, then `thm`
of each generated definition in the locale `x_global_addresses`. `ML`
markers record how far each theory got. `scripts/summarize2.py` turns a log
into the per-theory summaries in `results/`.

The mpv inputs were preprocessed with the exact flags from
`/home/user/rmpv/formal/.mpv-build/compile_commands.json`, with `-c`, `-o`,
`-M*` and warning flags removed and `-E -P` added. Output is in
`/home/user/spike-autocorres/mpv_pp/*.i`.

## 4. mpv files and functions tried

### Whole files, preprocessed, unchanged

All 15 `misc/` files listed in the task, with `[[clang_path=""]]`.

| File | Result | Errors | First causes |
| --- | --- | --- | --- |
| natural_sort.c | Accepted. All 10 functions translated and printed | 0 | Its only include is mpv's `misc/ctype.h`, which has no system headers |
| bstr.c, charset_conv.c, codepoint_width.c, dispatch.c, hash.c, io_utils.c, json.c, language.c, node.c, path_utils.c, random.c, rendezvous.c, thread_pool.c, thread_tools.c | Rejected by the parser | 567 to 3 295 per file | glibc headers: `__restrict`, `__attribute__`, variadic prototypes (`__format, ...`), `double`, `_Float32`, `__alignof__`, bitfields in `pthread` types (`:32`) |

The 14 rejected files fail before the parser reaches any mpv code. A real
fix needs a header-pruning pass that removes unused declarations from the
preprocessed file and rewrites GNU spellings. That pass would also have to
supply a specification for every libc function that remains.

### `mp_natural_sort_cmp` (misc/natural_sort.c)

Accepted as is, in 9.4 s for the `autocorres` command. The output
(`results/natural_sort_autocorres_output.txt`) is a `finally`/`whileLoop`
program in the exception monad over a byte heap `heap_w8`. Every read is
guarded by `IS_VALID(8 word)`. Early `return -1`/`return 1` become
`throw`. `(end1 - name1) < (end2 - name2)` becomes
`sint (end1 -p name1) < sint (end2 -p name2)`. I did not prove anything
about it.

### misc/random.c, extracted by hand

Bodies copied verbatim from the preprocessed file, plus 9 lines of typedefs
and prototypes in place of the headers.

| Stage | Change | Result |
| --- | --- | --- |
| v | none | Rejected: `mp_rand_next_double` (`double`, `0x1.0p-53`) |
| b | delete `mp_rand_next_double` | Rejected: the glibc `assert` expansion in `mp_rand_in_range32` |
| c | `assert` → `if (!(min < max)) __assert_fail("min < max", ...)` | Rejected: `__assert_fail is an illegal name`; with `allow_underscore_idents`: `Don't want to handle string literals!` |
| d | → `if (!(min < max)) abort();` plus `[no_body = av_random_bytes mp_raw_time_ns mp_round_next_power_of_2 abort]` | All 5 functions translated, but `splitmix64` fails its internal "may not modify globals" proof, so the theory fails |
| e | `uint64_t z = (*x += C);` → `*x += C; uint64_t z = *x;` | Accepted, no errors |

So 5 of 6 functions went through after three source rewrites and four
`no_body` declarations. The sixth (`mp_rand_next_double`) cannot be
translated at all. `mp_rand_seed`, which casts `&mp_rand_seed` and `&ret` to
integers, was accepted; the output uses `ptr_val`.

### misc/bstr.c, extracted by hand

`bstrcmp`, `bstrchr`, `bstrcspn`, `bstr_lstrip` and `mp_isspace`, verbatim
from the preprocessed file, with `struct bstr` and the prototypes of
`memcmp`, `memchr` and `strchr`.

- As is: `No implementation or specification for function prototype: memchr`.
- With `[no_body = memcmp memchr strchr]`: accepted
  (`results/bstr_nb_output.txt`). The libc calls become opaque constants
  such as `memcmp' p q n`. Nothing is known about what they return, so no
  useful property of `bstrcmp` can be proved until someone writes a
  specification for `memcmp`.

### Construct counts in the pilot folder

Rough `grep -cw` counts in the mpv sources (not parsed; comments and
includes count too):

| File | `double`/`float` | `goto` | `...`/`va_list` | mutex/cond/pthread |
| --- | --- | --- | --- | --- |
| bstr.c | 2 | 0 | 6 | 0 |
| json.c | 2 | 0 | 0 | 0 |
| path_utils.c | 0 | 3 | 1 | 0 |
| codepoint_width.c | 0 | 6 | 0 | 0 |
| charset_conv.c | 0 | 2 | 0 | 0 |
| dispatch.c | 1 | 0 | 0 | 40 |
| thread_tools.c | 1 | 0 | 0 | 34 |
| thread_pool.c | 0 | 0 | 0 | 21 |

All `goto`s in these files jump forward to a label at the end of the
function (`exit`, `done`, `failure`, `next`), so they look like the
"well-behaved" kind. I did not run those functions. One label in
`path_utils.c` is named `exit`, and AutoCorres2 gives `exit` special
meaning; I did not test whether that collides.

## 5. Cross-prover question

- Aeneas has backends for F*, Coq, HOL4 and Lean. Its README says "Our most
  mature backends are Lean and HOL4" and "We would be interested in having
  an Isabelle backend" (documented: <https://github.com/AeneasVerif/aeneas>,
  README). There is no Isabelle backend.
- HOL4 to Isabelle: Immler, Rädle and Wenzel (ITP 2019) ran HOL4 inside
  Isabelle's ML runtime with a virtual kernel that builds Isabelle/HOL
  theorems (documented: <https://drops.dagstuhl.de/opus/volltexte/2019/11076/>).
  The code, `immler/hol4isabelle`, is one commit, tested with Isabelle2019
  and one fixed HOL4 commit (documented: <https://github.com/immler/hol4isabelle>).
  Isabelle2026 ships an importer for HOL Light only
  (`src/HOL/Import/HOL_Light_Import.thy`, observed). So the route
  "Aeneas → HOL4 → Isabelle" would mean reviving a 2019 research artifact
  for Isabelle2026 and a current HOL4. I did not try it.
- Lean to Isabelle or back: a web search found no tool. I did not read
  further, so treat this as "none found", not "none exists".
- Even inside one prover the two models differ. Aeneas's semantics is
  "value-based, meaning there is no notion of memory, addresses or pointer
  arithmetic" (documented: <https://arxiv.org/abs/2206.07185>). AutoCorres's
  output reads and writes typed heaps (`heap_w8`, `heap_mp_rand_state_C`)
  with validity guards. An equivalence proof needs a relation between C heap
  states and Rust values in every case that involves pointers, whichever
  prover holds both sides.

Answer: no practical route today. To use AutoCorres2 output, the Rust side
would have to move to Isabelle, and there is no Rust-to-Isabelle translator
in the Aeneas toolchain. Writing an Isabelle backend for Aeneas, or reviving
the HOL4 bridge, is a project of its own and still leaves the C front end
problems in section 2. Building Achates for Lean keeps both sides in one
prover with tools that already exist on the Rust side.

## 6. What Achates should take from AutoCorres

Copy:

- **Two layers with a proof between them.** A literal, conservative model
  first (Simpl in AutoCorres), then automatic abstraction to a readable
  model with a machine-checked refinement theorem per function
  (`..._ac_corres`). The literal layer is what reviewers trust; the
  abstract layer is what proofs use.
- **Undefined behaviour as explicit guards.** Every heap access, shift and
  signed operation gets a guard, and a failed guard is program failure in
  the monad. This lines up with Aeneas's `Result` (`ok`/`fail`), so a
  Rust-equals-C theorem can say "if C does not fail, Rust returns the same
  value".
- **A state, exception and failure monad.** AutoCorres2 uses `exn_monad`
  with nested sum types for `break`, `continue`, `return`, `goto` and
  `exit` (NEWS 2024). Forward `goto` maps onto the same exception
  mechanism. mpv's cleanup `goto`s fit this.
- **Type strengthening.** AutoCorres picks the weakest monad that fits each
  function (`pure`, `gets`, `option`, `nondet`; seen in the logs as
  `--> pure`, `--> option`). Pure C helpers then come out as plain
  functions, which are easiest to compare with Aeneas output.
- **Heap abstraction (split heaps).** One typed heap per C type with
  `IS_VALID` predicates, derived from a byte-level heap with a proof. This
  is the right target for comparison with Aeneas's value-based model.
- **Word abstraction, as an option.** Mapping words to `Int`/`Nat` with
  overflow guards makes proofs easier, but Aeneas keeps Rust integers as
  bounded types. Achates should offer both, and default to bounded types so
  the two sides match.
- **Moving address-taken locals to the heap**, and the in-out parameter
  abstraction that turns `f(&x)` back into value passing (NEWS 2024). This
  matches how Aeneas returns updated `&mut` arguments.
- **Explicit contracts for external functions.** AutoCorres2 refuses to
  continue past a bodiless prototype until the user says "opaque" or gives a
  specification. Achates should do the same, and ship a library of libc and
  FFmpeg specifications.

Do differently:

- **Use clang as the front end.** The StrictC grammar cannot read glibc
  headers. clang already parses all of mpv with the real flags. Achates's
  front end does this (see `docs/frontend-report.md`).
- **Model floating point.** mpv uses `double` widely. Achates needs IEEE
  binary64 in Lean with the build's flags in mind (`-fno-math-errno`,
  `-fno-signed-zeros` and `-fno-trapping-math` are in the compile command).
- **Handle variadic functions and string literals.** At least as calls to
  specified externals (`mp_msg`, `snprintf`), with string literals as
  read-only global byte arrays.
- **Open-world function pointers.** mpv calls callbacks stored in structs
  everywhere. Model a function pointer as a value that maps to a known
  function or to a specified unknown one, without per-call annotations.
- **Concurrency.** AutoCorres is sequential, and it modelled
  `_Thread_local` as an ordinary global. dispatch.c, thread_pool.c and
  thread_tools.c need at least a model of mutexes and condition variables,
  or a decision to verify only their sequential parts.
- **Fail loudly and in one place.** AutoCorres2 accepted `*x += C` inside an
  expression and then failed an internal proof, and it crashed on inline
  assembly after parsing it. Achates should reject an unsupported construct
  in the front end with a message naming the construct.
- **Target the build's ABI by default.** AutoCorres2 defaults to 32-bit ARM
  unless `L4V_ARCH` is set. Achates should take target sizes and layout
  from the compile command.

## 7. Not verified

- Whether the different-size union model (P07) is sound, and whether the
  `exit` label in `path_utils.c` collides with AutoCorres2's `exit` support.
- Whether GNU statement expressions are accepted with
  `allow_underscore_idents` turned on.
- How AutoCorres handles mpv's real forward-`goto` functions (I tested only
  a small cleanup example).
- Performance on large functions. The largest function tried was
  `mp_rand_seed`.
- Whether anyone has applied AutoCorres or AutoCorres2 to C that was not
  written for verification. The PLDI 2014 evaluation used seL4, CapDL
  SysInit, Piccolo, eChronos and Schorr-Waite, all from verification
  projects. The only AFP entry that depends on AutoCorres2, Munta, imports
  only its `Subgoals` library theory (observed in `Munta_Model_Checker/ROOT`).
  I found no report of AutoCorres2 on general application code, and I did
  not find which Apple code it is used on.
- No Lean–Isabelle translator was found; this is a search result, not a
  proof of absence.

## Sources read

- AFP entry: <https://www.isa-afp.org/entries/AutoCorres2.html>; AFP download page <https://www.isa-afp.org/download/>
- AFP snapshot `afp-2026-11-19`, `thys/AutoCorres2/`: `README.md`, `NEWS`, `ROOT`, `c-parser/doc/ctranslation_body.tex`, `c-parser/StrictC.lex`, `c-parser/Absyn-CType.ML`, `c-parser/calculate_state.ML`, `c-parser/isar_install.ML`, `c-parser/Target_Architecture.thy`, `tests/proof-tests/fnptr_proto.thy`, `doc/quickstart/Chapter1_MinMax.thy`
- l4v C parser README: <https://github.com/seL4/l4v/blob/master/tools/c-parser/README.md>
- l4v AutoCorres README: <https://github.com/seL4/l4v/blob/master/tools/autocorres/README.md>
- AutoCorres project page: <https://trustworthy.systems/projects/OLD/autocorres/>
- Greenaway, Lim, Andronick, Klein, PLDI 2014: <https://www.trustworthy.systems/publications/nicta_full_text/7629.pdf>
- Isabelle home page (Isabelle2026, October 2026): <https://isabelle.in.tum.de/>
- Aeneas README: <https://github.com/AeneasVerif/aeneas>; Aeneas paper abstract: <https://arxiv.org/abs/2206.07185>
- Immler, Rädle, Wenzel, ITP 2019: <https://drops.dagstuhl.de/opus/volltexte/2019/11076/>; <https://github.com/immler/hol4isabelle>
