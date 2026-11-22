# Front end report

The front half of Achates reads C through clang 18 and produces a typed
intermediate representation (IR) of each function. This report describes the
IR, the clang command line, the result on mpv's `misc/`, the decisions the
task left open, and the known gaps.

Usage:

```sh
achates survey --compile-commands PATH --select misc/
achates dump --compile-commands PATH --select misc/bstr.c --function bstrcmp
achates dump ... --function bstrcmp --json   # for programs
achates survey ... --no-reachable-inlines      # main-file functions only
```

By default, `survey` and `dump` add every header function with a body that
the selected functions reach (see "Header functions and external callees").

## Result on `misc/`

`achates survey --compile-commands /home/user/rmpv/formal/.mpv-build/compile_commands.json --select misc/`

**141 of 141 functions fully represented, in 15 files.** No `Unsupported`
node occurs in any of them, in their types, or in the fields of any record
they reach.

**Stricter figure: 141 of 141** are fully represented together with every
header function they reach. **33 header functions** are reachable: 32 from
project headers and 1 from a system header (glibc's `bsearch`), all 33 fully
represented. The selection names **90 external functions** that it does not
define.

| File | Functions | Fully represented |
| --- | ---: | ---: |
| bstr.c | 36 | 36 |
| charset_conv.c | 5 | 5 |
| codepoint_width.c | 6 | 6 |
| dispatch.c | 15 | 15 |
| hash.c | 1 | 1 |
| io_utils.c | 2 | 2 |
| json.c | 13 | 13 |
| language.c | 4 | 4 |
| natural_sort.c | 1 | 1 |
| node.c | 13 | 13 |
| path_utils.c | 17 | 17 |
| random.c | 6 | 6 |
| rendezvous.c | 1 | 1 |
| thread_pool.c | 7 | 7 |
| thread_tools.c | 14 | 14 |

Table of unsupported constructs on `misc/`: empty.

The survey also lists the compiler builtins and atomic operations that
functions use. They are represented exactly (as calls, or as atomic nodes),
but a back end needs a model of each:

| Functions | Builtin or atomic operation |
| ---: | --- |
| 3 | `__builtin_va_end` |
| 2 | `__builtin_va_start` |
| 1 | `__builtin_va_copy` |
| 2 | `__builtin_isfinite` |
| 2 | `__c11_atomic_store` |
| 1 | `__c11_atomic_load` |

### Why 141 and not 178

The 141 are the function definitions clang sees in the 15 compiled files,
after preprocessing with the build's flags. The pilot's 178 counts 16 files
on preprocessed source. The difference:

- `jni.c` (9 functions) is not in the compilation database: it is not built
  on this configuration.
- 3 definitions are inside disabled `#if` blocks: `bstr_to_wchar`
  (`_WIN32`), `mp_cancel_get_event` (Windows) and `mp_uchardet`
  (`HAVE_UCHARDET`).
- The rest are `static inline` functions from headers. The functions in
  `misc/` call 29 distinct ones, 93 call sites in all: `bstr0` (15
  functions), `ta_oom_p` (12), `bstr_cut` (8), `mp_cond_broadcast` (8),
  `mp_cond_wait` (6), and 24 more from `bstr.h`, `ta.h`, `threads-posix.h`,
  `ctype.h` and glibc's `stdlib-bsearch.h`. They are not among the 141, but
  they and the 4 they reach in turn are now in the IR as header functions;
  see the next section.

### Header functions and external callees

With header functions included (the default), each translation unit also
holds every function with a body, defined in a header, that a selected
function names, directly or through other header functions. Naming covers
calls and taken addresses, because either way a back end needs the body.

33 header functions are reachable, 33 fully represented:

| Origin | Reachable | Fully represented | Places named |
| --- | ---: | ---: | ---: |
| project header | 32 | 32 | 139 |
| system header | 1 | 1 | 1 |

By header: `misc/bstr.h` 14 (`bstr0` is named at 29 places in 22 selected
functions, plus 7 places in other header functions; `bstr_cut` at 10),
`misc/ctype.h` 7, `osdep/threads-posix.h` 9 (the `mp_cond_*` and
`mp_mutex_init` wrappers, `mp_thread_set_name`), `ta/ta.h` 2 (`ta_oom_p`,
`ta_oom_s`), and glibc's `bits/stdlib-bsearch.h` 1 (`bsearch`). Four are
reached only through other header functions: `bstr_equals`, `mp_islower`,
`mp_isupper`, `mp_cond_timedwait`. The survey prints each with its origin,
line count, the places selected functions and header functions name it,
and how many selected functions reach it.

External functions are those named by a selected or reachable header
function and defined nowhere in the selection: not in a selected file and
not as a reachable header function. There are **90**. The top 30 by the
number of selected functions that name them directly:

| Selected callers | Header callers | Places | Function |
| ---: | ---: | ---: | --- |
| 23 | 7 | 49 | `__assert_fail` |
| 22 | 0 | 26 | `pthread_mutex_lock` |
| 22 | 0 | 28 | `pthread_mutex_unlock` |
| 16 | 0 | 21 | `ta_dbg_set_loc` |
| 11 | 0 | 11 | `ta_free` |
| 9 | 0 | 12 | `ta_get_size` |
| 8 | 0 | 11 | `ta_calc_array_size` |
| 8 | 0 | 10 | `ta_xrealloc_size` |
| 7 | 0 | 7 | `strchr` |
| 7 | 0 | 7 | `ta_alloc_size` |
| 6 | 0 | 8 | `ta_calc_prealloc_elems` |
| 4 | 1 | 8 | `pthread_self` |
| 4 | 1 | 8 | `ta_xstrdup` |
| 4 | 0 | 9 | `__errno_location` |
| 4 | 0 | 4 | `pthread_mutex_destroy` |
| 3 | 2 | 5 | `abort` |
| 3 | 1 | 4 | `mp_time_ns` |
| 3 | 1 | 4 | `strlen` |
| 3 | 0 | 3 | `memcpy` |
| 3 | 0 | 3 | `memmove` |
| 3 | 0 | 4 | `stat` |
| 3 | 0 | 4 | `strcmp` |
| 3 | 0 | 3 | `ta_set_destructor` |
| 3 | 0 | 4 | `ta_zalloc_size` |
| 2 | 2 | 4 | `memcmp` |
| 2 | 0 | 3 | `close` |
| 2 | 0 | 2 | `memchr` |
| 2 | 0 | 2 | `mp_time_ns_add` |
| 2 | 0 | 3 | `strcasecmp` |
| 2 | 0 | 4 | `strncmp` |

The other 60: `strtod`, `strtoll`, `ta_asprintf`, `ta_new_context`, `ta_steal_`, `ta_xstrndup`, `av_hash_alloc`, `av_hash_final`, `av_hash_freep`, `av_hash_get_size`, `av_hash_init`, `av_hash_update`, `av_random_bytes`, `fclose`, `fdopen`, `free`, `fwrite`, `getcwd`, `getenv`, `memrchr`, `memset`, `mkdir`, `mp_append_escaped_string`, `mp_append_utf8_bstr`, `mp_log2`, `mp_make_wakeup_pipe`, `mp_msg`, `mp_raw_time_ns`, `mp_round_next_power_of_2`, `mp_tprintf_buf`, `open`, `pthread_create`, `pthread_detach`, `pthread_join`, `read`, `realpath`, `rename`, `strncasecmp`, `ta_talloc_strdup_append_buffer`, `ta_talloc_strndup_append_buffer`, `unlink`, `vsnprintf`, `vsscanf`, `write`, `pthread_cond_wait`, `clock_gettime`, `pthread_cond_broadcast`, `pthread_cond_destroy`, `pthread_cond_init`, `pthread_cond_signal`, `pthread_cond_timedwait`, `pthread_condattr_destroy`, `pthread_condattr_init`, `pthread_condattr_setclock`, `pthread_mutex_init`, `pthread_mutexattr_destroy`, `pthread_mutexattr_init`, `pthread_mutexattr_settype`, `pthread_setname_np`, `strncpy`.

They are libc and POSIX (`strchr`, `memcpy`, `pthread_*`, `stat`, `open`),
glibc internals that macros expand to (`__assert_fail` from `assert`,
`__errno_location` from `errno`), mpv's talloc (`ta_*`), FFmpeg (`av_hash_*`,
`av_random_bytes`), and functions from other mpv directories (`mp_msg`,
`mp_time_ns`, `mp_append_escaped_string` in `common/`). A back end must take
each as a parameter or a model.

### Calibration

Counted on the IR of the 141 functions, against the pilot's numbers:

| Construct | IR | Pilot (178 functions, preprocessed source) |
| --- | ---: | ---: |
| `goto` | 5 | 5 |
| `switch` | 3 | 3 |
| atomic operations | 3 | 3 |
| calls | 127 (90%) | 79% |
| struct member access | 95 (67%) | 53% |
| array indexing | 47 (33%) | 20% |
| compound literals | 17 (12%) | 7% |
| reads of variadic arguments | 0 | 0 |

The percentages are higher because the pilot's denominator includes the
small header inline functions, which make fewer calls.

## The IR in brief

Source: `src/ir.rs` and `src/types.rs`. `achates dump --json` prints it.

- **Translation unit**: the file, the target widths, the functions, and the
  records, enums and file-scope variables the functions reach.
- **Function**: name, linkage (external or internal, resolved through
  earlier declarations), `inline`, parameters, return type, variadic,
  noreturn, attributes by name, body, file-scope variables used, location,
  line count.
- **Types** (`QualType` = type + `const`/`volatile`/`restrict`): `void`;
  `_Bool` with width; integers with C kind, width and signedness (`int:i32`,
  `unsigned long:u64`, `char:i8`); `float` and `double` with width; pointer
  to a type; array with length or unknown length; struct or union by name;
  enum by name; function type (return, parameters, variadic, prototyped,
  noreturn); `_Atomic`; and `Unsupported { spelling, reason }`. Typedefs are
  always resolved. Names are a tag (`struct bstr`), a typedef that names an
  anonymous tag (`struct (typedef mp_cond)`), or an anonymous tag by
  location.
- **Records**: kind, name, fields (name, type, bit-field width; an anonymous
  member has an empty name), attributes. No offsets.
- **Enums**: constants with values, and the compatible integer type clang
  chose.
- **Globals**: name, type, storage, initializer when this file gives one,
  whether it is declared in the main file.
- **Statements**: compound, declaration (local variables with a
  per-function number, storage, initializer, attributes), expression, `if`,
  `while`, `do`-`while`, `for`, `switch` with `case` and `default` labels
  left where they were written (so fall-through is kept), `break`,
  `continue`, `return`, `goto`, label, null, and `Unsupported`.
- **Expressions**: each node has its resolved type, whether it is an lvalue,
  and a location. Kinds: integer, floating (clang's text and the IEEE bits),
  character and string literals; variable (parameter by position, local by
  number, global by name); function (and whether it is a compiler builtin);
  enum constant with its value; unary operators (including pre/post
  increment and decrement, address-of, dereference, GNU `__extension__`);
  binary operators; logical `&&`/`||` as their own node with short-circuit
  meaning; comma; assignment; compound assignment with clang's computation
  types; conditional; call (with the callee expression always, and its name
  when it is a direct call); member access by `.` and `->`; subscript;
  casts, implicit or written, with clang's cast kind (19 kinds, among them
  `LValueToRValue`, `IntegralCast`, `ArrayToPointerDecay`,
  `FunctionToPointerDecay`, `NullToPointer`, `BitCast`,
  `IntegralToFloating`, `IntegralToBoolean`, `NoOp`, `ToVoid`);
  `sizeof`, `_Alignof` and `__alignof__` with clang's value and the operand
  kept but marked not evaluated; initializer lists (with the array filler
  and the union member set); compound literals; zero-initialization of
  omitted members; `__func__`; atomic operations; and `Unsupported
  { clang_kind, reason, location }`.

A function is fully represented when none of its statements, expressions or
types, nor the fields of any record it reaches, is `Unsupported`, and the
integer type of every enum it reaches is known.

## clang command line

For each entry, Achates runs clang 18 three or four times in the entry's
directory, with the entry's flags:

1. `-dM -E -x c /dev/null`, for the target widths.
2. `-fsyntax-only -Xclang -ast-dump=json FILE`, for the syntax tree.
3. The same on a generated probe file, for the constants (see below), with
   `-Xclang -ast-dump-filter=__achates_probe_` so its output is small.
4. When header functions are reachable, `-E FILE`, for which headers clang
   treats as system headers.

A failing run is an error that names the file and shows clang's last 20
lines of diagnostics. The survey stops there; it never continues with
partial data.

**Removed from the command line:**

- The compiler name and the source file.
- Output and dependency-file flags: `-c`, `-o FILE`, `-o<FILE>`, `-M`,
  `-MM`, `-MD`, `-MMD`, `-MP`, `-MG`, `-MF FILE`, `-MT TARGET`,
  `-MQ TARGET`, `-Wp,-M...`.
- gcc-only flags that clang 18.1.3 rejects with "unknown argument" (each one
  checked against the installed clang): `-fconserve-stack`, `-fipa-pta`,
  `-fno-allow-store-data-races`, `-fno-var-tracking-assignments`,
  `-fvar-tracking`, `-fno-ipa-cp-clone`, `-fanalyzer`, `-fno-gnu-unique`,
  `-flto-partition=*`. The survey prints the ones it removed.

**Added:** `-Wno-unknown-warning-option`, because gcc-only `-W` options make
clang warn but not fail, and `-fno-color-diagnostics`.

mpv's database contains none of the gcc-only flags: clang 18 accepts every
flag in it. Only `-c`, `-o`, `-MD`, `-MQ` and `-MF` are removed for `misc/`.

Everything else is kept, `-O2` included: it defines `__OPTIMIZE__`, which
selects which inline variants glibc's headers provide, and the IR should see
what the build sees.

## Decisions the task left open

1. **Crate shape.** One binary crate with modules, as in rmpv's tools. A
   library target alongside a binary makes the workspace's
   `unused_crate_dependencies` and `unreachable_pub` lints fire on items that
   are used. For programs that consume the IR, `dump --json` prints it.
   Dependencies: `anyhow`, `clap`, `serde`, `serde_json`. `serde_json`'s
   `preserve_order` feature (which pulls in `indexmap`) is needed because the
   order of keys in clang's output carries the location rule below.
2. **Which functions.** A `FunctionDecl` with a body whose name location,
   taken at its macro expansion point, is in the main file. A function
   produced by a macro used in the main file counts; a `static inline`
   function in a header does not; nor does one in a non-header file that
   the main file includes.
3. **Locations.** clang omits a location's `file` and `line` when they equal
   those of the location it printed just before, in document order, across
   the whole dump, macro `spellingLoc`/`expansionLoc` pairs included.
   Achates replays that rule over each top-level declaration as it streams
   in, so every location is complete before it is used. `includedFrom` names
   a file without being a location and does not move the state. Two mutation
   checks were run on the test: without the replay, and with spelling instead
   of expansion locations; each makes it fail.
4. **Streaming.** The dump is read with a serde visitor that holds one
   top-level declaration at a time and keeps only function definitions in
   the main file and the records, enums, typedefs and file-scope variables of
   the whole unit.
5. **Types from text.** clang's JSON gives expression types only as
   spellings (`qualType`). Achates parses them with a small C type-name
   parser and resolves typedef names through the unit's typedef
   declarations. When a spelling cannot be read, clang's
   `desugaredQualType` is tried; when neither can be read, the type is
   `Unsupported` with the reason. Anonymous tags are known by the location
   clang prints in `(unnamed struct at FILE:LINE:COL)`, which is the
   expansion location of their declaration. An anonymous tag named by a
   typedef is printed by clang as `struct NAME`; Achates tracks this
   through the typedef's `ownedTagDecl`.
6. **Widths.** From the macros clang predefines with the entry's flags:
   `__CHAR_BIT__`, `__CHAR_UNSIGNED__`, `__SHRT_WIDTH__`, `__INT_WIDTH__`,
   `__LONG_WIDTH__`, `__LLONG_WIDTH__`, `__SIZEOF_INT128__`,
   `__BOOL_WIDTH__`, `__POINTER_WIDTH__`, `__SIZEOF_FLOAT__`,
   `__SIZEOF_DOUBLE__`. No width is written in Achates's source.
7. **`sizeof` and `_Alignof` values.** clang 18's JSON does not print them.
   Achates writes a probe file that includes the source file and declares
   `typedef char __achates_probe_N[(sizeof(T)) + 1];` for each type measured,
   with `T` printed back from the IR with typedefs resolved. clang's array
   length is the answer. A type that cannot be named at file scope (an
   anonymous record, or a type declared inside a function) is not probed and
   the node is `Unsupported`. A probe clang rejects gets clang's message and
   the others are asked again.
8. **Enum integer types.** Also by probe: `_Generic((enum E)0, char: 1,
   ..., unsigned long long: 11, default: 0)`, which selects the type the enum
   is compatible with. In `misc/`, `enum mpv_format` and `enum track_flags`
   are `unsigned int`. Enumerator values come from clang's `value` on the
   initializer; an enumerator without one is the previous value plus one.
9. **Parentheses and `ConstantExpr`.** Dropped: clang has already applied
   them, and neither changes a value or a type.
10. **`case` values.** clang 18's JSON does not print them either. The IR
    keeps the label's constant expression, with its casts, and a `value`
    field that is filled only when clang prints one.
11. **Atomic operations.** Represented as an `Atomic` node with clang's
    builtin name and operands in clang's storage order (pointer, memory
    order, then the operation's values). The three uses in `misc/` are in
    `thread_tools.c`: a relaxed load in `mp_cancel_test` and sequentially
    consistent stores in `trigger_locked` and `mp_cancel_reset`. Their
    meaning for a sequential model is for the back end to decide.
12. **Compiler builtins** (`__builtin_va_start`, `__builtin_isfinite`, ...)
    are calls to a function marked builtin, typed with the builtin's
    declared type (clang gives the reference a placeholder type). The survey
    lists them.
13. **Unknown attributes on nodes.** Each node kind Achates converts has a
    list of the JSON keys it understands. A key outside the list makes the
    node `Unsupported`, so a clang flag with meaning is never dropped.
14. **Attributes.** Function attributes are kept by name. On a local
    variable only `unused`, `used` and `aligned` are accepted; any other
    (for example `cleanup`) makes the declaration `Unsupported`.
15. **Records reached through fields** count: a function whose struct has a
    field of an unrepresented type is not fully represented. A named record
    with no definition in the unit (`struct mp_log`) is an opaque type,
    which is exact; an anonymous record without a definition is
    `Unsupported`.
16. **Variables.** Parameters by position, locals by a number unique in the
    function, so shadowing cannot confuse two variables. The text dump shows
    locals as `name#N`.
17. **String literals.** The bytes written, without the terminating NUL.
    The type gives the array length, and bytes past the written ones are
    zero, which covers `char b[7] = ""`. Wide and UTF-16/32 literals are
    `Unsupported`.
18. **Floating literals.** clang's decimal text (17 significant digits for
    `double`) and the IEEE bits Rust parses from it.
19. **Subscripts** keep the operands in source order, `*(lhs + rhs)`, so
    `2[a]` is not rewritten.
20. **Selectors.** A path prefix or a glob (`*` within a component, `**`
    across, `?`), matched against the absolute path and every trailing run of
    its components, so `misc/` and `misc/b*.c` both work. A selector that
    matches nothing is an error. A file listed twice in the database is
    surveyed once, with its first command.
21. **Line count** is the span of the definition's range, first line to last.
22. **Exit code.** 0 whenever the survey completes, whatever it finds; 1 on
    any error.
23. **Header functions are on by default** for `survey` and `dump`, since
    without them "fully represented" overstates what a back end can
    translate; `--no-reachable-inlines` turns them off. Reachability follows
    every reference to a function, called or address taken, transitively
    through header functions, and stops at functions without a body in the
    unit.
24. **Origin** is `main file`, `project header` or `system header`. A header
    is a system header when clang's preprocessor marks it so (flag `3` on its
    `# LINE "FILE"` line markers): headers found through the default system
    directories or `-isystem`. A header found through `-I` is a project
    header, so a library header included with `-I` (FreeType, glib) would be
    counted as project; none is reached from `misc/`.
25. **Identity** of a header function is its defining file's absolute,
    lexically normalized path plus its name. The survey keeps one row per
    identity. Its places named and its references to externals are counted
    once, from the first unit that defines it. Two units whose IR for the
    same identity differs (signature or body, compared as dump text) stop the
    survey with an error naming the function and both units. `dump
    --function` prints a header function once.
26. **Two figures.** "Fully represented" for a selected function still
    means its own body. The stricter figure also requires every header
    function it reaches to be fully represented.
27. **External functions** are counted by name, with the selected functions
    and the header functions that name each, and the places. A function
    defined in another selected file is not external.
28. **Repository config.** `typos.toml` accepts `Parm` (clang's
    `ParmVarDecl`) and `implicits` (a Lean term in another agent's
    `docs/research/aeneas.md`, which otherwise fails `make ci`). `deny.toml` ignores the license of unpublished crates,
    because no license has been chosen for Achates.

Constructs Achates deliberately reports as `Unsupported`, with the reason it
gives (none occur in `misc/`; a test checks each). `va_arg` was one until the
back end modelled variadic arguments; it is now the node `VaArg`, whose
operand is the `va_list` as a pointer to its one element and whose type is
the type read.

| Construct | Reason |
| --- | --- |
| `({ ... })` | GNU statement expression |
| `a ?: b` | GNU binary conditional |
| inline assembly | inline assembly |
| `goto *p`, `&&label` | computed goto, address of a label |
| `case 1 ... 3` | GNU case range |
| `_Generic`, `__builtin_choose_expr` | selection |
| `offsetof` | clang does not print its value |
| struct, union, enum or typedef declared in a function | would shadow file scope |
| block-scope `extern`, thread-local locals | not represented |
| `long double`, `_Complex`, `_Float16`, `__float128`, `_BitInt`, `typeof` in a type spelling, variable-length arrays | type not represented |
| wide string literals | not decoded |
| `sizeof` of a type with no file-scope name | clang cannot be asked |
| any JSON key Achates does not know on a node | not understood |
| any other node kind | not represented |

## Known gaps

- **External functions** have no body in the IR by definition. Those from
  other mpv directories (`common/`, `ta/`) could be brought in by widening
  the selection; the survey would then count them as selected.
- **Origin follows clang's system-header rule**, which depends on how the
  header was found (`-I` versus system directories), not on who wrote it.
- **`case` values** are given as expressions, not numbers.
- **clang, not gcc.** The tree is clang's reading of the source. clang
  defines `__clang__` and its own builtins, so a header can take a different
  `#if` branch than under gcc. For `misc/` the three clang runs gave no
  errors, but the IR is of the clang build of mpv, not the gcc build.
- **Layout.** No field offsets, padding or record sizes, except through
  `sizeof` probes. `packed` and `aligned` are kept as attribute names only.
- **Evaluation order.** C leaves the order of most operands unspecified; the
  IR keeps source order and says nothing more. A back end must not read an
  order into it.
- **Bit-fields.** A member access does not say that the member is a
  bit-field; the record's field does.
- **Global initializers** are converted, but an `Unsupported` node in one is
  shown in the dump without counting against the functions that use the
  global.
- **`sizeof` of an anonymous type** (for example `sizeof *p` where `p`
  points to an unnamed struct) is `Unsupported`. Such a type could be named
  through a path from a named record (`__typeof__(((struct outer *)0)->m)`);
  `misc/` does not need it.
- **Type spellings** are parsed from text. A spelling clang prints in an
  unforeseen form becomes an `Unsupported` type, visibly, not a wrong type.
- **Three or four clang runs per file.** The survey of `misc/` takes about
  11 s with a debug build.
