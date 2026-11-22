# Pilot: mpv `misc/`

Goal: find out, with numbers, whether proofs that a Rust port equals mpv's C
can be generated instead of written by hand.

Target: mpv's `misc/` folder at the commit pinned in rmpv
(`d11ffba253def00b5172c4b8b47e6b2eb765cae1`): 16 C files, 4,430 lines, 178
functions, 886 paths. It was chosen because it is mostly self-contained
helpers (strings, JSON, sorting, paths, random numbers) with a few threaded
files (`dispatch.c`, `rendezvous.c`, `thread_pool.c`, `thread_tools.c`) that
show where a sequential translation stops.

## Questions

1. Does AutoCorres or AutoCorres2 already do the C-to-proof-assistant step for
   code like mpv's?
2. How good is a machine translation of the folder to Rust (c2rust) compared
   with a port written for the purpose?
3. How much of the folder can Achates translate to Lean, and does the
   translation agree with real mpv?
4. Given Lean definitions from Achates (C) and Aeneas (Rust), what fraction of
   "these two functions are equal" theorems can be stated and proved without
   a person?

## Answers

1. **No.** AutoCorres2 (Isabelle2026) rejects the folder before translating
   it: it has no floating point, rejects variadic prototypes (so glibc's
   headers fail), and rejects string-literal expressions. Its output is
   Isabelle/HOL, which has no route to Aeneas's Lean. Achates was built
   instead. Details: [research/autocorres.md](research/autocorres.md).
2. **The port written for the purpose is the only usable one.** c2rust makes
   223 of 223 functions `unsafe` with 1,657 raw pointer types, mistranslates
   `bstrtoll` on `0b` input, and Aeneas gives it no function bodies (it fails
   on 113 functions, then crashes after 17 minutes and 7 GB). The hand port
   (rmpv `crates/misc`) covers 105 of 141 functions with no `unsafe`, agrees
   with mpv on 104 of 104 tested functions over 12.8 million inputs, and
   Aeneas gives bodies for 99. Details: [research/c2rust.md](research/c2rust.md),
   [research/aeneas.md](research/aeneas.md), and rmpv's
   `docs/pilot-misc-rust.md`.
3. **135 of 141 functions are emitted**, plus 33 of 33 header helpers. The 6
   refusals are 3 variadic functions and 3 with unsequenced operands. Run
   against the compiled C on 770,000 generated inputs, no checkable function
   gave a different value: 54 are checked and shown sensitive (647 of 797
   planted bugs caught), 1 (`add_indent`) fails only because large indents
   run out of fuel, and 80 cannot be checked yet, mostly threading, `void *`
   parameters, unions and function pointers. The check found two runtime
   bugs in Achates, both fixed, and none in mpv. Details:
   [backend-report.md](backend-report.md), [check-report.md](check-report.md).
4. **11 of 36 generated theorems are proved with no hand-written proof**,
   each depending only on Lean's standard axioms. 120 of 174 C functions were
   paired with a Rust function by name; 84 pairs got no theorem, 57 of them
   because the C calls external functions that the generator cannot yet
   pass in. The 25 open theorems are blocked by C loops that need
   invariants (8), Rust recursion that needs induction (5), the proof budget
   (5), static tables (3), missing `strlen` lemmas (2), a `bstr` built in a
   local (1) and a variable shift (1). No theorem showed a real difference
   between the C and the port. One, `bstr_equals`, is unprovable because the
   C model refuses to compare two one-past-the-end pointers into different
   blocks, which real C allows. Details: [equiv-report.md](equiv-report.md).

## What to do before the next folder

- Prove loop invariants for the C side once, as lemmas, instead of per
  function: 8 open theorems are C `for` loops over a `bstr`.
- Give `achates equiv` the six pure externals (`strncasecmp`, `memrchr`,
  `mp_log2`, `strtoll`, `strcasecmp`, `mp_round_next_power_of_2`) as
  instances; that unblocks 25 pairs.
- Make pointer comparison across blocks nondeterministic in the runtime
  instead of `unsupported`.
- Drop the `Vec` capacity pattern in the port, which leaves 22 Aeneas
  bodies resting on assumptions.
