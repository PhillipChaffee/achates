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

## Log

Findings go in `docs/research/`, one file per question.
