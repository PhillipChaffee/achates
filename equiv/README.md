# equiv: C and Rust sides of misc/ in one Lean project

This Lake project builds both halves of the equality theorems:

| Library | Source | What |
| --- | --- | --- |
| `Misc` | `../pilot/misc` | mpv's `misc/` as Achates emits it, on the runtime in `../lean` |
| `MiscRec` | `../../rmpv/pilot/misc-lean` | the rmpv port as Aeneas translates it (`-loops-to-rec`) |
| `Equiv` | here | the correspondence, the proof tiers, the general lemmas, and the proved theorems |

Both generated sides are libraries of this package, not required packages,
because both of their Lake packages are called `misc`. Neither is edited.

| File | Content |
| --- | --- |
| `Equiv/Basic.lean` | The correspondence: integers, outcomes (`Agree`, `Equal`), memory (`Region`, `IsBstr`, `IsCStr`, `Unchanged`) |
| `Equiv/Simp.lean` | Tier 1's rewriting of both sides' primitive operations into bit-vector `if`s |
| `Equiv/Tactic.lean` | The tier 0 and tier 1 scripts |
| `Equiv/Mem.lean` | Tier 2: the C memory operations on a caller's memory extended by a call's locals |
| `Equiv/Libc.lean` | Tier 2: `bytesAt`, `checkRange`, `memcmp` of the C model over regions |
| `Equiv/Port.lean` | Tier 2: the port's `memcmp` loop, by induction |
| `Equiv/Lemmas.lean` | Tier 2 scripts, `StaticsReady` |
| `Equiv/Proved.lean` | Generated: the theorems some tier proved, with that tier's script |
| `open/Open.lean` | Generated, not built: the theorems no tier proved, each with its first error |
| `results.json`, `summary.txt` | Generated: per function, what happened |

`make equiv` (in the repository root) regenerates the last four and builds
the project; `make equiv-build` only builds it, which checks the committed
proofs. The report is `../docs/equiv-report.md`.

## Setting up

The project needs Lean 4.36.0, Mathlib `v4.36.0` and the Aeneas Lean library
at `/home/user/spike-aeneas/dist/backends/lean` (the copy the rmpv pilot
used; `lakefile.toml` names it). To reuse the Mathlib that is already built
for that copy instead of downloading and building it again:

```sh
mkdir -p equiv/.lake
ln -s /home/user/spike-aeneas/lean/.lake/packages equiv/.lake/packages
```

`lake build` from clean then takes about 4 minutes on 4 cores, most of it
the Aeneas output (`MiscRec.RmpvMisc`, 3.5 minutes).
