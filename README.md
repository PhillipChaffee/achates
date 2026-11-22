# Achates

Translates C into Lean 4, so that properties of C code can be proved and a
Rust port can be proved equal to the C it replaces.

[Aeneas](https://github.com/AeneasVerif/aeneas) translates Rust into Lean.
In the Aeneid, Achates is the companion who never leaves Aeneas's side.
Achates the tool does for C what Aeneas does for Rust, so the two outputs can
be compared inside one proof assistant.

Status: pilot. The first target is the `misc/` folder of
[mpv](https://mpv.io), for the [rmpv](https://github.com/PhillipChaffee/rmpv)
port. See [docs/pilot.md](docs/pilot.md).

The front end, which reads C through clang into a typed intermediate
representation, is described in
[docs/frontend-report.md](docs/frontend-report.md).

The back end, which emits Lean definitions from that representation and
provides the Lean runtime they run on, is described in
[docs/backend-report.md](docs/backend-report.md).

```sh
achates emit --compile-commands PATH --select misc/ --out DIR --name Misc
```

writes a Lake project to `DIR` and prints, for every function, whether it was
emitted and why not. `lean/` holds the runtime; `pilot/misc/` holds the
output for mpv's `misc/`; `make ci` builds both.

```sh
achates check --compile-commands PATH --select misc/ --name Misc \
  --cflags-file harness.rsp --link-file harness-link.rsp --json check.json
```

runs every emitted definition against the compiled C it came from, on
generated inputs, plants bugs in the C to show the comparison notices them,
and says per function whether the two agree. How it works and what it found
on `misc/` is in [docs/check-report.md](docs/check-report.md); `make
check-misc` reruns it and writes `pilot/misc/check.json`.
