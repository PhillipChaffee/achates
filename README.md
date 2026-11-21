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
