.PHONY: fmt lint test lean pilot-emit pilot-build ci equiv equiv-build

# Lean may be unpacked under ~/.local/lean. It goes last: that directory also
# holds a clang without system headers, which must not shadow the real one.
export PATH := $(PATH):$(HOME)/.local/lean/bin

# The compilation database of the mpv build the pilot translates. The step
# that needs it is skipped, with a message, where the file does not exist.
MPV_COMPILE_COMMANDS ?= $(CURDIR)/../rmpv/formal/.mpv-build/compile_commands.json

fmt:
	cargo fmt --all
	taplo fmt

lint:
	cargo fmt --all --check
	taplo fmt --check
	typos
	cargo clippy --all-targets --all-features --locked -- -D warnings
	cargo deny check

test:
	cargo test --all-features --locked

lean:
	cd lean && lake build --wfail

# Emits misc/ again and fails if the result differs from what is committed.
pilot-emit:
	@if [ -f "$(MPV_COMPILE_COMMANDS)" ]; then \
		cargo run --locked --quiet -- emit --compile-commands "$(MPV_COMPILE_COMMANDS)" \
			--select misc/ --out pilot/misc --name Misc > pilot/misc/summary.txt \
		&& git status --short -- pilot/misc \
		&& test -z "$$(git status --porcelain -- pilot/misc)"; \
	else \
		echo "pilot-emit skipped: $(MPV_COMPILE_COMMANDS) not found (set MPV_COMPILE_COMMANDS)"; \
	fi

pilot-build:
	cd pilot/misc && lake build --wfail
	cd pilot/misc-checks && lake build --wfail

ci: lint test lean pilot-emit pilot-build

# The equality theorems between mpv's misc/ in Lean (pilot/misc) and the rmpv
# port's Aeneas output. Not part of `ci`: the bridge project builds the
# Mathlib-based Aeneas side, about 4 minutes from clean on 4 cores, and the
# proof run takes about 5 minutes more. equiv/README.md says how to set up its
# Lake packages.
RMPV ?= $(CURDIR)/../rmpv
RMPV_LEAN ?= $(RMPV)/pilot/misc-lean/MiscRec/RmpvMisc.lean

equiv:
	@if [ -f "$(MPV_COMPILE_COMMANDS)" ] && [ -f "$(RMPV_LEAN)" ]; then \
		cargo run --locked --quiet -- equiv --compile-commands "$(MPV_COMPILE_COMMANDS)" \
			--select misc/ --c-project pilot/misc --rust-lean "$(RMPV_LEAN)" \
			--lake-dir equiv --prove > equiv/summary.txt \
		&& $(MAKE) equiv-build; \
	else \
		echo "equiv skipped: needs $(MPV_COMPILE_COMMANDS) and $(RMPV_LEAN)"; \
	fi

# Checks the committed proofs (equiv/Equiv/Proved.lean) without re-running the tiers.
equiv-build:
	cd equiv && lake build
