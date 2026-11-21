.PHONY: fmt lint test lean pilot-emit pilot-build check-misc check-misc-fast ci

# Lean may be unpacked under ~/.local/lean. It goes last: that directory also
# holds a clang without system headers, which must not shadow the real one.
export PATH := $(PATH):$(HOME)/.local/lean/bin

# The compilation database of the mpv build the pilot translates. The step
# that needs it is skipped, with a message, where the file does not exist.
MPV_COMPILE_COMMANDS ?= $(CURDIR)/../rmpv/formal/.mpv-build/compile_commands.json
MPV_BUILD = $(dir $(MPV_COMPILE_COMMANDS))
CHECK_ARGS = check --compile-commands "$(MPV_COMPILE_COMMANDS)" --select misc/ --name Misc \
	--cflags-file "$(MPV_BUILD)harness.rsp" --link-file "$(MPV_BUILD)harness-link.rsp"

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

# Every emitted function of misc/ against the compiled mpv C, with planted
# bugs; writes pilot/misc/check.json. About an hour on four cores.
check-misc:
	cargo run --locked --release --quiet -- $(CHECK_ARGS) --work target/check-misc \
		--json pilot/misc/check.json > pilot/misc/check.txt

# A few functions of each kind, with fewer inputs, for every CI run.
check-misc-fast:
	@if [ -f "$(MPV_COMPILE_COMMANDS)" ]; then \
		cargo run --locked --release --quiet -- $(CHECK_ARGS) --work target/check-fast \
			--count 2000 --mutants 8 --function bstrcmp --function bstr_split_tok \
			--function mp_rand_in_range32 --function bstrdup0 --function mp_isspace \
			--function bstr_decode_utf8 | tail -n 4; \
	else \
		echo "check-misc-fast skipped: $(MPV_COMPILE_COMMANDS) not found (set MPV_COMPILE_COMMANDS)"; \
	fi

ci: lint test lean pilot-emit pilot-build check-misc-fast
