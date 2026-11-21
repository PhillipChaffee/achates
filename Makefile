.PHONY: fmt lint test ci

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

ci: lint test
