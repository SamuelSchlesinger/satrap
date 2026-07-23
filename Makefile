.PHONY: check test release profiling smoke proof-smoke

PYTHON ?= python3
DRAT_TRIM ?= drat-trim

check:
	cargo fmt --all -- --check
	cargo clippy --all-targets --all-features -- -D warnings
	cargo test --all-targets
	$(PYTHON) -m unittest discover -s tools -p 'test_*.py'

test:
	cargo test --all-targets

release:
	RUSTFLAGS="-C target-cpu=native" cargo build --release

profiling:
	RUSTFLAGS="-C target-cpu=native" cargo build --profile profiling

smoke: release
	$(PYTHON) tools/benchmark.py --instances benchmarks/smoke --solver "sat=target/release/sat" --output -

proof-smoke: release
	$(PYTHON) tools/proof_smoke.py --solver target/release/sat --checker "$(DRAT_TRIM)"
