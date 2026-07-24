.PHONY: check check-fast check-msrv install-hooks test release profiling smoke proof-smoke

PYTHON ?= python3
DRAT_TRIM ?= drat-trim

check:
	PYTHON="$(PYTHON)" ./scripts/ci.sh

check-fast:
	./scripts/check-fast.sh

check-msrv:
	./scripts/check-msrv.sh

install-hooks:
	./scripts/install-hooks.sh

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
