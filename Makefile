.PHONY: audit check check-fast check-fuzz check-msrv check-proofs install-fuzz-tools install-hooks install-oracles install-proof-checkers profiling proof-smoke quality release smoke test

PYTHON ?= python3
DRAT_TRIM ?= drat-trim

check:
	PYTHON="$(PYTHON)" ./scripts/ci.sh

check-fast:
	PYTHON="$(PYTHON)" ./scripts/check-fast.sh

check-fuzz:
	./scripts/check-fuzz.sh

quality:
	PYTHON="$(PYTHON)" ./scripts/quality.sh

check-msrv:
	./scripts/check-msrv.sh

check-proofs:
	./scripts/check-proofs.sh

audit:
	./scripts/check-security.sh

install-hooks:
	./scripts/install-hooks.sh

install-fuzz-tools:
	./scripts/install-fuzz-tools.sh

install-oracles:
	./scripts/install-smt-oracles.sh

install-proof-checkers:
	./scripts/install-proof-checkers.sh

test:
	cargo test --all-targets --locked

release:
	RUSTFLAGS="-C target-cpu=native" cargo build --release --locked

profiling:
	RUSTFLAGS="-C target-cpu=native" cargo build --profile profiling --locked

smoke: release
	$(PYTHON) tools/benchmark.py --instances benchmarks/smoke --solver "sat=target/release/sat" --output -

proof-smoke: release
	$(PYTHON) tools/proof_smoke.py --solver target/release/sat --checker "$(DRAT_TRIM)"
