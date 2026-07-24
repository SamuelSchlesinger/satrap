.PHONY: audit check check-fast check-fuzz check-msrv check-proofs check-python install-fuzz-tools install-hooks install-oracles install-proof-checkers install-python-tools profiling proof-smoke quality release smoke smt-proof-smoke test

PYTHON ?= python3
PROOF_CHECKER_CACHE ?= .cache/proof-checkers
DRAT_TRIM ?= $(PROOF_CHECKER_CACHE)/bin/drat-trim

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

check-python:
	./scripts/check-python.sh

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

install-python-tools:
	./scripts/install-python-tools.sh

test:
	cargo test --all-targets --locked

release:
	RUSTFLAGS="-C target-cpu=native" cargo build --release --locked

profiling:
	RUSTFLAGS="-C target-cpu=native" cargo build --profile profiling --locked

smoke: release
	$(PYTHON) tools/benchmark.py \
		--instances benchmarks/smoke \
		--solver "sat=target/release/sat --proof {proof}" \
		--proof-checker "sat=$(DRAT_TRIM) {instance} {proof}" \
		--require-unsat-proofs \
		--output -

proof-smoke: release
	$(PYTHON) tools/proof_smoke.py --solver target/release/sat --checker "$(DRAT_TRIM)"

smt-proof-smoke: release
	@for formula in benchmarks/smt-proof-smoke/*.smt2; do \
		$(PYTHON) tools/check_smt_proof.py \
			--input "$$formula" \
			--solver target/release/smt \
			--checker "$(DRAT_TRIM)" || exit 1; \
	done
