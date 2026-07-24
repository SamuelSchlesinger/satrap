#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

required_drat_trim_revision=2e5e29cb0019d5cfd547d4208dca1b3ec290349f
proof_checker_root=${PROOF_CHECKER_CACHE:-"$repo_root/.cache/proof-checkers"}
drat_trim="$proof_checker_root/bin/drat-trim"
revision_path="$proof_checker_root/bin/drat-trim.revision"

if [ ! -x "$drat_trim" ] || [ ! -f "$revision_path" ]; then
    echo "the pinned DRAT-trim checker is required by the proof gate" >&2
    echo "run 'make install-proof-checkers'" >&2
    exit 1
fi
actual_drat_trim_revision=$(sed -n '1p' "$revision_path")
if [ "$actual_drat_trim_revision" != "$required_drat_trim_revision" ]; then
    echo "DRAT-trim $required_drat_trim_revision is required by the proof gate" >&2
    echo "found: $actual_drat_trim_revision" >&2
    exit 1
fi

cargo build --release --locked

check_proof() {
    "${PYTHON:-python3}" tools/proof_smoke.py \
        --solver target/release/sat \
        --checker "$drat_trim" \
        "$@"
}

check_proof --formula benchmarks/smoke/unsat.cnf
check_proof --formula benchmarks/smoke/chrono-unsat.cnf
check_proof --formula benchmarks/smoke/probe-unsat.cnf --solver-arg=--probe
check_proof --formula benchmarks/smoke/vivify-unsat.cnf --solver-arg=--vivify
check_proof --formula benchmarks/smoke/ssr-unsat.cnf --solver-arg=--subsume
check_proof \
    --formula benchmarks/smoke/binary-minimize-unsat.cnf \
    --solver-arg=--binary-minimize
check_proof --formula benchmarks/smoke/eliminate-unsat.cnf --solver-arg=--eliminate
check_proof --formula benchmarks/smoke/factor-unsat.cnf --solver-arg=--factor
check_proof \
    --formula benchmarks/smoke/factor-macro-unsat.cnf \
    --solver-arg=--factor-macro
