#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

fuzz_nightly=nightly-2026-06-01
required_cargo_fuzz_version=0.13.2
fuzz_runs=${FUZZ_RUNS:-256}

if ! rustc +"$fuzz_nightly" --version >/dev/null 2>&1; then
    echo "$fuzz_nightly is required by the fuzz gate" >&2
    echo "run 'make install-fuzz-tools'" >&2
    exit 1
fi
if ! command -v cargo-fuzz >/dev/null 2>&1; then
    echo "cargo-fuzz is required by the fuzz gate" >&2
    echo "run 'make install-fuzz-tools'" >&2
    exit 1
fi
actual_cargo_fuzz_version=$(cargo fuzz --version)
if [ "$actual_cargo_fuzz_version" != "cargo-fuzz $required_cargo_fuzz_version" ]; then
    echo "cargo-fuzz $required_cargo_fuzz_version is required by the fuzz gate" >&2
    echo "found: $actual_cargo_fuzz_version" >&2
    exit 1
fi

cargo +"$fuzz_nightly" metadata \
    --manifest-path fuzz/Cargo.toml \
    --locked \
    --no-deps \
    --format-version 1 >/dev/null
cargo +"$fuzz_nightly" fmt --manifest-path fuzz/Cargo.toml --all -- --check
cargo +"$fuzz_nightly" clippy \
    --manifest-path fuzz/Cargo.toml \
    --all-targets \
    --locked \
    -- \
    -D warnings
cargo +"$fuzz_nightly" fuzz build

fuzz_work=$(mktemp -d "${TMPDIR:-/tmp}/satrap-fuzz.XXXXXX")
fuzz_artifact_root=${FUZZ_ARTIFACT_ROOT:-"$fuzz_work/artifacts"}
cleanup() {
    rm -rf "$fuzz_work"
}
trap cleanup EXIT HUP INT TERM

run_target() {
    fuzz_target=$1
    fuzz_max_len=$2
    shift 2
    fuzz_corpus="$fuzz_work/corpus/$fuzz_target"
    fuzz_artifacts="$fuzz_artifact_root/$fuzz_target"
    mkdir -p "$fuzz_corpus" "$fuzz_artifacts"
    cargo +"$fuzz_nightly" fuzz run \
        "$fuzz_target" \
        "$fuzz_corpus" \
        "$repo_root/fuzz/corpus/$fuzz_target" \
        -- \
        "-artifact_prefix=$fuzz_artifacts/" \
        "-max_len=$fuzz_max_len" \
        "-rss_limit_mb=2048" \
        "-runs=$fuzz_runs" \
        "-seed=1337" \
        "-timeout=10" \
        -verbosity=0 \
        "$@"
}

run_target smt_session_bytes 4096 "-dict=$repo_root/fuzz/smtlib.dict"
run_target smt_structured_session 256
run_target sat_proof 512
