#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"
oracle_bin="$repo_root/.cache/smt-oracles/bin"
if [ -d "$oracle_bin" ]; then
    PATH="$oracle_bin:$PATH"
    export PATH
fi

required_z3_version=4.16.0
required_cvc5_version=1.3.3
required_bitwuzla_version=0.9.1

"$repo_root/scripts/quality.sh"

if ! command -v z3 >/dev/null 2>&1; then
    echo "z3 is required by the integration gate" >&2
    exit 1
fi
actual_z3_version=$(z3 --version)
case "$actual_z3_version" in
    "Z3 version $required_z3_version"*) ;;
    *)
        echo "z3 $required_z3_version is required by the integration gate" >&2
        echo "found: $actual_z3_version" >&2
        exit 1
        ;;
esac
echo "$actual_z3_version"

if ! command -v cvc5 >/dev/null 2>&1; then
    echo "cvc5 is required by the integration gate" >&2
    exit 1
fi
actual_cvc5_version=$(cvc5 --version)
case "$actual_cvc5_version" in
    "This is cvc5 version $required_cvc5_version"*) ;;
    *)
        echo "cvc5 $required_cvc5_version is required by the integration gate" >&2
        printf '%s\n' "found: $actual_cvc5_version" | sed -n '1p' >&2
        exit 1
        ;;
esac
printf '%s\n' "$actual_cvc5_version" | sed -n '1p'

if ! command -v bitwuzla >/dev/null 2>&1; then
    echo "bitwuzla is required by the integration gate" >&2
    exit 1
fi
actual_bitwuzla_version=$(bitwuzla --version)
case "$actual_bitwuzla_version" in
    "$required_bitwuzla_version") ;;
    *)
        echo "bitwuzla $required_bitwuzla_version is required by the integration gate" >&2
        echo "found: $actual_bitwuzla_version" >&2
        exit 1
        ;;
esac
echo "Bitwuzla version $actual_bitwuzla_version"

cargo test --all-targets --locked
"${PYTHON:-python3}" -m unittest discover -s tools -p 'test_*.py'
cargo build --release --locked
