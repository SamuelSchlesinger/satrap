#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

git config --local core.hooksPath .githooks
echo "Installed repository hooks from .githooks"

for tool in cargo-audit shellcheck actionlint; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        echo "Install $tool before pushing; see docs/QUALITY.md" >&2
    fi
done

oracle_bin="$repo_root/.cache/smt-oracles/bin"
for tool in z3 cvc5 bitwuzla; do
    if ! command -v "$tool" >/dev/null 2>&1 \
        && [ ! -x "$oracle_bin/$tool" ]; then
        echo "Run 'make install-oracles' before pushing; $tool is missing" >&2
    fi
done
