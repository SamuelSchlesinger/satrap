#!/bin/sh

set -eu

fuzz_nightly=nightly-2026-06-01
cargo_fuzz_version=0.13.2

if ! command -v rustup >/dev/null 2>&1; then
    echo "rustup is required to install the fuzz toolchain" >&2
    exit 1
fi

rustup toolchain install "$fuzz_nightly" --profile minimal --component rust-src

actual_cargo_fuzz_version=
if cargo fuzz --version >/dev/null 2>&1; then
    actual_cargo_fuzz_version=$(cargo fuzz --version)
fi
if [ "$actual_cargo_fuzz_version" != "cargo-fuzz $cargo_fuzz_version" ]; then
    cargo install cargo-fuzz --version "$cargo_fuzz_version" --locked
fi

echo "Installed $fuzz_nightly and cargo-fuzz $cargo_fuzz_version"
