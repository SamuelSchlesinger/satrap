#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cache_root=${PROOF_CHECKER_CACHE:-"$repo_root/.cache/proof-checkers"}
archive_root="$cache_root/archives"
bin_root="$cache_root/bin"

drat_trim_revision=2e5e29cb0019d5cfd547d4208dca1b3ec290349f
drat_trim_sha256=2ac28cd9e38e050b4f78fbff0efd4a1aa2349d157aef08c9b1fb6c7139949108
drat_trim_archive="drat-trim-$drat_trim_revision.tar.gz"
drat_trim_url="https://github.com/marijnheule/drat-trim/archive/$drat_trim_revision.tar.gz"

for tool in cc curl install tar; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        echo "$tool is required to install the proof checker" >&2
        exit 1
    fi
done
if ! command -v sha256sum >/dev/null 2>&1 \
    && ! command -v shasum >/dev/null 2>&1; then
    echo "sha256sum or shasum is required to verify the proof-checker archive" >&2
    exit 1
fi

mkdir -p "$archive_root" "$bin_root"
archive_path="$archive_root/$drat_trim_archive"
revision_path="$bin_root/drat-trim.revision"

verify_sha256() (
    checksum_path=$1
    checksum_expected=$2
    if command -v sha256sum >/dev/null 2>&1; then
        checksum_actual=$(sha256sum "$checksum_path" | awk '{print $1}')
    else
        checksum_actual=$(shasum -a 256 "$checksum_path" | awk '{print $1}')
    fi
    [ "$checksum_actual" = "$checksum_expected" ]
)

if [ ! -f "$archive_path" ] || ! verify_sha256 "$archive_path" "$drat_trim_sha256"; then
    curl --fail --location --silent --show-error \
        --output "$archive_path" \
        "$drat_trim_url"
fi
if ! verify_sha256 "$archive_path" "$drat_trim_sha256"; then
    echo "checksum mismatch for $archive_path" >&2
    exit 1
fi

build_root=$(mktemp -d "${TMPDIR:-/tmp}/satrap-proof-checker.XXXXXX")
cleanup() {
    rm -rf "$build_root"
}
trap cleanup EXIT HUP INT TERM

tar -xzf "$archive_path" -C "$build_root"
source_root="$build_root/drat-trim-$drat_trim_revision"
cc "$source_root/drat-trim.c" -std=c99 -O2 -o "$build_root/drat-trim"
install -m 755 "$build_root/drat-trim" "$bin_root/drat-trim"
printf '%s\n' "$drat_trim_revision" >"$revision_path"

echo "Installed DRAT-trim $drat_trim_revision in $bin_root"
