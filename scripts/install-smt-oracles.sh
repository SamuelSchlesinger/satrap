#!/bin/sh

set -eu

repo_root=$(git rev-parse --show-toplevel)
cache_root=${SMT_ORACLE_CACHE:-"$repo_root/.cache/smt-oracles"}
archive_root="$cache_root/archives"
unpack_root="$cache_root/unpacked"
bin_root="$cache_root/bin"

z3_version=4.16.0
cvc5_version=1.3.3
bitwuzla_version=0.9.1

case "$(uname -s):$(uname -m)" in
    Darwin:arm64)
        z3_asset="z3-${z3_version}-arm64-osx-15.7.3.zip"
        z3_sha256=41828fa07d5cb77bfaee326e8e6dac074f26329c09c633f9e66012bb917cf8ae
        cvc5_asset="cvc5-macOS-arm64-static.zip"
        cvc5_sha256=0ad2df5de1b35c0fda6afa9ca9f7b542a615c2137e1ec678a45deccdda1871b2
        bitwuzla_asset="Bitwuzla-macOS-arm64-static.zip"
        bitwuzla_sha256=86a6fb1af2b7cdaf3f7807662ab679088113bbf3e55d243597f98d826bcb7511
        ;;
    Linux:x86_64)
        z3_asset="z3-${z3_version}-x64-glibc-2.39.zip"
        z3_sha256=7288c49a5bd6dbafd7b0b0d1f65956b91672da24b08f09242919af159be3418e
        cvc5_asset="cvc5-Linux-x86_64-static.zip"
        cvc5_sha256=413f56f01f3a7374105c654581e67249eb66d4e430e748b17962d595cd4861b6
        bitwuzla_asset="Bitwuzla-Linux-x86_64-static.zip"
        bitwuzla_sha256=057f1546ae2068df57beb178f3eeab1678f0e5f0c378787a05b7bb294617c9c6
        ;;
    *)
        echo "unsupported SMT-oracle platform: $(uname -s) $(uname -m)" >&2
        exit 1
        ;;
esac

for tool in curl unzip; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        echo "$tool is required to install the SMT oracles" >&2
        exit 1
    fi
done
if ! command -v sha256sum >/dev/null 2>&1 \
    && ! command -v shasum >/dev/null 2>&1; then
    echo "sha256sum or shasum is required to verify SMT-oracle archives" >&2
    exit 1
fi

mkdir -p "$archive_root" "$unpack_root" "$bin_root"

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

fetch_archive() {
    fetch_url=$1
    fetch_sha256=$2
    fetch_path=$3
    if [ -f "$fetch_path" ] && verify_sha256 "$fetch_path" "$fetch_sha256"; then
        return
    fi
    curl --fail --location --silent --show-error \
        --output "$fetch_path" \
        "$fetch_url"
    if ! verify_sha256 "$fetch_path" "$fetch_sha256"; then
        echo "checksum mismatch for $fetch_path" >&2
        exit 1
    fi
}

z3_archive="$archive_root/$z3_asset"
cvc5_archive="$archive_root/$cvc5_asset"
bitwuzla_archive="$archive_root/$bitwuzla_asset"

fetch_archive \
    "https://github.com/Z3Prover/z3/releases/download/z3-${z3_version}/${z3_asset}" \
    "$z3_sha256" \
    "$z3_archive"
fetch_archive \
    "https://github.com/cvc5/cvc5/releases/download/cvc5-${cvc5_version}/${cvc5_asset}" \
    "$cvc5_sha256" \
    "$cvc5_archive"
fetch_archive \
    "https://github.com/bitwuzla/bitwuzla/releases/download/${bitwuzla_version}/${bitwuzla_asset}" \
    "$bitwuzla_sha256" \
    "$bitwuzla_archive"

unzip -q -o "$z3_archive" -d "$unpack_root"
unzip -q -o "$cvc5_archive" -d "$unpack_root"
unzip -q -o "$bitwuzla_archive" -d "$unpack_root"

z3_directory=${z3_asset%.zip}
cvc5_directory=${cvc5_asset%.zip}
bitwuzla_directory=${bitwuzla_asset%.zip}
ln -sf "$unpack_root/$z3_directory/bin/z3" "$bin_root/z3"
ln -sf "$unpack_root/$cvc5_directory/bin/cvc5" "$bin_root/cvc5"
ln -sf "$unpack_root/$bitwuzla_directory/bin/bitwuzla" "$bin_root/bitwuzla"

echo "Installed pinned SMT oracles in $bin_root"
