#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=$(realpath -m "${1:?pass an output directory}")
mkdir -p "$out"
cd "$root/05_formalization/lean435"
sha256sum -c evidence/SHA256SUMS > "$out/source-check.txt"
lake exe cache get > "$out/cache.log" 2>&1
./verify.sh "$out"
