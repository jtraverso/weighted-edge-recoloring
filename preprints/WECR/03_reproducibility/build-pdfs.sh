#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=$(realpath -m "${1:?pass an output directory}")
mkdir -p "$out"
export SOURCE_DATE_EPOCH=1795478400
export FORCE_SOURCE_DATE=1
for lang in en es; do
  (cd "$root/01_manuscript" && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$out" WECR_preprint_v1.0_"$lang".tex)
  (cd "$root/05_formalization" && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$out" WECR_FORMALIZATION_COMPANION_v1.0_"$lang".tex)
done
