#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
out=$(realpath -m "${1:?pass a directory for the verification reports}")
mkdir -p "$out"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

lake build > "$out/build.log" 2>&1
lake env lean --version > "$out/toolchain.txt"
lake env lean WECRAudit.lean > "$out/axioms.txt"
python3 - "$out/axioms.txt" <<'PY'
from pathlib import Path
import re
import sys

expected = re.findall(r"^#print axioms (\S+)$", Path("WECRAudit.lean").read_text(), re.M)
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", Path(sys.argv[1]).read_text())
assert expected and [name for name, _ in reports] == expected, "incomplete axiom report"
for name, axioms in reports:
    assert set(axioms.replace(",", "").split()) <= {"propext", "Classical.choice", "Quot.sound"}, name
print(f"{len(reports)} axiom reports passed")
PY

mapfile -d '' sources < <(find . -path './.lake' -prune -o -type f -name '*.lean' -printf '%P\0' | sort -z)
roots=()
for src in "${sources[@]}"; do
  prefix=${src%%/*}
  roots+=("${prefix%.lean}")
done
mapfile -t prefixes < <(printf '%s\n' "${roots[@]}" | sort -u)
lake env leanchecker -v "${prefixes[@]}" > "$out/kernel.txt" 2>&1
python3 - "$out/kernel.txt" "${sources[@]}" <<'PY'
from pathlib import Path
import re
import sys

modules = sorted(str(Path(src).with_suffix("")).replace("/", ".") for src in sys.argv[2:])
replayed = sorted(re.findall(r"^replaying (\S+)$", Path(sys.argv[1]).read_text(), re.M))
assert modules == replayed, {
    "missing": sorted(set(modules) - set(replayed)),
    "unexpected": sorted(set(replayed) - set(modules)),
}
print(f"{len(replayed)} modules replayed")
PY
sha256sum "${sources[@]}" lean-toolchain lakefile.toml lake-manifest.json verify.sh > "$out/SHA256SUMS"
