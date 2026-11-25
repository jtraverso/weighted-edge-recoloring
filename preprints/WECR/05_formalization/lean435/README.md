# WECR in Lean 4.35.0-rc3

This project accompanies *Weighted edge recoloring and 1-factorization across a cut*, Preprint 1.0. The manifest pins a single Mathlib revision for all proofs, including the recoloring, sequential completion, exact block deficits, simultaneous repair, and the two arguments for the sparse grid.

From this directory, run the following commands with Elan, Git, and Python 3 available.

```sh
sha256sum -c evidence/SHA256SUMS
lake exe cache get
./verify.sh /tmp/wecr-lean
```

The script builds the complete project, checks the axioms of the declarations named in `WECRAudit.lean`, and replays every source module with Lean's kernel. The recorded output is in `evidence/`. The [source notes](PROVENANCE.md) identify the pinned development and flow proofs.
