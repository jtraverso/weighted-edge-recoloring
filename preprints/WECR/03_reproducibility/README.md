# Reproduction

From the repository root, check the versioned package.

```sh
sha256sum -c preprints/WECR/04_integrity/SHA256SUMS
```

The PDF script uses pdfLaTeX, `latexmk`, and Latin Modern fonts for the Spanish edition. It builds the manuscript and companion in each language in the directory you pass.

```sh
preprints/WECR/03_reproducibility/build-pdfs.sh /tmp/wecr-pdfs
```

With Elan, Git, and Python 3 available, the Lean script builds the entire project under Lean 4.35.0-rc3 with one pinned Mathlib revision.

```sh
preprints/WECR/03_reproducibility/verify-lean.sh /tmp/wecr-lean
```

This checks the axioms of every declaration named in `WECRAudit.lean` and replays every source module. The source archive in `05_formalization/freeze` contains the full project, including the three pinned flow sources used by the block proofs. Its `evidence/` directory contains the verification reports. See [source provenance](../05_formalization/lean435/PROVENANCE.md) for the original commits and the proof edits used for migration.

The optional finite grid check uses SciPy's mixed-integer linear solver to find a helper schedule, then checks every selected pair and degree with integer arithmetic. Its two instances use \(q=12\) and \(b=1,2\).

```sh
python3 preprints/WECR/03_reproducibility/check-grid.py
```

The separate Certo certificate is in `certo-grid/`. With Certo 0.40.0 at commit `df0ec25178a6` installed, run `certo verify inertia.json --spec grid_inertia.py --complete` in that directory to compare the certificate to its specification.
