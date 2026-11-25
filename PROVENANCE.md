# Source provenance

The solution uses the Lean 4.35.0-rc3 development for WECR Preprint 1.0. The comparison targets use the original declaration names. The grid definitions are collected in `WECRGridModel.lean` and stated independently in `WECRRegistryChallenge.lean`. The challenge imports Mathlib.

- The weighted Hall reserves come from the WECR development based on the author's Overfull Criteria. [Palomar](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-08-000004)
- The bipartite residue uses the Kőnig proof inherited from the author's Erdős #81 Paper V. That development credits Aristotle, by Harmonic. [Paper V](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/papers-v-vi-notes-preprint-1.0/preprints/PAPER_V)
- The pinned Keevash nibble and Lovász local lemma proofs supply the probabilistic estimates used by the repair. [Nibble](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-19-000022) · [Local lemma](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-20-000004)
- The challenge uses the degree and codegree definitions from `PseudorandomLib.Defs`, a dependency of the pinned nibble development. [Dependency manifest](lake-manifest.json)
