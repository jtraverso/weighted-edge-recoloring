# Weighted edge recoloring and 1-factorization across a cut

This Lean project was prepared for Palomar registration of Theorem 9 and the growth estimates in Corollary 10 of Juan Pablo Traverso Gianini's Preprint 1.0. It uses Lean 4.35.0-rc3. The two comparison targets cover the hybrid factorization theorem and both growth rates. The solution also builds the direct sparse grid factorization and rectangle separation in Corollary 10.

The paper's [Preprint 1.0 release page](https://github.com/jtraverso/weighted-edge-recoloring/releases/tag/preprint-1.0) provides the full Lean development and the companion mapping all ten numbered results. This project's [source notes](PROVENANCE.md) credit its proof dependencies.

Build the solution and the challenge using the pinned dependencies.

~~~sh
lake exe cache get
lake build WECRRegistryChallenge WECRRegistrySolution
lake env lean CheckSolution.lean
lake comparator --config comparator.wecr.json
~~~

The explicit challenge holes occur only in the two compared theorem statements in `WECRRegistryChallenge.lean`. The solution imports the proofs from `HybridHost.lean`, `GridRectangle.lean`, and `GridGrowth.lean`.
