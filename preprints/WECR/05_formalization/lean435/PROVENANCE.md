# Source provenance

The original WECR core comes from commit `e64ceb9ba04ca04a1b4d071e8b1e541b5c1cfc3d`. The earlier spectral and block developments and the hybrid repair were taken from the preprint snapshot `wecr-lean-complete-v1` at commit `7e8d24985864680d846f83e2e89232907bda713d`. The source files for the earlier cut and block proofs now live in `WeightedPaper/Cut/` and `WeightedPaper/Blocks/`. These module paths allow the earlier spectral grid and the sparse repair grid to coexist. The core recoloring entry point is `WeightedPaper.Recolouring`. The shared weighted Hall and bipartite factorization modules each have one copy.

The edit to `OneFactor/Stair.lean` follows the author's earlier Lean 4.35 migration at commit `fc6d106777afcd48f00188dbda8848a1353b61d6`. The block graph uses `Finset.equivOfEq` to identify its second side with the complement of the first, using the current Mathlib API.

The three flow files used by the block proof come from the exact commits previously fetched by the verification script. Their sources and license texts accompany this snapshot.

| Module | Source |
| --- | --- |
| `LeanPool.MaxFlowMinCut` | [Dross fractional triangle decomposition, `7720b7b591e6`](https://github.com/jtraverso/dross-fractional-triangle-decomposition/blob/7720b7b591e606d5a56f1d935d8be650dcbf6c6f/LeanPool/MaxFlowMinCut.lean) |
| `BaranyaiLib.IntegralFlow` | [Baranyai's theorem, `0ff6d6f4005b`](https://github.com/jtraverso/baranyai-theorem/blob/0ff6d6f4005b0b68114e0b99e6d342742918b629/BaranyaiLib/IntegralFlow.lean) |
| `GaleHoffmanLib.Feasibility` | [Gale–Hoffman feasibility, `fa52c29c24ed`](https://github.com/jtraverso/gale-hoffman-feasibility/blob/fa52c29c24edf7e9afdb487df3764affd43c51c7/GaleHoffmanLib/Feasibility.lean) |
