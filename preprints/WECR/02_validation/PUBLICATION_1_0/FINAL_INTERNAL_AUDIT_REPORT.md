# Internal audit · Preprint 1.0

**PASS · November 25, 2026**

The audit covers the preprint, its formalization companion, the unified Lean source snapshot, and the accompanying computational evidence. The companion identifies the checked Lean statements and their hypotheses. The Preprint 1.0 source archive pins the verified Lean development.

| Check | Status | Evidence |
| --- | --- | --- |
| Prescribed-size recoloring and earlier crossing criteria | PASS | The original core and its spectral and exact-reserve extensions compile under Lean 4.35.0-rc3. |
| Block cuts, exact deficits, capacities, and host assembly | PASS | The block development and both auxiliary examples compile in the same project. The three flow proofs use their pinned source revisions. [Source provenance](../../05_formalization/lean435/PROVENANCE.md) |
| Axioms and kernel replay | PASS | Lean 4.35.0-rc3 replayed all 225 modules and audited 166 distinct declarations, covering the recoloring, block completion, and spectral repair developments. The audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`, or a subset of them. [Verification logs](../../05_formalization/lean435/evidence/) · [Source check](lean435-source-check.txt) |
| Coverage of Theorem 9 and Corollary 10 | PASS | The hybrid theorem preserves the initial palette under an injection and uses a threshold independent of the host and palette. The sparse grid satisfies the hybrid hypotheses at every sufficiently large size, uniformly after feasible exceptional matching. Lean checks both growth rates and the reserve spectrum for arbitrary positive cell size. [Hybrid theorem](../../05_formalization/lean435/HybridHost.lean) · [Application](../../05_formalization/lean435/GridHybrid.lean) · [Rates](../../05_formalization/lean435/GridGrowth.lean) |
| Constants in the manuscript and formalization | PASS | The formal proof gives a conflict budget of \(4/27\). The scalar bound is sharp for the common scaling and product estimate used there. The deterministic grid construction gives the factorization and rectangle separation for every even \(q\ge12\) and integer \(b\ge1\). [Derivation and scope](PROOF_CONSTANTS.md) |
| Independent finite calculations | PASS | A mixed-integer calculation found helper schedules for \(q=12\) and \(b=1,2\). A separate integer check verified every selected pair and the residual degrees. Certo checked the rectangular cell matrix by exact rational arithmetic and returned inertia \((1,28,3)\). [Grid check](grid-check.txt) · [Certo report](certo-replay.txt) |
| Manuscript and companion in English and Spanish | PASS | All four PDFs rebuilt byte for byte in two builds and list Juan Pablo Traverso Gianini as PDF Author. The reserved DOI 10.5281/zenodo.24521352 appears on the first page and in the PDF metadata of each document. The preceding text and links are preserved, and pages after the first render identically to the verified files. Both manuscripts have the same mathematical formulas, labels, and citation keys. The companion is numbered [23] with its full release URL in each manuscript. The final LaTeX runs reported no errors, warnings, or overfull boxes. [PDF verification](pdf-release-check.txt) |
| Frozen sources and integrity | PASS | The source archive was extracted and compared to the source tree. The extracted source hashes were checked. [Source archives](../../05_formalization/freeze/) · [Package checksums](../../04_integrity/SHA256SUMS) |

The verification used the pinned dependencies cached in the review environment. For this edition, all 229 source and configuration checksums were checked against the pinned Lean snapshot. The archive and the accompanying Lean source tree contain the same files and data.

## Numbered results

| Result | Lean evidence |
| --- | --- |
| Theorem 1 | `exists_balanced_in_span` and the squared-norm discrepancy in `IntrinsicBalance.lean`. |
| Corollary 2 | `exists_balanced_prescribed_sizes` and `sharp_connected_example`. |
| Lemma 3 | The rank-one and vector recoloring lemmas in `ExactReserves.lean` and `residual_row_weight_lower`. |
| Theorem 4 | `exists_factorization_of_exact_weighted_cut` and `exists_factorization_of_pair_degree_cut`. |
| Lemma 5 | `transport_cuts_iff_assignment` and `capacitated_cuts_iff_assignment`. |
| Corollary 6 | `route_of_block_capacity_cuts`, `packing_of_block_routing`, and `exists_factorization_of_block_capacity_cuts`. |
| Theorem 7 | `exists_exact_deficit_completion`, `exists_optimal_partial_packing`, and `transportDeficit_le_of_changed`, applied in both directions. |
| Lemma 8 | `repair_in_regular_reserve`, with the simultaneous probability estimates and disjoint reserve allocations. |
| Theorem 9 | `factorization_from_weighted_nibble` and the conclusion `HasSeededFactorization`. |
| Corollary 10 | `sparse_grid_factorization_and_separation`, `grid_host_ordinary_degrees`, and `sparse_grid_growth`. |

The application in Section 6.3 is checked by `grid_reserve_contraction`, `grid_norm_attained`, `grid_hybrid_certificates`, and `sparse_grid_hybrid_factorization`. The Euclidean lower-bound example is checked by `coordinate_matching_discrepancy`. The Certo calculation supplies the separate rational certificate for the finite rectangular illustration.

This report records internal review and reproducibility checks.
