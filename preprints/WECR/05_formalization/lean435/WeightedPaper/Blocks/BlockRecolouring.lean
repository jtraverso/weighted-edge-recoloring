import WeightedPaper.Blocks.BlockFactorization
import WeightedPaper.Cut.ExactIncidence

namespace WeightedPaper.Blocks

open Finset SimpleGraph
open scoped Classical

variable {J A V : Type*} [Fintype V] [DecidableEq V]

/-- Recolor each ordinary block with its own weights. This preserves every
labeled class size in every block and produces row certificates for
an arbitrary schedule of free exceptional vertices. -/
theorem recolour_blocks_with_reserves (M : MultiGraph V) (T : J → Finset V)
    (cap : ∀ j, A → T j → ℕ) (X : J → Finset A) (Y : ∀ j, Finset (T j))
    (k : ℕ) (gap : J → ℕ) (U : Fin k → Finset A)
    (C : ∀ j, (M.restrict (T j)).EdgeColoring k)
    (budget : ∀ j, ExactIncidenceBudget M (T j) (cap j) (X j) (Y j) k (gap j))
    (heq : ∀ j i i', (C j).colourMass i ≤ (C j).colourMass i' + 1)
    (hgap : ∀ j i i', (C j).colourMass i ≤ (C j).colourMass i' + gap j) :
    ∃ D : ∀ j, (M.restrict (T j)).EdgeColoring k,
      (∀ j i, (D j).colourMass i = (C j).colourMass i) ∧
      ∀ j, Nonempty (RowReserves U (missingOn (D j) (T j)) (cap j) univ (X j) (Y j)) := by
  classical
  choose D hmass hreserve using fun j => (budget j).exists_recolour (C j) (heq j) (hgap j)
  refine ⟨D,hmass,fun j => ?_⟩
  let P := budget j
  refine ⟨⟨P.weight,P.charge,P.bound,P.bound_pos,P.charge_nonneg,P.capacity,P.column,?_⟩⟩
  intro i _ x hx
  simp only [card_univ,Fintype.card_fin]
  convert hreserve j ⟨x,(mem_filter.mp hx).2⟩ i using 1
  apply sum_congr _ (fun _ _ => rfl)
  ext y
  simp

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.recolour_blocks_with_reserves
