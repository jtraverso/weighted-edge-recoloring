import WeightedPaper.Cut.SpectralCut
import WeightedPaper.Examples.Matrices
import Mathlib.Algebra.Order.Chebyshev

namespace WeightedPaper.Examples.Grid
open Finset
open scoped Classical
abbrev Copy := Quad (Fin 64)
abbrev Ord (q : ℕ) := Fin q × Fin q × Copy
variable {q : ℕ}
def adjacent (x y : Ord q) : Prop := x.1 = y.1 ∨ x.2.1 = y.2.1
instance (x y : Ord q) : Decidable (adjacent x y) := inferInstanceAs (Decidable (_ ∨ _))
@[simp] theorem card_copy : Fintype.card Copy = 256 := by rw [card_quad,Fintype.card_fin]
@[simp] theorem card_ord : Fintype.card (Ord q) = 256*q^2 := by
  simp only [Ord,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

/-- The ordinary biadjacency acts by adding a row and a column and subtracting
their common cell. This includes all copies in the corresponding cell. -/
theorem support_sum (v : Ord q → ℝ) (x : Ord q) :
    (∑ y, v y * (if adjacent x y then 1 else 0)) =
       (∑ j, ∑ c : Copy,v (x.1,j,c)) + (∑ i,∑ c : Copy,v (i,x.2.1,c)) -
       ∑ c : Copy,v (x.1,x.2.1,c) := by
  let z (i j : Fin q) := ∑ c : Copy,v (i,j,c)
  have hcell (i j : Fin q) :
      (∑ c : Copy,v (i,j,c)*(if adjacent x (i,j,c) then 1 else 0)) =
        (if x.1=i then z i j else 0)+(if x.2.1=j then z i j else 0)-
        (if x.1=i then if x.2.1=j then z i j else 0 else 0) := by
    by_cases hi : x.1=i <;> by_cases hj : x.2.1=j <;> simp [adjacent,z,hi,hj]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type (f := fun y : Fin q × Copy => _)]
  simp only [hcell,sum_sub_distrib,sum_add_distrib,sum_ite_irrel,sum_const_zero]
  simp [z]

end WeightedPaper.Examples.Grid
