import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace WeightedPaper.Repair
open Finset
open scoped Classical

/-- Each endpoint of matching edge j has weight R e_j. For every split
of the edges (in particular, an equal-size split), the two class loads have
distance 2 R sqrt(s). -/
theorem coordinate_matching_discrepancy (s : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (S : Finset (Fin s)) :
    let load (U : Finset (Fin s)) : EuclideanSpace ℝ (Fin s) :=
      WithLp.toLp 2 (fun j => if j ∈ U then 2*R else 0)
    ‖load S - load Sᶜ‖ = 2*R*√(s:ℝ) := by
  intro load
  have sqNorm := EuclideanSpace.real_norm_sq_eq (load S - load Sᶜ)
  have entry (j : Fin s) : ((load S - load Sᶜ) j)^2 = (2*R)^2 := by
    by_cases h : j ∈ S <;> simp [load, PiLp.sub_apply, h]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [show ‖load S-load Sᶜ‖^2 = ∑ j, ((load S-load Sᶜ) j)^2 from sqNorm]
  simp only [entry, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = (2*R)^2*(√(s:ℝ))^2 := by rw [Real.sq_sqrt (Nat.cast_nonneg s)]; ring
    _ = _ := (mul_pow _ _ _).symm

end WeightedPaper.Repair
