import Mathlib.Analysis.InnerProductSpace.PiL2
import WeightedPaper.EuclideanBalance

namespace WeightedPaper

open Finset SimpleGraph
open scoped Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sum of the vector weights of all vertices covered by a colour. -/
noncomputable def vectorLoad (C : M.EdgeColoring k) (w : V → E) (i : Fin k) : E :=
  ∑ v, ((C.colourGraph i).degree v : ℝ) • w v

theorem vectorLoad_sub_const (C : M.EdgeColoring k) (w : V → E) (c : E) (i : Fin k) :
    vectorLoad C (fun v => w v-c) i = vectorLoad C w i - (2*(C.colourMass i : ℝ)) • c := by
  simp only [vectorLoad, smul_sub, sum_sub_distrib, ← sum_smul, ← Nat.cast_sum,
    (C.colourGraph i).sum_degrees_eq_twice_edgeCount, Nat.cast_mul, Nat.cast_ofNat,
    MultiGraph.EdgeColoring.colourMass]

/-- The Euclidean balance theorem in the intrinsic dimension of the centered
profiles. The squared-norm statement has the same discrepancy constants. -/
theorem exists_balanced_in_span [FiniteDimensional ℝ E] (C : M.EdgeColoring k)
    (w : V → E) (center : E) (R : ℝ) (hR : 0 ≤ R) (hw : ∀ v, ‖w v-center‖ ≤ R) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      ∀ a b, ‖vectorLoad D (fun v => w v-center) a -
        vectorLoad D (fun v => w v-center) b‖^2 ≤
          (2*R)^2 * discrepancyFactorSq
            (Module.finrank ℝ (Submodule.span ℝ (Set.range fun v => w v-center)))
            ((C.colourMass a : ℝ)-C.colourMass b) := by
  let S := Submodule.span ℝ (Set.range fun v => w v-center)
  let z (v : V) : S := ⟨w v-center, Submodule.subset_span ⟨v,rfl⟩⟩
  let basis := stdOrthonormalBasis ℝ S
  let coord (v : V) (j : Fin (Module.finrank ℝ S)) := basis.repr (z v) j
  have hcoord (v : V) : energy (fun j => coord v j - 0) ≤ R^2 := by
    simp only [sub_zero, coord, energy, ← EuclideanSpace.real_norm_sq_eq,
      LinearIsometryEquiv.norm_map]
    exact pow_le_pow_left₀ (norm_nonneg _) (hw v) 2
  obtain ⟨D,hD,hbal⟩ := exists_balanced_euclidean_prescribed_sizes C coord (fun _ => 0) R hR hcoord
  refine ⟨D,hD,fun a b => ?_⟩
  have hcoe (i : Fin k) : (vectorLoad D z i : S).val = vectorLoad D (fun v => w v-center) i := by
    simp only [vectorLoad, Submodule.coe_sum, Submodule.coe_smul, z]
  have hrepr (i : Fin k) (j : Fin (Module.finrank ℝ S)) :
      basis.repr (vectorLoad D z i) j = WeightedRecolouring.load D (fun v => coord v j) i := by
    let proj : S →ₗ[ℝ] ℝ :=
      (EuclideanSpace.projₗ j).comp basis.repr.toLinearEquiv.toLinearMap
    change proj (vectorLoad D z i) = _
    simp only [vectorLoad, map_sum, map_smul, WeightedRecolouring.load, smul_eq_mul]
    exact sum_congr rfl (fun v _ => mul_comm _ _)
  have hnorm : ‖vectorLoad D (fun v => w v-center) a -
      vectorLoad D (fun v => w v-center) b‖^2 =
      energy (fun j => WeightedRecolouring.load D (fun v => coord v j) a -
        WeightedRecolouring.load D (fun v => coord v j) b) := by
    rw [← hcoe a, ← hcoe b]
    change ‖vectorLoad D z a - vectorLoad D z b‖^2 = _
    rw [← basis.repr.norm_map, EuclideanSpace.real_norm_sq_eq, map_sub]
    simp only [energy, PiLp.sub_apply, hrepr]
  rw [hnorm]
  simpa using hbal a b

end WeightedPaper
