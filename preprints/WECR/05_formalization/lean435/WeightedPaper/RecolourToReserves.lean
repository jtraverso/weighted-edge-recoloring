import WeightedPaper.VectorBalance
import WeightedPaper.RankOne
import OverfullWork.AlignedInternal

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V X : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k n : ℕ}

noncomputable def uncoveredWeight (C : M.EdgeColoring k) (w : V → ℝ) (i : Fin k) : ℝ :=
  ∑ v ∈ univ.filter (fun v => (C.colourGraph i).degree v = 0), w v

/-- The real-scaled exceptional reserve, using the row inequality
multiplied by the palette size. -/
theorem reserve_of_balanced_load (C : M.EdgeColoring k) (w : V → ℝ)
    (bound scale H : ℝ) (σ : ℕ)
    (hw : ∀ v, 0 ≤ w v) (hσ : ∀ v, w v ≠ 0 → M.degree v ≤ σ)
    (hgap : ∀ i j, WeightedRecolouring.load C w i - WeightedRecolouring.load C w j ≤ H)
    (hbudget : (k : ℝ) * (bound + (k-1 : ℕ)*scale) + (k-1 : ℕ)*H ≤
      ((k : ℝ)-σ)*(∑ v,w v)) :
    ∀ i, bound + (k-1 : ℕ)*scale ≤ uncoveredWeight C w i := by
  intro i
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have h := uncovered_weight_lower C w H σ hw hσ i (hgap i)
  apply le_of_mul_le_mul_left _ hk
  change _ ≤ (k : ℝ) * ∑ v ∈ univ.filter (fun v => (C.colourGraph i).degree v = 0), w v
  linarith only [h,hbudget]

theorem exists_rank_one_recolour_with_reserves (C : M.EdgeColoring k)
    (t : V → ℝ) (u scale : X → ℝ) (R bound : ℝ) (σ : ℕ)
    (hR : 0 ≤ R) (ht₀ : ∀ v, 0 ≤ t v) (htR : ∀ v, t v ≤ R) (hu : ∀ x, 0 ≤ u x)
    (heq : ∀ i j, C.colourMass i ≤ C.colourMass j + 1)
    (hσ : ∀ v, t v ≠ 0 → M.degree v ≤ σ)
    (hbudget : ∀ x, (k : ℝ) * (bound + (k-1 : ℕ)*scale x) +
      (k-1 : ℕ)*(2*R*u x) ≤ ((k : ℝ)-σ)*(∑ v, t v*u x)) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      ∀ x i, bound + (k-1 : ℕ)*scale x ≤ uncoveredWeight D (fun v => t v*u x) i := by
  obtain ⟨D,hD,hgap,_⟩ := exists_recolour_rank_one C t u R hR ht₀ htR hu heq
  refine ⟨D,hD,fun x => reserve_of_balanced_load D (fun v => t v*u x) bound (scale x)
    (2*R*u x) σ (fun v => mul_nonneg (ht₀ v) (hu x)) ?_ (fun i j => (abs_le.mp (hgap x i j)).2)
    (hbudget x)⟩
  intro v hv
  apply hσ v
  intro h
  exact hv (by simp [h])


def dot {J : Type*} [Fintype J] (u v : J → ℝ) : ℝ := ∑ j, u j * v j

private theorem load_dot (C : M.EdgeColoring k) (u : Fin n → ℝ)
    (w : V → Fin n → ℝ) (i : Fin k) :
    WeightedRecolouring.load C (fun v => dot u (w v)) i =
      dot u (fun j => WeightedRecolouring.load C (fun v => w v j) i) := by
  simp only [WeightedRecolouring.load,dot,mul_sum,sum_mul]
  rw [sum_comm]
  refine sum_congr rfl (fun j _ => sum_congr rfl (fun v _ => ?_))
  ring

private theorem load_eq_on_nonisolated (C : M.EdgeColoring k) (w z : V → ℝ)
    (h : ∀ v, M.degree v ≠ 0 → w v = z v) (i : Fin k) :
    WeightedRecolouring.load C w i = WeightedRecolouring.load C z i := by
  unfold WeightedRecolouring.load
  apply sum_congr rfl
  intro v _
  by_cases hv : M.degree v = 0
  · have hdeg : (C.colourGraph i).degree v = 0 :=
      Nat.eq_zero_of_le_zero ((C.incidence_le_degree v i).trans (Nat.le_of_eq hv))
    simp [hdeg]
  · rw [h v hv]

/-- Changing weights by a constant on the nonisolated vertices adds
the constant times twice the prescribed matching size to the load. -/
theorem load_of_translated_profile (C : M.EdgeColoring k) (w z : V → ℝ)
    (center : ℝ) (i : Fin k) (h : ∀ v, M.degree v ≠ 0 → w v = center + z v) :
    WeightedRecolouring.load C w i =
      WeightedRecolouring.load C z i + 2 * center * (C.colourMass i : ℝ) := by
  have hrel : ∀ v, M.degree v ≠ 0 → w v - center = z v := by
    intro v hv
    rw [h v hv]
    ring
  have he := load_eq_on_nonisolated C (fun v => w v - center) z hrel i
  rw [WeightedRecolouring.load_shift] at he
  linarith

/-- The profiles may be translated in each row. For nonuniform masses,
the translation costs at most twice the center magnitude times the mass gap. -/
theorem exists_vector_recolour_with_reserves (C : M.EdgeColoring k)
    (w : V → Fin n → ℝ) (u : X → Fin n → ℝ) (actual : X → V → ℝ)
    (center charge : X → ℝ) (R H bound : ℝ) (σ d : ℕ)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hwt : ∀ v, energy (w v) ≤ R^2) (hu : ∀ x, energy (u x) ≤ 1)
    (hw₀ : ∀ x v, 0 ≤ actual x v)
    (htrans : ∀ x v, M.degree v ≠ 0 → actual x v = center x + dot (u x) (w v))
    (hm : ∀ i j, C.colourMass i ≤ C.colourMass j + d)
    (hHsq : (2*R)^2*((d : ℝ)^2+4*n) ≤ H^2)
    (hσ : ∀ x v, actual x v ≠ 0 → M.degree v ≤ σ)
    (hbudget : ∀ x, (k : ℝ) * (bound + (k-1 : ℕ)*charge x) +
      (k-1 : ℕ)*(H+2*|center x| *d) ≤ ((k : ℝ)-σ)*(∑ v, actual x v)) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      ∀ x i, bound + (k-1 : ℕ)*charge x ≤ uncoveredWeight D (actual x) i := by
  obtain ⟨D,hD,hW⟩ := exists_balanced_vector_prescribed_sizes C w R hR hwt
  refine ⟨D,hD,fun x => reserve_of_balanced_load D (actual x) bound (charge x)
    (H+2*|center x| *d) σ (hw₀ x) (hσ x) ?_ (hbudget x)⟩
  intro i j
  let f (t : Fin n) := WeightedRecolouring.load D (fun v => w v t) i -
    WeightedRecolouring.load D (fun v => w v t) j
  let gap := (C.colourMass i : ℝ) - C.colourMass j
  have he : WeightedRecolouring.load D (actual x) i -
      WeightedRecolouring.load D (actual x) j = dot (u x) f + 2*center x*gap := by
    have hload (a : Fin k) := load_of_translated_profile D (actual x)
      (fun v => dot (u x) (w v)) (center x) a (htrans x)
    rw [hload i,hload j,load_dot,load_dot,hD,hD]
    simp only [dot, f, mul_sub,sum_sub_distrib,gap]
    ring
  rw [he]
  have hmass (i j : Fin k) : (C.colourMass i : ℝ) - C.colourMass j ≤ d := by
    have h : (C.colourMass i : ℝ) ≤ (C.colourMass j : ℝ) + d := by exact_mod_cast hm i j
    linarith
  have habs : |gap| ≤ (d : ℝ) := abs_le.mpr ⟨by
    dsimp [gap]
    linarith only [hmass j i], hmass i j⟩
  have hd2 : gap^2 ≤ (d : ℝ)^2 :=
    sq_le_sq.mpr (habs.trans_eq (abs_of_nonneg (show 0 ≤ (d : ℝ) from Nat.cast_nonneg d)).symm)
  have hbound : energy f ≤ H^2 := (hW i j).trans
    ((mul_le_mul_of_nonneg_left (add_le_add_left hd2 _) (sq_nonneg (2*R))).trans hHsq)
  have hf : (dot (u x) f)^2 ≤ energy (u x) * energy f := sum_mul_sq_le_sq_mul_sq univ (u x) f
  have hx := hf.trans ((mul_le_mul_of_nonneg_right (hu x) (energy_nonneg f)).trans
    (by simpa only [one_mul] using hbound))
  have hdot : dot (u x) f ≤ H := by nlinarith [sq_nonneg (dot (u x) f-H)]
  have hshift : 2*center x*gap ≤ 2*|center x| *(d : ℝ) := by
    calc
      _ ≤ |2*center x*gap| := le_abs_self _
      _ = 2*|center x| *|gap| := by simp [abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left habs (by positivity)
  exact add_le_add hdot hshift

end WeightedPaper
