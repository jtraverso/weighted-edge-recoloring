import WeightedPaper.RecolourToReserves

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V X : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k n : ℕ}

/-- Use the exact weighted internal degree as the palette-wide debit. -/
theorem reserve_of_balanced_load_exact (C : M.EdgeColoring k) (w : V → ℝ)
    (bound scale H : ℝ)
    (hgap : ∀ i j, WeightedRecolouring.load C w i - WeightedRecolouring.load C w j ≤ H)
    (hbudget : (k : ℝ) * (bound + (k-1 : ℕ)*scale) + (k-1 : ℕ)*H ≤
      (k:ℝ)*(∑ v,w v) - ∑ v, w v*(M.degree v:ℝ)) :
    ∀ i, bound + (k-1 : ℕ)*scale ≤ uncoveredWeight C w i := by
  intro i
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have htotal := load_le_average_add (WeightedRecolouring.load C w) i H (hgap i)
  rw [Fintype.card_fin, sum_load] at htotal
  have hcompl : uncoveredWeight C w i + WeightedRecolouring.load C w i = ∑ v, w v := by
    unfold uncoveredWeight WeightedRecolouring.load
    rw [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    have hp := C.colourGraph_degree_le_one i v
    by_cases hz : (C.colourGraph i).degree v = 0
    · simp [hz]
    · have ho : (C.colourGraph i).degree v = 1 := by omega
      simp [ho]
  apply le_of_mul_le_mul_left _ hk
  linarith only [htotal,hbudget, congrArg (fun z : ℝ => (k : ℝ) * z) hcompl]

theorem exists_rank_one_recolour_with_exact_reserves (C : M.EdgeColoring k)
    (t : V → ℝ) (u scale : X → ℝ) (R bound : ℝ)
    (hR : 0 ≤ R) (ht₀ : ∀ v, 0 ≤ t v) (htR : ∀ v, t v ≤ R) (hu : ∀ x, 0 ≤ u x)
    (heq : ∀ i j, C.colourMass i ≤ C.colourMass j + 1)
    (hbudget : ∀ x, (k : ℝ) * (bound + (k-1 : ℕ)*scale x) +
      (k-1 : ℕ)*(2*R*u x) ≤ (k:ℝ)*(∑ v, t v*u x) -
        ∑ v,(t v*u x)*(M.degree v:ℝ)) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      ∀ x i, bound + (k-1 : ℕ)*scale x ≤ uncoveredWeight D (fun v => t v*u x) i := by
  obtain ⟨D,hD,hgap,_⟩ := exists_recolour_rank_one C t u R hR ht₀ htR hu heq
  exact ⟨D,hD,fun x => reserve_of_balanced_load_exact D (fun v => t v*u x) bound (scale x)
    (2*R*u x) (fun i j => (abs_le.mp (hgap x i j)).2) (hbudget x)⟩

private theorem load_dot (C : M.EdgeColoring k) (u : Fin n → ℝ)
    (w : V → Fin n → ℝ) (i : Fin k) :
    WeightedRecolouring.load C (fun v => dot u (w v)) i =
      dot u (fun j => WeightedRecolouring.load C (fun v => w v j) i) := by
  simp only [WeightedRecolouring.load,dot,mul_sum,sum_mul]
  rw [sum_comm]
  refine sum_congr rfl (fun j _ => sum_congr rfl (fun v _ => ?_))
  ring

/-- The profiles may be translated in each row. For nonuniform masses,
the translation costs at most twice the center magnitude times the mass gap. -/
theorem exists_vector_recolour_with_exact_reserves (C : M.EdgeColoring k)
    (w : V → Fin n → ℝ) (u : X → Fin n → ℝ) (actual : X → V → ℝ)
    (center charge : X → ℝ) (R bound : ℝ) (H : X → ℝ) (d : ℕ)
    (hR : 0 ≤ R) (hH : ∀ x, 0 ≤ H x) (hwt : ∀ v, energy (w v) ≤ R^2)
    (htrans : ∀ x v, M.degree v ≠ 0 → actual x v = center x + dot (u x) (w v))
    (hm : ∀ i j, C.colourMass i ≤ C.colourMass j + d)
    (hHsq : ∀ x, energy (u x)*((2*R)^2*((d : ℝ)^2+4*n)) ≤ (H x)^2)
    (hbudget : ∀ x, (k : ℝ) * (bound + (k-1 : ℕ)*charge x) +
      (k-1 : ℕ)*(H x+2*|center x| *d) ≤ (k:ℝ)*(∑ v, actual x v) -
        ∑ v,actual x v*(M.degree v:ℝ)) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      ∀ x i, bound + (k-1 : ℕ)*charge x ≤ uncoveredWeight D (actual x) i := by
  obtain ⟨D,hD,hW⟩ := exists_balanced_vector_prescribed_sizes C w R hR hwt
  refine ⟨D,hD,fun x => reserve_of_balanced_load_exact D (actual x) bound (charge x)
    (H x+2*|center x| *d) ?_ (hbudget x)⟩
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
  have hbound : energy f ≤ (2*R)^2*((d:ℝ)^2+4*n) :=
    (hW i j).trans (mul_le_mul_of_nonneg_left (add_le_add_left hd2 _) (sq_nonneg (2*R)))
  have hf : (dot (u x) f)^2 ≤ energy (u x) * energy f := sum_mul_sq_le_sq_mul_sq univ (u x) f
  have hx := hf.trans ((mul_le_mul_of_nonneg_left hbound (energy_nonneg (u x))).trans (hHsq x))
  have hdot : dot (u x) f ≤ H x := by nlinarith [hH x, sq_nonneg (dot (u x) f-H x)]
  have hshift : 2*center x*gap ≤ 2*|center x| *(d : ℝ) := by
    calc
      _ ≤ |2*center x*gap| := le_abs_self _
      _ = 2*|center x| *|gap| := by simp [abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left habs (by positivity)
  exact add_le_add hdot hshift

end WeightedPaper

#print axioms WeightedPaper.reserve_of_balanced_load_exact
#print axioms WeightedPaper.exists_rank_one_recolour_with_exact_reserves
#print axioms WeightedPaper.exists_vector_recolour_with_exact_reserves
