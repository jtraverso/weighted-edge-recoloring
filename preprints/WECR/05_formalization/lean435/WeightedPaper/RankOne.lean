import WeightedRecolouring.Balance
import WeightedPaper.ScaledHall

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V X : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

/-- Summing the covered weights over the palette counts each vertex
exactly as often as its internal degree. -/
theorem sum_load (C : M.EdgeColoring k) (w : V → ℝ) :
    (∑ i, WeightedRecolouring.load C w i) = ∑ v, w v * (M.degree v : ℝ) := by
  unfold WeightedRecolouring.load
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [← mul_sum, ← Nat.cast_sum]
  congr 1
  simp only [MultiGraph.degree, MultiGraph.EdgeColoring.colourGraph]
  rw [sum_comm]
  exact_mod_cast (sum_congr rfl (fun e _ => C.sum_col e))

/-- The deviation from the average costs only the other (k-1) colours. -/
theorem load_le_average_add {I : Type*} [Fintype I] (f : I → ℝ) (i : I)
    (H : ℝ) (hgap : ∀ j, f i - f j ≤ H) :
    (Fintype.card I : ℝ) * f i ≤ (∑ j, f j) + (Fintype.card I - 1 : ℕ) * H := by
  classical
  have hsum := sum_le_sum (s := univ.erase i) (fun j _ => hgap j)
  rw [sum_sub_distrib] at hsum
  have htotal := sum_erase_add univ f (mem_univ i)
  have hcard : ((univ : Finset I).erase i).card = Fintype.card I - 1 := by simp
  have hI : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  simp only [sum_const, nsmul_eq_mul, hcard] at hsum
  rw [Nat.cast_sub hI, Nat.cast_one] at hsum
  rw [Nat.cast_sub hI, Nat.cast_one]
  linarith [htotal]

/-- Use one scalar colouring for all nonnegative multiples of the same
vertex-weight function. The inequalities preserve the sign of a gap
when the colour classes have different sizes. -/
theorem exists_recolour_rank_one (C : M.EdgeColoring k) (t : V → ℝ) (u : X → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (ht₀ : ∀ v, 0 ≤ t v) (htR : ∀ v, t v ≤ R) (hu : ∀ x, 0 ≤ u x)
    (heq : ∀ i j, C.colourMass i ≤ C.colourMass j + 1) :
    ∃ D : M.EdgeColoring k, (∀ i, D.colourMass i = C.colourMass i) ∧
      (∀ x i j, |WeightedRecolouring.load D (fun v => t v * u x) i -
        WeightedRecolouring.load D (fun v => t v * u x) j| ≤ 2 * R * u x) ∧
      (∀ x i j, C.colourMass j < C.colourMass i →
        WeightedRecolouring.load D (fun v => t v * u x) j ≤
          WeightedRecolouring.load D (fun v => t v * u x) i) := by
  obtain ⟨D, hD, hEqual, hStrict⟩ :=
    WeightedRecolouring.exists_balanced_prescribed_sizes C t 0 R hR ht₀ htR
  have hscale (x : X) (i : Fin k) :
      WeightedRecolouring.load D (fun v => t v * u x) i =
        WeightedRecolouring.load D t i * u x := by
    unfold WeightedRecolouring.load
    rw [sum_mul]
    apply sum_congr rfl
    intro v _
    ring
  have hstrict' (i j : Fin k) (h : C.colourMass j < C.colourMass i) :
      0 ≤ WeightedRecolouring.load D t i - WeightedRecolouring.load D t j ∧
      WeightedRecolouring.load D t i - WeightedRecolouring.load D t j ≤ 2 * R := by
    have hh := hStrict i j h
    have hmass : C.colourMass i = C.colourMass j + 1 :=
      le_antisymm (heq i j) (Nat.succ_le_of_lt h)
    simp only [hmass, Nat.cast_add, Nat.cast_one, mul_zero, add_sub_cancel_left, mul_one] at hh
    exact hh
  refine ⟨D, hD, ?_, ?_⟩
  · intro x i j
    rw [hscale, hscale, ← sub_mul, abs_mul, abs_of_nonneg (hu x)]
    apply mul_le_mul_of_nonneg_right _ (hu x)
    rcases lt_trichotomy (C.colourMass i) (C.colourMass j) with h|h|h
    · rw [abs_sub_comm, abs_of_nonneg (hstrict' j i h).1]
      exact (hstrict' j i h).2
    · simpa using hEqual i j h
    · rw [abs_of_nonneg (hstrict' i j h).1]
      exact (hstrict' i j h).2
  · intro x i j hij
    rw [hscale, hscale]
    exact mul_le_mul_of_nonneg_right (sub_nonneg.mp (hstrict' i j hij).1) (hu x)

/-- Common pairwise load bounds turn into row reserves on the set
uncovered by each colour, for any nonnegative family of vertex weights. -/
theorem uncovered_weight_lower (C : M.EdgeColoring k) (w : V → ℝ) (H : ℝ) (σ : ℕ)
    (hw : ∀ v, 0 ≤ w v) (hdegree : ∀ v, w v ≠ 0 → M.degree v ≤ σ)
    (i : Fin k) (hgap : ∀ j, WeightedRecolouring.load C w i -
      WeightedRecolouring.load C w j ≤ H) :
    (k : ℝ) * (∑ v ∈ univ.filter (fun v => (C.colourGraph i).degree v = 0), w v) ≥
      ((k : ℝ) - σ) * (∑ v, w v) - (k - 1 : ℕ) * H := by
  have htotal := load_le_average_add (WeightedRecolouring.load C w) i H hgap
  rw [Fintype.card_fin, sum_load] at htotal
  have hupper : (∑ v, w v * (M.degree v : ℝ)) ≤ (∑ v,w v) * (σ : ℝ) := by
    rw [sum_mul]
    apply sum_le_sum
    intro v _
    by_cases hz : w v = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdegree v hz) (hw v)
  have hcompl :
      (∑ v ∈ univ.filter (fun v => (C.colourGraph i).degree v = 0), w v) +
        WeightedRecolouring.load C w i = ∑ v, w v := by
    unfold WeightedRecolouring.load
    rw [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    have hp := C.colourGraph_degree_le_one i v
    by_cases hz : (C.colourGraph i).degree v = 0
    · simp [hz]
    · have ho : (C.colourGraph i).degree v = 1 := by omega
      simp [ho]
  nlinarith only [hupper, htotal, congrArg (fun z : ℝ => (k : ℝ) * z) hcompl]

end WeightedPaper
