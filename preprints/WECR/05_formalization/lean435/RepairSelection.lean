import PathPacking

namespace WeightedPaper.Repair
open Finset MeasureTheory

/-- Counting a path's resources in expectation. This allows repeated visits
within a walk because the input records distinct resources. -/
theorem sum_resource_probabilities {Ω R : Type*} [Fintype Ω] [Fintype R] [DecidableEq R]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (law : Measure Ω) [IsProbabilityMeasure law]
    (resources : Ω → Finset R) (L : ℝ) (length : ∀ z, ((resources z).card : ℝ) ≤ L) :
    ∑ r, law.real {z | r ∈ resources z} ≤ L := by
  classical
  have expand (r : R) : law.real {z | r ∈ resources z} =
      ∑ z, if r ∈ resources z then law.real {z} else 0 := by
    rw [← sum_filter, sum_measureReal_singleton]
    congr 1
    ext z
    simp
  simp_rw [expand]
  rw [sum_comm]
  calc
    _ = ∑ z, (resources z).card * law.real {z} := by
      apply sum_congr rfl
      intro z _
      simp [← sum_filter]
    _ ≤ ∑ z, L*law.real {z} := sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_right (length z) measureReal_nonneg
    _ = L := by rw [← mul_sum, sum_measureReal_singleton]; simp

/-- The two resource bounds of Lemma 8 imply the simultaneous selection
of reserve-copy-disjoint paths that never compete for a colored matched edge. -/
theorem select_repairs {Q R M : Type*} [Fintype Q] [LinearOrder Q] [Fintype R] [Fintype M]
    [DecidableEq R] [DecidableEq M] {Ω : Q → Type*} [∀ q, Fintype (Ω q)]
    [∀ q, MeasurableSpace (Ω q)] [∀ q, MeasurableSingletonClass (Ω q)]
    (law : ∀ q, Measure (Ω q)) [∀ q, IsProbabilityMeasure (law q)]
    (reserve : ∀ q, Ω q → Finset R) (old : ∀ q, Ω q → Finset M)
    (ℓ μR μM : ℝ) (hR : 0 ≤ μR) (hM : 0 ≤ μM)
    (lengthR : ∀ q z, ((reserve q z).card : ℝ) ≤ ℓ)
    (lengthM : ∀ q z, ((old q z).card : ℝ) ≤ ℓ-1)
    (loadR : ∀ r, ∑ q, (law q).real {z | r ∈ reserve q z} ≤ μR)
    (loadM : ∀ r, ∑ q, (law q).real {z | r ∈ old q z} ≤ μM)
    (budget : ℓ*μR+(ℓ-1)*μM ≤ 4/27) :
    ∃ ω : ∀ q, Ω q, ∀ i j, i ≠ j →
      Disjoint (reserve i (ω i)) (reserve j (ω j)) ∧ Disjoint (old i (ω i)) (old j (ω j)) := by
  let uses (q : Q) : R ⊕ M → Set (Ω q) :=
    Sum.elim (fun r => {z | r ∈ reserve q z}) (fun e => {z | e ∈ old q z})
  let cap : R ⊕ M → ℝ := Sum.elim (fun _ => μR) (fun _ => μM)
  have loads (r) : ∑ q, (law q).real (uses q r) ≤ cap r := by
    cases r with | inl r => exact loadR r | inr m => exact loadM m
  have hb (q) : ∑ r, (law q).real (uses q r)*cap r ≤ 4/27 := by
    rw [Fintype.sum_sum_type]
    simp only [uses,cap,Sum.elim_inl,Sum.elim_inr,← sum_mul]
    refine le_trans (add_le_add ?_ ?_) budget
    · exact mul_le_mul_of_nonneg_right (sum_resource_probabilities _ _ _ (lengthR q)) hR
    · exact mul_le_mul_of_nonneg_right (sum_resource_probabilities _ _ _ (lengthM q)) hM
  obtain ⟨ω,hw⟩ := paths_of_resource_loads law uses cap loads hb
  refine ⟨ω,fun i j h => ⟨disjoint_left.mpr fun {r} hi hj => ?_,
    disjoint_left.mpr fun {m} hi hj => ?_⟩⟩
  · exact hw i j h (.inl r) hi hj
  · exact hw i j h (.inr m) hi hj

end WeightedPaper.Repair
