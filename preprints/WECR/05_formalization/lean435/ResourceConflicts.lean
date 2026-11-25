import ConflictSelection

namespace WeightedPaper.Repair
open Finset MeasureTheory ProbabilityTheory

variable {Q R : Type*} [Fintype Q] [DecidableEq Q] [Fintype R] {Ω : Q → Type*}
  [∀ q, Fintype (Ω q)] [∀ q, MeasurableSpace (Ω q)] [∀ q, MeasurableSingletonClass (Ω q)]

/-- Union bound for a collision of two sampled requests, expressed in
their individual laws. A resource can be a physical reserve copy or a
matched pair tagged with its color. -/
theorem pair_conflict_le (law : ∀ q, Measure (Ω q)) [∀ q, IsProbabilityMeasure (law q)]
    (uses : ∀ q, R → Set (Ω q)) (i j : Q) (hij : i ≠ j) :
    (Measure.pi law).real {ω | ∃ r, ω i ∈ uses i r ∧ ω j ∈ uses j r} ≤
      ∑ r, (law i).real (uses i r) * (law j).real (uses j r) := by
  classical
  let ev (q : Q) := fun ω : (∀ q, Ω q) => ω q
  let μ := Measure.pi law
  have ind : iIndepFun ev μ := iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have eq : {ω | ∃ r, ω i ∈ uses i r ∧ ω j ∈ uses j r} =
      ⋃ r, ev i ⁻¹' uses i r ∩ ev j ⁻¹' uses j r := by ext ω; simp [ev]
  rw [eq]
  apply (measureReal_iUnion_fintype_le _).trans_eq
  apply sum_congr rfl
  intro r _
  have hm := (ind.indepFun hij).measure_inter_preimage_eq_mul (uses i r) (uses j r)
    (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
  have hi := (measurePreserving_eval law i).measure_preimage
    (Set.toFinite (uses i r)).measurableSet.nullMeasurableSet
  have hj := (measurePreserving_eval law j).measure_preimage
    (Set.toFinite (uses j r)).measurableSet.nullMeasurableSet
  exact_mod_cast (show (μ (ev i ⁻¹' uses i r ∩ ev j ⁻¹' uses j r)).toReal = _ by
    rw [hm, ENNReal.toReal_mul]; simpa only [ev, μ, hi, hj, Measure.real])

/-- Sum the collision probabilities for one request against an arbitrary
set of other requests before applying the local lemma. -/
theorem incident_conflict_le (law : ∀ q, Measure (Ω q)) [∀ q, IsProbabilityMeasure (law q)]
    (uses : ∀ q, R → Set (Ω q)) (i : Q) (others : Finset Q) (hi : i ∉ others)
    (capacity : R → ℝ) (hc : ∀ r, ∑ j ∈ others, (law j).real (uses j r) ≤ capacity r) :
    (∑ j ∈ others, (Measure.pi law).real {ω | ∃ r, ω i ∈ uses i r ∧ ω j ∈ uses j r}) ≤
      ∑ r, (law i).real (uses i r) * capacity r := by
  calc
    _ ≤ ∑ j ∈ others, ∑ r, (law i).real (uses i r) * (law j).real (uses j r) :=
      sum_le_sum fun j hj => pair_conflict_le law uses i j (fun e => hi (e ▸ hj))
    _ = _ := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro r _
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (hc r) measureReal_nonneg

end WeightedPaper.Repair
