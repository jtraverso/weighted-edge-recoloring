module

public import ResourceConflicts
public import MatchingRepair

@[expose] public section


namespace WeightedPaper.Repair
open Finset MeasureTheory ProbabilityTheory

variable {Q R : Type*} [Fintype Q] [LinearOrder Q] [Fintype R] {Ω : Q → Type*}
  [∀ q, Fintype (Ω q)] [∀ q, MeasurableSpace (Ω q)] [∀ q, MeasurableSingletonClass (Ω q)]

/-- Select paths with disjoint resource sets, directly from marginal use
in the individual request laws. Each unordered pair gets one bad event. -/
theorem paths_of_resource_loads (law : ∀ q, Measure (Ω q)) [∀ q, IsProbabilityMeasure (law q)]
    (uses : ∀ q, R → Set (Ω q)) (cap : R → ℝ)
    (load : ∀ r, ∑ q, (law q).real (uses q r) ≤ cap r)
    (budget : ∀ q, ∑ r, (law q).real (uses q r)*cap r ≤ 4/27) :
    ∃ ω : ∀ q, Ω q, ∀ i j, i ≠ j → ∀ r, ω i ∈ uses i r → ω j ∉ uses j r := by
  classical
  let Edge := {p : Q × Q // p.1 < p.2}
  let e := (Fintype.equivFin Edge).symm
  let l (i : Fin (Fintype.card Edge)) := (e i).val.1
  let r (i : Fin (Fintype.card Edge)) := (e i).val.2
  let bad (i j : Q) := (Measure.pi law).real {ω | ∃ z, ω i ∈ uses i z ∧ ω j ∈ uses j z}
  have sym (i j : Q) : bad i j = bad j i := by simp only [bad, and_comm]
  have dist (i) : l i < r i := (e i).prop
  have pair_inj (i j) (h : l i = l j) (h' : r i = r j) : i = j :=
    e.injective (Subtype.ext (Prod.ext h h'))
  have lemma_budget (q : Q) :
      ∑ i ∈ univ.filter (fun i => q = l i ∨ q = r i), bad (l i) (r i) ≤ 4/27 := by
    let S := univ.filter (fun i => q = l i ∨ q = r i)
    let other i := if q = l i then r i else l i
    have orient (i) (hi : i ∈ S) : (q = l i ∧ other i = r i) ∨ (q = r i ∧ other i = l i) := by
      by_cases h : q = l i
      · exact Or.inl ⟨h,if_pos h⟩
      · exact Or.inr ⟨(mem_filter.mp hi).2.resolve_left h,if_neg h⟩
    have inj : Set.InjOn other (↑S) := by
      intro i hi j hj eq
      rcases orient i hi with ⟨a,b⟩ | ⟨a,b⟩ <;> rcases orient j hj with ⟨c,d⟩ | ⟨c,d⟩
      · exact pair_inj i j (a.symm.trans c) (b.symm.trans (eq.trans d))
      · exfalso; have := dist i; have := dist j; grind
      · exfalso; have := dist i; have := dist j; grind
      · exact pair_inj i j (b.symm.trans (eq.trans d)) (a.symm.trans c)
    have notself : q ∉ S.image other := by
      intro h
      obtain ⟨i,hi,eq⟩ := mem_image.mp h
      rcases orient i hi with ⟨a,b⟩ | ⟨a,b⟩ <;> have := dist i <;> grind
    calc
      _ = ∑ i ∈ S, bad q (other i) := by
        apply sum_congr rfl
        intro i hi
        rcases orient i hi with ⟨a,b⟩ | ⟨a,b⟩
        · rw [a,b]
        · rw [a,b,sym]
      _ = ∑ j ∈ S.image other, bad q j := (sum_image inj).symm
      _ ≤ _ := incident_conflict_le law uses q _ notself cap fun z =>
        (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => measureReal_nonneg)).trans (load z)
      _ ≤ _ := budget q
  obtain ⟨ω, hω⟩ := select_without_pair_conflicts law l r
    (fun i a b => ∃ z, a ∈ uses (l i) z ∧ b ∈ uses (r i) z) lemma_budget
  have ordered (i j : Q) (h : i < j) : ¬ ∃ z, ω i ∈ uses i z ∧ ω j ∈ uses j z := by
    let pair : Edge := ⟨(i,j),h⟩
    obtain ⟨k,hk⟩ := e.surjective pair
    let avoid (p : Edge) := ¬ ∃ z, ω p.val.1 ∈ uses p.val.1 z ∧ ω p.val.2 ∈ uses p.val.2 z
    exact (congrArg avoid hk).mp (hω k)
  refine ⟨ω,fun i j h z hi hj => ?_⟩
  rcases lt_or_gt_of_ne h with h | h
  · exact ordered i j h ⟨z,hi,hj⟩
  · exact ordered j i h ⟨z,hj,hi⟩
end WeightedPaper.Repair
