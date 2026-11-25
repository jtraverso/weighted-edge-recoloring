module

public import ResourceTotals
public import BridgeLaw

@[expose] public section


namespace WeightedPaper.Repair
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def arcs (x : V) : List V → V → List (V × V)
  | [], y => [(x,y)]
  | z :: zs, y => (x,z) :: arcs z zs y

theorem edgeWeight_length_union (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y)
    (x u v y : V) (zs : List V) :
    (if (u,v) ∈ arcs x zs y then pathWeight K x zs y else 0) ≤
      ∑ j ∈ range (zs.length+1), edgeWeight K u v j x zs y := by
  induction zs generalizing x with
  | nil =>
    simp only [arcs,List.mem_singleton, List.length_nil, zero_add, sum_range_one,edgeWeight,pathWeight]
    by_cases e : x=u ∧ y=v
    · obtain ⟨rfl,rfl⟩ := e; simp
    · simp [e, show (u,v) ≠ (x,y) by rintro h; cases h; exact e ⟨rfl,rfl⟩]
  | cons z zs ih =>
    simp only [arcs, List.mem_cons, List.length_cons]
    rw [sum_range_succ']
    simp only [edgeWeight, ← mul_sum]
    by_cases he : x = u ∧ z = v
    · obtain ⟨rfl,rfl⟩ := he
      simp only [true_and, ite_true, true_or]
      linarith [mul_nonneg (hn x z) (sum_nonneg (s := range (zs.length+1))
        fun j _ => edgeWeight_nonneg K hn x z j z zs y)]
    · have pair : (u,v) ≠ (x,z) := by rintro h; cases h; exact he ⟨rfl,rfl⟩
      simp only [pair, false_or, he, ite_false, pathWeight, ← mul_ite_zero, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (ih z) (hn x z)

/-- Probability that a retained bridge uses the fixed directed reserve edge
at least once, bounded by its unconditioned endpoint marginals divided by
the retained endpoint mass. The same arc may recur within a sample. -/
theorem reserve_occupancy (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y)
    (x u v y : V) (n : ℕ) (allowed : Finset (Fin n → V))
    (mass : ℝ) (pos : 0 < mass) :
    (∑ f ∈ allowed, if (u,v) ∈ arcs x (List.ofFn f) y then pathWeight K x (List.ofFn f) y else 0)/mass ≤
      ∑ j ∈ range (n+1), stepMass K j (n-j) x u v y /mass := by
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ pos.le
  calc
    _ ≤ ∑ f ∈ allowed, ∑ j ∈ range (n+1), edgeWeight K u v j x (List.ofFn f) y :=
      sum_le_sum fun f _ => by simpa using edgeWeight_length_union K hn x u v y (List.ofFn f)
    _ = _ := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      have jn : j ≤ n := by simpa using hj
      suffices aux : ∀ b n, n = b+j → ∀ A : Finset (Fin n → V),
          ∑ f ∈ A, edgeWeight K u v j x (List.ofFn f) y ≤ stepMass K j b x u v y by
        exact aux (n-j) n (by omega) allowed
      intro b n eq
      subst n
      exact restricted_edge_marginal K hn u v x y j b

/-- Probability of visiting a matched vertex at least once. The union over
intermediate slots accounts for repetitions without assuming a simple path. -/
theorem matched_occupancy (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y)
    (x z y : V) (n : ℕ) (allowed : Finset (Fin (n+1) → V)) (mass : ℝ) (pos : 0 < mass) :
    (∑ f ∈ allowed, if (∃ j, f j = z) then pathWeight K x (List.ofFn f) y else 0)/mass ≤
      ∑ j : Fin (n+1), (K^(j.val+1)) x z * (K^(n+1-j.val)) z y /mass := by
  classical
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ pos.le
  let w (f : Fin (n+1) → V) := pathWeight K x (List.ofFn f) y
  have wn f : 0 ≤ w f := pathWeight_nonneg K hn _ _ _
  have nonneg (j : Fin (n+1)) f : 0 ≤ (if f j = z then w f else 0) := by split <;> simp [wn]
  calc
    _ ≤ ∑ f ∈ allowed, ∑ j, if f j = z then w f else 0 := by
      apply sum_le_sum
      intro f _
      by_cases h : ∃ j, f j=z
      · obtain ⟨j,hj⟩ := h
        simpa only [ite_eq_left (show ∃ i, f i=z from ⟨j,hj⟩),ite_eq_left hj] using
          (single_le_sum (f := fun j => if f j=z then w f else 0)
            (fun i _ => nonneg i f) (mem_univ j))
      · rw [ite_eq_right h]; exact sum_nonneg fun i _ => nonneg i f
    _ = _ := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      refine (sum_le_sum_of_subset_of_nonneg (subset_univ allowed) (fun f _ _ => nonneg j f)).trans_eq ?_
      simpa [w] using slot_mass K x y {z} n j

/-- Apply the normalization law to a physical-use event. Summing over the
positive support and then including the zero-weight samples leaves its mass
unchanged. -/
theorem restricted_event_mass {Ω : Type*} [DecidableEq Ω] (A : Finset Ω)
    (w : Ω → ℝ) (wn : ∀ x, 0 ≤ w x) (event : Ω → Prop) [DecidablePred event] :
    let good := A.filter (fun f => 0 < w f)
    ∀ (p : PMF good), (∀ S : Finset good,
      (∑ f ∈ S, (p f).toReal) = (∑ f ∈ S, w f.val)/(∑ f ∈ A, w f)) →
      (∑ f : good, if event f.val then (p f).toReal else 0) =
        (∑ f ∈ A, if event f then w f else 0)/(∑ f ∈ A, w f) := by
  intro good p law
  rw [← sum_filter, law, sum_filter]
  congr 1
  change (∑ f ∈ good.attach, (fun a => if event a then w a else 0) f.val) = _
  rw [sum_attach good (fun a => if event a then w a else 0)]
  apply sum_subset (filter_subset _ _)
  intro f fa fg
  have hz : w f = 0 := le_antisymm (le_of_not_gt (fun h => fg (mem_filter.mpr ⟨fa,h⟩))) (wn f)
  simp [hz]

/-- Across all colors the first transition has an atom at its physical
starting vertex. Its total cost is proportional to the number of requests
there. Reversal applies the same bound at the terminal end. -/
theorem endpoint_resource_use {Q : Type*} [Fintype Q] (endpoint : Q → Prop)
    [DecidablePred endpoint] (hit keep : Q → ℝ) (c d t : ℝ) (hc : 0 < c)
    (hd : 0 < d) (accepted : ∀ q, c/2 ≤ keep q)
    (one : ∀ q, hit q ≤ if endpoint q then 3*c/d else 0)
    (count : ((univ.filter endpoint).card : ℝ) ≤ t) :
    ∑ q, hit q / keep q ≤ 6*t/d := by
  calc
    _ ≤ ∑ q, if endpoint q then 6/d else 0 := by
      apply sum_le_sum
      intro q _
      apply (div_le_iff₀ (by linarith [accepted q])).2
      by_cases e : endpoint q
      · simp only [e, ite_true]
        calc
          _ ≤ 3*c/d := by simpa [e] using one q
          _ = (6/d)*(c/2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (accepted q) (by positivity)
      · simpa [e] using one q
    _ = ((univ.filter endpoint).card : ℝ)*(6/d) := by
      rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      calc
        _ ≤ t*(6/d) := mul_le_mul_of_nonneg_right count (by positivity)
        _ = _ := by ring

end WeightedPaper.Repair
