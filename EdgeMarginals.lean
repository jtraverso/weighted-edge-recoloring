module

public import AdmissibleBridge

@[expose] public section


namespace WeightedPaper.Repair
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unnormalized mass of a path with a specified transition at position a.
The paths have fixed endpoints, so the final edge can also be tested. -/
noncomputable def edgeWeight (K : Matrix V V ℝ) (u v : V) : ℕ → V → List V → V → ℝ
  | 0, x, [], y => if x = u ∧ y = v then K x y else 0
  | 0, x, z :: zs, y => if x = u ∧ z = v then pathWeight K x (z::zs) y else 0
  | _+1, _, [], _ => 0
  | a+1, x, z :: zs, y => K x z * edgeWeight K u v a z zs y

theorem edgeWeight_nonneg (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y) (u v : V)
    (a : ℕ) (x : V) (zs : List V) (y : V) : 0 ≤ edgeWeight K u v a x zs y := by
  induction a generalizing x zs with
  | zero =>
    cases zs <;> simp only [edgeWeight] <;> split
    all_goals first | exact hn _ _ | exact pathWeight_nonneg K hn _ _ _ | exact le_rfl
  | succ a ih => cases zs <;> simp only [edgeWeight]; exact le_rfl; exact mul_nonneg (hn _ _) (ih _ _)

/-- Summing over complete paths gives the prefix-edge-suffix formula even
at the first and last position. -/
theorem edge_marginal (K : Matrix V V ℝ) (u v x y : V) (a b : ℕ) :
    (∑ f : Fin (b+a) → V, edgeWeight K u v a x (List.ofFn f) y) = stepMass K a b x u v y := by
  have cons (n : ℕ) (z : V) (g : Fin n → V) :
      List.ofFn ((Fin.consEquiv (fun _ : Fin (n+1) => V)) (z,g)) = z :: List.ofFn g := by
    rw [List.ofFn_succ]; simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  induction a generalizing x with
  | zero =>
    cases b with
    | zero =>
      by_cases h : x = u <;> by_cases t : y = v <;> simp_all [edgeWeight, stepMass, Matrix.one_apply, eq_comm]
    | succ b =>
      simp only [Nat.add_zero]
      rw [← (Fin.consEquiv (fun _ : Fin (b+1) => V)).sum_comp, Fintype.sum_prod_type]
      simp only [cons, edgeWeight, pathWeight, stepMass, pow_zero, Matrix.one_apply]
      simp_rw [sum_ite_irrel, sum_const_zero, ← mul_sum, pathWeight_total]
      by_cases h : x = u <;> simp [h]
  | succ a ih =>
    change (∑ f : Fin (b+a+1) → V, edgeWeight K u v (a+1) x (List.ofFn f) y) = _
    rw [← (Fin.consEquiv (fun _ : Fin (b+a+1) => V)).sum_comp, Fintype.sum_prod_type]
    simp only [cons, edgeWeight]
    simp_rw [← mul_sum, ih]
    simp only [stepMass, pow_succ' K a, Matrix.mul_apply, sum_mul]
    apply sum_congr rfl
    intro z _
    ring

/-- Upper bound on the actual mass of a marked transition after restricting
to any collection of admissible paths. -/
theorem restricted_edge_marginal (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y)
    (u v x y : V) (a b : ℕ) (allowed : Finset (Fin (b+a) → V)) :
    ∑ f ∈ allowed, edgeWeight K u v a x (List.ofFn f) y ≤ stepMass K a b x u v y := by
  rw [← edge_marginal]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun f _ _ => edgeWeight_nonneg K hn _ _ _ _ _ _

/-- The matched edge at an intermediate slot is identified by its contracted
vertex. This is the one-slot counterpart of the reserve-edge estimate. -/
theorem summed_matched_slot {Q : Type*} [Fintype Q] (K : Matrix V V ℝ)
    (hn : ∀ u v, 0 ≤ K u v) (start stop : Q → V) (a b : ℕ) (z : V)
    (c ρ : ℝ) (hc : 0 < c)
    (long : ∀ q, (K^b) z (stop q) ≤ 3*c) (spread : ∑ q, (K^a) (start q) z ≤ ρ)
    (keep hit : Q → ℝ) (accepted : ∀ q, c/2 ≤ keep q)
    (submass : ∀ q, hit q ≤ (K^a) (start q) z * (K^b) z (stop q)) :
    ∑ q, hit q / keep q ≤ 6*ρ := by
  have each (q : Q) : hit q / keep q ≤ 6 * (K^a) (start q) z := by
    have pre := power_nonneg K hn a (start q) z
    apply (div_le_iff₀ (by linarith [accepted q])).2
    have H := (submass q).trans (mul_le_mul_of_nonneg_left (long q) pre)
    nlinarith [mul_le_mul_of_nonneg_left (accepted q) pre]
  exact (sum_le_sum fun q _ => each q).trans (by rw [← mul_sum]; linarith)

end WeightedPaper.Repair
