module

public import WalkResources

@[expose] public section


namespace WeightedPaper.Repair
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathWeight_nonneg (K : Matrix V V ℝ) (hn : ∀ u v, 0 ≤ K u v) (x y : V) (zs : List V) :
    0 ≤ pathWeight K x zs y := by
  induction zs generalizing x with
  | nil => exact hn x y
  | cons z zs ih => exact mul_nonneg (hn x z) (ih z)

/-- Exact unnormalized marginal at the j-th intermediate slot of a bridge. -/
theorem slot_mass (K : Matrix V V ℝ) (x y : V) (bad : Finset V) (n : ℕ)
    (j : Fin (n+1)) :
    (∑ f : Fin (n+1) → V, if f j ∈ bad then pathWeight K x (List.ofFn f) y else 0) =
      ∑ z ∈ bad, (K^(j.val+1)) x z * (K^(n+1-j.val)) z y := by
  have cons (m : ℕ) (a z : V) (g : Fin m → V) :
      pathWeight K a (List.ofFn ((Fin.consEquiv (fun _ : Fin (m+1) => V)) (z,g))) y = K a z * pathWeight K z (List.ofFn g) y := by
    rw [List.ofFn_succ]; simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, pathWeight]
  induction n generalizing x with
  | zero =>
    have hj : j = 0 := by apply Fin.ext; omega
    subst j
    rw [← (Fin.consEquiv (fun _ : Fin 1 => V)).sum_comp, Fintype.sum_prod_type]
    simp [List.ofFn_succ, pathWeight, sum_filter]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+2) => V)).sum_comp, Fintype.sum_prod_type]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.consEquiv_apply, Fin.cons_zero, cons,
         Fin.val_zero, zero_add, Nat.sub_zero, pow_one]
      simp_rw [sum_ite_irrel, sum_const_zero, ← mul_sum, pathWeight_total, ← sum_filter]
      simp
    · simp only [Fin.consEquiv_apply, Fin.cons_succ, cons,
         Fin.val_succ, Nat.succ_sub_succ_eq_sub]
      simp_rw [← mul_ite_zero, ← mul_sum, ih]
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro z _
      rw [pow_succ' K (i.val+1), Matrix.mul_apply, sum_mul]
      exact sum_congr rfl fun a _ => by ring

/-- A uniform lower bound for the mass of actual admissible paths from x to y.
With 2h intermediate slots, every slot has a long segment on at least one side. -/
theorem admissible_endpoint_mass [Nonempty V] (K : Matrix V V ℝ)
    (hn : ∀ x y, 0 ≤ K x y) (row : ∀ x, ∑ y, K x y = 1)
    (col : ∀ y, ∑ x, K x y = 1) {σ ρ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (hρ : 0 ≤ ρ)
    (op : ∀ f : V → ℝ, ∑ x, f x = 0 → ∑ y, (advance K f y)^2 ≤ σ^2 * ∑ x, (f x)^2)
    (bad : Finset V) (forward : ∀ u, ∑ v ∈ bad, K u v ≤ ρ)
    (backward : ∀ v, ∑ u ∈ bad, K u v ≤ ρ)
    (h : ℕ) (hh : 0 < h) (mix : σ^h ≤ 1/(2*(Fintype.card V : ℝ)))
    (budget : 3*(2*h : ℕ)*ρ ≤ 1/2) (x y : V) :
    (K^(2*h+1)) x y / 2 ≤
      ∑ f ∈ (univ : Finset (Fin (2*h) → V)).filter (fun f => ∀ j, f j ∉ bad),
        pathWeight K x (List.ofFn f) y := by
  classical
  let c : ℝ := 1/(2*(Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have bound := long_segment_bounds K row col hσ hσ' op (n := 2*h+1) (by omega) mix x y
  obtain ⟨n, he⟩ : ∃ n, 2*h = n+1 := ⟨2*h-1, by omega⟩
  rw [he] at bound budget ⊢
  let w (f : Fin (n+1) → V) := pathWeight K x (List.ofFn f) y
  let rejects (j : Fin (n+1)) := univ.filter (fun f : Fin (n+1) → V => f j ∈ bad)
  have hj (j : Fin (n+1)) : ∑ f ∈ rejects j, w f ≤ 3*ρ*(∑ f, w f) := by
    dsimp [rejects, w]
    rw [sum_filter, slot_mass, pathWeight_total]
    let a := j.val
    have ha : a ≤ n := by dsimp [a]; omega
    change ∑ z ∈ bad, (K^(a+1)) x z * (K^(n+1-a)) z y ≤ _
    by_cases hl : h ≤ n+1-a
    · have e := missed_bridge_slot K hn row bad ρ c hc hρ forward a (n+1-a) x y
        (fun z _ => by simpa [c, div_eq_mul_inv] using (long_segment_bounds K row col hσ hσ' op hl mix z y).2)
      simpa only [show a+1+(n+1-a) = n+1+1 by omega] using
        e (by simpa only [show a+1+(n+1-a) = n+1+1 by omega] using bound.1)
    · have hl' : h ≤ a+1 := by omega
      have e := missed_bridge_slot K.transpose (fun u v => hn v u) col bad ρ c hc hρ backward
        (n-a) (a+1) y x (fun z _ => by
          rw [← Matrix.transpose_pow, Matrix.transpose_apply]
          simpa [c, div_eq_mul_inv] using (long_segment_bounds K row col hσ hσ' op hl' mix x z).2)
      simp only [← Matrix.transpose_pow, Matrix.transpose_apply,
        show n+1-a+(a+1) = n+1+1 by omega,
        show n-a+1 = n+1-a by omega] at e
      simpa only [mul_comm ((K^(n+1-a)) _ _)] using e bound.1
  have retain := retained_half w (fun f => pathWeight_nonneg K hn x y _) rejects ρ hj
    (by simpa using budget)
  have eqset : univ \ univ.biUnion rejects =
      univ.filter (fun f : Fin (n+1) → V => ∀ j, f j ∉ bad) := by
    ext f
    simp [rejects]
  simpa only [eqset, w, pathWeight_total] using retain

end WeightedPaper.Repair
