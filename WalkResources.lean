module

public import WalkKernel

@[expose] public section


namespace WeightedPaper.Repair
open Finset Matrix
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A step conditioned to end at a specified vertex. The prefix and suffix
may have length zero. Summing these masses gives the full endpoint mass. -/
noncomputable def stepMass (K : Matrix V V ℝ) (a b : ℕ) (x u v y : V) :=
  (K^a) x u * K u v * (K^b) v y

theorem sum_stepMass (K : Matrix V V ℝ) (a b : ℕ) (x y : V) :
    ∑ u, ∑ v, stepMass K a b x u v y = (K^(a+1+b)) x y := by
  rw [pow_add, pow_succ, Matrix.mul_apply]
  simp only [Matrix.mul_apply, sum_mul, stepMass]
  rw [sum_comm]

theorem stepMass_reverse (K : Matrix V V ℝ) (a b : ℕ) (x u v y : V) :
    stepMass K.transpose b a y v u x = stepMass K a b x u v y := by
  simp only [stepMass, ← transpose_pow, transpose_apply]
  ring

theorem power_nonneg (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y)
    (n : ℕ) (x y : V) : 0 ≤ (K^n) x y := by
  induction n generalizing x y with
  | zero => simp [Matrix.one_apply]; split <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact sum_nonneg fun z _ => mul_nonneg (ih x z) (hn z y)

/-- Aggregate starts in a fixed color. After their first step is dispersed,
the upper bound persists at every positive time. The starts may be indexed
by requests directly. The same statement applies to the reverse kernel. -/
theorem requests_spread {Q : Type*} [Fintype Q] (start : Q → V)
    (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y) (col : ∀ y, ∑ x, K x y = 1)
    (ρ : ℝ) (first : ∀ y, ∑ q, K (start q) y ≤ ρ) (a : ℕ) (u : V) :
    ∑ q, (K^(a+1)) (start q) u ≤ ρ := by
  induction a generalizing u with
  | zero => simpa using first u
  | succ a ih =>
    simp only [pow_succ K (a+1), Matrix.mul_apply]
    rw [sum_comm]
    simp_rw [← sum_mul]
    exact advance_bound K hn col (fun x => ih x) u

/-- The first-step estimate from the *distinct* starting endpoints and their
common reserve-neighbor budget. -/
theorem first_step_of_neighbors {Q : Type*} [Fintype Q] (start : Q ↪ V)
    (adj : V → V → Prop) [DecidableRel adj] (d ρ : ℝ) (hd : 0 < d) (v : V)
    (h : ((univ.image start).filter (fun u => adj u v)).card ≤ ρ*d) :
    (∑ q, if adj (start q) v then 1/d else 0) ≤ ρ := by
  classical
  have eqc : ((univ.image start).filter (fun u => adj u v)).card =
      (univ.filter (fun q => adj (start q) v)).card := by
    rw [filter_image, card_image_of_injective _ start.injective]
  rw [eqc] at h
  simp only [← sum_filter, sum_const, nsmul_eq_mul, ← div_eq_mul_one_div]
  exact (div_le_iff₀ hd).2 h

/-- If each slot rejects mass at most 3ρ under the endpoint law, the
intersection of the accepted slots retains at least half of its mass. -/
theorem retained_half {Ω J : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype J]
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (bad : J → Finset Ω) (ρ : ℝ)
    (slot : ∀ j, ∑ z ∈ bad j, w z ≤ 3*ρ*(∑ z, w z))
    (budget : 3*(Fintype.card J : ℝ)*ρ ≤ 1/2) :
    (∑ z, w z)/2 ≤ ∑ z ∈ univ \ univ.biUnion bad, w z := by
  classical
  have union_le (T : Finset J) : ∑ z ∈ T.biUnion bad, w z ≤ ∑ j ∈ T, ∑ z ∈ bad j, w z := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [biUnion_insert, sum_insert hi]
      have e := sum_union_inter (s₁ := bad i) (s₂ := S.biUnion bad) (f := w)
      have pos : 0 ≤ ∑ z ∈ bad i ∩ S.biUnion bad, w z := sum_nonneg fun z _ => hw z
      linarith
  have hunion := union_le univ
  have bounds := (sum_le_sum fun j (_ : j ∈ (univ : Finset J)) => slot j)
  have hu := hunion.trans bounds
  simp only [sum_const, card_univ, nsmul_eq_mul] at hu
  have hprod := mul_le_mul_of_nonneg_right budget (sum_nonneg (s := univ) fun z _ => hw z)
  have hsplit := sum_sdiff (s₁ := univ.biUnion bad) (s₂ := univ) (f := w) (subset_univ _)
  linarith only [hsplit, hu, hprod]

/-- Probability after both conditionings, summed over all requests, for
one fixed reserve edge at one fixed position. A long suffix is used here.
Reversal gives the long-prefix version. The retained mass and numerator
are unnormalized endpoint masses, so no independence assumption is needed. -/
theorem summed_step_use {Q : Type*} [Fintype Q] (K : Matrix V V ℝ)
    (hn : ∀ u v, 0 ≤ K u v) (start stop : Q → V) (a b : ℕ) (u v : V)
    (c d load : ℝ) (hc : 0 < c) (hd : 0 < d)
    (long : ∀ q, (K^b) v (stop q) ≤ 3*c)
    (spread : ∑ q, (K^a) (start q) u ≤ load) (edge : K u v ≤ 1/d)
    (keep hit : Q → ℝ) (accepted : ∀ q, c/2 ≤ keep q)
    (submass : ∀ q, hit q ≤ stepMass K a b (start q) u v (stop q)) :
    ∑ q, hit q / keep q ≤ 6*load/d := by
  have each (q : Q) : hit q / keep q ≤ (K^a) (start q) u * (6/d) := by
    have pre := power_nonneg K hn a (start q) u
    apply (div_le_iff₀ (by linarith [accepted q])).2
    calc
      hit q ≤ _ := submass q
      _ ≤ (K^a) (start q) u * (1/d) * (3*c) := by
        unfold stepMass
        exact mul_le_mul (mul_le_mul_of_nonneg_left edge pre) (long q)
          (power_nonneg K hn b v (stop q)) (by positivity)
      _ = ((K^a) (start q) u * (6/d)) * (c/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (accepted q) (by positivity)
  calc
    _ ≤ _ := sum_le_sum fun q _ => each q
    _ = (∑ q, (K^a) (start q) u) * (6/d) := by rw [sum_mul]
    _ ≤ load * (6/d) := mul_le_mul_of_nonneg_right spread (by positivity)
    _ = _ := by ring


theorem power_rows (K : Matrix V V ℝ) (row : ∀ x, ∑ y, K x y = 1)
    (n : ℕ) (x : V) : ∑ y, (K^n) x y = 1 := by
  induction n with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [sum_comm]
    simp_rw [← mul_sum, row, mul_one]; exact ih

/-- Before endpoint conditioning, any positive-length segment puts at most
ρ mass on the forbidden intermediate vertices if each row puts at most ρ there. -/
theorem missed_mass (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y) (row : ∀ x, ∑ y, K x y = 1)
    (bad : Finset V) (ρ : ℝ) (avoid : ∀ u, ∑ v ∈ bad, K u v ≤ ρ) (n : ℕ) (x : V) :
    ∑ v ∈ bad, (K^(n+1)) x v ≤ ρ := by
  simp only [pow_succ, Matrix.mul_apply]
  rw [sum_comm]
  simp_rw [← mul_sum]
  calc
    _ ≤ ∑ u, (K^n) x u * ρ := sum_le_sum fun u _ =>
      mul_le_mul_of_nonneg_left (avoid u) (power_nonneg K hn _ _ _)
    _ = ρ := by rw [← sum_mul, power_rows K row, one_mul]

/-- Unnormalized endpoint mass through a forbidden intermediate state.
Apply in the direction whose remaining segment is long. -/
theorem missed_bridge_slot (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y)
    (row : ∀ x, ∑ y, K x y = 1) (bad : Finset V) (ρ c : ℝ) (hc : 0 ≤ c)
    (hρ : 0 ≤ ρ) (avoid : ∀ u, ∑ v ∈ bad, K u v ≤ ρ)
    (n b : ℕ) (x y : V) (long : ∀ v ∈ bad, (K^b) v y ≤ 3*c)
    (endpoint : c ≤ (K^(n+1+b)) x y) :
    ∑ v ∈ bad, (K^(n+1)) x v * (K^b) v y ≤ 3*ρ*(K^(n+1+b)) x y := by
  calc
    _ ≤ ∑ v ∈ bad, (K^(n+1)) x v * (3*c) := sum_le_sum fun v hv =>
      mul_le_mul_of_nonneg_left (long v hv) (power_nonneg K hn _ _ _)
    _ = (∑ v ∈ bad, (K^(n+1)) x v) * (3*c) := by rw [sum_mul]
    _ ≤ ρ * (3*c) := mul_le_mul_of_nonneg_right (missed_mass K hn row bad ρ avoid n x) (by positivity)
    _ = (3*ρ)*c := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left endpoint (by positivity)

end WeightedPaper.Repair
