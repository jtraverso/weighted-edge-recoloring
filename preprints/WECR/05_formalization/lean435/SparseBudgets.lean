import WalkKernel

namespace WeightedPaper.Repair
open Filter Real Asymptotics
open scoped Topology

/-- The uncovered-demand bound in rank three at δ = 1/4. -/
noncomputable def nibbleBound (d η z : ℝ) :=
  max ((η + d ^ (-(1/1800 : ℝ))) * z) (3 * d^(1/4 : ℝ) / (1-η))

theorem grid_error (d r : ℝ) (hd : 1 ≤ d) (hr : r ≤ √d) :
    (r+2)/d ≤ 3*d^(-(1/1800 : ℝ)) := by
  have pos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hs : 1 ≤ √d := by simpa using Real.sqrt_le_sqrt hd
  calc
    _ ≤ 3*√d/d := by apply div_le_div_of_nonneg_right _ pos.le; linarith
    _ = 3*d^(-(1/2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_one d, Real.rpow_one]
      congr 1
      conv_lhs => rhs; rw [← Real.rpow_one d]
      rw [← Real.rpow_sub pos]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hd (by norm_num)) (by norm_num)

theorem sparse_nibble_bound (d η : ℝ) (hd : 1 ≤ d) (he : η ≤ 1/2)
    (herr : η ≤ 3*d^(-(1/1800 : ℝ))) :
    nibbleBound d η d / d ≤ 6*d^(-(1/1800 : ℝ)) := by
  have pos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have ep := Real.rpow_pos_of_pos pos (-(1/1800 : ℝ))
  apply (div_le_iff₀ pos).2
  apply max_le
  · exact mul_le_mul_of_nonneg_right (by linarith) pos.le
  · apply (div_le_iff₀ (by linarith : 0 < 1-η)).2
    have powle : d^(1/4 : ℝ) ≤ d^(-(1/1800 : ℝ))*d := by
      rw [← Real.rpow_add_one pos.ne']
      apply Real.rpow_le_rpow_of_exponent_le hd
      norm_num
    nlinarith [mul_nonneg (mul_nonneg ep.le pos.le) (show 0 ≤ 1/2-η by linarith)]

/-- For k=d the two budgets in (P) are bounded by explicit multiples of
ℓ² d^(-1/1800), including the small-test term in the maximum. -/
theorem sparse_budget_bounds (d η ℓ : ℝ) (hd : 1 ≤ d) (he : η ≤ 1/2)
    (herr : η ≤ 3*d^(-(1/1800 : ℝ))) (hl : 2 ≤ ℓ) :
    let t := nibbleBound d η d
    let ρ := η+t/d
    3*(ℓ-1)*ρ ≤ 27*ℓ^2*d^(-(1/1800 : ℝ)) ∧
      6*ℓ*(2*t+(ℓ-2)*d*ρ)/d + 6*(ℓ-1)^2*ρ ≤ 180*ℓ^2*d^(-(1/1800 : ℝ)) := by
  dsimp only
  let ε := d^(-(1/1800 : ℝ))
  let t := nibbleBound d η d
  let ρ := η+t/d
  have ht : t/d ≤ 6*ε := sparse_nibble_bound d η hd he herr
  have hr : ρ ≤ 9*ε := by dsimp [ρ]; linarith
  have epos : 0 ≤ ε := Real.rpow_nonneg (by linarith) _
  have pos : 0 < d := by linarith
  have L : ℓ ≤ ℓ^2 := by nlinarith [mul_nonneg (show 0 ≤ ℓ by linarith) (show 0 ≤ ℓ-1 by linarith)]
  change 3*(ℓ-1)*ρ ≤ 27*ℓ^2*ε ∧ 6*ℓ*(2*t+(ℓ-2)*d*ρ)/d+6*(ℓ-1)^2*ρ ≤ 180*ℓ^2*ε
  constructor
  · calc
      _ ≤ 3*(ℓ-1)*(9*ε) := mul_le_mul_of_nonneg_left hr (by linarith)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right L epos]
  · have eq : 6*ℓ*(2*t+(ℓ-2)*d*ρ)/d = 6*ℓ*(2*(t/d)+(ℓ-2)*ρ) := by field_simp
    rw [eq]
    calc
      _ ≤ 6*ℓ*(2*(6*ε)+(ℓ-2)*(9*ε))+6*(ℓ-1)^2*(9*ε) := by gcongr <;> linarith
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ ℓ^2-1 by linarith) epos, mul_nonneg (show 0 ≤ ℓ by linarith) epos]

theorem logarithmic_repair_rate :
    Tendsto (fun d : ℝ => (Real.log d)^2 / d^(1/1800 : ℝ)) atTop (𝓝 0) := by
  simpa using (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s := 1/1800) (by norm_num)).tendsto_div_nhds_zero

end WeightedPaper.Repair
