import SparseBudgets

namespace WeightedPaper.Repair
open Real Filter
open scoped Topology

/-- Choose a concrete mixing length for a normalized singular gap at most 1/2. -/
theorem choose_mixing_length (N d : ℝ) (hN : 1 ≤ N) (hd : 1 ≤ Real.log d)
    (pos : 0 < d) (scale : N ≤ d^2) :
    ∃ h : ℕ, 0 < h ∧ (1/2 : ℝ)^h ≤ 1/(2*N) ∧
      (2*h+1 : ℝ) ≤ (5 + 4/Real.log 2)*Real.log d := by
  let L := Real.log (2*N) / Real.log 2
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have lN : 0 < Real.log (2*N) := Real.log_pos (by linarith)
  have lpos : 0 < L := div_pos lN l2
  let h := ⌈L⌉₊
  have low : L ≤ (h : ℝ) := Nat.le_ceil _
  have high : (h : ℝ) < L+1 := Nat.ceil_lt_add_one lpos.le
  have hpos : 0 < h := by
    by_contra! hh
    have hz : h = 0 := by omega
    rw [hz, Nat.cast_zero] at low
    linarith
  refine ⟨h, hpos, ?_, ?_⟩
  · have hl := (div_le_iff₀ l2).mp low
    have powbound : 2*N ≤ (2:ℝ)^h := (Real.log_le_log_iff (by linarith) (by positivity)).mp
      (by rwa [Real.log_pow])
    rw [one_div_pow]
    exact one_div_le_one_div_of_le (by linarith) powbound
  · have hlog := Real.log_le_log (by linarith : 0 < N) scale
    rw [Real.log_pow] at hlog
    norm_num at hlog
    have hhigh : L ≤ 1 + 2*Real.log d/Real.log 2 := by
      dsimp [L]
      rw [Real.log_mul (by norm_num) (by linarith)]
      apply (div_le_iff₀ l2).2
      field_simp
      nlinarith
    have h1 : 2*(h:ℝ)+1 ≤ 5+4*Real.log d/Real.log 2 := by
      rw [show 4*Real.log d/Real.log 2 = 2*(2*Real.log d/Real.log 2) by ring]
      linarith
    refine h1.trans ?_
    rw [add_mul]
    linarith [show (4/Real.log 2)*Real.log d = 4*Real.log d/Real.log 2 by ring]

/-- For all sufficiently large degrees both numerical budgets (P) hold,
uniformly over N ≤ d² and r ≤ √d, with k = Δ = d and η = β = (r+2)/d. -/
theorem grid_budgets_eventually :
    ∀ᶠ d : ℝ in atTop, ∀ N r : ℝ, 1 ≤ N → N ≤ d^2 → 0 ≤ r → r ≤ √d →
    ∃ h : ℕ, 0 < h ∧ (1/2 : ℝ)^h ≤ 1/(2*N) ∧
      let ℓ : ℝ := 2*h+1
      let η := (r+2)/d
      let t := nibbleBound d η d
      let ρ := η+t/d
      3*(ℓ-1)*ρ ≤ 1/2 ∧ 6*ℓ*(2*t+(ℓ-2)*d*ρ)/d+6*(ℓ-1)^2*ρ ≤ 4/27 := by
  let C := 5+4/Real.log 2
  have cpos : 0 < C := by dsimp [C]; positivity
  have lim := logarithmic_repair_rate.const_mul (180*C^2)
  rw [mul_zero] at lim
  filter_upwards [lim.eventually_le_const (show (0:ℝ) < 4/27 by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (64:ℝ)] with d hsmall hlog hd
  intro N r hN hscale hr hroot
  have pos : 0 < d := by linarith
  have hd1 : 1 ≤ d := by linarith
  obtain ⟨h,hh,mix,hlen⟩ := choose_mixing_length N d hN hlog pos hscale
  refine ⟨h,hh,mix,?_⟩
  have dsq := Real.sq_sqrt pos.le
  have hs := Real.sqrt_nonneg d
  have herr : (r+2)/d ≤ 1/2 := (div_le_iff₀ pos).2 (by nlinarith [sq_nonneg (√d-2)])
  let ℓ : ℝ := 2*h+1
  have hl : 2 ≤ ℓ := by
    dsimp [ℓ]
    have : (1:ℝ) ≤ h := by exact_mod_cast hh
    linarith
  obtain ⟨b1,b2⟩ := sparse_budget_bounds d ((r+2)/d) ℓ hd1 herr (grid_error d r hd1 hroot) hl
  have sqle : ℓ^2 ≤ (C*Real.log d)^2 := pow_le_pow_left₀ (by linarith) hlen 2
  have ep := Real.rpow_nonneg pos.le (-(1/1800 : ℝ))
  have upper : 180*ℓ^2*d^(-(1/1800 : ℝ)) ≤ 4/27 := by
    calc
      _ ≤ 180*(C*Real.log d)^2*d^(-(1/1800 : ℝ)) := by gcongr
      _ = (180*C^2)*((Real.log d)^2/d^(1/1800 : ℝ)) := by rw [Real.rpow_neg pos.le]; ring
      _ ≤ _ := hsmall
  exact ⟨b1.trans (by nlinarith [mul_nonneg (sq_nonneg ℓ) ep]), b2.trans upper⟩

/-- Substitute the actual grid parameters. The assertion is eventual in q
and hence also applies along the even subsequence used for the construction. -/
theorem grid_parameters_pass (b : ℕ) (hb : 0 < b) :
    ∀ᶠ q : ℕ in atTop,
      let N : ℝ := (b : ℝ)*q^2
      let d : ℝ := b*(2*(q:ℝ)-1)
      let σ := ((q:ℝ)-1)/(2*q-1)
      ∃ h : ℕ, 0 < h ∧ σ^h ≤ 1/(2*N) ∧
        let ℓ : ℝ := 2*h+1
        let η := ((Nat.sqrt q : ℝ)+2)/d
        let t := nibbleBound d η d
        let ρ := η+t/d
        3*(ℓ-1)*ρ ≤ 1/2 ∧ 6*ℓ*(2*t+(ℓ-2)*d*ρ)/d+6*(ℓ-1)^2*ρ ≤ 4/27 := by
  have big : Tendsto (fun q : ℕ => (b:ℝ)*(2*(q:ℝ)-1)) atTop atTop := by
    refine tendsto_atTop_mono' (f₁ := fun q : ℕ => (q:ℝ)) atTop ?_ tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (1:ℕ)] with q hq
    have Q : (1:ℝ) ≤ q := by exact_mod_cast hq
    have B : (1:ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [mul_nonneg (sub_nonneg.mpr B) (show 0 ≤ 2*(q:ℝ)-1 by linarith)]
  filter_upwards [big.eventually grid_budgets_eventually, eventually_ge_atTop (1:ℕ)] with q good hq
  have Q : (1:ℝ) ≤ q := by exact_mod_cast hq
  have B : (1:ℝ) ≤ b := by exact_mod_cast hb
  let d : ℝ := b*(2*(q:ℝ)-1)
  have D : (b:ℝ)*q ≤ d := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have qd : (q:ℝ) ≤ d := (by simpa using mul_le_mul_of_nonneg_right B (Nat.cast_nonneg q) : (q:ℝ) ≤ b*q).trans D
  have scale : (b:ℝ)*q^2 ≤ d^2 := by
    calc
      _ ≤ ((b:ℝ)*q)^2 := by nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg b) (sub_nonneg.mpr B)) (sq_nonneg (q:ℝ))]
      _ ≤ d^2 := pow_le_pow_left₀ (by positivity) D _
  have root : (Nat.sqrt q : ℝ) ≤ √d := by
    apply (Real.le_sqrt (by positivity) (by linarith)).2
    have : (Nat.sqrt q : ℝ)*(Nat.sqrt q : ℝ) ≤ q := by exact_mod_cast Nat.sqrt_le q
    nlinarith
  have npos : (1:ℝ) ≤ (b:ℝ)*q^2 := one_le_mul_of_one_le_of_one_le B (one_le_pow₀ Q)
  obtain ⟨h,hh,mix,budgets⟩ := good _ _ npos scale (Nat.cast_nonneg _) root
  refine ⟨h,hh,le_trans (pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) ?_ h) mix,budgets⟩
  apply (div_le_iff₀ (by linarith)).2
  linarith

end WeightedPaper.Repair
