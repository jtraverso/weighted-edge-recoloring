import WeightedPaper.Cut.Mixing

namespace WeightedPaper

/-- The deletion budget and the Hall size deficit share the same allowance.
Keeping their dependence proves the criterion at spectral ratio 3/4. -/
theorem spectral_deficit_impossible_three_fourths {N d h p s t e : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hdN : d ≤ N)
    (hh : 0 ≤ h) (hp : 0 ≤ p) (hcost : 8 * (h + p) ≤ d)
    (hs : d - h - p < s) (ht : d - h - p < t) (hsum : N - h < s + t)
    (hspent : e ≤ p * min s t)
    (hmix : 16 * (N * e - d * s * t)^2 ≤ 9 * d^2 * s * t * ((N-s)*(N-t))) : False := by
  let u := 8 * p / d
  have hud : u * d = 8 * p := div_mul_cancel₀ _ hd.ne'
  have hu : 0 ≤ u := div_nonneg (by positivity) hd.le
  have hu₁ : u ≤ 1 := (div_le_iff₀ hd).mpr (by linarith)
  have hNu : 8 * h ≤ (1-u) * N := by
    have h₁ : 8 * h ≤ (1-u) * d := by nlinarith only [hcost,hud]
    exact h₁.trans (mul_le_mul_of_nonneg_left hdN (by linarith))
  let b := 7 + u
  have hb : 0 < b := by dsimp [b]; linarith
  have hMax : b * N < 16 * max s t := by
    have h := add_le_add (le_max_left s t) (le_max_right s t)
    dsimp [b]
    nlinarith only [h,hNu,hsum]
  have hMin : 7*d < 8*min s t := by
    rcases le_total s t with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hl : 0 < min s t := by linarith
  have hst : min s t * max s t = s*t := min_mul_max _ _
  have hA : 0 < s*t := mul_pos (by linarith) (by linarith)
  have hMain : 0 < d * (s*t) := mul_pos hd hA
  have hProd : 7 * b * (d*N) ≤ 128*(s*t) := by
    have h₁ := mul_le_mul_of_nonneg_right hMax.le (show 0 ≤ 7*d by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hMin.le
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) ((show 0 ≤ s by linarith).trans (le_max_left s t)))
    nlinarith only [h₁,h₂,hst]
  have hRatio : 7*b*((N-s)*(N-t)) ≤ (65-9*u)*(s*t) := by
    have hH : 8*h ≤ (1-u)*d := by nlinarith only [hcost,hud]
    have h₁ := mul_le_mul_of_nonneg_right (show N-s-t ≤ h by linarith) (show 0 ≤ 7*b*N by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hH (show 0 ≤ 7*b*N by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hProd (show 0 ≤ 1-u by linarith)
    nlinarith only [h₁,h₂,h₃,show b = 7+u from rfl]
  have hUpper : b*(N*e) ≤ 2*u*(d*(s*t)) := by
    have h₁ := mul_le_mul_of_nonneg_left hspent (show 0 ≤ b*N by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hMax.le (show 0 ≤ p*min s t by positivity)
    have h₃ : u*d*(s*t) = 8*p*(min s t * max s t) := by rw [←hst,←mul_assoc, hud]; ring
    nlinarith only [h₁,h₂,h₃]
  have hSharp (hp' : 0 < p) : b*(N*e) < 2*u*(d*(s*t)) := by
    have h₁ := mul_le_mul_of_nonneg_left hspent (show 0 ≤ b*N by positivity)
    have h₂ := mul_lt_mul_of_pos_right hMax (mul_pos hp' hl)
    have h₃ : u*d*(s*t) = 8*p*(min s t * max s t) := by rw [←hst,←mul_assoc, hud]; ring
    nlinarith only [h₁,h₂,h₃]
  have hGap : (7-u)*(d*(s*t)) ≤ b*(d*(s*t)-N*e) := by
    nlinarith only [hUpper,show b = 7+u from rfl,
      congrArg (fun z : ℝ => z*(d*(s*t))) (show b = 7+u from rfl)]
  have hGap₀ : 0 ≤ (7-u)*(d*(s*t)) :=
    mul_nonneg (by linarith) hMain.le
  have hSq := (sq_le_sq' (by linarith [hGap,hGap₀] : -(b*(d*(s*t)-N*e)) ≤ (7-u)*(d*(s*t))) hGap)
  have hPoly : 112*(7-u)^2 - 9*b*(65-9*u) = (1-u)*(1393-193*u) := by dsimp [b]; ring
  have hMixScale := mul_le_mul_of_nonneg_right hmix (show 0 ≤ 7*b^2 by positivity)
  have hRatioScale := mul_le_mul_of_nonneg_right hRatio (show 0 ≤ 9*b*d^2*(s*t) by positivity)
  have hMix' : 112*(b*(d*(s*t)-N*e))^2 ≤ 9*b*(65-9*u)*(d*(s*t))^2 := by
    nlinarith only [hMixScale,hRatioScale]
  by_cases huLt : u < 1
  · have hPoly' : 9*b*(65-9*u) < 112*(7-u)^2 := by
      linarith only [hPoly, mul_pos (sub_pos.mpr huLt) (show 0 < 1393-193*u by linarith)]
    have hn := mul_lt_mul_of_pos_right hPoly' (sq_pos_of_pos hMain)
    nlinarith only [hSq,hMix',hn]
  · have huEq : u = 1 := by linarith
    have hp' : 0 < p := by rw [huEq,one_mul] at hud; linarith
    have hGap' : (7-u)*(d*(s*t)) < b*(d*(s*t)-N*e) := by
      nlinarith only [hSharp hp',congrArg (fun z : ℝ => z*(d*(s*t))) (show b = 7+u from rfl)]
    have hSq' := sq_lt_sq' (show -(b*(d*(s*t)-N*e)) < (7-u)*(d*(s*t)) by linarith) hGap'
    rw [huEq,sub_self,zero_mul,sub_eq_zero] at hPoly
    have hPoly' := congrArg (fun z : ℝ => z*(d*(s*t))^2) hPoly
    rw [huEq] at hSq' hMix'
    nlinarith only [hSq',hMix',hPoly']

end WeightedPaper

#print axioms WeightedPaper.spectral_deficit_impossible_three_fourths
