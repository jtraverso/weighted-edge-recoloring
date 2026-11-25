import WeightedPaper.Cut.GridFactorization

namespace WeightedPaper.Examples.Grid
open Finset
variable {q : ℕ}

/-- A nonzero mean-zero direction attains the norm bound in the manuscript. -/
theorem attained (hq : 2 ≤ q) :
    ∃ v : Ord q → ℝ, (∑ x,v x)=0 ∧ (∃ x,v x≠0) ∧
      ∀ x, applySupport v x=256*((q:ℝ)-1)*v x := by
  let i : Fin q := ⟨0,by omega⟩
  let j : Fin q := ⟨1,by omega⟩
  have hij : i≠j := by intro h; have := congrArg Fin.val h; change 0=1 at this; omega
  let f (h : Fin q) : ℝ := (if h=i then 1 else 0)-(if h=j then 1 else 0)
  have hf : (∑ h,f h)=0 := by simp [f,sum_sub_distrib]
  refine ⟨fun x => f x.1,?_,⟨(i,i,false,false,0),by simp [f,hij]⟩,row_eigenvector f hf⟩
  rw [sum_coords]
  simp only [sum_const,card_univ,card_copy,Fintype.card_fin,nsmul_eq_mul,← mul_sum,hf,mul_zero]

theorem degree_sqrt (hq : 1 ≤ q) : (degree q : ℝ) = 32*Real.sqrt (order q)-256 := by
  have h : (order q : ℝ)=(16*(q:ℝ))^2 := by simp [order]; ring
  rw [h,Real.sqrt_sq (by positivity)]
  simp only [degree,Nat.cast_mul,Nat.cast_sub (by omega : 1≤2*q),Nat.cast_one,Nat.cast_ofNat]
  ring

/-- For any integer C, once q > 2C the ordinary density is below 1/C
when C is positive. The inequality uses no division. -/
theorem density_bound (C : ℕ) (hq : 2*C<q) : C*degree q < order q := by
  have h := Nat.mul_lt_mul_of_pos_right hq (by omega : 0<q)
  have hh := Nat.mul_le_mul_left C (Nat.sub_le (2*q) 1)
  unfold degree order
  nlinarith

end WeightedPaper.Examples.Grid
