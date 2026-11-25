import WeightedPaper.Cut.RectFactorization
import WeightedPaper.Cut.RectSeparation

namespace WeightedPaper.Examples.RectGrid
open Finset
open scoped Classical
variable {q : ℕ}

/-- The norm bound is attained by a mean-zero column profile. -/
theorem attained (hq : 2 ≤ q) : ∃ v : Ord q → ℝ,
    (∑ y,v y) = 0 ∧ (∑ y,(v y)^2) > 0 ∧
    ∀ x, applySupport v x = 256*(2*(q:ℝ)-1)*v x := by
  let j₀ : Fin q := ⟨0,by omega⟩
  let j₁ : Fin q := ⟨1,by omega⟩
  have hNe : j₀ ≠ j₁ := by
    intro h
    have he := congrArg Fin.val h
    change (0 : ℕ) = 1 at he
    omega
  let f : Fin q → ℝ := fun j => basis j₀ j - basis j₁ j
  have hF : ∑ j, f j = 0 := by simp [f,basis,sum_sub_distrib]
  let v : Ord q → ℝ := fun x => f x.2.1
  refine ⟨v,?_,?_,column_eigenvector f hF⟩
  · rw [sum_coords]
    simp only [v,sum_const,nsmul_eq_mul,card_univ,card_copy]
    simp only [← mul_sum,hF,mul_zero,sum_const_zero]
  · let x : Ord q := ((0,j₀),j₀,false,false,0)
    have hX : v x = 1 := by simp [v,x,f,basis,hNe]
    exact (show 0 < (v x)^2 by simp [hX]).trans_le
      (single_le_sum (f:=fun y => (v y)^2) (fun _ _ => sq_nonneg _) (mem_univ x))

/-- Even allowing arbitrary palette and matching budgets, the old
variational ratio 1/2 cannot hold on this support. -/
theorem not_old_spectral (hq : 49 ≤ q) (a k : ℕ) :
    ¬ Nonempty (SpectralCut ((host q).cap false true) (exSet (Row q) (Ord q) false)
      (exSet (Row q) (Ord q) true) a k) := by
  rintro ⟨H⟩
  obtain ⟨v,hV,hE,hEig⟩ := attained (by omega : 2 ≤ q)
  let u (b : Bool) : half (Row q) (Ord q) b → ℝ := fun x => x.val.2.elim (fun _ => 0) v
  let j : Fin q := ⟨0,by omega⟩
  let x : Ord q := ((0,j),j,false,false,0)
  have hD := H.leftDegree (ordEmb false x) (ordEmb_not_mem_exSet false x)
  have hCount := ((host q).ordinaryNeighbours_compl Bool.false_ne_true x).trans (support_degree x)
  simp only [ordinary_complement] at hD hCount
  have hDegree : H.d = degree q := hD.symm.trans hCount
  have hZero (b : Bool) (de : DecidableEq (half (Row q) (Ord q) b)) :
      (∑ x ∈ @compl _ (@BooleanAlgebra.toCompl _ (@Finset.booleanAlgebra _ _ de))
        (exSet (Row q) (Ord q) b), u b x) = 0 := by
    rw [ordinary_complement b de,ordSet,sum_map]
    exact hV
  have hBad := H.spectral (u false) (u true) (hZero false _) (hZero true _)
  simp only [ordinary_complement,ordSet,sum_map,incidence,Host.capOrd _ Bool.false_ne_true] at hBad
  change 4*(∑ x,v x*(∑ y,v y*(if 0 < ordinary x y then 1 else 0)))^2 ≤
    (H.d:ℝ)^2*(∑ x,(v x)^2)*(∑ y,(v y)^2) at hBad
  simp only [support_iff] at hBad
  change 4*(∑ x,v x*applySupport v x)^2 ≤ _ at hBad
  simp_rw [hEig] at hBad
  have hDot : (∑ x, v x*(256*(2*(q:ℝ)-1)*v x)) =
      256*(2*(q:ℝ)-1)*(∑ x,(v x)^2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  rw [hDot,hDegree] at hBad
  have hRatio : (degree q : ℝ) < 2*(256*(2*(q:ℝ)-1)) := by
    simp only [degree,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (by omega : 1 ≤ 3*q),Nat.cast_one]
    have hq' : (49:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hPos : 0 ≤ (degree q : ℝ) := Nat.cast_nonneg _
  have hStrict := mul_lt_mul_of_pos_right hRatio hE
  have hNonneg := mul_nonneg hPos hE.le
  have hSq := sq_lt_sq' (show -(2*(256*(2*(q:ℝ)-1))*∑ y,(v y)^2) <
      (degree q:ℝ)*∑ y,(v y)^2 by linarith only [hStrict,hNonneg]) hStrict
  nlinarith only [hSq,hBad]

/-- This spectral ratio is also above the constant using the two uniform
estimates from the audit, represented without square roots. -/
theorem ratio_above_uniform (hq : 49 ≤ q) :
    25 * (256 * (3*(q:ℝ)-1))^2 < 65 * (256 * (2*(q:ℝ)-1))^2 := by
  have hq' : (49:ℝ) ≤ q := by exact_mod_cast hq
  nlinarith [sq_nonneg ((q:ℝ)-49)]

end WeightedPaper.Examples.RectGrid

#print axioms WeightedPaper.Examples.RectGrid.attained
#print axioms WeightedPaper.Examples.RectGrid.not_old_spectral
#print axioms WeightedPaper.Examples.RectGrid.ratio_above_uniform
