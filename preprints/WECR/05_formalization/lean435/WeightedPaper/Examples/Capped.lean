import WeightedPaper.Examples.Matrices

namespace WeightedPaper.Examples

open Finset
open scoped Classical

def cappedCopies {r : ℕ} (p : Fin r) (y : Quad (Fin r)) : ℕ :=
  (if y = (true,false,p) then 4*r else 0) + (if y.1 = false then 1 else 0)

def cappedWeight {r : ℕ} (p : Fin r) (y : Quad (Fin r)) : ℝ :=
  (if y = (true,false,p) then 1 else 0) + (if y.1 = false then 1 else 0)

def cappedHost {r : ℕ} (p : Fin r) : Host (Fin 2) (Quad (Fin r)) where
  internal := quadInternal
  internal_symm := quadInternal_symm
  internal_diag := fun _ => quadInternal_zero _ _ rfl
  ordinary := diagExtra (fun y => 2*(4*r-cappedCopies p y))
  ordinary_symm := diagExtra_symm _
  incidence := fun _ => cappedCopies p
  exceptional := fun x y => if x=y then 6*r+2 else 0
  exceptional_symm := fun _ _ => if_congr eq_comm rfl rfl

private theorem sum_first_half {r : ℕ} {S : Type*} [AddCommMonoid S] (s : S) :
    (∑ y : Quad (Fin r), if y.1 = false then s else 0) = (2*r) • s := by
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [Prod.fst,Bool.true_eq_false,if_false,if_true,sum_const_zero,zero_add,add_zero,
    sum_const,card_univ,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]

theorem cappedCopies_sum {r : ℕ} (p : Fin r) : (∑ y,cappedCopies p y) = 6*r := by
  unfold cappedCopies
  rw [sum_add_distrib,sum_first_half]
  simp only [Finset.sum_ite_eq',mem_univ,if_true,nsmul_eq_mul,Nat.cast_id,mul_one]
  ring

theorem cappedWeight_sum {r : ℕ} (p : Fin r) : (∑ y,cappedWeight p y) = 2*(r : ℝ)+1 := by
  unfold cappedWeight
  rw [sum_add_distrib,sum_first_half]
  simp only [Finset.sum_ite_eq',mem_univ,if_true,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,mul_one]
  ring

private theorem cappedWeight_bounds {r : ℕ} (p : Fin r) (y : Quad (Fin r)) :
    0 ≤ cappedWeight p y ∧ cappedWeight p y ≤ 1 ∧
    cappedWeight p y ≤ (cappedCopies p y : ℝ) ∧ cappedCopies p y ≤ 4*r := by
  have hr := p.isLt
  by_cases hy : y = (true,false,p)
  · subst y
    simp [cappedCopies,cappedWeight]
    exact_mod_cast (show 1 ≤ 4*r by omega)
  · by_cases h : y.1 = false <;> simp [cappedCopies,cappedWeight,hy,h] <;> omega

/-- This family cannot pass even the zero-spending, zero-discrepancy
conditions for positive fixed rescaling of its actual multiplicities. -/
theorem cappedHost_scaling_obstruction {r : ℕ} (p : Fin r) :
    ¬ ∃ (scale : Fin 2 → ℝ) (C : ℝ), 0 < C ∧
      (∀ x, C ≤ scale x * (6*r : ℕ)) ∧
      ∑ x, scale x * (cappedCopies p (true,false,p) : ℝ) ≤ C := by
  rintro ⟨scale,C,hC,hrow,hcol⟩
  have hR : 0 < r := Nat.zero_lt_of_lt p.isLt
  have hn := column_normalized_mass_le_one (univ : Finset (Fin 2))
    (fun _ => ((6*r : ℕ) : ℝ)) (fun _ => (cappedCopies p (true,false,p) : ℝ))
    scale C hC (fun _ _ => by exact_mod_cast (show 0 < 6*r by omega)) (fun _ _ => by positivity)
    (fun x _ => hrow x) hcol
  have ht : cappedCopies p (true,false,p) = 4*r := by simp [cappedCopies]
  rw [Fin.sum_univ_two,ht,Nat.cast_mul,Nat.cast_mul] at hn
  have hp : 0 < 6*(r : ℝ) := by positivity
  have hh : (4*(r : ℝ)+4*(r : ℝ))/(6*(r : ℝ)) ≤ 1 := by
    rw [add_div]
    exact hn
  have he := (div_le_iff₀ hp).mp hh
  have hr : 0 < (r : ℝ) := by exact_mod_cast hR
  nlinarith

/-- The capped weights give a factorization of the very same cut. -/
theorem cappedHost_factorization {r : ℕ} (hr : 8 ≤ r) (p : Fin r) :
    ∃ F : (cappedHost p).graph.EdgeColoring (12*r+2), F.IsFactorization := by
  let P := cappedHost p
  have hreg : P.graph.IsRegularOfDegree (12*r+2) := by
    apply P.regular
    · intro x
      change (∑ y : Fin 2,if x=y then 6*r+2 else 0) + (∑ y,cappedCopies p y) = _
      rw [cappedCopies_sum]
      simp
      omega
    · intro y
      have h := (cappedWeight_bounds p y).2.2.2
      change (∑ z,quadInternal y z) + (∑ x : Fin 2,cappedCopies p y) +
        (∑ z,diagExtra (fun w => 2*(4*r-cappedCopies p w)) y z) = _
      rw [quadInternal_degree,diagExtra_degree,card_quad,Fintype.card_fin]
      simp
      omega
  have hmass := P.edgeCount_inside false 2 (fun y => quadInternal_degree y)
  rw [card_quad,Fintype.card_fin] at hmass
  apply P.finish (12*r+2) 4 r (by omega) hreg (by omega)
    (P.colourable_inside false 4 Prod.fst quadInternal_zero (fun y => by change (∑ z,quadInternal y z) ≤ 4; rw [quadInternal_degree]; decide))
    (P.colourable_inside true 4 Prod.fst quadInternal_zero (fun y => by change (∑ z,quadInternal y z) ≤ 4; rw [quadInternal_degree]; decide))
  · refine ⟨fun _ => cappedWeight p,fun _ => 1,2,2,by norm_num,fun _ => by norm_num,?_,?_,?_,?_⟩
    · intro x y
      exact ⟨(cappedWeight_bounds p y).1,by simpa [P,cappedHost] using (cappedWeight_bounds p y).2.2.1⟩
    · intro y
      simpa [Fin.sum_univ_two,two_mul] using
        (show cappedWeight p y + cappedWeight p y ≤ 2 by linarith [(cappedWeight_bounds p y).2.1])
    · intro y
      change (∑ z,quadInternal y z) ≤ 2
      rw [quadInternal_degree]
    · left
      refine ⟨1,cappedWeight p,fun _ => 1,by norm_num,
        fun y => ⟨(cappedWeight_bounds p y).1,(cappedWeight_bounds p y).2.1⟩,
        fun _ => by norm_num,fun _ _ => mul_one _,?_⟩
      intro _
      rw [cappedWeight_sum]
      have h : (8:ℝ) ≤ r := by exact_mod_cast hr
      norm_num
      linarith
  · left
    apply P.dense Bool.false_ne_true r 4 (4*r)
    · simp only [Fintype.card_fin,card_quad]
      omega
    · intro y
      change 4*r ≤ (univ.filter (fun z => 0 < diagExtra (fun w => 2*(4*r-cappedCopies p w)) y z)).card
      rw [diagExtra_neighbours,card_quad,Fintype.card_fin]

end WeightedPaper.Examples
