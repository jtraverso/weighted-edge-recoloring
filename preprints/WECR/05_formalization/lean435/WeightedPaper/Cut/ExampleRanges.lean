import WeightedPaper.Cut.ReleaseAudit
import WeightedPaper.Examples.Capped

namespace WeightedPaper.Examples
open Finset SimpleGraph
open scoped Classical

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
theorem cappedHost_factorization_from_six {r : ℕ} (hr : 6 ≤ r) (p : Fin r) :
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
      have h : (6:ℝ) ≤ r := by exact_mod_cast hr
      norm_num
      linarith
  · left
    apply P.dense Bool.false_ne_true r 4 (4*r)
    · simp only [Fintype.card_fin,card_quad]
      omega
    · intro y
      change 4*r ≤ (univ.filter (fun z => 0 < diagExtra (fun w => 2*(4*r-cappedCopies p w)) y z)).card
      rw [diagExtra_neighbours,card_quad,Fintype.card_fin]

theorem centredHost_factorization_from_six {r q : ℕ} (hr : 6 ≤ r) (hq : 2 ≤ q) :
    ∃ F : (centredHost r q).graph.EdgeColoring (4*r*q+4), F.IsFactorization := by
  let P := centredHost r q
  have hprod : 2*r ≤ r*q := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right r hq
  have hsub : 4*r ≤ 3*r*q+1 := by nlinarith
  have hreg : P.graph.IsRegularOfDegree (4*r*q+4) := by
    apply P.regular
    · intro x
      change (∑ _y : Fin r,0) + (∑ y,centredCopies q x y) = _
      simp only [sum_const_zero,zero_add,centredCopies_row]
    · intro y
      change (∑ z,quadInternal y z) + (∑ x,centredCopies q x y) +
        (∑ z,diagExtra (fun _ => 3*r*q+1-4*r) y z) = _
      rw [quadInternal_degree,centredCopies_col,diagExtra_degree,card_quad,Fintype.card_fin]
      rw [show 3*r*q = 3*(r*q) by ring,show 4*r*q = 4*(r*q) by ring]
      rw [show 3*r*q = 3*(r*q) by ring] at hsub
      omega
  have hmass := P.edgeCount_inside false 2 (fun y => quadInternal_degree y)
  rw [card_quad,Fintype.card_fin] at hmass
  have hgap : equitableGap 4 (P.graph.restrict (half (Fin r) (Quad (Fin r)) false)).edgeCount = 0 := by
    rw [show (P.graph.restrict (half (Fin r) (Quad (Fin r)) false)).edgeCount = 4*r by omega]
    simp [equitableGap]
  apply P.finish (4*r*q+4) 4 r (by omega) hreg (by omega)
    (P.colourable_inside false 4 Prod.fst quadInternal_zero (fun y => by change (∑ z,quadInternal y z) ≤ 4; rw [quadInternal_degree]; decide))
    (P.colourable_inside true 4 Prod.fst quadInternal_zero (fun y => by change (∑ z,quadInternal y z) ≤ 4; rw [quadInternal_degree]; decide))
  · rw [hgap]
    refine ⟨fun x y => (centredCopies q x y : ℝ),fun _ => 1,(r*q+1 : ℕ),2,
      by positivity,fun _ => by norm_num,?_,?_,?_,?_⟩
    · intro x y
      exact ⟨Nat.cast_nonneg _,by simp [P,centredHost]⟩
    · intro y
      rw [← Nat.cast_sum,centredCopies_col]
    · intro y
      change (∑ z,quadInternal y z) ≤ 2
      rw [quadInternal_degree]
    · right
      refine ⟨r,1,2*r,fun y => basis y.2.2,basis,fun _ => (q : ℝ), by norm_num,by positivity,
        fun y => by simp [energy_basis],fun _ => by simp [energy_basis],?_,?_,?_⟩
      · have hh : (6 : ℝ) ≤ r := by exact_mod_cast hr
        push_cast
        nlinarith [mul_nonneg (show (0:ℝ) ≤ r by positivity) (sub_nonneg.mpr hh)]
      · intro x y
        rw [dot_basis]
        unfold centredCopies basis
        push_cast
        simp [eq_comm]
      · intro x
        rw [← Nat.cast_sum,centredCopies_row]
        have hh : (6 : ℝ) ≤ r := by exact_mod_cast hr
        have hhq : (2 : ℝ) ≤ q := by exact_mod_cast hq
        push_cast
        norm_num
        nlinarith [mul_nonneg (show (0:ℝ) ≤ r by positivity) (sub_nonneg.mpr hhq)]
  · left
    apply P.dense Bool.false_ne_true r 4 (4*r)
    · simp only [Fintype.card_fin,card_quad]
      omega
    · intro y
      change 4*r ≤ (univ.filter (fun z => 0 < diagExtra (fun _ => 3*r*q+1-4*r) y z)).card
      rw [diagExtra_neighbours,card_quad,Fintype.card_fin]

/-- The baseline columns span the full coordinate space before centering.
This is the elementary kernel calculation for their square matrix. -/
theorem centredHost_indicator_budget_from_six {r q gap : ℕ} (hr : 6 ≤ r) (hq : 2 ≤ q) :
    ∃ B : HostBudget (centredHost r q) 4 gap, ∀ x y, B.weight x y = 1 := by
  let weight : Fin r → Quad (Fin r) → ℝ := fun _ _ => 1
  have hbound : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  refine ⟨⟨weight,fun _ => 1,r,2,hbound,fun _ => zero_le_one,?_,?_,?_,?_⟩,fun _ _ => rfl⟩
  · intro x y
    have hc : 1 ≤ centredCopies q x y := by unfold centredCopies; omega
    refine ⟨zero_le_one, ?_⟩
    change (1:ℝ) ≤ 1*(centredCopies q x y : ℝ)
    rw [one_mul]
    exact_mod_cast hc
  · intro y
    simp [weight]
  · intro y
    exact (quadInternal_degree y).le
  · left
    refine ⟨1,fun _ => 1,fun _ => 1,zero_le_one,fun _ => ⟨zero_le_one,le_rfl⟩,
      fun _ => zero_le_one,fun _ _ => one_mul _,?_⟩
    intro x
    have hr' : (6:ℝ) ≤ r := by exact_mod_cast hr
    simp [weight]
    linarith

end WeightedPaper.Examples

#print axioms WeightedPaper.Examples.cappedHost_factorization_from_six
#print axioms WeightedPaper.Examples.centredHost_factorization_from_six
#print axioms WeightedPaper.Examples.centredHost_indicator_budget_from_six
