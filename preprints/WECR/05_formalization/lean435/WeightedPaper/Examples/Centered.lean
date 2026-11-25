import WeightedPaper.Examples.Matrices

namespace WeightedPaper.Examples

open Finset
open scoped Classical

def centredCopies {r : ℕ} (q : ℕ) (x : Fin r) (y : Quad (Fin r)) : ℕ :=
  q + if x=y.2.2 then 1 else 0

def centredHost (r q : ℕ) : Host (Fin r) (Quad (Fin r)) where
  internal := quadInternal
  internal_symm := quadInternal_symm
  internal_diag := fun _ => quadInternal_zero _ _ rfl
  ordinary := diagExtra (fun _ => 3*r*q+1-4*r)
  ordinary_symm := diagExtra_symm _
  incidence := centredCopies q
  exceptional := fun _ _ => 0
  exceptional_symm := fun _ _ => rfl

theorem centredCopies_row {r : ℕ} (q : ℕ) (x : Fin r) :
    ∑ y, centredCopies q x y = 4*r*q+4 := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,centredCopies,Prod.snd]
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,
    Finset.sum_ite_eq,mem_univ,if_true]
  ring

theorem centredCopies_col {r : ℕ} (q : ℕ) (y : Quad (Fin r)) :
    ∑ x, centredCopies q x y = r*q+1 := by
  simp [centredCopies,sum_add_distrib]

/-- A common baseline cancels from the load differences. The coordinates
used for the discrepancy are unit vectors. -/
theorem centredHost_factorization {r q : ℕ} (hr : 8 ≤ r) (hq : 2 ≤ q) :
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
      · have hh : (8 : ℝ) ≤ r := by exact_mod_cast hr
        push_cast
        nlinarith [mul_nonneg (show (0:ℝ) ≤ r by positivity) (sub_nonneg.mpr hh)]
      · intro x y
        rw [dot_basis]
        unfold centredCopies basis
        push_cast
        simp [eq_comm]
      · intro x
        rw [← Nat.cast_sum,centredCopies_row]
        have hh : (8 : ℝ) ≤ r := by exact_mod_cast hr
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
theorem baseline_columns_independent {r : ℕ} (q : ℝ) (hq : 0 ≤ q) (v : Fin r → ℝ)
    (h : ∀ x, (∑ j, (q + basis j x) * v j) = 0) : ∀ x, v x = 0 := by
  have he (x : Fin r) : q*(∑ j,v j) + v x = 0 := by
    have hh := h x
    simp only [add_mul,sum_add_distrib,← mul_sum] at hh
    have hsingle : (∑ j,basis j x * v j) = v x := by simp [basis,ite_mul,eq_comm]
    rwa [hsingle] at hh
  have hs := sum_congr (s₁ := (univ : Finset (Fin r))) rfl (fun x _ => he x)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,sum_const_zero] at hs
  have hf : ((r : ℝ)*q+1)*(∑ j, v j) = 0 := by convert hs using 1 <;> ring
  have hpos : 0 < (r : ℝ)*q+1 := by positivity
  have ht := (mul_eq_zero.mp hf).resolve_left hpos.ne'
  intro x
  have hh := he x
  rwa [ht,mul_zero,zero_add] at hh

/-- Even arbitrary fixed positive row scales cannot pass the uncentered
Euclidean allowance and row reserve on this cut. -/
theorem centredHost_uncentered_obstruction {r q : ℕ} (hr : 8 ≤ r) (hq : 2 ≤ q)
    (scale : Fin r → ℝ) (hs : ∀ x, 0 < scale x) (R H : ℝ) (hH : 0 ≤ H)
    (hRadius : ∀ y : Quad (Fin r), energy (fun x => scale x * (centredCopies q x y : ℝ)) ≤ R^2)
    (hAllow : (2*R)^2*(4*(r : ℝ)) ≤ H^2) :
    ¬ ∀ x, 3*H/4 ≤ ((4*(r : ℝ)*q+4)/2)*scale x := by
  intro hrow
  have hn : Nonempty (Fin r) := ⟨⟨0,by omega⟩⟩
  letI := hn
  obtain ⟨a,_,ha⟩ := (univ : Finset (Fin r)).exists_min_image scale univ_nonempty
  let y : Quad (Fin r) := (false,false,a)
  let low := (q : ℝ)*scale a
  have hlo : 0 ≤ low := mul_nonneg (Nat.cast_nonneg q) (hs a).le
  have he : (r : ℝ)*low^2 ≤ energy (fun x => scale x * (centredCopies q x y : ℝ)) := by
    unfold energy
    calc
      _ = ∑ _x : Fin r,low^2 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro x _
        have hc : (q : ℝ) ≤ (centredCopies q x y : ℝ) := by
          exact_mod_cast (Nat.le_add_right q (if x=y.2.2 then 1 else 0))
        have hsx := ha x (mem_univ x)
        have hq' : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
        have hprod : low ≤ scale x * (centredCopies q x y : ℝ) :=
          (by simpa [low,mul_comm] using mul_le_mul_of_nonneg_right hsx hq' :
            low ≤ scale x * (q : ℝ)).trans (mul_le_mul_of_nonneg_left hc (hs x).le)
        have hpos : 0 ≤ scale x * (centredCopies q x y : ℝ) :=
          mul_nonneg (hs x).le (Nat.cast_nonneg _)
        exact sq_le_sq.mpr (by rwa [abs_of_nonneg hlo,abs_of_nonneg hpos])
  have hmul := mul_le_mul_of_nonneg_right (he.trans (hRadius y))
    (show 0 ≤ 16*(r : ℝ) by positivity)
  have hsq : (4*(r : ℝ)*low)^2 ≤ H^2 := by nlinarith only [hmul,hAllow]
  have hbig : 4*(r : ℝ)*low ≤ H := by
    have h := sq_le_sq.mp hsq
    simpa [abs_of_nonneg (show 0 ≤ 4*(r : ℝ)*low by positivity),abs_of_nonneg hH] using h
  have hrs : (8 : ℝ) ≤ r := by exact_mod_cast hr
  have hqs : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hp : 0 < ((r : ℝ)*q-2)*scale a := by
    apply mul_pos _ (hs a)
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity) (sub_nonneg.mpr hqs)]
  dsimp [low] at hbig
  nlinarith only [hbig,hrow a,hp]

end WeightedPaper.Examples
