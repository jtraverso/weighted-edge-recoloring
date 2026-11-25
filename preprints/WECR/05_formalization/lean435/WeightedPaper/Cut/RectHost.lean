import WeightedPaper.Cut.RectCoordinates

namespace WeightedPaper.Examples.RectGrid
open Finset SimpleGraph

variable {q : ℕ}
instance : DecidableEq (Vertex (Row q) (Ord q)) :=
  @instDecidableEqProd Bool (Row q ⊕ Ord q) inferInstance (@instDecidableEqSum (Row q) (Ord q) inferInstance inferInstance)
def order (q : ℕ) := 512*q^2
def degree (q : ℕ) := 256*(3*q-1)
def internal (x y : Ord q) : ℕ :=
  if x.1=y.1 then if x.2.1=y.2.1 then quadInternal x.2.2 y.2.2 else 0 else 0
def ordinary (x y : Ord q) : ℕ :=
  (if adjacent x y then 1 else 0) + if x=y then order q-degree q-2*q-2 else 0
def host (q : ℕ) : Host (Row q) (Ord q) where
  internal := internal
  internal_symm x y := by exact if_congr eq_comm (if_congr eq_comm (quadInternal_symm _ _) rfl) rfl
  internal_diag x := by simp [internal,quadInternal_zero _ _ rfl]
  ordinary := ordinary
  ordinary_symm x y := by exact congrArg₂ (·+·) (if_congr (or_congr eq_comm eq_comm) rfl rfl) (if_congr eq_comm rfl rfl)
  incidence x y := if x=y.1 then 2*q else 0
  exceptional _ _ := 0
  exceptional_symm _ _ := rfl

@[simp] theorem support_iff (x y : Ord q) : 0<ordinary x y ↔ adjacent x y := by
  by_cases h : adjacent x y
  · simp [ordinary,h]
  · have hn : x≠y := by rintro rfl; exact h (Or.inl rfl)
    simp [ordinary,h,hn]

theorem sum_coords {R : Type*} [AddCommMonoid R] (f : Ord q → R) :
    (∑ y,f y) = ∑ i,∑ j,∑ c : Copy,f (i,j,c) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type (f := fun y : Fin q × Copy => _)]

theorem inside_degree (x : Ord q) : (∑ y,internal x y)=2 := by
  rw [sum_coords]
  simp only [internal,Prod.fst,Prod.snd,sum_ite_irrel,sum_const_zero,quadInternal_degree]
  simp

theorem support_degree (x : Ord q) : (univ.filter fun y => 0<ordinary x y).card=degree q := by
  classical
  have h := support_sum (fun _ : Ord q => (1:ℝ)) x
  have hq : 1 ≤ 3*q := by have := x.1.2.isLt; omega
  simp only [one_mul,sum_const,card_univ,card_copy,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,nsmul_eq_mul,Nat.cast_ofNat,mul_one] at h
  have hd : (degree q : ℝ)=256*(3*(q:ℝ)-1) := by simp [degree,Nat.cast_sub hq]
  exact_mod_cast (show (((univ.filter fun y => 0<ordinary x y).card : ℕ):ℝ) = degree q by
    simp only [support_iff,← sum_boole,hd]
    linarith)

theorem slack (hq : 49 ≤ q) : degree q+2*q+2 ≤ order q ∧ 2*degree q ≤ order q := by
  unfold degree order
  have : 3*q-1+1=3*q := by omega
  constructor <;> nlinarith [Nat.mul_le_mul_right q hq]

theorem regular (hq : 49 ≤ q) : (host q).graph.IsRegularOfDegree (order q) := by
  apply (host q).regular
  · intro x
    change (∑ _ : Row q,0)+(∑ y : Ord q,if x=y.1 then 2*q else 0)=_
    rw [sum_coords]
    simp only [sum_const_zero,zero_add]
    change (∑ i : Row q,∑ _ : Fin q,∑ _ : Copy,if x=i then 2*q else 0) = 512*q^2
    simp only [sum_const,card_univ,card_copy,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,nsmul_eq_mul,
      ← mul_sum,sum_ite_eq,mem_univ,if_true,Nat.cast_id]
    ring
  · intro x
    change (∑ y,internal x y)+(∑ i : Row q,if i=x.1 then 2*q else 0)+(∑ y,ordinary x y)=_
    rw [inside_degree]
    have hs : (∑ y : Ord q,if adjacent x y then 1 else 0) = degree q := by
      simpa only [card_filter,support_iff] using support_degree x
    simp only [ordinary,sum_add_distrib,hs,sum_ite_eq',sum_ite_eq,mem_univ,if_true]
    have := (slack hq).1
    omega

theorem internal_mass (b : Bool) : ((host q).graph.restrict (half (Row q) (Ord q) b)).edgeCount=order q := by
  have h := (host q).edgeCount_inside b 2 inside_degree
  rw [card_ord] at h
  unfold order
  omega

noncomputable def row_budget (hq : 49 ≤ q) : HostBudget (host q) (32*q) 0 := by
  let w (i : Row q) (y : Ord q) : ℝ := if i=y.1 then 1 else 0
  have hq' : 49 ≤ (q:ℝ) := by exact_mod_cast hq
  have hrow (x : Row q) : (∑ y,w x y) = 256*(q:ℝ) := by
    rw [sum_coords]
    change (∑ i : Row q,∑ _ : Fin q,∑ _ : Copy,if x=i then (1:ℝ) else 0) = _
    simp only [sum_const,card_univ,card_copy,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,nsmul_eq_mul,Nat.cast_ofNat,
      ← mul_sum,sum_ite_eq,mem_univ,if_true,mul_one]
    ring
  refine ⟨w,fun _ => 1,1,2,by norm_num,fun _ => by norm_num,?_,?_,fun x => (inside_degree x).le,?_⟩
  · intro x y
    change 0 ≤ w x y ∧ w x y ≤ 1*( (if x=y.1 then 2*q else 0 : ℕ) : ℝ)
    by_cases he : x=y.1 <;> simp [w,he] <;> linarith
  · intro y; simp [w]
  · right
    let E : Row q ≃ Fin (Fintype.card (Row q)) := Fintype.equivFin _
    refine ⟨Fintype.card (Row q),1,4*Real.sqrt (2*(q:ℝ)),fun y => basis (E y.1),fun x => basis (E x),
      fun _ => 0,by norm_num,by positivity,fun y => by simp [energy_basis],
      fun x => (energy_basis (E x)).le,?_,?_,?_⟩
    · have hnonneg : 0 ≤ 2*(q:ℝ) := by positivity
      simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,mul_pow,Real.sq_sqrt hnonneg]
      norm_num
      <;> ring_nf
      <;> exact le_rfl
    · intro x y; simp [w,dot_basis,basis]
    · intro x
      rw [hrow]
      have he : 1 ≤ 32*q := by omega
      simp [Nat.cast_sub he]
      have hSqrt : Real.sqrt (2*(q:ℝ)) ≤ (q:ℝ) := by
        by_contra! hn
        have hs := sq_lt_sq' (show -Real.sqrt (2*(q:ℝ)) < (q:ℝ) by
          have h := Real.sqrt_nonneg (2*(q:ℝ)); linarith) hn
        rw [Real.sq_sqrt (by positivity)] at hs
        nlinarith only [hs,mul_nonneg (show 0 ≤ (q:ℝ) by positivity) (show 0 ≤ (q:ℝ)-2 by linarith)]
      simp [Real.sqrt_mul] at hSqrt
      nlinarith [sq_nonneg (q:ℝ),mul_nonneg (show 0≤32*(q:ℝ)-1 by linarith) (sub_nonneg.mpr hSqrt)]
 
/-- Expose ordinary coordinates with either implementation of decidable
equality on a part (the abstract cut uses classical equality). -/
theorem ordinary_complement (b : Bool) (de : DecidableEq (half (Row q) (Ord q) b)) :
    @compl _ (@BooleanAlgebra.toCompl _ (@Finset.booleanAlgebra _ _ de))
      (exSet (Row q) (Ord q) b) = ordSet (Row q) (Ord q) b := by
  rw [← exSet_compl]
  ext x
  simp only [mem_compl]

end WeightedPaper.Examples.RectGrid

#print axioms WeightedPaper.Examples.RectGrid.regular
#print axioms WeightedPaper.Examples.RectGrid.row_budget
