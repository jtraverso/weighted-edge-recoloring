import WeightedPaper.Cut.GridCoordinates

namespace WeightedPaper.Examples.Grid
open Finset
open scoped Classical
variable {q : ℕ}

private theorem twice_sum (z : Fin q → Fin q → ℝ) (r c : Fin q → ℝ)
    (hr : ∀ i, ∑ j,z i j = r i) (hc : ∀ j, ∑ i,z i j = c j)
    (hz : ∑ j,c j = 0) (a b : ℝ) :
    (∑ i, ∑ j, (a*z i j+b*(r i+c j))^2) =
      a^2*(∑ i,∑ j,(z i j)^2) +
      (2*a*b+q*b^2)*((∑ i,(r i)^2)+(∑ j,(c j)^2)) := by
  have hzr : (∑ i, ∑ j, r i * z i j) = ∑ i, (r i)^2 := by
    simp_rw [← mul_sum,hr,pow_two]
  have hzc : (∑ i, ∑ j, c j * z i j) = ∑ j, (c j)^2 := by
    rw [sum_comm]
    simp_rw [← mul_sum,hc,pow_two]
  have hrc : (∑ i,∑ j,r i*c j)=0 := by simp_rw [← mul_sum,hz,mul_zero,sum_const_zero]
  have expand (i j : Fin q) : (a*z i j+b*(r i+c j))^2 =
      a^2*(z i j)^2 + (2*a*b)*(r i*z i j) + (2*a*b)*(c j*z i j) +
      b^2*(r i)^2+b^2*(c j)^2+(2*b^2)*(r i*c j) := by ring
  have pull (t : ℝ) (f : Fin q → Fin q → ℝ) :
      (∑ i,∑ j,t*f i j)=t*(∑ i,∑ j,f i j) := by simp_rw [mul_sum]
  have rr : (∑ i,∑ _j : Fin q,(r i)^2) = (q:ℝ)*∑ i,(r i)^2 := by
    simp [mul_sum]
  have cc : (∑ _i : Fin q,∑ j,(c j)^2) = (q:ℝ)*∑ j,(c j)^2 := by simp
  simp only [expand,sum_add_distrib]
  rw [pull (a^2) (fun i j => (z i j)^2),pull (2*a*b) (fun i j => r i*z i j),
    pull (2*a*b) (fun i j => c j*z i j),pull (b^2) (fun i _ => (r i)^2),
    pull (b^2) (fun _ j => (c j)^2),pull (2*b^2) (fun i j => r i*c j)]
  rw [hzr,hzc,rr,cc,hrc]
  ring

private theorem cell_energy (hq : 2 ≤ q) (z : Fin q → Fin q → ℝ)
    (hz : ∑ i,∑ j,z i j = 0) :
    (∑ i, ∑ j, ((∑ l,z i l)+(∑ l,z l j)-z i j)^2) ≤
       ((q:ℝ)-1)^2*(∑ i,∑ j,(z i j)^2) := by
  let r := fun i => ∑ j,z i j
  let c := fun j => ∑ i,z i j
  have hzero : ∑ j,c j = 0 := by change (∑ j,∑ i,z i j)=0; rw [sum_comm]; exact hz
  have h1 := twice_sum z r c (fun _ => rfl) (fun _ => rfl) hzero q (-1)
  have h2 := twice_sum z r c (fun _ => rfl) (fun _ => rfl) hzero (-1) 1
  have hpos : 0 ≤ ∑ i,∑ j,((q:ℝ)*z i j + (-1)*(r i+c j))^2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hq' : 2 ≤ (q:ℝ) := by exact_mod_cast hq
  have h₃ : (∑ i,(r i)^2)+(∑ j,(c j)^2) ≤ (q:ℝ)*(∑ i,∑ j,(z i j)^2) := by
    by_contra! h
    nlinarith [mul_pos (show 0<(q:ℝ) by linarith) (sub_pos.mpr h)]
  change (∑ i,∑ j,(r i+c j-z i j)^2) ≤ _
  simp only [neg_one_mul,one_mul] at h2
  simp_rw [show ∀ i j,-z i j+(r i+c j)=r i+c j-z i j by intros;ring] at h2
  nlinarith [mul_nonneg (sub_nonneg.mpr hq') (sub_nonneg.mpr h₃)]

def applySupport (v : Ord q → ℝ) (x : Ord q) : ℝ :=
  ∑ y, v y * (if adjacent x y then 1 else 0)

theorem norm_bound (hq : 2 ≤ q) (v : Ord q → ℝ) (hz : ∑ y,v y=0) :
    (∑ x,(applySupport v x)^2) ≤ (256*((q:ℝ)-1))^2*(∑ y,(v y)^2) := by
  let z (i j : Fin q) := ∑ c : Copy,v (i,j,c)
  have hsum (f : Ord q → ℝ) : (∑ x,f x) = ∑ i,∑ j,∑ c : Copy,f (i,j,c) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type (f := fun y : Fin q × Copy => _)]
  have hzero : (∑ i,∑ j,z i j)=0 := (hsum v).symm.trans hz
  have hcell := cell_energy hq z hzero
  have henergy : (∑ i,∑ j,(z i j)^2) ≤ 256*(∑ y,(v y)^2) := by
    rw [hsum (fun y => (v y)^2)]
    simp only [mul_sum]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => by
      simpa only [z,card_univ,card_copy,Nat.cast_ofNat,mul_sum] using
        (sq_sum_le_card_mul_sum_sq (s := (univ : Finset Copy)) (f := fun c => v (i,j,c)))
  rw [hsum (fun x => (applySupport v x)^2)]
  simp only [applySupport,support_sum,Prod.fst,Prod.snd,sum_const,card_univ,card_copy,
    nsmul_eq_mul,Nat.cast_ofNat,← mul_sum]
  change 256*(∑ i,∑ j,((∑ l,z i l)+(∑ l,z l j)-z i j)^2) ≤ _
  calc
    _ ≤ 256*(((q:ℝ)-1)^2*(∑ i,∑ j,(z i j)^2)) := by linarith
    _ ≤ 256*(((q:ℝ)-1)^2*(256*(∑ y,(v y)^2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy (sq_nonneg _)) (by norm_num)
    _ = _ := by ring

theorem bilinear_bound (hq : 2 ≤ q) (u v : Ord q → ℝ) (hz : ∑ y,v y=0) :
    4*(∑ x,u x * applySupport v x)^2 ≤
      (256*(2*(q:ℝ)-1))^2*(∑ x,(u x)^2)*(∑ y,(v y)^2) := by
  have h := (sum_mul_sq_le_sq_mul_sq univ u (applySupport v)).trans
    (mul_le_mul_of_nonneg_left (norm_bound hq v hz) (sum_nonneg fun _ _ => sq_nonneg _))
  have hq' : 2 ≤ (q:ℝ) := by exact_mod_cast hq
  have hn : 4*(256*((q:ℝ)-1))^2 ≤ (256*(2*(q:ℝ)-1))^2 := by nlinarith
  have hw := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn
    (sum_nonneg (s:=univ) fun x _ => sq_nonneg (u x))) (sum_nonneg (s:=univ) fun y _ => sq_nonneg (v y))
  linarith only [h,hw]

/-- Every zero-sum row profile lifts to an eigenvector with eigenvalue
256(q-1). Nonzero such profiles exist as soon as there are two rows. -/
theorem row_eigenvector (f : Fin q → ℝ) (hf : ∑ i,f i=0) (x : Ord q) :
    applySupport (fun y => f y.1) x = 256*((q:ℝ)-1)*f x.1 := by
  rw [applySupport,support_sum]
  simp only [sum_const,card_univ,card_copy,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,
    ← mul_sum,hf,mul_zero,add_zero]
  ring

end WeightedPaper.Examples.Grid
