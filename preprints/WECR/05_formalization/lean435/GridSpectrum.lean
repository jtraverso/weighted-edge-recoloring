import GridLayout
import Mathlib.Algebra.Order.Chebyshev

namespace WeightedPaper.Repair.Grid
open Finset
open scoped Classical

variable {q b : ℕ}

private def adjacent (x y : CellVertex q b) : Prop := x.1 = y.1 ∨ x.2.1 = y.2.1
private instance (x y : CellVertex q b) : Decidable (adjacent x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem mem_gridNeighbors_iff (x y : CellVertex q b) :
    y ∈ gridNeighbors x ↔ adjacent x y := by
  rcases x with ⟨i,j,t⟩
  rcases y with ⟨i',j',t'⟩
  simp [gridNeighbors, adjacent, eq_comm]

/-- The ordinary biadjacency acts by adding a row and a column and subtracting
their common cell. This includes all copies in the corresponding cell. -/
theorem support_sum (v : CellVertex q b → ℝ) (x : CellVertex q b) :
    (∑ y, v y * (if adjacent x y then 1 else 0)) =
       (∑ j, ∑ c : Fin b,v (x.1,j,c)) + (∑ i,∑ c : Fin b,v (i,x.2.1,c)) -
       ∑ c : Fin b,v (x.1,x.2.1,c) := by
  let z (i j : Fin q) := ∑ c : Fin b,v (i,j,c)
  have hcell (i j : Fin q) :
      (∑ c : Fin b,v (i,j,c)*(if adjacent x (i,j,c) then 1 else 0)) =
        (if x.1=i then z i j else 0)+(if x.2.1=j then z i j else 0)-
        (if x.1=i then if x.2.1=j then z i j else 0 else 0) := by
    by_cases hi : x.1=i <;> by_cases hj : x.2.1=j <;> simp [adjacent,z,hi,hj]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type (f := fun y : Fin q × Fin b => _)]
  simp only [hcell,sum_sub_distrib,sum_add_distrib,sum_ite_irrel,sum_const_zero]
  simp [z]


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

def applySupport (v : CellVertex q b → ℝ) (x : CellVertex q b) : ℝ :=
  ∑ y, v y * (if adjacent x y then 1 else 0)

private theorem sum_coords (f : CellVertex q b → ℝ) :
    (∑ x, f x) = ∑ i, ∑ j, ∑ t : Fin b, f (i,j,t) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type (f := fun y : Fin q × Fin b => _)]

theorem norm_bound (hq : 2 ≤ q) (v : CellVertex q b → ℝ) (hz : ∑ y,v y=0) :
    (∑ x,(applySupport v x)^2) ≤ ((b:ℝ)*((q:ℝ)-1))^2*(∑ y,(v y)^2) := by
  let z (i j : Fin q) := ∑ c : Fin b,v (i,j,c)
  have hzero : (∑ i,∑ j,z i j)=0 := (sum_coords v).symm.trans hz
  have hcell := cell_energy hq z hzero
  have henergy : (∑ i,∑ j,(z i j)^2) ≤ (b:ℝ)*(∑ y,(v y)^2) := by
    rw [sum_coords (fun y => (v y)^2)]
    simp only [mul_sum]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => by
      simpa only [z,card_univ,Fintype.card_fin,mul_sum] using
        (sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin b))) (f := fun c => v (i,j,c)))
  rw [sum_coords (fun x => (applySupport v x)^2)]
  simp only [applySupport,support_sum,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,← mul_sum]
  change (b:ℝ)*(∑ i,∑ j,((∑ l,z i l)+(∑ l,z l j)-z i j)^2) ≤ _
  calc
    _ ≤ (b:ℝ)*(((q:ℝ)-1)^2*(∑ i,∑ j,(z i j)^2)) := mul_le_mul_of_nonneg_left hcell (Nat.cast_nonneg b)
    _ ≤ (b:ℝ)*(((q:ℝ)-1)^2*((b:ℝ)*(∑ y,(v y)^2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy (sq_nonneg _)) (Nat.cast_nonneg b)
    _ = _ := by ring


/-- Every zero-sum row profile lifts to an eigenvector with eigenvalue
b(q-1). Nonzero such profiles exist as soon as there are two rows. -/
theorem row_eigenvector (f : Fin q → ℝ) (hf : ∑ i,f i=0) (x : CellVertex q b) :
    applySupport (fun y => f y.1) x = (b:ℝ)*((q:ℝ)-1)*f x.1 := by
  rw [applySupport,support_sum]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    ← mul_sum,hf,mul_zero,add_zero]
  ring


theorem grid_norm_attained (hq : 2 ≤ q) (hb : 0 < b) :
    ∃ f : CellVertex q b → ℝ, (∑ x, f x) = 0 ∧ (∃ x, f x ≠ 0) ∧
      ∀ x, applySupport f x = (b:ℝ)*((q:ℝ)-1)*f x := by
  let i : Fin q := ⟨0, by omega⟩
  let j : Fin q := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have e : (0:ℕ) = 1 := congrArg Fin.val h
    omega
  let f (u : Fin q) : ℝ := (if u=i then 1 else 0) - (if u=j then 1 else 0)
  have hf : (∑ u, f u) = 0 := by simp [f, sum_sub_distrib]
  refine ⟨fun x => f x.1, ?_, ⟨(i,i,⟨0,hb⟩), by simp [f,hij]⟩, row_eigenvector f hf⟩
  rw [sum_coords]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum, hf, mul_zero, sum_const_zero]

theorem constant_eigenvector (c : ℝ) (x : CellVertex q b) :
    applySupport (fun _ => c) x = (b:ℝ)*(2*(q:ℝ)-1)*c := by
  rw [applySupport, support_sum]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem column_eigenvector (f : Fin q → ℝ) (hf : ∑ i, f i = 0) (x : CellVertex q b) :
    applySupport (fun y => f y.2.1) x = (b:ℝ)*((q:ℝ)-1)*f x.2.1 := by
  rw [applySupport, support_sum]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_sum, hf, mul_zero, zero_add]
  ring

theorem product_eigenvector (f g : Fin q → ℝ) (hf : ∑ i, f i = 0) (hg : ∑ j, g j = 0)
    (x : CellVertex q b) :
    applySupport (fun y => f y.1*g y.2.1) x = -(b:ℝ)*(f x.1*g x.2.1) := by
  rw [applySupport, support_sum]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have row : (∑ j, (b:ℝ)*(f x.1*g j)) = 0 := by
    simp_rw [← mul_assoc, ← mul_sum, hg, mul_zero]
  have col : (∑ i, (b:ℝ)*(f i*g x.2.1)) = 0 := by
    calc
      _ = (b:ℝ)*((∑ i, f i)*g x.2.1) := by
        rw [sum_mul, mul_sum]
      _ = 0 := by rw [hf, zero_mul, mul_zero]
  rw [row,col]
  ring

theorem cell_zero_kernel (f : CellVertex q b → ℝ)
    (hf : ∀ i j, ∑ t : Fin b, f (i,j,t) = 0) (x : CellVertex q b) :
    applySupport f x = 0 := by
  rw [applySupport, support_sum]
  simp [hf]

/-- The normalized reserve on the physical ordinary vertices contracts the
mean-zero space by at most (q-1)/(2q-1), for every positive cell size. -/
theorem grid_reserve_contraction (m : Marked q ↪ CellVertex q b) (hq : 2 ≤ q) (hb : 0 < b)
    (f : Ordinary (Fin (Nat.sqrt q)) (Intact m) → ℝ) (hz : ∑ x, f x = 0) :
    (∑ y, (∑ x, f x * (if support m x y then 1/(b*(2*(q:ℝ)-1)) else 0))^2) ≤
      (((q:ℝ)-1)/(2*q-1))^2 * ∑ x, (f x)^2 := by
  let e := coordinates m
  let v : CellVertex q b → ℝ := f ∘ e.symm
  let d : ℝ := b*(2*(q:ℝ)-1)
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have dv : 0 < d := mul_pos hb' (by linarith)
  have hv : ∑ x, v x = 0 := (e.symm.sum_comp f).trans hz
  have cell y : (∑ x, f x * (if support m x y then 1/d else 0)) =
      applySupport v (e y) / d := by
    rw [← e.symm.sum_comp (fun x => f x * (if support m x y then 1/d else 0))]
    unfold applySupport
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro x _
    have hs : support m (e.symm x) y ↔ adjacent (e y) x := by
      change e y ∈ gridNeighbors (e (e.symm x)) ↔ _
      rw [e.apply_symm_apply, gridNeighbors_symmetric]
      exact mem_gridNeighbors_iff _ _
    by_cases h : adjacent (e y) x
    · simp [v, hs.mpr h, h, div_eq_mul_inv]
    · simp [v, mt hs.mp h, h]
  change (∑ y, (∑ x, f x * (if support m x y then 1/d else 0))^2) ≤ _
  simp_rw [cell, div_pow]
  rw [← sum_div, e.sum_comp (fun u => (applySupport v u)^2),
    ← e.symm.sum_comp (fun x => (f x)^2), ← div_pow]
  change (∑ x, (applySupport v x)^2) / d^2 ≤
    (((q:ℝ)-1)/(2*q-1))^2 * ∑ x, (v x)^2
  apply (div_le_iff₀ (sq_pos_of_pos dv)).2
  have hd : 2*(q:ℝ)-1 ≠ 0 := by linarith
  have scale : (((q:ℝ)-1)/(2*q-1))^2*d^2 = ((b:ℝ)*((q:ℝ)-1))^2 := by
    rw [← mul_pow]
    congr 1
    calc
      _ = (b:ℝ)*(((q:ℝ)-1)/(2*q-1)*(2*q-1)) := by dsimp [d]; ring
      _ = _ := by rw [div_mul_cancel₀ _ hd]
  rw [mul_right_comm, scale]
  exact norm_bound hq v hv

end WeightedPaper.Repair.Grid
