import WeightedPaper.Examples.FiveBlocks

namespace WeightedPaper.Examples

open Finset
open scoped Classical

private def b (t : ℕ) := 400*(t+1)
private def g (t : ℕ) := 400*t+398
private def r (t : ℕ) := 5*g t
private def ell (t : ℕ) := 100*(t+1)*g t
private def B (t : ℕ) := 4*ell t
private def a (t : ℕ) := 20*(t+1)*g t
private def rho (t : ℕ) := 50*(t+1)*g t

abbrev RobustOrd (t : ℕ) := Quad (Fin 5 × Fin (ell t))
abbrev RobustCentre (t : ℕ) := Fin (r t)

private def π (t : ℕ) (v : RobustOrd t) : Fin 5 := v.2.2.1

private theorem card_ord (t : ℕ) : Fintype.card (RobustOrd t) = 5*B t := by
  simp [B,Fintype.card_prod]
  ring

private theorem card_block (t : ℕ) (j : Fin 5) :
    fiberCount (π t) (univ : Finset (RobustOrd t)) j = B t := by
  unfold fiberCount
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [π,Fintype.sum_prod_type,Fintype.sum_bool]
  let s := ∑ i : Fin 5, ∑ _k : Fin (ell t), if i=j then (1:ℕ) else 0
  change (s+s)+(s+s) = B t
  have hn : s = ell t := by
    calc
      _ = ∑ i : Fin 5, if i=j then ell t else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i=j <;> simp [hij]
      _ = ell t := by simp
  rw [hn]
  unfold B
  ring

private theorem block_size (t : ℕ) : B t = b t*g t := by unfold B ell b; ring

noncomputable def robustGroups (t : ℕ) : RobustOrd t ≃ RobustCentre t × Fin (b t) :=
  Fintype.equivOfCardEq (by
    rw [card_ord,block_size,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
    unfold r
    ring)

instance (t : ℕ) : NeZero (r t) := ⟨by unfold r g; omega⟩

private def shares (t : ℕ) (x i : RobustCentre t) : Prop := x=i ∨ x=i+1
instance (t : ℕ) (x i : RobustCentre t) : Decidable (shares t x i) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem fin_one_ne_zero (t : ℕ) : (1 : RobustCentre t) ≠ 0 := by
  intro h
  have h1 : 1 < r t := by unfold r g; omega
  have hv := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt h1] at hv

private theorem sum_bool_of_pair {A : Type*} [Fintype A] [DecidableEq A] (x y : A) (h : x ≠ y) :
    (∑ z : A, if z=x ∨ z=y then (1:ℕ) else 0) = 2 := by
  classical
  rw [← sum_filter, ← card_eq_sum_ones]
  have he : (univ.filter fun z => z=x ∨ z=y) = {x,y} := by ext z; simp
  rw [he,card_pair h]

private def flag (t : ℕ) (x i : RobustCentre t) : ℕ := if shares t x i then 1 else 0
private theorem flag_cols (t : ℕ) (i : RobustCentre t) : ∑ x,flag t x i = 2 :=
  sum_bool_of_pair i (i+1) (by
    intro h
    exact fin_one_ne_zero t ((add_left_cancel (show i+1 = i+0 by simpa using h.symm))))

private theorem flag_rows (t : ℕ) (x : RobustCentre t) : ∑ i,flag t x i = 2 := by
  have he (i : RobustCentre t) : shares t x i ↔ i=x ∨ i=x-1 := by
    unfold shares
    apply or_congr eq_comm
    calc
      _ ↔ x-1=i := sub_eq_iff_eq_add.symm
      _ ↔ i=x-1 := eq_comm
  unfold flag
  simp_rw [he]
  have h : x ≠ x-1 := by
    intro hn
    have hh := (sub_eq_iff_eq_add).mp hn.symm
    exact fin_one_ne_zero t (add_left_cancel (show x+1 = x+0 by simpa using hh.symm))
  exact sum_bool_of_pair x (x-1) h

private def unitProfile (t : ℕ) (x i : RobustCentre t) : ℝ := (flag t x i : ℝ)
private theorem unitProfile_energy (t : ℕ) (i : RobustCentre t) :
    energy (fun x => unitProfile t x i) ≤ 2^2 := by
  have h : ∀ x, (unitProfile t x i)^2 = (flag t x i : ℝ) := by
    intro x
    by_cases hx : shares t x i <;> simp [unitProfile,flag,hx]
  simp only [energy,h,← Nat.cast_sum,flag_cols]
  norm_num

noncomputable def robustHost (t : ℕ) : Host (RobustCentre t) (RobustOrd t) where
  internal := quadInternal
  internal_symm := quadInternal_symm
  internal_diag := fun _ => quadInternal_zero _ _ rfl
  ordinary := blockCopies (π t)
  ordinary_symm := blockCopies_symm _
  incidence := fun x y => (g t+1)*flag t x (robustGroups t y).1
  exceptional := fun _ _ => 0
  exceptional_symm := fun _ _ => rfl

private theorem flag_rows_on_host (t : ℕ) (x : RobustCentre t) :
    (∑ y : RobustOrd t,flag t x (robustGroups t y).1) = 2*b t := by
  rw [Fintype.sum_equiv (robustGroups t) _ (fun y => flag t x y.1) (fun _ => rfl),
    Fintype.sum_prod_type]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,← mul_sum,flag_rows]
  ring

private theorem robust_reg (t : ℕ) :
    (robustHost t).graph.IsRegularOfDegree (2*b t*(g t+1)) := by
  apply Host.regular
  · intro x
    change (∑ _y : RobustCentre t,0) +
      ∑ y, (g t+1)*flag t x (robustGroups t y).1 = _
    rw [sum_const_zero,zero_add,← mul_sum,flag_rows_on_host]
    ring
  · intro y
    change (∑ z,quadInternal y z) + (∑ x,(g t+1)*flag t x (robustGroups t y).1) +
      (∑ z,blockCopies (π t) y z) = _
    rw [quadInternal_degree,← mul_sum,flag_cols,blockCopies_degree _ _ (card_block t),block_size]
    have h : b t = g t+2 := by unfold b g; omega
    rw [h]
    ring

theorem robustHost_ordinary_degree (t : ℕ) (v : RobustOrd t) :
    (univ.filter fun w => 0 < (robustHost t).ordinary v w).card = 2*B t :=
  blockCopies_neighbours _ _ (card_block t) v

/-- Every choice of internal class bound and palette on this cut fails the dense condition. -/
theorem robustHost_not_dense (t a k : ℕ) :
    ¬ DenseCut ((robustHost t).cap false true)
      (exSet (RobustCentre t) (RobustOrd t) false) (exSet (RobustCentre t) (RobustOrd t) true)
      (Fintype.card (RobustCentre t) + Fintype.card (RobustOrd t)) a k := by
  have hℓ : 0 < ell t := by unfold ell g; positivity
  let v : RobustOrd t := (false,false,0,⟨0,hℓ⟩)
  apply (robustHost t).not_dense_of_ordinary_upper Bool.false_ne_true a k (2*B t) v
    (robustHost_ordinary_degree t v).le
  rw [card_ord]
  have hBpos : 0 < B t := by unfold B; omega
  omega

private theorem robust_arithmetic (t : ℕ) :
    2*a t+r t ≤ rho t ∧ 100 ≤ rho t ∧
    5*rho t+(2*a t+r t)+99 ≤ 2*B t ∧ 6*rho t ≤ B t := by
  have hu : 1 ≤ t+1 := by omega
  have hg : 398 ≤ g t := by unfold g; omega
  have hprod : g t ≤ (t+1)*g t := by simpa using Nat.mul_le_mul_right (g t) hu
  unfold a r rho B ell
  constructor
  · nlinarith only [hprod]
  constructor
  · nlinarith only [hprod,hg]
  constructor
  · nlinarith only [hprod,hg]
  · nlinarith

/-- The robust example has (2/5) of the opposite ordinary vertices
as crossing neighbors and can be factored for every parameter. -/
theorem robustHost_factorization (t : ℕ) :
    ∃ F : (robustHost t).graph.EdgeColoring (2*b t*(g t+1)), F.IsFactorization := by
  let P := robustHost t
  have hb : 400 ≤ b t := by unfold b; omega
  have hd : 100 ≤ 2*b t*(g t+1) := by
    have hg : 398 ≤ g t := by unfold g; omega
    nlinarith
  have hmass := P.edgeCount_inside false 2 (fun y => quadInternal_degree y)
  rw [card_ord] at hmass
  have hka : 100*a t = 5*B t := by unfold a B ell; ring
  have he : (P.graph.restrict (half (RobustCentre t) (RobustOrd t) false)).edgeCount = 100*a t := by omega
  have hgap : equitableGap 100 (P.graph.restrict (half (RobustCentre t) (RobustOrd t) false)).edgeCount = 0 := by
    rw [he]; simp [equitableGap]
  apply P.finish (2*b t*(g t+1)) 100 (a t) hd (robust_reg t) he.le
    (P.colourable_inside false 100 Prod.fst quadInternal_zero (fun y => by change (∑ z,quadInternal y z) ≤ 100; rw [quadInternal_degree]; decide))
    (P.colourable_inside true 100 Prod.fst quadInternal_zero (fun y => by change (∑ z,quadInternal y z) ≤ 100; rw [quadInternal_degree]; decide))
  · rw [hgap]
    refine ⟨fun x y => unitProfile t x (robustGroups t y).1,fun _ => 1,2,2,
      by norm_num,fun _ => by norm_num,?_,?_,?_,?_⟩
    · intro x y
      let f := flag t x (robustGroups t y).1
      have hle : f ≤ (g t+1)*f := by
        simpa only [one_mul] using Nat.mul_le_mul_right f (show 1 ≤ g t+1 by omega)
      change 0 ≤ (f : ℝ) ∧ (f : ℝ) ≤ 1 * (((g t+1)*f : ℕ) : ℝ)
      exact ⟨Nat.cast_nonneg _,by simpa only [one_mul] using (Nat.cast_le.mpr hle : (f : ℝ) ≤ _)⟩
    · intro y
      change (∑ x,(flag t x (robustGroups t y).1 : ℝ)) ≤ 2
      rw [← Nat.cast_sum,flag_cols]
      norm_num
    · intro y
      change (∑ z,quadInternal y z) ≤ 2
      rw [quadInternal_degree]
    · right
      refine ⟨r t,2,b t,fun y x => unitProfile t x (robustGroups t y).1,basis,
        fun _ => 0,by norm_num,by positivity,
        fun y => unitProfile_energy t (robustGroups t y).1,fun _ => by simp [energy_basis],?_,?_,?_⟩
      · have hb' : (400:ℝ) ≤ b t := by exact_mod_cast hb
        have hr' : (r t : ℝ) ≤ 5*(b t : ℝ) := by unfold r b g; push_cast; linarith
        have hb₀ : 0 ≤ (b t : ℝ) := Nat.cast_nonneg _
        have hm := mul_nonneg hb₀ (sub_nonneg.mpr hb')
        have hPoly : 64 * (r t : ℝ) ≤ (b t : ℝ)^2 := calc
          _ ≤ 320 * (b t : ℝ) := by linarith only [hr']
          _ ≤ _ := by nlinarith only [hm,hb₀]
        convert hPoly using 1
        push_cast
        ring
      · intro x y
        change unitProfile t x (robustGroups t y).1 =
          0 + dot (basis x) (fun z => unitProfile t z (robustGroups t y).1)
        rw [dot_basis,zero_add]
      · intro x
        have hrowSum : (∑ y : RobustOrd t, unitProfile t x (robustGroups t y).1) =
            ((2 * b t : ℕ) : ℝ) := by
          simp only [unitProfile, ← Nat.cast_sum, flag_rows_on_host]
        rw [hrowSum]
        norm_num only [Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, abs_zero, mul_zero,
          add_zero, mul_one, Nat.cast_mul]
        have hb' : (400:ℝ) ≤ b t := by exact_mod_cast hb
        linarith only [hb']
  · right
    obtain ⟨h1,h2,h3,h4⟩ := robust_arithmetic t
    apply P.robust Bool.false_ne_true (a t) 100 (rho t) (5*rho t)
    · simpa only [Fintype.card_fin] using h1
    · exact h2
    · intro v
      rw [robustHost_ordinary_degree,Fintype.card_fin]
      exact h3
    · exact block_robust (π t) (B t) (rho t) (5*rho t) (card_block t) (card_ord t) h4 le_rfl

end WeightedPaper.Examples
