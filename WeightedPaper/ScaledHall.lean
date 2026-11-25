module

public import WeightedPaper.Hall

@[expose] public section


/-! Real row scales are used only in the Hall certificate. An edge is
available precisely when its residual multiplicity is positive. -/
namespace WeightedPaper
open Finset
open scoped Classical

theorem hall_of_real_column_budget {A B : Type*} (X : Finset A) (Y : Finset B)
    (w : A → B → ℝ) (L : ℝ) (hL : 0 < L)
    (hnonneg : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ w x y)
    (hrow : ∀ x ∈ X, L ≤ ∑ y ∈ Y, w x y)
    (hcol : ∀ y ∈ Y, (∑ x ∈ X, w x y) ≤ L)
    (S : Finset A) (hSX : S ⊆ X) :
    S.card ≤ (Y.filter fun y => ∃ x ∈ S, 0 < w x y).card := by
  classical
  let N := Y.filter fun y => ∃ x ∈ S, 0 < w x y
  have hNY : N ⊆ Y := filter_subset _ _
  have hmass : (∑ y ∈ N, ∑ x ∈ S, w x y) = ∑ y ∈ Y, ∑ x ∈ S, w x y := by
    apply sum_subset hNY
    intro y hy hn
    apply sum_eq_zero
    intro x hx
    exact le_antisymm (le_of_not_gt fun h => hn (mem_filter.mpr ⟨hy,x,hx,h⟩))
      (hnonneg x (hSX hx) y hy)
  have hh : (S.card : ℝ) * L ≤ N.card * L := by
    calc
      _ = ∑ _x ∈ S, L := by simp
      _ ≤ ∑ x ∈ S, ∑ y ∈ Y, w x y := sum_le_sum (fun x hx => hrow x (hSX hx))
      _ = ∑ y ∈ N, ∑ x ∈ S, w x y := by rw [hmass, sum_comm]
      _ ≤ ∑ _y ∈ N, L := by
        apply sum_le_sum
        intro y hy
        exact (sum_le_sum_of_subset_of_nonneg hSX
          (fun x hx _ => hnonneg x hx y (hNY hy))).trans (hcol y (hNY hy))
      _ = _ := by simp
  exact_mod_cast (le_of_mul_le_mul_right hh hL : (S.card : ℝ) ≤ N.card)

theorem scaled_reserve_after_spending {B : Type*} (T : Finset B) (w spent : B → ℕ)
    (C scale : ℝ) (p : ℕ) (hs : 0 ≤ scale)
    (hrow : C + p * scale ≤ ∑ v ∈ T, scale * (w v : ℝ))
    (hspent : (∑ v ∈ T, spent v) ≤ p) :
    C ≤ ∑ v ∈ T, scale * ((w v - spent v : ℕ) : ℝ) := by
  have h : (∑ v ∈ T, scale * (w v : ℝ)) ≤
      ∑ v ∈ T, (scale * ((w v - spent v : ℕ) : ℝ) + scale * (spent v : ℝ)) := by
    apply sum_le_sum
    intro v hv
    rw [← mul_add, ← Nat.cast_add]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show w v ≤ w v - spent v + spent v by omega)) hs
  rw [sum_add_distrib] at h
  have hb : (∑ v ∈ T, scale * (spent v : ℝ)) ≤ scale * (p : ℝ) := by
    rw [← mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hspent) hs
  nlinarith only [h, hrow, hb]

/-- Hall's condition for exceptional rows with independent positive scales. -/
theorem hall_of_scaled_residual {A B : Type*} (X : Finset A) (Y : Finset B)
    (w spent : A → B → ℕ) (scale : A → ℝ) (C : ℝ) (p : ℕ)
    (hC : 0 < C) (hs : ∀ x ∈ X, 0 < scale x)
    (hrow : ∀ x ∈ X, C + p * scale x ≤ ∑ y ∈ Y, scale x * (w x y : ℝ))
    (hspent : ∀ x ∈ X, (∑ y ∈ Y, spent x y) ≤ p)
    (hcol : ∀ y ∈ Y, (∑ x ∈ X, scale x * (w x y : ℝ)) ≤ C)
    (S : Finset A) (hSX : S ⊆ X) :
    S.card ≤ (Y.filter fun y => ∃ x ∈ S, 0 < w x y - spent x y).card := by
  classical
  let W := fun x y => scale x * ((w x y - spent x y : ℕ) : ℝ)
  have h := hall_of_real_column_budget X Y W C hC
    (fun x hx y _ => mul_nonneg (hs x hx).le (Nat.cast_nonneg _))
    (fun x hx => scaled_reserve_after_spending Y (w x) (spent x) C (scale x) p
      (hs x hx).le (hrow x hx) (hspent x hx))
    (fun y hy => (sum_le_sum fun x hx =>
       mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le (w x y) (spent x y))
         (hs x hx).le).trans (hcol y hy)) S hSX
  refine h.trans (card_le_card ?_)
  intro y hy
  obtain ⟨hy, x, hx, hpos⟩ := mem_filter.mp hy
  exact mem_filter.mpr ⟨hy, x, hx, by
    have : 0 < ((w x y - spent x y : ℕ) : ℝ) :=
      pos_of_mul_pos_right hpos (hs x (hSX hx)).le
    exact_mod_cast this⟩

/-- Spending at most `p` copies reduces the certificate weight of a row
by at most `p * charge`. -/
theorem residual_row_weight_lower {B : Type*} (Y : Finset B) (weight : B → ℝ)
    (spent : B → ℕ) (charge : ℝ) (p : ℕ) (hcharge : 0 ≤ charge)
    (hspent : (∑ y ∈ Y, spent y) ≤ p) :
    (∑ y ∈ Y, weight y) - charge * p ≤ ∑ y ∈ Y, max 0 (weight y - charge * spent y) := by
  have hdebit : (∑ y ∈ Y, charge * (spent y : ℝ)) ≤ charge * p := by
    rw [← mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hspent) hcharge
  have hkeep : (∑ y ∈ Y, (weight y - charge * (spent y : ℝ))) ≤
      ∑ y ∈ Y, max 0 (weight y - charge * (spent y : ℝ)) :=
    sum_le_sum (fun y _ => le_max_right _ _)
  rw [sum_sub_distrib] at hkeep
  linarith only [hdebit, hkeep]

/-- A certificate weight can be smaller than the charge for spending all
copies of the pair. A positive residual weight certifies positive
residual multiplicity on that pair. -/
theorem hall_of_bounded_pair_weights {A B : Type*} (X : Finset A) (Y : Finset B)
    (cap spent : A → B → ℕ) (weight : A → B → ℝ) (charge : A → ℝ)
    (C : ℝ) (p : ℕ) (hC : 0 < C)
    (hcharge : ∀ x ∈ X, 0 ≤ charge x)
    (hweight : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ weight x y ∧ weight x y ≤ charge x * cap x y)
    (hrow : ∀ x ∈ X, C + (p : ℝ) * charge x ≤ ∑ y ∈ Y, weight x y)
    (hspent : ∀ x ∈ X, (∑ y ∈ Y, spent x y) ≤ p)
    (hcol : ∀ y ∈ Y, (∑ x ∈ X, weight x y) ≤ C)
    (Q : Finset A) (hQ : Q ⊆ X) :
    Q.card ≤ (Y.filter fun y => ∃ x ∈ Q, 0 < cap x y - spent x y).card := by
  classical
  let rem (x : A) (y : B) := max 0 (weight x y - charge x * spent x y)
  have hrow' (x : A) (hx : x ∈ X) : C ≤ ∑ y ∈ Y, rem x y := by
    have h := residual_row_weight_lower Y (weight x) (spent x) (charge x) p
      (hcharge x hx) (hspent x hx)
    change _ ≤ ∑ y ∈ Y, rem x y at h
    linarith only [hrow x hx, h]
  have hcol' (y : B) (hy : y ∈ Y) : (∑ x ∈ X, rem x y) ≤ C := by
    refine (sum_le_sum (fun x hx => ?_)).trans (hcol y hy)
    apply max_le (hweight x hx y hy).1
    exact sub_le_self _ (mul_nonneg (hcharge x hx) (Nat.cast_nonneg _))
  have hh := hall_of_real_column_budget X Y rem C hC
    (fun _ _ _ _ => le_max_left _ _) hrow' hcol' Q hQ
  apply hh.trans
  apply card_le_card
  intro y hy
  obtain ⟨hyY, x, hxQ, hxp⟩ := mem_filter.mp hy
  have hx := hQ hxQ
  refine mem_filter.mpr ⟨hyY,x,hxQ,?_⟩
  by_contra! hn
  have he : cap x y ≤ spent x y := by omega
  have hb : weight x y ≤ charge x * (spent x y : ℝ) :=
    (hweight x hx y hyY).2.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast he) (hcharge x hx))
  exact (not_lt_of_ge (max_le le_rfl (sub_nonpos.mpr hb))) hxp

/-- An overloaded column is an obstruction to every fixed positive row
scaling, even before the recolouring and copy spending allowances. -/
theorem column_normalized_mass_le_one {A : Type*} (X : Finset A)
    (total cell scale : A → ℝ) (C : ℝ) (hC : 0 < C)
    (htotal : ∀ x ∈ X, 0 < total x) (hcell : ∀ x ∈ X, 0 ≤ cell x)
    (hrow : ∀ x ∈ X, C ≤ scale x * total x)
    (hcol : (∑ x ∈ X, scale x * cell x) ≤ C) :
    ∑ x ∈ X, cell x / total x ≤ 1 := by
  have h : C * (∑ x ∈ X, cell x / total x) ≤ C := by
    rw [mul_sum]
    refine (sum_le_sum (fun x hx => ?_)).trans hcol
    have hh : C / total x ≤ scale x := (div_le_iff₀ (htotal x hx)).mpr (hrow x hx)
    calc
      _ = (C / total x) * cell x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (hcell x hx)
  exact le_of_mul_le_mul_left (h.trans_eq (mul_one C).symm) hC

end WeightedPaper
