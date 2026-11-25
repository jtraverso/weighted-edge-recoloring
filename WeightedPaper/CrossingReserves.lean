module

public import WeightedPaper.ScaledHall

@[expose] public section


namespace WeightedPaper

open Finset
open scoped Classical

/-- A fixed certificate on exceptional-to-ordinary pairs. The charge is
an upper bound on the certificate weight of one copy, for each row. -/
structure RowReserves {I A B : Type*} (U : I → Finset A) (W : I → Finset B)
    (cap : A → B → ℕ) (K : Finset I) (X : Finset A) (Y : Finset B) where
  weight : A → B → ℝ
  charge : A → ℝ
  bound : ℝ
  bound_pos : 0 < bound
  charge_nonneg : ∀ x ∈ X, 0 ≤ charge x
  capacity : ∀ x ∈ X, ∀ y ∉ Y, 0 ≤ weight x y ∧ weight x y ≤ charge x * cap x y
  column : ∀ y ∉ Y, (∑ x ∈ X, weight x y) ≤ bound
  reserve : ∀ i ∈ K, ∀ x ∈ (U i).filter (· ∈ X),
    bound + (K.card - 1 : ℕ) * charge x ≤ ∑ y ∈ (W i).filter (· ∉ Y), weight x y

theorem RowReserves.hall {I A B : Type*} [Fintype B]
    {U : I → Finset A} {W : I → Finset B} {cap : A → B → ℕ}
    {K : Finset I} {X : Finset A} {Y : Finset B} (P : RowReserves U W cap K X Y)
    (i : I) (hi : i ∈ K) (spent : A → B → ℕ)
    (hs : ∀ x, (∑ y, spent x y) ≤ K.card - 1)
    (Q : Finset A) (hQ : Q ⊆ (U i).filter (· ∈ X)) :
    Q.card ≤ ((W i).filter fun y => y ∉ Y ∧ ∃ x ∈ Q, 0 < cap x y - spent x y).card := by
  classical
  have hX : (U i).filter (· ∈ X) ⊆ X := fun _ hx => (mem_filter.mp hx).2
  have h := hall_of_bounded_pair_weights ((U i).filter (· ∈ X)) ((W i).filter (· ∉ Y))
    cap spent P.weight P.charge P.bound (K.card - 1) P.bound_pos
    (fun x hx => P.charge_nonneg x (hX hx))
    (fun x hx y hy => P.capacity x (hX hx) y (mem_filter.mp hy).2)
    (P.reserve i hi)
    (fun x _ => (sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun y _ _ => Nat.zero_le (spent x y))).trans (hs x))
    (fun y hy => (sum_le_sum_of_subset_of_nonneg hX (fun x hx _ =>
      (P.capacity x hx y (mem_filter.mp hy).2).1)).trans (P.column y (mem_filter.mp hy).2))
    Q hQ
  simpa only [filter_filter] using h

end WeightedPaper
