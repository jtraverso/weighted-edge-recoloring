import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Conditional expectations for Euclidean sign rounding, expressed
in coordinates so the proof uses only finite sums of squares. -/
namespace WeightedPaper
open Finset
open scoped Classical

variable {J : Type*} [Fintype J]

def energy (v : J → ℝ) : ℝ := ∑ j, (v j)^2

private theorem energy_round_one (u v : J → ℝ) (r : ℝ) (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1) :
    ∃ t : ℝ, (t = 1 ∨ t = -1) ∧
      energy (fun j => u j + t * v j) ≤
        energy (fun j => u j + r * v j) + (1-r^2) * energy v := by
  let plus := energy (fun j => u j + v j)
  let minus := energy (fun j => u j - v j)
  have hId : energy (fun j => u j + r * v j) + (1-r^2) * energy v =
      ((1+r)/2) * plus + ((1-r)/2) * minus := by
    simp only [energy, plus, minus, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have hp : 0 ≤ (1+r)/2 := by linarith
  have hm : 0 ≤ (1-r)/2 := by linarith
  by_cases h : plus ≤ minus
  · refine ⟨1,Or.inl rfl,?_⟩
    have hb := mul_le_mul_of_nonneg_left h hm
    simp only [one_mul]
    change plus ≤ _
    rw [hId]
    nlinarith only [hb]
  · refine ⟨-1,Or.inr rfl,?_⟩
    have hb := mul_le_mul_of_nonneg_left (le_of_not_ge h) hp
    simp only [neg_mul,one_mul,← sub_eq_add_neg]
    change minus ≤ _
    rw [hId]
    nlinarith only [hb]

/-- Round coefficients to signs with at most the total variance cost. -/
theorem exists_rounding_signs {I : Type*} (S : Finset I) (v : I → J → ℝ)
    (u : J → ℝ) (r : I → ℝ) (hr : ∀ i ∈ S, -1 ≤ r i ∧ r i ≤ 1) :
    ∃ t : I → ℝ, (∀ i ∈ S, t i = 1 ∨ t i = -1) ∧
      energy (fun j => u j + ∑ i ∈ S, t i * v i j) ≤
        energy (fun j => u j + ∑ i ∈ S, r i * v i j) +
          ∑ i ∈ S, (1-(r i)^2) * energy (v i) := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty => exact ⟨fun _ => 1,by simp,by simp⟩
  | insert a S ha ih =>
    have hra := hr a (mem_insert_self _ _)
    obtain ⟨e,he,hRound⟩ := energy_round_one (fun j => u j + ∑ i ∈ S, r i * v i j)
      (v a) (r a) hra.1 hra.2
    obtain ⟨t,ht,hTail⟩ := ih (fun j => u j + e * v a j)
      (fun i hi => hr i (mem_insert_of_mem hi))
    let f : I → ℝ := Function.update t a e
    refine ⟨f, ?_, ?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl|hs
      · simpa [f] using he
      · simpa [f, Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hs))] using ht i hs
    · simp only [sum_insert ha]
      have hF (j : J) : (∑ i ∈ S,f i * v i j) = ∑ i ∈ S,t i * v i j := by
        apply sum_congr rfl
        intro i hi
        rw [show f i = t i by simp [f, Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hi))]]
      simp only [hF, show f a = e by simp [f], ← add_assoc]
      have hPerm (c : ℝ) :
          (fun j => u j + (∑ i ∈ S,r i * v i j) + c * v a j) =
            (fun j => u j + c * v a j + ∑ i ∈ S,r i * v i j) := by
        funext j
        ring
      rw [hPerm e, hPerm (r a)] at hRound
      linarith only [hRound,hTail]

/-- If the fractional coefficients balance to zero, the cost depends
on their count. Each coefficient at a sign contributes zero variance. -/
theorem exists_signs_of_sparse_fractional_balance {I : Type*} (S : Finset I)
    (v : I → J → ℝ) (u : J → ℝ) (r : I → ℝ) (C : ℝ) (s : ℕ)
    (hr : ∀ i ∈ S, -1 ≤ r i ∧ r i ≤ 1) (hz : ∀ j, (∑ i ∈ S, r i * v i j) = 0)
    (hC : ∀ i ∈ S, energy (v i) ≤ C) (hCn : 0 ≤ C)
    (hFrac : (S.filter fun i => r i ≠ 1 ∧ r i ≠ -1).card ≤ s) :
    ∃ t : I → ℝ, (∀ i ∈ S, t i = 1 ∨ t i = -1) ∧
      energy (fun j => u j + ∑ i ∈ S,t i * v i j) ≤ energy u + s * C := by
  obtain ⟨t,ht,h⟩ := exists_rounding_signs S v u r hr
  simp only [hz,add_zero] at h
  let F := S.filter fun i => r i ≠ 1 ∧ r i ≠ -1
  have hsum : (∑ i ∈ S, (1-(r i)^2) * energy (v i)) =
      ∑ i ∈ F, (1-(r i)^2) * energy (v i) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hi hnot
    have hSign : r i = 1 ∨ r i = -1 := by
      by_contra! hn
      exact hnot (mem_filter.mpr ⟨hi,hn⟩)
    rcases hSign with hEq|hEq <;> norm_num [hEq]
  have hBound : (∑ i ∈ F, (1-(r i)^2) * energy (v i)) ≤ (s : ℝ) * C := by
    calc
      _ ≤ ∑ _i ∈ F,C := by
        apply sum_le_sum
        intro i hi
        have hv : 0 ≤ energy (v i) := sum_nonneg (fun j _ => sq_nonneg (v i j))
        exact (show (1-(r i)^2) * energy (v i) ≤ energy (v i) by
          nlinarith [mul_nonneg (sq_nonneg (r i)) hv]).trans (hC i (mem_filter.mp hi).1)
      _ = (F.card : ℝ) * C := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show F.card ≤ s from hFrac)) hCn
  exact ⟨t,ht,by linarith only [h,hsum,hBound]⟩

end WeightedPaper
