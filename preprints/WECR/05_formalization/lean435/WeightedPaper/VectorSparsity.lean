import WeightedPaper.VectorRounding

/-! Move a balanced fractional signing to the boundary. Gaussian
elimination on the finite coordinate set gives the needed dependence. -/
namespace WeightedPaper
open Finset
open scoped Classical

private theorem exists_dependence {I : Type*} (S : Finset I) (n : ℕ) (hn : n < S.card)
    (v : I → Fin n → ℝ) :
    ∃ c : I → ℝ, (∃ i ∈ S, c i ≠ 0) ∧ ∀ j, (∑ i ∈ S, c i * v i j) = 0 := by
  classical
  induction n generalizing S with
  | zero =>
    obtain ⟨i,hi⟩ := card_pos.mp hn
    exact ⟨fun _ => 1,⟨i,hi,one_ne_zero⟩,fun j => Fin.elim0 j⟩
  | succ n ih =>
    by_cases hzero : ∀ i ∈ S, v i 0 = 0
    · obtain ⟨c,hc,hbal⟩ := ih S (by omega) (fun i j => v i j.succ)
      refine ⟨c,hc,?_⟩
      intro j
      refine Fin.cases ?_ hbal j
      exact sum_eq_zero (fun i hi => by simp [hzero i hi])
    · push Not at hzero
      obtain ⟨a,ha,hva⟩ := hzero
      have hc : n < (S.erase a).card := by rw [card_erase_of_mem ha]; omega
      let q (i : I) := v i 0 / v a 0
      obtain ⟨c,hc,hbal⟩ := ih (S.erase a) hc
        (fun i j => v i j.succ - q i * v a j.succ)
      let d := -(∑ i ∈ S.erase a,c i * q i)
      let f := Function.update c a d
      have hfa : f a = d := by simp [f]
      have hf (i : I) (hi : i ∈ S.erase a) : f i = c i := by
        simp [f,Function.update_of_ne (mem_erase.mp hi).1]
      obtain ⟨i,hi,hci⟩ := hc
      refine ⟨f,⟨i,(mem_erase.mp hi).2,by rwa [hf i hi]⟩,?_⟩
      intro j
      rw [← sum_erase_add _ _ ha, hfa, sum_congr rfl (fun i hi => by rw [hf i hi])]
      refine Fin.cases ?_ (fun j => ?_) j
      · change (∑ i ∈ S.erase a,c i * v i 0) + d * v a 0 = 0
        have h0 (i : I) : c i * q i * v a 0 = c i * v i 0 := by
          dsimp [q]
          rw [mul_assoc,div_mul_cancel₀ _ hva]
        simp only [d,neg_mul,sum_mul,h0]
        ring
      · change (∑ i ∈ S.erase a,c i * v i j.succ) + d * v a j.succ = 0
        have h := hbal j
        simp only [mul_sub,sum_sub_distrib] at h
        simpa only [d,neg_mul,sum_mul,← sub_eq_add_neg,mul_assoc] using h

/-- Feasible centered coefficients can be chosen with at most one
fractional coordinate per dimension of the displayed real coordinate space. -/
theorem exists_sparse_fractional_balance {I : Type*} (S : Finset I) (n : ℕ)
    (v : I → Fin n → ℝ) :
    ∃ x : I → ℝ, (∀ i ∈ S, -1 ≤ x i ∧ x i ≤ 1) ∧
      (∀ j, (∑ i ∈ S,x i * v i j) = 0) ∧
      (S.filter fun i => x i ≠ 1 ∧ x i ≠ -1).card ≤ n := by
  classical
  let Fr (x : I → ℝ) := S.filter fun i => x i ≠ 1 ∧ x i ≠ -1
  suffices h : ∀ m, ∀ x : I → ℝ, (Fr x).card = m →
      (∀ i ∈ S, -1 ≤ x i ∧ x i ≤ 1) →
      (∀ j, (∑ i ∈ S,x i * v i j) = 0) →
      ∃ y : I → ℝ, (∀ i ∈ S, -1 ≤ y i ∧ y i ≤ 1) ∧
        (∀ j, (∑ i ∈ S,y i * v i j) = 0) ∧ (Fr y).card ≤ n from
    h _ (fun _ => 0) rfl (by simp) (by simp)
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro x hx hb hz
    by_cases hm : m ≤ n
    · exact ⟨x,hb,hz,hx.trans_le hm⟩
    obtain ⟨c,hc,hbal⟩ := exists_dependence (Fr x) n (by omega) v
    let d (i : I) := if i ∈ Fr x then c i else 0
    let T := (Fr x).filter fun i => c i ≠ 0
    have hT : T.Nonempty := by
      obtain ⟨i,hi,hci⟩ := hc
      exact ⟨i,mem_filter.mpr ⟨hi,hci⟩⟩
    have hne (i : I) (hi : i ∈ T) : d i ≠ 0 := by
      obtain ⟨hFr,hn⟩ := mem_filter.mp hi
      simp [d,hFr,hn]
    have hvan (i : I) (hi : i ∉ T) : d i = 0 := by
      by_cases hFr : i ∈ Fr x
      · have hci : c i = 0 := by by_contra hn; exact hi (mem_filter.mpr ⟨hFr,hn⟩)
        simp [d,hFr,hci]
      · simp [d,hFr]
    have hbal' (j : Fin n) : (∑ i ∈ S,d i * v i j) = 0 := by
      calc
        _ = ∑ i ∈ Fr x, d i * v i j := by
          symm
          apply sum_subset (filter_subset _ _)
          intro i _ hi
          change i ∉ Fr x at hi
          rw [show d i = 0 from if_neg hi,zero_mul]
        _ = ∑ i ∈ Fr x, c i * v i j := sum_congr rfl (fun i hi => by rw [show d i = c i from if_pos hi])
        _ = 0 := hbal j
    let step (i : I) := if 0 < d i then (1-x i)/d i else (-1-x i)/d i
    obtain ⟨a,ha,hMin⟩ := T.exists_min_image step hT
    have bounds (i : I) (hi : i ∈ T) : -1 < x i ∧ x i < 1 := by
      obtain ⟨hiS,hi1,hi0⟩ := mem_filter.mp (mem_filter.mp hi).1
      obtain ⟨hlo,hhi⟩ := hb i hiS
      exact ⟨lt_of_le_of_ne hlo (Ne.symm hi0),lt_of_le_of_ne hhi hi1⟩
    have hstep : 0 ≤ step a := by
      obtain ⟨hlo,hhi⟩ := bounds a ha
      by_cases hp : 0 < d a
      · simp only [step,if_pos hp]
        exact div_nonneg (by linarith) hp.le
      · simp only [step,if_neg hp]
        exact div_nonneg_of_nonpos (by linarith) (le_of_not_gt hp)
    let y (i : I) := x i + step a * d i
    have hy (i : I) (hi : i ∈ S) : -1 ≤ y i ∧ y i ≤ 1 := by
      by_cases ht : i ∈ T
      · have hsmall := hMin i ht
        obtain ⟨hlo,hhi⟩ := bounds i ht
        by_cases hp : 0 < d i
        · simp only [step,if_pos hp] at hsmall
          have hh := (le_div_iff₀ hp).mp hsmall
          have hn := mul_nonneg hstep hp.le
          dsimp [y]
          constructor <;> linarith
        · have hn : d i < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hne i ht)
          simp only [step,if_neg hp] at hsmall
          have hh := (le_div_iff_of_neg hn).mp hsmall
          have hs := mul_nonpos_of_nonneg_of_nonpos hstep hn.le
          dsimp [y]
          constructor <;> linarith
      · simpa [y,hvan i ht] using hb i hi
    have hybal (j : Fin n) : (∑ i ∈ S,y i * v i j) = 0 := by
      simp only [y,add_mul,mul_assoc,sum_add_distrib,← mul_sum,hbal' j,hz j,mul_zero,add_zero]
    have hsub : Fr y ⊆ Fr x := by
      intro i hi
      by_contra hf
      have ht : i ∉ T := fun ht => hf (mem_filter.mp ht).1
      have hh : y i = x i := by simp [y,hvan i ht]
      obtain ⟨hiS,hy1,hy0⟩ := mem_filter.mp hi
      exact hf (mem_filter.mpr ⟨hiS,hh ▸ hy1,hh ▸ hy0⟩)
    have haend : y a = 1 ∨ y a = -1 := by
      by_cases hp : 0 < d a
      · left
        simp only [y,step,if_pos hp]
        rw [div_mul_cancel₀ _ (hne a ha)]
        ring
      · right
        simp only [y,step,if_neg hp]
        rw [div_mul_cancel₀ _ (hne a ha)]
        ring
    have hproper : Fr y ⊂ Fr x :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun h =>
        have hh := mem_filter.mp (show a ∈ Fr y from h ▸ (mem_filter.mp ha).1)
        haend.elim hh.2.1 hh.2.2⟩
    exact ih (Fr y).card ((card_lt_card hproper).trans_le hx.le) y rfl hy hybal

/-- Euclidean sign balancing in dimension `n`, with a fixed offset. -/
theorem exists_euclidean_sign_balance {I : Type*} (S : Finset I) (n : ℕ)
    (v : I → Fin n → ℝ) (u : Fin n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ i ∈ S, energy (v i) ≤ C) :
    ∃ t : I → ℝ, (∀ i ∈ S, t i = 1 ∨ t i = -1) ∧
      energy (fun j => u j + ∑ i ∈ S,t i * v i j) ≤ energy u + n * C := by
  obtain ⟨x,hx,hz,hfrac⟩ := exists_sparse_fractional_balance S n v
  exact exists_signs_of_sparse_fractional_balance S v u x C n hx hz hv hC hfrac

end WeightedPaper
