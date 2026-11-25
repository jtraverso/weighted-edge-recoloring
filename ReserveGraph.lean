module

public import SpectralRepair

@[expose] public section


namespace WeightedPaper.Repair
open Finset Matrix

/-- Counting requests over a physical coordinate gives the number of colors
in which that coordinate is free and missed. Each such color contributes once. -/
private theorem count_coordinates {I A B : Type*} [Fintype I] [Fintype A] [DecidableEq A] [DecidableEq B]
    (H : I → Finset A) (π : I → A ≃ B) (y : B) :
    (univ.filter (fun q : Σ i, ↥(H i) => π q.1 q.2.val = y)).card =
      (univ.filter (fun i => (π i).symm y ∈ H i)).card := by
  classical
  rw [card_eq_sum_ones, card_eq_sum_ones, sum_filter, Fintype.sum_sigma, sum_filter]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter,sum_const,nsmul_one]
  by_cases h : (π i).symm y ∈ H i
  · let x : ↥(H i) := ⟨(π i).symm y,h⟩
    have eq : (univ.filter fun z : ↥(H i) => π i z.val = y) = {x} := by
      ext z
      simp [x, Subtype.ext_iff, ← Equiv.eq_symm_apply]
    simp [h,eq]
  · have eq : (univ.filter fun z : ↥(H i) => π i z.val = y) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have e := (π i).injective ((mem_filter.mp hz).2.trans ((π i).apply_symm_apply y).symm)
      exact h (e ▸ z.property)
    simp [h,eq]

/-- Lemma 8 on a simple regular reserve with given matchings. The result is
a bijection of the actual free left and right sets for each color. Each pair
either comes from that color's old matching or uses a reserved physical edge.
The latter edge sets are disjoint over the whole palette. -/
theorem repair_in_regular_reserve {I A B : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B]
    (same : Fintype.card A = Fintype.card B)
    (R : A → B → Prop) [DecidableRel R] (d : ℕ) (hd : 0 < d)
    (regA : ∀ a, (univ.filter (R a)).card = d)
    (regB : ∀ b, (univ.filter (fun a => R a b)).card = d)
    (X U : I → Finset A) (Y W : I → Finset B)
    (leftFree : ∀ i, U i ⊆ X i) (rightFree : ∀ i, W i ⊆ Y i)
    (balanced : ∀ i, (X i).card = (Y i).card) (M : ∀ i, ↥(U i) ≃ ↥(W i))
    (σ ρ t : ℝ) (s0 : 0 ≤ σ) (s1 : σ ≤ 1) (r0 : 0 ≤ ρ) (t0 : 0 ≤ t)
    (op : ∀ f : A → ℝ, ∑ x, f x = 0 →
      (∑ y, (∑ x, f x * (if R x y then 1/(d:ℝ) else 0))^2) ≤ σ^2 * ∑ x, (f x)^2)
    (fnbr : ∀ i x, (((W i)ᶜ.filter (R x)).card : ℝ) ≤ ρ*d)
    (bnbr : ∀ i y, (((U i)ᶜ.filter (fun x => R x y)).card : ℝ) ≤ ρ*d)
    (starts : ∀ a, ((univ.filter (fun i => a ∈ X i \ U i)).card : ℝ) ≤ t)
    (ends : ∀ b, ((univ.filter (fun i => b ∈ Y i \ W i)).card : ℝ) ≤ t)
    (h : ℕ) (hh : 0 < h) (mix : σ^h ≤ 1/(2*(Fintype.card A : ℝ)))
    (budget1 : 3*(2*h : ℕ)*ρ ≤ 1/2)
    (budget2 : (2*(h:ℝ)+1)*(6*(2*t+(2*h-1 : ℕ)*(Fintype.card I : ℝ)*ρ)/d) +
      (2*(h:ℝ))*(6*(2*h : ℕ)*ρ) ≤ 4/27) :
    ∃ (alloc : I → Finset (A × B)) (F : ∀ i, ↥(X i) ≃ ↥(Y i)),
      (∀ i j, i ≠ j → Disjoint (alloc i) (alloc j)) ∧ ∀ i (a : ↥(X i)),
      (∃ ha : a.val ∈ U i, (F i a).val = (M i ⟨a.val,ha⟩).val) ∨
      (R a (F i a) ∧ (a.val,(F i a).val) ∈ alloc i) := by
  classical
  choose π keep matchSet freeSet using fun i => extend_matching_on_free_sets (X i) (U i) (Y i) (W i)
    (leftFree i) (rightFree i) same (balanced i) (M i)
  let P (a : A) (b : B) : ℝ := if R a b then 1/d else 0
  have D : 0 < (d:ℝ) := by exact_mod_cast hd
  have row a : ∑ b, P a b = 1 := by simp [P, ← sum_filter, regA, D.ne']
  have col b : ∑ a, P a b = 1 := by simp [P, ← sum_filter, regB, D.ne']
  have hn a b : 0 ≤ P a b := by dsimp [P]; split <;> positivity
  have cap a b : P a b ≤ 1/d := by dsimp [P]; split <;> first | exact le_rfl | positivity
  have norm (S : Finset A) (r : A → Prop) [DecidablePred r]
      (n : ((S.filter r).card : ℝ) ≤ ρ*d) : (∑ z ∈ S, if r z then 1/(d:ℝ) else 0) ≤ ρ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, ← div_eq_mul_one_div]
    exact (div_le_iff₀ D).mpr n
  have fw i x : ∑ z ∈ (U i)ᶜ, P x (π i z) ≤ ρ := by
    have e : ((U i)ᶜ.filter fun z => R x (π i z)).card = ((W i)ᶜ.filter (R x)).card := by
      apply card_bij' (fun a _ => π i a) (fun b _ => (π i).symm b)
      · intro a ha
        simpa [← matchSet] using ha
      · intro b hb
        simpa [matchSet] using hb
      · simp
      · simp
    exact norm _ (fun z => R x (π i z)) (by rw [e]; exact fnbr i x)
  have countEnd b :
      ((univ.filter (fun q : Σ i, ↥(X i \ U i) => π q.1 q.2.val = b)).card : ℝ) ≤ t := by
    rw [count_coordinates]
    simpa [mem_sdiff,freeSet,matchSet] using ends b
  have countStart (a : A) :
      ((univ.filter (fun q : Σ i, ↥(X i \ U i) => q.2.val = a)).card : ℝ) ≤ t := by
    have eq := count_coordinates (fun i => X i \ U i) (fun _ => Equiv.refl A) a
    have en : (univ.filter (fun q : Σ i, ↥(X i \ U i) => q.2.val = a)).card =
        (univ.filter fun i => a ∈ X i \ U i).card := eq
    rw [en]; exact starts a
  obtain ⟨alloc,F,disj,cover⟩ := spectral_repair_on_free_sets P hn row col σ ρ d t s0 s1 r0 D t0 cap op
    π X U leftFree fw (fun i y => norm _ (fun z => R z y) (bnbr i y))
    countStart
    countEnd h hh mix budget1 budget2
  let Z (i : I) := (F i).trans ((π i).subtypeEquiv (freeSet i))
  refine ⟨alloc,Z,disj,fun i a => ?_⟩
  rcases cover i a with ⟨ha,f⟩ | ⟨pos,useR⟩
  · refine Or.inl ⟨ha,?_⟩
    change π i (F i a).val = _
    rw [f]
    exact keep i ⟨a.val,ha⟩
  · refine Or.inr ⟨?_,useR⟩
    change R a.val (π i (F i a).val)
    by_contra no
    simp [P,no] at pos
end WeightedPaper.Repair
