import HybridCertificate

namespace WeightedPaper.Repair
open Finset
open scoped Classical
variable {I A B A₀ B₀ E T : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype A₀]
  [Fintype B₀] [Fintype E] [Fintype T] [DecidableEq I] [DecidableEq A₀] [DecidableEq B₀]
  [DecidableEq E] [Nonempty A₀]

noncomputable def pullback {V W : Type*} [Fintype V] (j : V ↪ W) (S : Finset W) :=
  univ.filter fun x => j x ∈ S

private noncomputable def freeCoordinates {V W : Type*} [Fintype V] (j : V ↪ W) (S : Finset W)
    (covers : ∀ v ∈ S, v ∈ Set.range j) : ↥(pullback j S) ≃ ↥S := by
  apply Equiv.ofBijective (fun x => ⟨j x.val,(mem_filter.mp x.property).2⟩)
  refine ⟨fun x y h => Subtype.ext (j.injective (congrArg Subtype.val h)),?_⟩
  intro v
  obtain ⟨x,e⟩ := covers _ v.property
  exact ⟨⟨x,mem_filter.mpr ⟨mem_univ _,e.symm ▸ v.property⟩⟩,Subtype.ext e⟩

/-- The hybrid host criterion at a fixed nibble threshold. The graph,
palette, and set of physical copies may all vary above this threshold. -/
def WeightedNibbleAt (δ Δ₀ : ℝ) : Prop :=
  ∀ {I A B A₀ B₀ E T : Type}
      [Fintype I] [Fintype A] [Fintype B] [Fintype A₀] [Fintype B₀] [Fintype E] [Fintype T]
      [DecidableEq I] [DecidableEq A₀] [DecidableEq B₀] [DecidableEq E] [Nonempty A₀],
    ∀ (cap leftCap rightCap ordinaryCap : A → B → ℕ)
    (l r : T → A ⊕ B) (loopless : ∀ e, l e ≠ r e) (seed : T → I) (D : ℕ),
    Fintype.card I ≤ D →
    (∀ a b, leftCap a b + rightCap a b + ordinaryCap a b ≤ cap a b) →
    ∀ (U : I → Finset A) (W : I → Finset B) (X : Finset A) (Y : Finset B)
      (jA : A₀ ↪ A) (jB : B₀ ↪ B) (a : E → A₀) (b : E → B₀)
      (R : A₀ → B₀ → Prop) [decR : DecidableRel R],
    (∀ x ∉ X, x ∈ Set.range jA) → (∀ y ∉ Y, y ∈ Set.range jB) →
    (∀ x y, ordinaryCapacity a b R x y ≤ ordinaryCap (jA x) (jB y)) →
    (∀ x, (univ.filter (fun e => l e = .inl x ∨ r e = .inl x)).card +
      ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.1 = x)).card = D) →
    (∀ y, (univ.filter (fun e => l e = .inr y ∨ r e = .inr y)).card +
      ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.2 = y)).card = D) →
    (∀ i x, (univ.filter (fun e => seed e = i ∧ (l e = .inl x ∨ r e = .inl x))).card =
      if x ∈ U i then 0 else 1) →
    (∀ i y, (univ.filter (fun e => seed e = i ∧ (l e = .inr y ∨ r e = .inr y))).card =
      if y ∈ W i then 0 else 1) →
    WeightedPaper.RowReserves U W leftCap univ X Y →
    WeightedPaper.RowReserves W U (fun y x => rightCap x y) univ Y X →
    (∀ (P : I → Finset (A × B)),
      (∀ x y, spending univ P x y ≤ leftCap x y + rightCap x y) →
      (∀ i, ∃ (f : ↥(U i ∩ X) ↪ ↥(W i \ Y)) (g : ↥(W i ∩ Y) ↪ ↥(U i \ X)),
        P i = pairsOf f ∪ transposePairs (pairsOf g)) →
      Nonempty (HybridCertificate δ Δ₀ a b R
        (fun i => pullback jA (remaining (U i) (P i)))
        (fun i => pullback jB (remaining (W i) (transposePairs (P i)))))) →
    HasSeededFactorization l r
      (fun e : CrossingCopy cap => e.1.1) (fun e : CrossingCopy cap => e.1.2) seed D

/-- Weighted exceptional reserves, the finite nibble hypotheses on the free
ordinary sets they leave, and (P) together yield a 1-factorization of the
entire host. Each pool is charged to the actual host multiplicity. -/
theorem factorization_from_weighted_nibble (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ Δ₀ : ℝ, WeightedNibbleAt δ Δ₀ := by
  classical
  obtain ⟨Δ₀,complete⟩ := ordinary_completion_of_hybrid δ hδ hδ'
  refine ⟨Δ₀,?_⟩
  unfold WeightedNibbleAt
  intro I A B A₀ B₀ E T _ _ _ _ _ _ _ _ _ _ _ _
  intro cap leftCap rightCap ordinaryCap l r loopless seed D kD capBound U W X Y jA jB a b R dec
    ordinaryA ordinaryB capOrd regA regB seedA seedB certA certB hybrid
  refine factorize_with_exceptional_reserves cap leftCap rightCap ordinaryCap capBound l r loopless seed D kD
    U W X Y regA regB (fun i x => ?_) (fun i y => ?_) certA certB ?_
  · convert seedA i x using 1 <;> first | (congr 1; ext; simp) | (split_ifs <;> rfl)
  · convert seedB i y using 1 <;> first | (congr 1; ext; simp) | (split_ifs <;> rfl)
  intro P bound matchP
  obtain ⟨H⟩ := hybrid P bound matchP
  obtain ⟨F,heap⟩ := complete a b R _ _ H
  have sep i : Disjoint (remaining (U i) (P i)) X ∧ Disjoint (remaining (W i) (transposePairs (P i))) Y := by
    obtain ⟨f,g,e⟩ := matchP i
    simpa only [← e] using (exceptional_rows (U i) (W i) X Y f g).2.2.2.2
  let L (i : I) := freeCoordinates jA (remaining (U i) (P i))
    (fun x hx => ordinaryA x (fun he => disjoint_left.mp (sep i).1 hx he))
  let J (i : I) := freeCoordinates jB (remaining (W i) (transposePairs (P i)))
    (fun y hy => ordinaryB y (fun he => disjoint_left.mp (sep i).2 hy he))
  let M (i : I) := (L i).symm.trans ((F i).trans (J i))
  have conv i x y : (jA x,jB y) ∈ pairsOf (M i) ↔ (x,y) ∈ pairsOf (F i) := by
    rw [mem_pairsOf,mem_pairsOf]
    constructor
    · rintro ⟨u,hu,hv⟩
      exact ⟨(L i).symm u,jA.injective ((congrArg Subtype.val ((L i).apply_symm_apply u)).trans hu),
        jB.injective hv⟩
    · rintro ⟨u,hu,hv⟩
      exact ⟨L i u,congrArg jA hu, by change jB (F i ((L i).symm (L i u))).val = _; rw [Equiv.symm_apply_apply,hv]⟩
  refine ⟨M,fun x y => ?_⟩
  by_cases hx : x ∈ Set.range jA
  · obtain ⟨x,rfl⟩ := hx
    by_cases hy : y ∈ Set.range jB
    · obtain ⟨y,rfl⟩ := hy
      have e : spending univ (fun i => pairsOf (M i)) (jA x) (jB y) =
          spending univ (fun i => pairsOf (F i)) x y := by simp only [spending,conv]
      rw [e]; exact (heap x y).trans (capOrd x y)
    · have e : (univ.filter fun i => (jA x,y) ∈ pairsOf (M i)) = ∅ := by
        ext i
        simp only [mem_filter,mem_univ,true_and,mem_pairsOf,notMem_empty,iff_false]
        rintro ⟨u,_,hv⟩
        exact hy ⟨(F i ((L i).symm u)).val,hv⟩
      simp [spending,e]
  · have e : (univ.filter fun i => (x,y) ∈ pairsOf (M i)) = ∅ := by
      ext i
      simp only [mem_filter,mem_univ,true_and,mem_pairsOf,notMem_empty,iff_false]
      rintro ⟨u,hu,_⟩
      exact hx ⟨((L i).symm u).val,(congrArg Subtype.val ((L i).apply_symm_apply u)).trans hu⟩
    simp [spending,e]
end WeightedPaper.Repair
