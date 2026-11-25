module

public import RegularHost

@[expose] public section


namespace WeightedPaper.Repair
open Finset
open scoped Classical
variable {I A B E : Type*} [Fintype I] [Fintype A] [Fintype B] [Fintype E]

noncomputable def transposePairs (P : Finset (B × A)) : Finset (A × B) :=
  P.map (Equiv.prodComm B A).toEmbedding

@[simp] theorem mem_transposePairs (P : Finset (B × A)) (a : A) (b : B) :
    (a,b) ∈ transposePairs P ↔ (b,a) ∈ P := by
  simp [transposePairs,Equiv.prodComm_apply]

noncomputable def remaining (U : Finset A) (P : Finset (A × B)) :=
  U \ P.image Prod.fst

theorem pairsOf_col {X : Finset A} {Y : Finset B} (f : X ≃ Y) (b : B) :
    (univ.filter fun a => (a,b) ∈ pairsOf f).card = if b ∈ Y then 1 else 0 := by
  have eq (a : A) : (a,b) ∈ pairsOf f ↔ (b,a) ∈ pairsOf f.symm := by
    simp only [mem_pairsOf]
    constructor
    · rintro ⟨x,rfl,rfl⟩; exact ⟨f x,rfl,by simp⟩
    · rintro ⟨y,rfl,rfl⟩; exact ⟨f.symm y,rfl,by simp⟩
  simpa only [eq] using pairsOf_row f.symm b

private theorem merge_rows (U : Finset A) (P Q : Finset (A × B))
    (inside : P.image Prod.fst ⊆ U)
    (atMost : ∀ a, (univ.filter fun b => (a,b) ∈ P).card ≤ 1)
    (rest : ∀ a, (univ.filter fun b => (a,b) ∈ Q).card = if a ∈ remaining U P then 1 else 0) :
    ∀ a, (univ.filter fun b => (a,b) ∈ (P ∪ Q)).card = if a ∈ U then 1 else 0 := by
  intro a
  let u := univ.filter fun b => (a,b) ∈ P
  let v := univ.filter fun b => (a,b) ∈ Q
  have split : (univ.filter fun b => (a,b) ∈ (P ∪ Q)) = u ∪ v := by
    ext b; simp [u,v]
  have hit : a ∈ P.image Prod.fst ↔ u.Nonempty := by
    simp only [u,mem_image,Finset.Nonempty,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨⟨x,y⟩,hp,rfl⟩; exact ⟨y,hp⟩
    · exact fun ⟨b,hb⟩ => ⟨(a,b),hb,rfl⟩
  rw [split]
  by_cases h : a ∈ P.image Prod.fst
  · have hu : u.card = 1 := le_antisymm (atMost a) (card_pos.mpr (hit.mp h))
    have hv := rest a
    have notRest : a ∉ remaining U P := fun ha => (mem_sdiff.mp ha).2 h
    rw [ite_eq_right notRest] at hv
    have empty : v = ∅ := card_eq_zero.mp hv
    rw [empty,union_empty,hu,ite_eq_left (inside h)]
  · have empty : u = ∅ := not_nonempty_iff_eq_empty.mp (fun hn => h (hit.mpr hn))
    simpa [empty,remaining,h] using rest a

/-- The two orientations of exceptional matching have disjoint endpoints.
The remaining free sets contain only ordinary vertices. -/
theorem exceptional_rows (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (f : ↥(U ∩ X) ↪ ↥(W \ Y)) (g : ↥(W ∩ Y) ↪ ↥(U \ X)) :
    let P := pairsOf f ∪ transposePairs (pairsOf g)
    P.image Prod.fst ⊆ U ∧ (transposePairs P).image Prod.fst ⊆ W ∧
      (∀ a, (univ.filter fun b => (a,b) ∈ P).card ≤ 1) ∧
      (∀ b, (univ.filter fun a => (a,b) ∈ P).card ≤ 1) ∧
      Disjoint (remaining U P) X ∧ Disjoint (remaining W (transposePairs P)) Y := by
  intro P
  have edge (a : A) (b : B) (h : (a,b) ∈ P) :
      (a ∈ U ∩ X ∧ b ∈ W \ Y) ∨ (a ∈ U \ X ∧ b ∈ W ∩ Y) := by
    rcases mem_union.mp h with h|h
    · obtain ⟨u,rfl,rfl⟩ := (mem_pairsOf f _ _).mp h
      exact Or.inl ⟨u.property,(f u).property⟩
    · obtain ⟨u,rfl,rfl⟩ := (mem_pairsOf g _ _).mp ((mem_transposePairs _ _ _).mp h)
      exact Or.inr ⟨(g u).property,u.property⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rintro a ha
    obtain ⟨⟨x,y⟩,h,rfl⟩ := mem_image.mp ha
    rcases edge _ _ h with ⟨hx,_⟩|⟨hx,_⟩
    · exact (mem_inter.mp hx).1
    · exact (mem_sdiff.mp hx).1
  · rintro b hb
    obtain ⟨⟨y,x⟩,h,rfl⟩ := mem_image.mp hb
    rcases edge x y ((mem_transposePairs _ _ _).mp h) with ⟨_,hy⟩|⟨_,hy⟩
    · exact (mem_sdiff.mp hy).1
    · exact (mem_inter.mp hy).1
  · intro a
    by_cases ex : a ∈ X
    · have eq : (univ.filter fun b => (a,b) ∈ P) = univ.filter fun b => (a,b) ∈ pairsOf f := by
        ext b
        simp only [mem_filter,mem_univ,true_and,P,mem_union,mem_transposePairs]
        exact or_iff_left (fun h => by
          obtain ⟨u,_,e⟩ := (mem_pairsOf g _ _).mp h
          exact (mem_sdiff.mp (g u).property).2 (e.symm ▸ ex))
      rw [eq,pairsOf_row]
      split <;> omega
    · have eq : (univ.filter fun b => (a,b) ∈ P) = univ.filter fun b => (b,a) ∈ pairsOf g := by
        ext b
        simp only [mem_filter,mem_univ,true_and,P,mem_union,mem_transposePairs]
        exact or_iff_right (fun h => by
          obtain ⟨u,e,_⟩ := (mem_pairsOf f _ _).mp h
          exact ex (e ▸ (mem_inter.mp u.property).2))
      rw [eq]
      exact pairsOf_col_le g a
  · intro b
    by_cases ex : b ∈ Y
    · have eq : (univ.filter fun a => (a,b) ∈ P) = univ.filter fun a => (b,a) ∈ pairsOf g := by
        ext a
        simp only [mem_filter,mem_univ,true_and,P,mem_union,mem_transposePairs]
        exact or_iff_right (fun h => by
          obtain ⟨u,_,e⟩ := (mem_pairsOf f _ _).mp h
          exact (mem_sdiff.mp (f u).property).2 (e.symm ▸ ex))
      rw [eq,pairsOf_row]
      split <;> omega
    · have eq : (univ.filter fun a => (a,b) ∈ P) = univ.filter fun a => (a,b) ∈ pairsOf f := by
        ext a
        simp only [mem_filter,mem_univ,true_and,P,mem_union,mem_transposePairs]
        exact or_iff_left (fun h => by
          obtain ⟨u,e,_⟩ := (mem_pairsOf g _ _).mp h
          exact ex (e ▸ (mem_inter.mp u.property).2))
      rw [eq]
      exact pairsOf_col_le f b
  · apply disjoint_left.mpr
    intro a h ex
    obtain ⟨hu,notPa⟩ := mem_sdiff.mp h
    let u : ↥(U ∩ X) := ⟨a,mem_inter.mpr ⟨hu,ex⟩⟩
    exact notPa (mem_image.mpr ⟨(a,(f u).val),mem_union_left _ ((mem_pairsOf _ _ _).mpr ⟨u,rfl,rfl⟩),rfl⟩)
  · apply disjoint_left.mpr
    intro b h ex
    obtain ⟨hw,notPb⟩ := mem_sdiff.mp h
    let u : ↥(W ∩ Y) := ⟨b,mem_inter.mpr ⟨hw,ex⟩⟩
    apply notPb
    refine mem_image.mpr ⟨(b,(g u).val),?_,rfl⟩
    simp only [P,mem_transposePairs,mem_union]
    exact Or.inr ((mem_pairsOf _ _ _).mpr ⟨u,rfl,rfl⟩)

theorem spending_union_le (P Q : I → Finset (A × B)) (a : A) (b : B) :
    spending univ (fun i => P i ∪ Q i) a b ≤ spending univ P a b + spending univ Q a b := by
  simp only [spending,mem_union,filter_or]
  exact card_union_le _ _

/-- Choose exceptional matchings using weighted row certificates, then complete
the ordinary vertices with the provided capacity test. The test is applied to
the free sets left by the two selected exceptional matchings. -/
theorem factorize_with_exceptional_reserves (cap leftCap rightCap ordinaryCap : A → B → ℕ)
    (capBound : ∀ a b, leftCap a b + rightCap a b + ordinaryCap a b ≤ cap a b)
    (l r : E → A ⊕ B) (loopless : ∀ e, l e ≠ r e)
    (seed : E → I) (D : ℕ) (kD : Fintype.card I ≤ D)
    (U : I → Finset A) (W : I → Finset B) (X : Finset A) (Y : Finset B)
    (regA : ∀ a, (univ.filter (fun e => l e = .inl a ∨ r e = .inl a)).card +
      ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.1 = a)).card = D)
    (regB : ∀ b, (univ.filter (fun e => l e = .inr b ∨ r e = .inr b)).card +
      ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.2 = b)).card = D)
    (seedA : ∀ i a, (univ.filter (fun e => seed e = i ∧ (l e = .inl a ∨ r e = .inl a))).card =
      if a ∈ U i then 0 else 1)
    (seedB : ∀ i b, (univ.filter (fun e => seed e = i ∧ (l e = .inr b ∨ r e = .inr b))).card =
      if b ∈ W i then 0 else 1)
    (certA : WeightedPaper.RowReserves U W leftCap univ X Y)
    (certB : WeightedPaper.RowReserves W U (fun b a => rightCap a b) univ Y X)
    (ordinary : ∀ (P : I → Finset (A × B)),
      (∀ a b, spending univ P a b ≤ leftCap a b + rightCap a b) →
      (∀ i, ∃ (f : ↥(U i ∩ X) ↪ ↥(W i \ Y)) (g : ↥(W i ∩ Y) ↪ ↥(U i \ X)),
        P i = pairsOf f ∪ transposePairs (pairsOf g)) →
      ∃ (F : ∀ i, ↥(remaining (U i) (P i)) ≃ ↥(remaining (W i) (transposePairs (P i)))),
        ∀ a b, spending univ (fun i => pairsOf (F i)) a b ≤ ordinaryCap a b) :
    HasSeededFactorization l r
      (fun e : CrossingCopy cap => e.1.1) (fun e : CrossingCopy cap => e.1.2) seed D := by
  classical
  obtain ⟨L,mL,bL⟩ := pack_exceptional_rows U W leftCap univ X Y certA
  obtain ⟨R,mR,bR⟩ := pack_exceptional_rows W U (fun b a => rightCap a b) univ Y X certB
  let P i := L i ∪ transposePairs (R i)
  have matchP i : ∃ (f : ↥(U i ∩ X) ↪ ↥(W i \ Y)) (g : ↥(W i ∩ Y) ↪ ↥(U i \ X)),
      P i = pairsOf f ∪ transposePairs (pairsOf g) := by
    obtain ⟨f,hf⟩ := mL i (mem_univ _)
    obtain ⟨g,hg⟩ := mR i (mem_univ _)
    exact ⟨f,g,by simp only [P,hf,hg]⟩
  have excBound a b : spending univ P a b ≤ leftCap a b + rightCap a b := by
    have rev : spending univ (fun i => transposePairs (R i)) a b = spending univ R b a := by simp [spending]
    exact (spending_union_le L _ a b).trans (add_le_add (bL a b) (rev.symm ▸ bR b a))
  obtain ⟨F,bF⟩ := ordinary P excBound matchP
  let Q i := P i ∪ pairsOf (F i)
  have sep i : (P i).image Prod.fst ⊆ U i ∧ (transposePairs (P i)).image Prod.fst ⊆ W i ∧
      (∀ a, (univ.filter fun b => (a,b) ∈ P i).card ≤ 1) ∧
      (∀ b, (univ.filter fun a => (a,b) ∈ P i).card ≤ 1) ∧
      Disjoint (remaining (U i) (P i)) X ∧ Disjoint (remaining (W i) (transposePairs (P i))) Y := by
    obtain ⟨f,g,e⟩ := matchP i
    simpa only [← e] using exceptional_rows (U i) (W i) X Y f g
  apply factorize_regular_host cap l r loopless seed Q D kD regA regB
  · intro i a
    have h := merge_rows (U i) (P i) (pairsOf (F i)) (sep i).1 (sep i).2.2.1 (pairsOf_row (F i)) a
    simp only [Q,seedA,h]
    by_cases h : a ∈ U i <;> simp [h]
  · intro i b
    have h := merge_rows (W i) (transposePairs (P i)) (transposePairs (pairsOf (F i))) (sep i).2.1
      (fun b => by simpa using (sep i).2.2.2.1 b) (fun b => by simpa using pairsOf_col (F i) b) b
    have h' : (univ.filter fun (a : A) => (a,b) ∈ Q i).card = if b ∈ W i then 1 else 0 := by
      simpa [Q] using h
    simp only [seedB,h']
    by_cases h : b ∈ W i <;> simp [h]
  · intro a b
    exact (spending_union_le P _ a b).trans ((add_le_add (excBound a b) (bF a b)).trans (capBound a b))
end WeightedPaper.Repair
