import WeightedPaper.Blocks.BlockFactorization

namespace WeightedPaper
open Finset
open scoped Classical

variable {I A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']

private theorem memMap {T T' : Type*} (e : T ≃ T') (S : Finset T) (x : T') :
    x ∈ S.map e.toEmbedding ↔ e.symm x ∈ S := by
  simp only [mem_map,Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa
  · intro h
    exact ⟨e.symm x,h,e.apply_symm_apply x⟩

/-- Transport a capacity-respecting packing to two equivalent vertex types. -/
noncomputable def CrossingPacking.relabel {U : I → Finset A} {W : I → Finset B}
    {cap : A → B → ℕ} {K : Finset I} (P : CrossingPacking U W cap K)
    (a : A ≃ A') (b : B ≃ B') :
    CrossingPacking (fun i => (U i).map a.toEmbedding) (fun i => (W i).map b.toEmbedding)
      (fun x y => cap (a.symm x) (b.symm y)) K := by
  classical
  let M := fun i => (P.pairs i).map (Equiv.prodCongr a b).toEmbedding
  have memM (i : I) (x : A') (y : B') :
      (x,y) ∈ M i ↔ (a.symm x,b.symm y) ∈ P.pairs i := by
    change (x,y) ∈ (P.pairs i).map (Equiv.prodCongr a b).toEmbedding ↔ _
    rw [mem_map]
    constructor
    · rintro ⟨⟨p,q⟩,hp,hpq⟩
      change (a p,b q) = (x,y) at hpq
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hpq
      simpa using hp
    · intro h
      refine ⟨(a.symm x,b.symm y),h,?_⟩
      change (a (a.symm x),b (b.symm y)) = (x,y)
      simp
  refine ⟨M,?_,?_,?_⟩
  · intro i hi x
    have he : (univ.filter fun y => (x,y) ∈ M i) =
        (univ.filter fun y => (a.symm x,y) ∈ P.pairs i).map b.toEmbedding := by
      ext y
      simp only [mem_filter, mem_univ,true_and,memM,memMap]
    rw [he,card_map,P.row i hi]
    by_cases h : a.symm x ∈ U i
    · simp [h]
    · simp [h]
  · intro i hi y
    have he : (univ.filter fun x => (x,y) ∈ M i) =
        (univ.filter fun x => (x,b.symm y) ∈ P.pairs i).map a.toEmbedding := by
      ext x
      simp only [mem_filter, mem_univ,true_and,memM,memMap]
    rw [he,card_map,P.col i hi]
    by_cases h : b.symm y ∈ W i
    · simp [h]
    · simp [h]
  · intro x y
    have he : (K.filter fun i => (x,y) ∈ M i) = K.filter fun i => (a.symm x,b.symm y) ∈ P.pairs i := by
      ext i
      simp only [mem_filter,memM]
    unfold spent
    rw [he]
    exact P.bounded _ _

end WeightedPaper
