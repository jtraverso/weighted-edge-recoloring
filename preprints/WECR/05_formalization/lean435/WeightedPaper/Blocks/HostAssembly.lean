import WeightedPaper.Assembly

namespace WeightedPaper.RepairHost
open Finset SimpleGraph
open scoped Classical

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

noncomputable def graphPairs {U : Finset A} {W : Finset B} (f : U ≃ W) : Finset (A × B) :=
  univ.image (fun x : U => (x.val,(f x).val))

private theorem row {U : Finset A} {W : Finset B} (f : U ≃ W) (a : A) :
    (univ.filter fun b => (a,b) ∈ graphPairs f).card = if a ∈ U then 1 else 0 := by
  classical
  by_cases h : a ∈ U
  · have eq : (univ.filter fun b => (a,b) ∈ graphPairs f) = {(f ⟨a,h⟩).val} := by
      ext b
      simp only [mem_filter,mem_univ,true_and,graphPairs,mem_image,Prod.mk.injEq,mem_singleton]
      constructor
      · rintro ⟨x,hx,hy⟩
        exact hy.symm.trans (congrArg (fun z => (f z).val) (Subtype.ext hx))
      · rintro rfl; exact ⟨_,rfl,rfl⟩
    simp [eq,h]
  · have eq : (univ.filter fun b => (a,b) ∈ graphPairs f) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨x,_,he⟩ := mem_image.mp (mem_filter.mp hb).2
      have hx : x.val = a := congrArg Prod.fst he
      exact h (hx ▸ x.property)
    simp [eq,h]

private theorem col {U : Finset A} {W : Finset B} (f : U ≃ W) (b : B) :
    (univ.filter fun a => (a,b) ∈ graphPairs f).card = if b ∈ W then 1 else 0 := by
  have e a : (a,b) ∈ graphPairs f ↔ (b,a) ∈ graphPairs f.symm := by
    simp only [graphPairs,mem_image,mem_univ,true_and,Prod.mk.injEq]
    constructor
    · rintro ⟨x,rfl,rfl⟩; exact ⟨f x,rfl,by simp⟩
    · rintro ⟨y,rfl,rfl⟩; exact ⟨f.symm y,rfl,by simp⟩
  simpa only [e] using (row f.symm b)

private theorem merged_card {T : Type*} [Fintype T] [DecidableEq T] (S T' : Finset T)
    (u v : Prop) [Decidable u] [Decidable v] (s : S.card = if u then 1 else 0)
    (t : T'.card = if v then 1 else 0) (apart : ¬ (u ∧ v)) :
    (S ∪ T').card = if u ∨ v then 1 else 0 := by
  by_cases a : u
  · have b : ¬ v := fun hv => apart ⟨a,hv⟩
    have empty : T' = ∅ := card_eq_zero.mp (by simpa [b] using t)
    simpa [a,b,empty] using s
  · have empty : S = ∅ := card_eq_zero.mp (by simpa [a] using s)
    simpa [a,empty] using t

/-- Join the exceptional pairs and the repaired ordinary pairs, then reuse
the frozen regular bipartite residue theorem. Capacities count physical
copies across all colors. -/
theorem factorization_of_exceptional_and_ordinary_matchings {V : Type*} [Fintype V] [DecidableEq V]
    (M : MultiGraph V) (L : Finset V) (D k : ℕ) (hk : k ≤ D) (reg : M.IsRegularOfDegree D)
    (C : (M.internalPart L).EdgeColoring k)
    (U X : Fin k → Finset L) (W Y : Fin k → Finset (Lᶜ : Finset V))
    (exc : ∀ i, ↥(U i) ≃ ↥(W i)) (ord : ∀ i, ↥(X i) ≃ ↥(Y i))
    (left : ∀ i, U i ∪ X i = missingOn C L i) (right : ∀ i, W i ∪ Y i = missingOn C Lᶜ i)
    (apartL : ∀ i, Disjoint (U i) (X i)) (apartR : ∀ i, Disjoint (W i) (Y i))
    (cap : ∀ a b, spent (fun i => graphPairs (exc i)) univ a b +
      spent (fun i => graphPairs (ord i)) univ a b ≤ M.mult s(a.val,b.val)) :
    ∃ F : M.EdgeColoring D, F.IsFactorization := by
  classical
  apply exists_factorization_of_crossing_packing M L D k hk reg C
  let pairs (i) := graphPairs (exc i) ∪ graphPairs (ord i)
  refine ⟨pairs,?_,?_,?_⟩
  · intro i _ a
    simp only [← left, pairs, mem_union, filter_or]
    apply merged_card _ _ (a ∈ U i) (a ∈ X i) _ _ (fun h => disjoint_left.mp (apartL i) h.1 h.2)
    · convert row (exc i) a using 1 <;> first | (apply congrArg Finset.card; ext; simp) | (split_ifs <;> rfl)
    · convert row (ord i) a using 1 <;> first | (apply congrArg Finset.card; ext; simp) | (split_ifs <;> rfl)
  · intro i _ b
    simp only [← right, pairs, mem_union, filter_or]
    apply merged_card _ _ (b ∈ W i) (b ∈ Y i) _ _ (fun h => disjoint_left.mp (apartR i) h.1 h.2)
    · convert col (exc i) b using 1 <;> first | (apply congrArg Finset.card; ext; simp) | (split_ifs <;> rfl)
    · convert col (ord i) b using 1 <;> first | (apply congrArg Finset.card; ext; simp) | (split_ifs <;> rfl)
  · intro a b
    apply le_trans _ (cap a b)
    simp only [spent,pairs,mem_union,filter_or]
    exact card_union_le _ _
#print axioms factorization_of_exceptional_and_ordinary_matchings
end WeightedPaper.RepairHost
