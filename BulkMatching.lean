module

public import DemandTests
public import ReserveGraph

@[expose] public section


namespace WeightedPaper.Repair
open Finset
variable {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E]

/-- Recover the actual old matching and its physical copies for each color
of the bulk packing. -/
theorem matching_of_bulk (a : E → A) (b : E → B) (P : Finset (I × E))
    (pack : validPacking a b P) (i : I) :
    let C := covered a b P
    let U := univ.filter fun x => Sum.inl (i,x) ∈ C
    let W := univ.filter fun y => Sum.inr (Sum.inl (i,y)) ∈ C
    ∃ M : ↥U ≃ ↥W, ∀ x : ↥U, ∃ e, (i,e) ∈ P ∧ a e = x.val ∧ b e = (M x).val := by
  classical
  intro C U W
  have L x : x ∈ U ↔ ∃ e, (i,e) ∈ P ∧ a e = x := by
    simp only [U,C,covered,triple,mem_filter,mem_univ,true_and,mem_biUnion,mem_insert,
      mem_singleton,reduceCtorEq,or_false,Sum.inl.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨j,e⟩,hm,h,eq⟩; change i = j at h; subst j; exact ⟨e,hm,eq.symm⟩
    · rintro ⟨e,hm,rfl⟩; exact ⟨(i,e),hm,rfl,rfl⟩
  have R y : y ∈ W ↔ ∃ e, (i,e) ∈ P ∧ b e = y := by
    simp only [W,C,covered,triple,mem_filter,mem_univ,true_and,mem_biUnion,mem_insert,
      mem_singleton,reduceCtorEq,false_or,or_false,Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨j,e⟩,hm,h,eq⟩; change i = j at h; subst j; exact ⟨e,hm,eq.symm⟩
    · rintro ⟨e,hm,rfl⟩; exact ⟨(i,e),hm,rfl,rfl⟩
  have uniqueL e f (he : (i,e) ∈ P) (hf : (i,f) ∈ P) (eq : a e = a f) : e=f := by
    by_contra neq
    exact ((pack _ he _ hf (fun h => neq (congrArg Prod.snd h))).2 rfl).1 eq
  have uniqueR e f (he : (i,e) ∈ P) (hf : (i,f) ∈ P) (eq : b e = b f) : e=f := by
    by_contra neq
    exact ((pack _ he _ hf (fun h => neq (congrArg Prod.snd h))).2 rfl).2 eq
  choose f hf af using fun x : ↥U => (L x).1 x.property
  choose g hg bg using fun y : ↥W => (R y).1 y.property
  let F (x : ↥U) : ↥W := ⟨b (f x), (R _).2 ⟨_,hf x,rfl⟩⟩
  let G (y : ↥W) : ↥U := ⟨a (g y), (L _).2 ⟨_,hg y,rfl⟩⟩
  have left x : G (F x) = x := by
    apply Subtype.ext
    change a (g (F x)) = x.val
    rw [uniqueR _ _ (hg (F x)) (hf x) (bg (F x)), af]
  have right y : F (G y) = y := by
    apply Subtype.ext
    change b (f (G y)) = y.val
    rw [uniqueL _ _ (hf (G y)) (hg y) (af (G y)), bg]
  exact ⟨⟨F,G,left,right⟩,fun x => ⟨f x,hf x,af x,rfl⟩⟩

/-- Remove covered demands from an injectively labeled test. -/
private theorem test_difference {S T : Type*} [DecidableEq S] [DecidableEq T]
    (X : Finset S) (f : S → T) (inj : Function.Injective f) (C : Finset T) :
    (X.image f \ C).card = (X.filter fun x => f x ∉ C).card := by
  classical
  rw [← card_image_of_injective _ inj]
  congr 1
  ext t
  simp only [mem_sdiff,mem_image,mem_filter]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hc⟩
    exact ⟨x,⟨hx,hc⟩,rfl⟩
  · rintro ⟨x,⟨hx,hc⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,hc⟩

/-- Read the nibble's four test bounds in the coordinates used by Lemma 8. -/
theorem physical_test_bounds (a : E → A) (b : E → B) (P : Finset (I × E))
    (X : I → Finset A) (Y : I → Finset B) (N : A → Finset B) (N' : B → Finset A)
    (t s : ℝ)
    (test : ∀ j, ((demandTest X Y N N' j \ covered a b P).card : ℝ) ≤
      Sum.elim (fun _ => t) (fun _ => s) j) :
    let U (i : I) := univ.filter fun x => Sum.inl (i,x) ∈ covered a b P
    let W (i : I) := univ.filter fun y => Sum.inr (Sum.inl (i,y)) ∈ covered a b P
    (∀ x, ((univ.filter fun i => x ∈ X i \ U i).card : ℝ) ≤ t) ∧
    (∀ y, ((univ.filter fun i => y ∈ Y i \ W i).card : ℝ) ≤ t) ∧
    (∀ i x, ((N x ∩ (Y i \ W i)).card : ℝ) ≤ s) ∧
    (∀ i y, ((N' y ∩ (X i \ U i)).card : ℝ) ≤ s) := by
  intro U W
  refine ⟨fun x => ?_,fun y => ?_,fun i x => ?_,fun i y => ?_⟩
  · have h := test (.inl (.inl x))
    dsimp only [demandTest,Sum.elim] at h
    rw [test_difference _ _ (by intro i j e; simpa using e)] at h
    simpa [U,filter_filter] using h
  · have h := test (.inl (.inr y))
    dsimp only [demandTest,Sum.elim] at h
    rw [test_difference _ _ (by intro i j e; simpa using e)] at h
    simpa [W,filter_filter] using h
  · have h := test (.inr (.inl (i,x)))
    dsimp only [demandTest,Sum.elim] at h
    rw [test_difference _ _ (by intro a b e; simpa using e)] at h
    convert h using 2
    congr 1
    ext u
    simp [W,and_assoc]
  · have h := test (.inr (.inr (i,y)))
    dsimp only [demandTest,Sum.elim] at h
    rw [test_difference _ _ (by intro a b e; simpa using e)] at h
    convert h using 2
    congr 1
    ext u
    simp [U,and_assoc]
end WeightedPaper.Repair
