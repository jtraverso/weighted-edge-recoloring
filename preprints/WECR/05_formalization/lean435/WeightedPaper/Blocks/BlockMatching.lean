import WeightedPaper.Cut.PairDegreeFactorization

namespace WeightedPaper.Blocks

open Finset SimpleGraph
open scoped Classical

variable {I J A B : Type*} [Fintype A] [Fintype B]

noncomputable def fiber (U : Finset A) (block : A → J) (j : J) : Finset A :=
  U.filter (fun x => block x = j)

omit [Fintype A] in
theorem mem_fiber {U : Finset A} {block : A → J} {j : J} {x : A} :
    x ∈ fiber U block j ↔ x ∈ U ∧ block x = j := mem_filter

/-- Every large nonempty ordinary rectangle contains a vertex with at least
`k` incident crossing copies in the rectangle. -/
def Rectangle (cap : A → B → ℕ) (L : Finset A) (R : Finset B)
    (threshold k : ℕ) : Prop :=
  ∀ S ⊆ L, ∀ T ⊆ R, S.Nonempty → T.Nonempty → threshold < S.card + T.card →
    (∃ x ∈ S, k ≤ ∑ y ∈ T, cap x y) ∨ (∃ y ∈ T, k ≤ ∑ x ∈ S, cap x y)

noncomputable def ordinary (X : Finset A) : Finset A := univ.filter (· ∉ X)

@[simp] theorem mem_ordinary (X : Finset A) (x : A) : x ∈ ordinary X ↔ x ∉ X := by
  simp [ordinary]

set_option maxHeartbeats 800000 in
/-- A local matching uses only the two exceptional Hall tests and the ordinary rectangle test. -/
theorem matching_of_rectangle (U : Finset A) (W : Finset B)
    (X L : Finset A) (Y R : Finset B) (cap loss : A → B → ℕ)
    (threshold k : ℕ) (hk : 0 < k)
    (hUW : U.card = W.card)
    (hL : U \ X ⊆ L) (hR : W \ Y ⊆ R)
    (hsize : threshold + (U ∩ X).card + (W ∩ Y).card ≤ U.card)
    (hrow : ∀ x, (∑ y, loss x y) ≤ k-1)
    (hcol : ∀ y, (∑ x, loss x y) ≤ k-1)
    (hexA : ∀ S ⊆ U ∩ X, S.card ≤ (W.filter fun y => ∃ x ∈ S, 0 < cap x y-loss x y).card)
    (hexB : ∀ T ⊆ W ∩ Y, T.card ≤ (U.filter fun x => ∃ y ∈ T, 0 < cap x y-loss x y).card)
    (H : Rectangle cap L R threshold k) :
    ∃ f : U ≃ W, ∀ x : U, 0 < cap x (f x)-loss x (f x) := by
  classical
  let Adj := fun x y => 0 < cap x y-loss x y
  let _ : DecidableRel Adj := fun x y => Classical.propDecidable (Adj x y)
  apply exists_equiv_of_finset_hall U W Adj hUW
  intro S hS
  let Z := W.filter fun y => ∃ x ∈ S, Adj x y
  let T := W \ Z
  by_contra! hBad
  change Z.card < S.card at hBad
  have hT : T ⊆ W := sdiff_subset
  have hsum : T.card + Z.card = W.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have hspent (x) (hx : x ∈ S) (y) (hy : y ∈ T) : cap x y ≤ loss x y := by
    have hn : ¬ Adj x y := fun h =>
      (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨hT hy,x,hx,h⟩)
    dsimp [Adj] at hn
    omega
  have hBadT : (U.filter fun x => ∃ y ∈ T, Adj x y).card < T.card := by
    have hsub : (U.filter fun x => ∃ y ∈ T, Adj x y) ⊆ U \ S := by
      intro x hx
      obtain ⟨hUx,y,hy,he⟩ := mem_filter.mp hx
      exact mem_sdiff.mpr ⟨hUx,fun h => Nat.not_lt_of_ge (hspent x h y hy) (Nat.sub_pos_iff_lt.mp he)⟩
    have hh := card_le_card hsub
    rw [card_sdiff_of_subset hS] at hh
    have hSU := card_le_card hS
    omega
  have hsX : (S \ X).Nonempty := by
    by_contra hn
    have hsub := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hn)
    apply Nat.not_le_of_gt hBad
    convert hexA S (fun _ hx => mem_inter.mpr ⟨hS hx,hsub hx⟩) using 2
    ext y
    simp [Z,Adj]
  have htY : (T \ Y).Nonempty := by
    by_contra hn
    have hsub := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hn)
    apply Nat.not_le_of_gt hBadT
    convert hexB T (fun _ hy => mem_inter.mpr ⟨hT hy,hsub hy⟩) using 2
    ext x
    simp [Adj]
  have hLarge : threshold < (S \ X).card + (T \ Y).card := by
    have h₁ := card_sdiff_add_card_inter S X
    have h₂ := card_sdiff_add_card_inter T Y
    have h₃ := card_le_card (show S ∩ X ⊆ U ∩ X from fun _ hz => mem_inter.mpr ⟨hS (mem_inter.mp hz).1,(mem_inter.mp hz).2⟩)
    have h₄ := card_le_card (show T ∩ Y ⊆ W ∩ Y from fun _ hz => mem_inter.mpr ⟨hT (mem_inter.mp hz).1,(mem_inter.mp hz).2⟩)
    omega
  rcases H (S \ X) (by
      intro x hx; exact hL (mem_sdiff.mpr ⟨hS (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩))
      (T \ Y) (by
      intro y hy; exact hR (mem_sdiff.mpr ⟨hT (mem_sdiff.mp hy).1,(mem_sdiff.mp hy).2⟩))
      hsX htY hLarge with ⟨x,hx,h⟩ | ⟨y,hy,h⟩
  · have hcap := sum_le_sum (s:=T \ Y) (fun y hy => hspent x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1)
    have hbudget := (sum_le_univ_sum_of_nonneg (s:=T \ Y) (fun y => Nat.zero_le (loss x y))).trans (hrow x)
    omega
  · have hcap := sum_le_sum (s:=S \ X) (fun x hx => hspent x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1)
    have hbudget := (sum_le_univ_sum_of_nonneg (s:=S \ X) (fun x => Nat.zero_le (loss x y))).trans (hcol y)
    omega

omit [Fintype A] [Fintype B] in
/-- Piecewise matching on disjoint fibers, preserving all original capacities. -/
theorem glue_matchings (U : Finset A) (W : Finset B) (aBlock : A → J) (bBlock : B → J)
    (Rel : A → B → Prop)
    (h : ∀ j, ∃ f : fiber U aBlock j ≃ fiber W bBlock j, ∀ x : fiber U aBlock j, Rel x (f x)) :
    ∃ f : U ≃ W, ∀ x : U, Rel x (f x) := by
  classical
  choose f hf using h
  let src (x : U) : fiber U aBlock (aBlock x) := ⟨x,mem_fiber.mpr ⟨x.2,rfl⟩⟩
  let map (x : U) : W := ⟨f (aBlock x) (src x), (mem_fiber.mp (f (aBlock x) (src x)).2).1⟩
  have hlabel (x : U) : bBlock (map x) = aBlock x :=
    (mem_fiber.mp (f (aBlock x) (src x)).2).2
  have transport (j j' : J) (hj : j = j') (u : fiber U aBlock j) (v : fiber U aBlock j')
      (huv : (u : A) = v) : (f j u : B) = f j' v := by
    subst j'
    exact congrArg (fun z : fiber U aBlock j => (f j z : B)) (Subtype.ext huv)
  have hinj : Function.Injective map := by
    intro x y hxy
    have same : aBlock x = aBlock y := (hlabel x).symm.trans ((congrArg (fun z : W => bBlock z) hxy).trans (hlabel y))
    let y' : fiber U aBlock (aBlock x) := ⟨y,mem_fiber.mpr ⟨y.2,same.symm⟩⟩
    have he : (f (aBlock x) (src x) : B) = f (aBlock y) (src y) := congrArg Subtype.val hxy
    have eqv := he.trans (transport _ _ same.symm (src y) y' rfl)
    have hout := (f (aBlock x)).injective (Subtype.ext eqv)
    exact Subtype.ext (congrArg (fun z : fiber U aBlock (aBlock x) => (z : A)) hout)
  have hsurj : Function.Surjective map := by
    intro y
    let dst : fiber W bBlock (bBlock y) := ⟨y,mem_fiber.mpr ⟨y.2,rfl⟩⟩
    let pre := (f (bBlock y)).symm dst
    have hp := mem_fiber.mp pre.2
    refine ⟨⟨pre,hp.1⟩,Subtype.ext ?_⟩
    have hh : (f (bBlock y) pre : B) = y := congrArg Subtype.val ((f (bBlock y)).apply_symm_apply dst)
    exact (transport _ _ hp.2 (src ⟨pre,hp.1⟩) pre rfl).trans hh
  exact ⟨Equiv.ofBijective map ⟨hinj,hsurj⟩,fun x => hf (aBlock x) (src x)⟩

end WeightedPaper.Blocks
