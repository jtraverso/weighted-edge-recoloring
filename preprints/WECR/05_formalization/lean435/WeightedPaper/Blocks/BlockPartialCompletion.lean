import WeightedPaper.Blocks.BlockDeficit
import WeightedPaper.Blocks.BlockTrim
import WeightedPaper.Blocks.BlockCutCriterion

namespace WeightedPaper.Blocks

open Finset
open scoped Classical

variable {I J A B : Type*} [Fintype J] [Fintype A] [Fintype B]

/-- A partial completion covers every free exceptional vertex, uses only
eligible assignments, and matches within the resulting blocks. -/
structure PartialCompletion (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (eA : A → J → Prop) (eB : B → J → Prop)
    (rel : A → B → Prop) where
  routeA : ↥(U ∩ X) → J
  routeB : ↥(W ∩ Y) → J
  eligibleA : ∀ x : ↥(U ∩ X), eA x (routeA x)
  eligibleB : ∀ y : ↥(W ∩ Y), eB y (routeB y)
  matchedA : Finset A
  matchedB : Finset B
  subsetA : matchedA ⊆ U
  subsetB : matchedB ⊆ W
  coversA : U ∩ X ⊆ matchedA
  coversB : W ∩ Y ⊆ matchedB
  pairing : matchedA ≃ matchedB
  edges : ∀ x : matchedA, rel x (pairing x) ∧
    extendAssignment U X left routeA x = extendAssignment W Y right routeB (pairing x)

noncomputable def completionDeficit (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (eA : A → J → Prop) (eB : B → J → Prop) : ℕ :=
  transportDeficit (fun (x : ↥(U ∩ X)) j => eA x j) (fun (y : ↥(W ∩ Y)) j => eB y j)
    (imbalance U W X Y left right)

/-- Both ordinary sides retain the threshold after any choice of eligible
assignment, even if all opposite exceptions use this block. -/
def CompletionWidth (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (threshold : J → ℕ) : Prop :=
  (∀ j, threshold j + (W ∩ Y).card ≤ (fiber (U \ X) left j).card) ∧
  (∀ j, threshold j + (U ∩ X).card ≤ (fiber (W \ Y) right j).card)

omit [Fintype J] [Fintype A] [Fintype B] in
private theorem remainder_eq_fiber_difference (U : Finset A) (W : Finset B)
    (X : Finset A) (Y : Finset B) (left : A → J) (right : B → J)
    (a : ↥(U ∩ X) → J) (b : ↥(W ∩ Y) → J) (j : J) :
    remainder (imbalance U W X Y left right) a b j =
      ((fiber U (extendAssignment U X left a) j).card : ℤ) -
        (fiber W (extendAssignment W Y right b) j).card := by
  classical
  have hA := card_sdiff_add_card_inter (fiber U (extendAssignment U X left a) j) X
  have hB := card_sdiff_add_card_inter (fiber W (extendAssignment W Y right b) j) Y
  rw [routed_ordinary,routed_exceptional] at hA hB
  simp only [remainder,assignedCount,imbalance,Finset.univ_eq_attach] at *
  omega

omit [Fintype A] in
private theorem count_loss_in_fibers (U P : Finset A) (label : A → J) (hP : P ⊆ U) :
    (∑ j, ((fiber U label j).card-(fiber P label j).card)) = U.card-P.card := by
  have gle (j : J) : (fiber P label j).card ≤ (fiber U label j).card :=
    card_le_card (fun x hx => mem_fiber.mpr ⟨hP (mem_fiber.mp hx).1,(mem_fiber.mp hx).2⟩)
  rw [sum_tsub_distrib _ (fun j _ => gle j),sum_fiber_card,sum_fiber_card]

omit [Fintype J] [Fintype A] [Fintype B] in
private theorem paired_fiber_cards {P : Finset A} {Q : Finset B} (f : P ≃ Q)
    (a : A → J) (b : B → J) (h : ∀ x : P, a x = b (f x)) (j : J) :
    (fiber P a j).card = (fiber Q b j).card := by
  classical
  apply card_bij (fun x hx => (f ⟨x,(mem_fiber.mp hx).1⟩).val)
  · intro x hx
    exact mem_fiber.mpr ⟨(f _).2,(h _).symm.trans (mem_fiber.mp hx).2⟩
  · intro x hx y hy he
    let x' : P := ⟨x,(mem_fiber.mp hx).1⟩
    let y' : P := ⟨y,(mem_fiber.mp hy).1⟩
    have hh : f x' = f y' := Subtype.ext he
    exact congrArg (fun z : P => z.val) (f.injective hh)
  · intro y hy
    let y' : Q := ⟨y,(mem_fiber.mp hy).1⟩
    let x := f.symm y'
    have hyx : f x = y' := f.apply_symm_apply y'
    have ha : a x = j := (h x).trans (by rw [hyx]; exact (mem_fiber.mp hy).2)
    exact ⟨x,mem_fiber.mpr ⟨x.2,ha⟩,congrArg (fun z : Q => z.val) hyx⟩

omit [Fintype A] [Fintype B] in
/-- Every eligible completion has at least the maximum cut deficit. -/
theorem completionDeficit_le_unmatched {U : Finset A} {W : Finset B} {X : Finset A} {Y : Finset B}
    {left : A → J} {right : B → J} {eA : A → J → Prop} {eB : B → J → Prop}
    {rel : A → B → Prop} (P : PartialCompletion U W X Y left right eA eB rel) :
    completionDeficit U W X Y left right eA eB ≤ U.card-P.matchedA.card := by
  classical
  let a := extendAssignment U X left P.routeA
  let b := extendAssignment W Y right P.routeB
  refine (transportDeficit_le_assignment _ _ _ P.routeA P.routeB P.eligibleA P.eligibleB).trans ?_
  unfold assignmentDeficit
  rw [← count_loss_in_fibers U P.matchedA a P.subsetA]
  apply sum_le_sum
  intro j _
  rw [remainder_eq_fiber_difference]
  have hEq := paired_fiber_cards P.pairing a b (fun x => (P.edges x).2) j
  have hB : (fiber P.matchedB b j).card ≤ (fiber W b j).card :=
    card_le_card (fun y hy => mem_fiber.mpr ⟨P.subsetB (mem_fiber.mp hy).1,(mem_fiber.mp hy).2⟩)
  change (↑(fiber U a j).card - (↑(fiber W b j).card : ℤ)).toNat ≤ _
  omega

omit [Fintype A] in
private theorem fiber_biUnion (U : Finset A) (f : A → J) (Q : J → Finset A)
    (hQ : ∀ j, Q j ⊆ fiber U f j) (j : J) :
    fiber (univ.biUnion Q) f j = Q j := by
  classical
  ext x
  rw [mem_fiber,mem_biUnion]
  constructor
  · rintro ⟨⟨j',_,hx⟩,hj⟩
    have hsame : j' = j := (mem_fiber.mp (hQ j' hx)).2.symm.trans hj
    exact hsame ▸ hx
  · intro hx
    exact ⟨⟨j,mem_univ _,hx⟩,(mem_fiber.mp (hQ j hx)).2⟩

omit [Fintype J] [Fintype A] in
private theorem hall_in_assigned_block (U : I → Finset A) (W : I → Finset B) (cap : A → B → ℕ)
    (K : Finset I) (X : Finset A) (Y : Finset B) (left : A → J) (right : B → J)
    (eligible : I → A → J → Prop) (rows : BlockReserves U W cap K X Y right eligible)
    (i : I) (hi : i ∈ K) (loss : A → B → ℕ)
    (hrow : ∀ x, (∑ y, loss x y) ≤ K.card-1)
    (a : ↥(U i ∩ X) → J) (b : ↥(W i ∩ Y) → J)
    (ha : ∀ x : ↥(U i ∩ X), eligible i x (a x)) (j : J)
    (S : Finset A) (hS : S ⊆ fiber (U i) (extendAssignment (U i) X left a) j ∩ X) :
    S.card ≤ ((fiber (W i) (extendAssignment (W i) Y right b) j \ Y).filter
      fun y => ∃ x ∈ S, 0 < cap x y-loss x y).card := by
  classical
  have hsub : S ⊆ ((U i).filter fun x => eligible i x j).filter (· ∈ X) := by
    intro x hx
    obtain ⟨hxf,hxX⟩ := mem_inter.mp (hS hx)
    obtain ⟨hxU,hxj⟩ := mem_fiber.mp hxf
    have hx' := mem_inter.mpr ⟨hxU,hxX⟩
    have hj : a ⟨x,hx'⟩ = j := by simpa [extendAssignment,hx'] using hxj
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hxU,hj ▸ ha ⟨x,hx'⟩⟩,hxX⟩
  apply ((rows j).hall i hi loss hrow S hsub).trans
  apply card_le_card
  intro y hy
  obtain ⟨hy₁,hyY,hyAdj⟩ := mem_filter.mp hy
  obtain ⟨hyW,hyj⟩ := mem_fiber.mp hy₁
  rw [routed_ordinary]
  exact mem_filter.mpr ⟨mem_fiber.mpr ⟨mem_sdiff.mpr ⟨hyW,hyY⟩,hyj⟩,hyAdj⟩

omit [Fintype J] [Fintype A] [Fintype B] in
private theorem assigned_block_width (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (threshold : J → ℕ)
    (width : CompletionWidth U W X Y left right threshold)
    (a : ↥(U ∩ X) → J) (b : ↥(W ∩ Y) → J) (j : J) :
    let P := fiber U (extendAssignment U X left a) j
    let Q := fiber W (extendAssignment W Y right b) j
    threshold j + (P ∩ X).card + (Q ∩ Y).card ≤ min P.card Q.card := by
  classical
  intro P Q
  have hPA : (P \ X).card = (fiber (U \ X) left j).card :=
    congrArg Finset.card (routed_ordinary U X left a j)
  have hQB : (Q \ Y).card = (fiber (W \ Y) right j).card :=
    congrArg Finset.card (routed_ordinary W Y right b j)
  have hPX : (P ∩ X).card ≤ (U ∩ X).card :=
    card_le_card (fun x hx => mem_inter.mpr ⟨(mem_fiber.mp (mem_inter.mp hx).1).1,(mem_inter.mp hx).2⟩)
  have hQY : (Q ∩ Y).card ≤ (W ∩ Y).card :=
    card_le_card (fun y hy => mem_inter.mpr ⟨(mem_fiber.mp (mem_inter.mp hy).1).1,(mem_inter.mp hy).2⟩)
  have hP := card_sdiff_add_card_inter P X
  have hQ := card_sdiff_add_card_inter Q Y
  have hA := width.1 j
  have hB := width.2 j
  omega

set_option maxHeartbeats 900000 in
/-- For a color and any allowable prior spending, the largest failed
cut is exactly the minimum number of unmatched vertices per side. -/
theorem exists_exact_deficit_completion (U : I → Finset A) (W : I → Finset B) (cap : A → B → ℕ)
    (K : Finset I) (X : Finset A) (Y : Finset B) (left : A → J) (right : B → J)
    (threshold : J → ℕ) (eligibleA : I → A → J → Prop) (eligibleB : I → B → J → Prop)
    (hrect : ∀ j, Rectangle cap (fiber (ordinary X) left j) (fiber (ordinary Y) right j) (threshold j) K.card)
    (rowsA : BlockReserves U W cap K X Y right eligibleA)
    (rowsB : BlockReserves W U (fun y x => cap x y) K Y X left eligibleB)
    (i : I) (hi : i ∈ K) (hUW : (U i).card = (W i).card)
    (width : CompletionWidth (U i) (W i) X Y left right threshold)
    (hA : ∀ x : ↥(U i ∩ X), ∃ j, eligibleA i x j)
    (hB : ∀ y : ↥(W i ∩ Y), ∃ j, eligibleB i y j)
    (loss : A → B → ℕ) (hrow : ∀ x, (∑ y, loss x y) ≤ K.card-1)
    (hcol : ∀ y, (∑ x, loss x y) ≤ K.card-1) :
    ∃ P : PartialCompletion (U i) (W i) X Y left right (eligibleA i) (eligibleB i)
        (fun x y => 0 < cap x y-loss x y),
      let d := completionDeficit (U i) (W i) X Y left right (eligibleA i) (eligibleB i)
      (U i).card-P.matchedA.card = d ∧ (W i).card-P.matchedB.card = d := by
  classical
  obtain ⟨a,b,ha,hb,hopt⟩ := exists_assignment_exact_deficit _ _
    (imbalance (U i) (W i) X Y left right) hA hB (sum_imbalance _ _ X Y left right hUW)
  let la := extendAssignment (U i) X left a
  let lb := extendAssignment (W i) Y right b
  let P j := fiber (U i) la j
  let Q j := fiber (W i) lb j
  let rel x y := 0 < cap x y-loss x y
  have hlocal (j : J) : ∃ P' ⊆ P j, ∃ Q' ⊆ Q j, (P j ∩ X) ⊆ P' ∧ (Q j ∩ Y) ⊆ Q' ∧
      P'.card = min (P j).card (Q j).card ∧ (∃ f : P' ≃ Q', ∀ x : P', rel x (f x)) := by
    apply trim_and_match_of_rectangle (P j) (Q j) X _ Y _ cap loss (threshold j) K.card
      (card_pos.mpr ⟨i,hi⟩) _ _ (assigned_block_width (U i) (W i) X Y left right threshold width a b j)
      hrow hcol _ _ (hrect j)
    · change fiber (U i) (extendAssignment (U i) X left a) j \ X ⊆ _
      rw [routed_ordinary]
      intro x hx
      obtain ⟨hxU,hxj⟩ := mem_fiber.mp hx
      exact mem_fiber.mpr ⟨(mem_ordinary X x).mpr (mem_sdiff.mp hxU).2,hxj⟩
    · change fiber (W i) (extendAssignment (W i) Y right b) j \ Y ⊆ _
      rw [routed_ordinary]
      intro y hy
      obtain ⟨hyW,hyj⟩ := mem_fiber.mp hy
      exact mem_fiber.mpr ⟨(mem_ordinary Y y).mpr (mem_sdiff.mp hyW).2,hyj⟩
    · exact hall_in_assigned_block U W cap K X Y left right eligibleA rowsA i hi loss hrow a b ha j
    · exact hall_in_assigned_block W U (fun y x => cap x y) K Y X right left eligibleB rowsB
        i hi (fun y x => loss x y) hcol b a hb j
  choose P' hP' Q' hQ' hPA hQB hcard hmatch using hlocal
  let UA := univ.biUnion P'
  let WB := univ.biUnion Q'
  have hUA : UA ⊆ U i := by
    intro x hx
    obtain ⟨j,_,hxj⟩ := mem_biUnion.mp hx
    exact (mem_fiber.mp (hP' j hxj)).1
  have hWB : WB ⊆ W i := by
    intro y hy
    obtain ⟨j,_,hyj⟩ := mem_biUnion.mp hy
    exact (mem_fiber.mp (hQ' j hyj)).1
  have hcoverA : U i ∩ X ⊆ UA := by
    intro x hx
    have hx' := mem_inter.mp hx
    exact mem_biUnion.mpr ⟨la x,mem_univ _,hPA _ (mem_inter.mpr ⟨mem_fiber.mpr ⟨hx'.1,rfl⟩,hx'.2⟩)⟩
  have hcoverB : W i ∩ Y ⊆ WB := by
    intro y hy
    have hy' := mem_inter.mp hy
    exact mem_biUnion.mpr ⟨lb y,mem_univ _,hQB _ (mem_inter.mpr ⟨mem_fiber.mpr ⟨hy'.1,rfl⟩,hy'.2⟩)⟩
  obtain ⟨f,hf⟩ := glue_matchings UA WB la lb (fun x y => rel x y ∧ la x = lb y) (by
    intro j
    rw [fiber_biUnion (U i) la P' hP' j,fiber_biUnion (W i) lb Q' hQ' j]
    obtain ⟨fj,hj⟩ := hmatch j
    exact ⟨fj,fun x => ⟨hj x,(mem_fiber.mp (hP' j x.2)).2.trans (mem_fiber.mp (hQ' j (fj x).2)).2.symm⟩⟩)
  let result : PartialCompletion (U i) (W i) X Y left right (eligibleA i) (eligibleB i) rel :=
    ⟨a,b,ha,hb,UA,WB,hUA,hWB,hcoverA,hcoverB,f,hf⟩
  refine ⟨result,?_⟩
  dsimp only [result]
  have he : (U i).card-UA.card = completionDeficit (U i) (W i) X Y left right (eligibleA i) (eligibleB i) := by
    unfold completionDeficit
    rw [← count_loss_in_fibers (U i) UA la hUA,← hopt]
    unfold assignmentDeficit
    apply sum_congr rfl
    intro j _
    rw [fiber_biUnion (U i) la P' hP' j,hcard,remainder_eq_fiber_difference]
    change (P j).card-min (P j).card (Q j).card = (↑(P j).card - (↑(Q j).card : ℤ)).toNat
    omega
  have hcards : UA.card = WB.card := by simpa only [Fintype.card_coe] using Fintype.card_congr f
  exact ⟨he,by rw [← hUW,← hcards]; exact he⟩

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.completionDeficit_le_unmatched
#print axioms WeightedPaper.Blocks.exists_exact_deficit_completion
