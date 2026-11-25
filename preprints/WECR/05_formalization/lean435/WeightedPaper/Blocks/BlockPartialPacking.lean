import WeightedPaper.Blocks.BlockPartialCompletion

namespace WeightedPaper.Blocks

open Finset
open scoped Classical

variable {I J A B : Type*} [Fintype J] [Fintype A] [Fintype B]

section Completion

variable {U : Finset A} {W : Finset B} {X : Finset A} {Y : Finset B}
  {left : A → J} {right : B → J} {eA : A → J → Prop} {eB : B → J → Prop}
  {rel rel' : A → B → Prop}

omit [Fintype J] [Fintype A] [Fintype B] in
noncomputable def PartialCompletion.pairs (P : PartialCompletion U W X Y left right eA eB rel) :
    Finset (A × B) :=
  P.matchedA.attach.image (fun x => (x.val,(P.pairing x).val))

omit [Fintype J] [Fintype A] [Fintype B] in
theorem PartialCompletion.mem_pairs (P : PartialCompletion U W X Y left right eA eB rel) (x : A) (y : B) :
    (x,y) ∈ P.pairs ↔ ∃ hx : x ∈ P.matchedA, (P.pairing ⟨x,hx⟩).val = y := by
  classical
  constructor
  · intro h
    obtain ⟨z,_,hz⟩ := mem_image.mp h
    obtain ⟨he,hy⟩ := Prod.mk.inj hz
    subst x
    exact ⟨z.2,hy⟩
  · rintro ⟨hx,rfl⟩
    exact mem_image.mpr ⟨⟨x,hx⟩,mem_attach _ _,rfl⟩

omit [Fintype J] [Fintype B] in
theorem PartialCompletion.col_le_one (P : PartialCompletion U W X Y left right eA eB rel)
    (b : B) : (univ.filter fun a => (a,b) ∈ P.pairs).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxa,hxb⟩ := (P.mem_pairs _ _).mp (mem_filter.mp hx).2
  obtain ⟨hya,hyb⟩ := (P.mem_pairs _ _).mp (mem_filter.mp hy).2
  have e : P.pairing ⟨x,hxa⟩ = P.pairing ⟨y,hya⟩ := Subtype.ext (hxb.trans hyb.symm)
  exact congrArg (fun z : P.matchedA => z.val) (P.pairing.injective e)

omit [Fintype J] [Fintype A] in
theorem PartialCompletion.row_le_one (P : PartialCompletion U W X Y left right eA eB rel)
    (a : A) : (univ.filter fun b => (a,b) ∈ P.pairs).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨_,hxa⟩ := (P.mem_pairs _ _).mp (mem_filter.mp hx).2
  obtain ⟨_,hya⟩ := (P.mem_pairs _ _).mp (mem_filter.mp hy).2
  exact hxa.symm.trans hya

omit [Fintype J] [Fintype A] [Fintype B] in
def PartialCompletion.mono (P : PartialCompletion U W X Y left right eA eB rel)
    (h : ∀ a b, rel a b → rel' a b) :
    PartialCompletion U W X Y left right eA eB rel' :=
  { P with edges := fun x => ⟨h x (P.pairing x) (P.edges x).1,(P.edges x).2⟩ }

end Completion

omit [Fintype J] [Fintype A] in
private theorem spending_row (F : I → Finset (A × B)) (T : Finset I) (a : A)
    (h : ∀ i ∈ T, (univ.filter fun b => (a,b) ∈ F i).card ≤ 1) :
    (∑ b, spent F T a b) ≤ T.card := by
  classical
  simp only [spent,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro i hi
  simpa only [card_eq_sum_ones,sum_filter] using h i hi

omit [Fintype J] [Fintype B] in
private theorem spending_col (F : I → Finset (A × B)) (T : Finset I) (b : B)
    (h : ∀ i ∈ T, (univ.filter fun a => (a,b) ∈ F i).card ≤ 1) :
    (∑ a, spent F T a b) ≤ T.card := by
  classical
  simp only [spent,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro i hi
  simpa only [card_eq_sum_ones,sum_filter] using h i hi

set_option maxHeartbeats 950000 in
/-- All colors can attain their own exact deficit simultaneously, with
the total demand on each pair bounded by its original copy multiplicity. -/
theorem exists_optimal_partial_packing (U : I → Finset A) (W : I → Finset B) (cap : A → B → ℕ)
    (K : Finset I) (X : Finset A) (Y : Finset B) (left : A → J) (right : B → J)
    (threshold : J → ℕ) (eligibleA : I → A → J → Prop) (eligibleB : I → B → J → Prop)
    (hrect : ∀ j, Rectangle cap (fiber (ordinary X) left j) (fiber (ordinary Y) right j) (threshold j) K.card)
    (rowsA : BlockReserves U W cap K X Y right eligibleA)
    (rowsB : BlockReserves W U (fun y x => cap x y) K Y X left eligibleB)
    (hUW : ∀ i ∈ K, (U i).card = (W i).card)
    (width : ∀ i ∈ K, CompletionWidth (U i) (W i) X Y left right threshold)
    (hA : ∀ i ∈ K, ∀ x : ↥(U i ∩ X), ∃ j, eligibleA i x j)
    (hB : ∀ i ∈ K, ∀ y : ↥(W i ∩ Y), ∃ j, eligibleB i y j) :
    ∃ F : I → Finset (A × B), (∀ a b, spent F K a b ≤ cap a b) ∧
      ∀ i ∈ K, ∃ P : PartialCompletion (U i) (W i) X Y left right (eligibleA i) (eligibleB i)
          (fun a b => 0 < cap a b),
        F i = P.pairs ∧
        let d := completionDeficit (U i) (W i) X Y left right (eligibleA i) (eligibleB i)
        (U i).card-P.matchedA.card = d ∧ (W i).card-P.matchedB.card = d := by
  classical
  let Best (F : I → Finset (A × B)) (i : I) := ∃ P :
      PartialCompletion (U i) (W i) X Y left right (eligibleA i) (eligibleB i) (fun a b => 0 < cap a b),
      F i = P.pairs ∧
      let d := completionDeficit (U i) (W i) X Y left right (eligibleA i) (eligibleB i)
      (U i).card-P.matchedA.card = d ∧ (W i).card-P.matchedB.card = d
  suffices hs : ∀ T ⊆ K, ∃ F, (∀ a b, spent F T a b ≤ cap a b) ∧ ∀ i ∈ T, Best F i
    from hs K Subset.rfl
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => ∅,by simp [spent],by simp⟩
  | insert i T hi ih =>
    intro hK
    have hiK : i ∈ K := hK (mem_insert_self i T)
    obtain ⟨F,hcap,hBest⟩ := ih (fun _ hj => hK (mem_insert_of_mem hj))
    have hsize : T.card ≤ K.card-1 := by
      have h := card_le_card hK
      rw [card_insert_of_notMem hi] at h
      omega
    have hr (a : A) : (∑ b, spent F T a b) ≤ K.card-1 := by
      refine (spending_row F T a (fun j hj => ?_)).trans hsize
      obtain ⟨P,hF,_⟩ := hBest j hj
      rw [hF]
      exact P.row_le_one a
    have hc (b : B) : (∑ a, spent F T a b) ≤ K.card-1 := by
      refine (spending_col F T b (fun j hj => ?_)).trans hsize
      obtain ⟨P,hF,_⟩ := hBest j hj
      rw [hF]
      exact P.col_le_one b
    obtain ⟨P,hopt⟩ := exists_exact_deficit_completion U W cap K X Y left right threshold
      eligibleA eligibleB hrect rowsA rowsB i hiK (hUW i hiK) (width i hiK)
      (hA i hiK) (hB i hiK) (spent F T) hr hc
    let F' := Function.update F i P.pairs
    refine ⟨F',?_,?_⟩
    · intro a b
      have keep : (T.filter fun j => (a,b) ∈ F' j) = T.filter (fun j => (a,b) ∈ F j) := by
        apply filter_congr
        intro j hj
        simp [F',Function.update_of_ne (show j ≠ i from fun eq => hi (eq ▸ hj))]
      by_cases he : (a,b) ∈ P.pairs
      · obtain ⟨ha,hb⟩ := (P.mem_pairs _ _).mp he
        have hfree := (P.edges ⟨a,ha⟩).1
        rw [hb] at hfree
        change 0 < cap a b - spent F T a b at hfree
        rw [spent,filter_insert,show F' i = P.pairs by simp [F'],if_pos he,
          card_insert_of_notMem (fun h => hi (mem_filter.mp h).1),keep]
        unfold spent at hfree
        omega
      · rw [spent,filter_insert,show F' i = P.pairs by simp [F'],if_neg he,keep]
        exact hcap a b
    · intro j hj
      rcases mem_insert.mp hj with rfl|hj
      · let Q := P.mono (fun a b h => by omega : ∀ a b, 0 < cap a b-spent F T a b → 0 < cap a b)
        refine ⟨Q,?_,hopt⟩
        simp only [F',Function.update_self]
        rfl
      · obtain ⟨P,hF,hopt⟩ := hBest j hj
        exact ⟨P,by simpa [F',Function.update_of_ne (show j ≠ i from fun h => hi (h ▸ hj))] using hF,hopt⟩

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.exists_optimal_partial_packing
