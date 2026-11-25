import WeightedPaper.Blocks.BlockCutCriterion
import WeightedPaper.Blocks.BlockSpectral

namespace WeightedPaper.Blocks.Example

open Finset
open scoped Classical

abbrev Index (n : ℕ) := Fin (n+2)
abbrev Copy (n : ℕ) := Bool ⊕ Fin (2*n+4)
abbrev Ord (n : ℕ) := Index n × Copy n
abbrev Side (n : ℕ) := Bool ⊕ Ord n

variable {n : ℕ}

def first : Index n := ⟨0,by omega⟩
def second : Index n := ⟨1,by omega⟩

theorem different : (first : Index n) ≠ second := by
  intro h
  have := congrArg Fin.val h
  simp [first,second] at this

def blockOf (chosen : Index n) : Side n → Index n
  | .inl _ => chosen
  | .inr o => o.1

def exceptional : Finset (Side n) := univ.map Function.Embedding.inl

@[simp] theorem ex_left (b : Bool) : Sum.inl b ∈ exceptional (n:=n) := by
  simp [exceptional]

@[simp] theorem ex_right (a : Ord n) : Sum.inr a ∉ exceptional (n:=n) := by
  simp [exceptional]

@[simp] theorem ex_card : (exceptional (n:=n)).card = 2 := by simp [exceptional]

def uncovered (chosen : Index n) : Side n → Prop
  | .inr (j,.inl _) => j ≠ chosen
  | _ => True

noncomputable def free (chosen : Index n) : Finset (Side n) := univ.filter (uncovered chosen)

@[simp] theorem mem_free (chosen : Index n) (x : Side n) : x ∈ free chosen ↔ uncovered chosen x := by
  simp [free]

private def place (chosen j : Index n) : Copy n → Side n
  | .inl b => if j = chosen then .inl b else .inr (j,.inl b)
  | .inr i => .inr (j,.inr i)

private def augEmbed (chosen j : Index n) : Copy n ↪ Side n :=
  ⟨place chosen j,by
    intro a b h
    cases a <;> cases b <;> by_cases hj : j = chosen <;> simp_all [place]⟩

private theorem fiber_free (chosen j : Index n) :
    fiber (free chosen) (blockOf chosen) j = univ.map (augEmbed chosen j) := by
  classical
  ext x
  simp only [mem_fiber,mem_free,mem_map,mem_univ,true_and]
  cases x with
  | inl b =>
    change True ∧ chosen = j ↔ ∃ c, place chosen j c = .inl b
    constructor
    · intro h
      exact ⟨.inl b,by simp [place,h.2.symm]⟩
    · rintro ⟨c,h⟩
      cases c <;> by_cases hj : j = chosen <;> simp_all [place]
  | inr x =>
    obtain ⟨i,c⟩ := x
    constructor
    · rintro ⟨h,rfl⟩
      cases c with
      | inl b =>
        refine ⟨.inl b,?_⟩
        change place chosen i (.inl b) = _
        simp [place,show i ≠ chosen from h]
      | inr z =>
        exact ⟨.inr z,rfl⟩
    · rintro ⟨p,h⟩
      change place chosen j p = .inr (i,c) at h
      cases p with
      | inl b =>
        by_cases hj : j = chosen
        · simp [place,hj] at h
        · simp only [place,hj,if_false,Sum.inr.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          exact ⟨hj,rfl⟩
      | inr z =>
        simp only [place,Sum.inr.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ⟨trivial,rfl⟩

private theorem aug_card (chosen j : Index n) :
    (fiber (free chosen) (blockOf chosen) j).card = 2*n+6 := by
  rw [fiber_free,card_map,card_univ]
  simp [Fintype.card_sum]
  omega

private theorem free_ordinary_count (u j : Index n)
    (decideEx : DecidablePred (fun x : Side n => x ∉ exceptional)) :
    (@Finset.filter _ (· ∉ exceptional) decideEx (fiber (free u) (blockOf u) j)).card =
      if j = u then 2*n+4 else 2*n+6 := by
  classical
  rw [fiber_free,filter_map,card_map]
  by_cases h : j = u
  · rw [if_pos h]
    let e : Fin (2*n+4) ↪ Copy n := Function.Embedding.inr
    have he : (univ.filter ((· ∉ exceptional) ∘ augEmbed u j)) = univ.map e := by
      ext x
      cases x <;> simp [e,augEmbed,place,h]
    rw [he,card_map,card_univ,Fintype.card_fin]
  · rw [if_neg h,filter_true_of_mem]
    · simp [Fintype.card_sum]
      omega
    · intro x _
      change place u j x ∉ exceptional
      cases x <;> simp [place,h]

private theorem imbalance_count (u v j : Index n) :
    imbalance (free u) (free v) exceptional exceptional (blockOf u) (blockOf v) j =
      (if j = u then (2*n+4 : ℕ) else 2*n+6 : ℕ) -
      ((if j = v then (2*n+4 : ℕ) else 2*n+6 : ℕ) : ℤ) := by
  classical
  unfold imbalance
  have count (w : Index n) (de : DecidableEq (Side n)) :
      (fiber (@SDiff.sdiff _ (@Finset.instSDiff _ de) (free w) exceptional) (blockOf w) j).card =
        if j = w then 2*n+4 else 2*n+6 := by
    let _ : DecidableEq (Side n) := de
    have he : fiber (free w \ exceptional) (blockOf w) j =
        (fiber (free w) (blockOf w) j).filter (· ∉ exceptional) := by
      ext x
      simp only [mem_fiber,mem_sdiff,mem_filter,and_left_comm,and_comm]
    change (fiber (free w \ exceptional) (blockOf w) j).card = _
    rw [he]
    exact free_ordinary_count w j _
  rw [count u _, count v _]

/-- The free ordinary counts differ in opposite directions at the two
special blocks for every color of the internal seed. -/
theorem opposite_imbalances (n : ℕ) :
    let U : Finset (Side n) := free first
    let W : Finset (Side n) := free second
    imbalance U W exceptional exceptional (blockOf first) (blockOf second) first = -2 ∧
    imbalance U W exceptional exceptional (blockOf first) (blockOf second) second = 2 := by
  dsimp only
  constructor
  · rw [imbalance_count]
    simp [different]
  · rw [imbalance_count]
    simp [Ne.symm different]

private theorem enough_free (chosen j : Index n)
    (decideEx : DecidablePred (fun x : Side n => x ∉ exceptional)) :
    2*n+4 ≤ (@Finset.filter _ (· ∉ exceptional) decideEx (fiber (free chosen) (blockOf chosen) j)).card := by
  rw [free_ordinary_count]
  split <;> omega

private noncomputable def rows (cap : Side n → Side n → ℕ) (u v : Index n)
    (hcap : ∀ (e : Bool) (o : Ord n), 0 < cap (.inl e) (.inr o)) :
    BlockReserves (I:=Fin (n+1)) (fun _ => free u) (fun _ => free v) cap
      univ exceptional exceptional (blockOf v) (fun _ _ _ => True) := by
  classical
  intro j
  refine ⟨fun _ _ => 1,fun _ => 1,2,by norm_num,fun _ _ => by norm_num,?_,?_,?_⟩
  · intro x hx y hy
    cases x with
    | inl e =>
      cases y with
      | inl f => exact (hy (ex_left f)).elim
      | inr o =>
        have hh := hcap e o
        constructor
        · norm_num
        · simpa using (show (1:ℝ) ≤ (cap (.inl e) (.inr o) : ℝ) by exact_mod_cast hh)
    | inr o => exact ((ex_right o) hx).elim
  · intro y _
    simp
  · intro i _ x _
    simp only [card_univ,Fintype.card_fin,Nat.add_sub_cancel,sum_const,nsmul_eq_mul,mul_one]
    apply le_trans (show 2+(n:ℝ) ≤ (↑(2*n+4) : ℝ) by exact_mod_cast (show 2+n ≤ 2*n+4 by omega))
    exact_mod_cast (enough_free v j _)

private theorem size_of_aug_cards {A B : Type*} (U X : Finset A) (W Y : Finset B)
    (th : ℕ) (h : th + X.card + Y.card ≤ U.card) :
    th + (U ∩ X).card + (W ∩ Y).card ≤ U.card := by
  have h₁ := card_le_card (inter_subset_right : U ∩ X ⊆ X)
  have h₂ := card_le_card (inter_subset_right : W ∩ Y ⊆ Y)
  omega

private noncomputable def routing (u v : Index n) :
    Routing (free u) (free v) exceptional exceptional (blockOf u) (blockOf v)
      (fun _ => 2*n+2) (fun _ _ => True) (fun _ _ => True) := by
  classical
  exact {
  assignA := blockOf u
  assignB := blockOf v
  ordinaryA := fun _ _ => rfl
  ordinaryB := fun _ _ => rfl
  exceptionalA := fun _ _ => trivial
  exceptionalB := fun _ _ => trivial
  balance := fun j => (aug_card u j).trans (aug_card v j).symm
  size := by
    intro j
    apply size_of_aug_cards
    simp only [aug_card,ex_card]
    omega }


theorem packing (cap : Side n → Side n → ℕ)
    (hOrd : ∀ x y : Ord n, x.1 = y.1 → 0 < cap (.inr x) (.inr y))
    (hA : ∀ (e : Bool) (o : Ord n), 0 < cap (.inl e) (.inr o))
    (hB : ∀ (e : Bool) (o : Ord n), 0 < cap (.inr o) (.inl e)) :
    Nonempty (CrossingPacking (I:=Fin (n+1)) (fun _ => free first) (fun _ => free second) cap univ) := by
  classical
  apply packing_of_block_routing (fun _ => free first) (fun _ => free second) cap
    univ exceptional exceptional (blockOf first) (blockOf second) (fun _ => 2*n+2)
    (fun _ _ _ => True) (fun _ _ _ => True)
  · intro j
    simp only [card_univ,Fintype.card_fin]
    apply rectangle_of_complete_support _ _ _ _ _ (by omega)
    intro x hx y hy
    obtain ⟨hx₁,hx₂⟩ := mem_fiber.mp hx
    obtain ⟨hy₁,hy₂⟩ := mem_fiber.mp hy
    cases x with
    | inl e => exact (((mem_ordinary _ _).mp hx₁) (ex_left e)).elim
    | inr x =>
      cases y with
      | inl e => exact (((mem_ordinary _ _).mp hy₁) (ex_left e)).elim
      | inr y => exact hOrd x y (hx₂.trans hy₂.symm)
  · exact rows cap first second hA
  · exact rows (fun y x => cap x y) second first hB
  · exact fun _ _ => ⟨routing first second⟩

theorem original_pair_fails (cap : Side n → Side n → ℕ)
    (hZero : ∀ x y : Ord n, x.1 ≠ y.1 → cap (.inr x) (.inr y) = 0)
    (a k : ℕ) (hk : 0 < k) :
    ¬ PairDegreeCondition cap exceptional exceptional (Fintype.card (Side n)) a k := by
  classical
  let S : Finset (Side n) := (univ.filter fun x : Ord n => x.1 = first).map Function.Embedding.inr
  let T : Finset (Side n) := (univ.filter fun x : Ord n => x.1 ≠ first).map Function.Embedding.inr
  have hS : S ⊆ ordinary exceptional := by
    intro x hx
    obtain ⟨o,_,rfl⟩ := mem_map.mp hx
    exact (mem_ordinary _ _).mpr (ex_right o)
  have hT : T ⊆ ordinary exceptional := by
    intro x hx
    obtain ⟨o,_,rfl⟩ := mem_map.mp hx
    exact (mem_ordinary _ _).mpr (ex_right o)
  have hs : S.Nonempty := ⟨.inr (first,.inl false),mem_map.mpr ⟨_,by simp,rfl⟩⟩
  have ht : T.Nonempty := ⟨.inr (second,.inl false),mem_map.mpr ⟨_,by simp [Ne.symm different],rfl⟩⟩
  have hsum : S.card + T.card = Fintype.card (Ord n) := by
    simp only [S,T,card_map]
    simpa using (card_filter_add_card_filter_not (s := (univ : Finset (Ord n))) (fun x => x.1 = first))
  apply not_pair_degree_of_empty_rectangle cap _ _ S T hS hT hs ht _ a k hk
  · rw [Fintype.card_sum,hsum]
    simp
    omega
  · intro x hx y hy
    obtain ⟨u,hu,he⟩ := (mem_map (f := (Function.Embedding.inr : Ord n ↪ Side n))
      (s := univ.filter fun x : Ord n => x.1 = first)).mp hx
    obtain ⟨v,hv,he'⟩ := (mem_map (f := (Function.Embedding.inr : Ord n ↪ Side n))
      (s := univ.filter fun x : Ord n => x.1 ≠ first)).mp hy
    change Sum.inr u = x at he
    change Sum.inr v = y at he'
    subst x
    subst y
    exact hZero u v (fun he => (mem_filter.mp hv).2 (he.symm.trans (mem_filter.mp hu).2))

end WeightedPaper.Blocks.Example

#print axioms WeightedPaper.Blocks.Example.opposite_imbalances
#print axioms WeightedPaper.Blocks.Example.packing
#print axioms WeightedPaper.Blocks.Example.original_pair_fails
