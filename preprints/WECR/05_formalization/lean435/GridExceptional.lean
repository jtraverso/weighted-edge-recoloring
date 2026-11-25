import GridLayout
import HybridHost

namespace WeightedPaper.Repair.Grid
open Finset
open scoped Classical

variable {H W : Type} [Fintype H] [Fintype W]

private abbrev ordinaryIn : Ordinary H W ↪ Side H W := Function.Embedding.inl

noncomputable def exceptionSet : Finset (Side H W) :=
  (univ : Finset H).map Function.Embedding.inr

@[simp] theorem inr_mem_exceptionSet (h : H) : (Sum.inr h : Side H W) ∈ exceptionSet := by
  simp [exceptionSet]

@[simp] theorem inl_not_mem_exceptionSet (x : Ordinary H W) :
    (Sum.inl x : Side H W) ∉ exceptionSet := by
  simp [exceptionSet]

theorem ordinary_of_not_exception {v : Side H W} (h : v ∉ exceptionSet) :
    v ∈ Set.range (ordinaryIn : Ordinary H W ↪ Side H W) := by
  cases v with
  | inl x => exact ⟨x,rfl⟩
  | inr x => exact (h (inr_mem_exceptionSet x)).elim

def leftEndpoint : Fin 2 ↪ Ordinary H W := Function.Embedding.inl

def rightEndpoint : Fin 2 ↪ Ordinary H W :=
  Function.Embedding.inl.trans Function.Embedding.inr

noncomputable def gridFree (ends : Fin 2 ↪ Ordinary H W) : Finset (Side H W) :=
  univ.filter fun x => x ∉ (univ : Finset (Fin 2)).map (ends.trans ordinaryIn)

@[simp] theorem inl_mem_gridFree (ends : Fin 2 ↪ Ordinary H W) (x : Ordinary H W) :
    Sum.inl x ∈ gridFree ends ↔ x ∉ univ.map ends := by
  simp [gridFree, Function.Embedding.coe_trans, ordinaryIn]

@[simp] theorem inr_mem_gridFree (ends : Fin 2 ↪ Ordinary H W) (h : H) :
    Sum.inr h ∈ gridFree ends := by
  simp [gridFree, Function.Embedding.coe_trans, ordinaryIn]

@[simp] theorem mark_mem_gridFree (h : H) (c : Bool) :
    mark h c ∈ gridFree (leftEndpoint : Fin 2 ↪ Ordinary H W) ∧
      mark h c ∈ gridFree (rightEndpoint : Fin 2 ↪ Ordinary H W) := by
  simp [mark, leftEndpoint, rightEndpoint, Function.Embedding.coe_trans]

private theorem gridFree_inter_exception [DecidableEq (Side H W)] (ends : Fin 2 ↪ Ordinary H W) :
    gridFree ends ∩ exceptionSet = exceptionSet := by
  apply inter_eq_right.mpr
  intro x hx
  obtain ⟨h,_,rfl⟩ := mem_map.mp hx
  exact inr_mem_gridFree ends h

/-- Every exception can use its two switched ordinary coordinates. -/
noncomputable def exceptionCap (d : ℕ) (x y : Side H W) : ℕ :=
  if ∃ h c, x = Sum.inr h ∧ y = mark h c then d else 0

theorem grid_exception_capacities (R : Ordinary H W → Ordinary H W → Prop) (d : ℕ)
    (x y : Side H W) :
    exceptionCap d x y + exceptionCap d y x +
      (if ordinary R x y then 2 else 0) ≤ capacity R d x y := by
  unfold exceptionCap capacity
  split <;> split
  · rename_i hx hy
    obtain ⟨h,c,rfl,rfl⟩ := hx
    simp [mark] at hy
  · rename_i hx _
    obtain ⟨h,c,rfl,rfl⟩ := hx
    simp [static, mark]
  · rename_i _ hy
    obtain ⟨h,c,rfl,rfl⟩ := hy
    simp [static, mark]
  · omega

noncomputable def grid_exception_reserves (d : ℕ) (hd : 0 < d) (U V : Fin 2 ↪ Ordinary H W)
    (marksFree : ∀ h c, mark h c ∈ gridFree V) :
    WeightedPaper.RowReserves (fun _ : Fin d => gridFree U) (fun _ => gridFree V)
      (exceptionCap d) univ exceptionSet exceptionSet := by
  classical
  refine ⟨fun x y => (exceptionCap d x y : ℝ), fun _ => 1, d, by exact_mod_cast hd,
    fun _ _ => by norm_num, fun _ _ _ _ => by simp, ?_, ?_⟩
  · intro y _
    rw [show (exceptionSet : Finset (Side H W)) = univ.map Function.Embedding.inr from rfl, sum_map]
    have eq : (∑ h : H, (exceptionCap d (.inr h) y : ℝ)) =
        ∑ h : H, if ∃ c, y = mark h c then (d:ℝ) else 0 := by
      apply sum_congr rfl
      intro h _
      simp [exceptionCap]
    change (∑ h : H, (exceptionCap d (.inr h) y : ℝ)) ≤ _
    rw [eq, ← sum_filter, sum_const, nsmul_eq_mul]
    have atMost : (univ.filter fun (h : H) => ∃ c, y = mark h c).card ≤ 1 := by
      rw [card_le_one]
      intro h hh j hj
      obtain ⟨c,hc⟩ := (mem_filter.mp hh).2
      obtain ⟨e,he⟩ := (mem_filter.mp hj).2
      have eq := hc.symm.trans he
      simpa [mark, Prod.mk.injEq] using congrArg Prod.fst
        (show (h,c) = (j,e) by simpa [mark] using eq)
    have ha : ((univ.filter fun (h : H) => ∃ c, y = mark h c).card : ℝ) ≤ 1 := by
      exact_mod_cast atMost
    exact (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg d)).trans_eq (one_mul _)
  · intro i _ x hx
    have he : x ∈ (exceptionSet : Finset (Side H W)) := by
      simp only [mem_filter] at hx
      exact hx.2
    obtain ⟨h,_,rfl⟩ := mem_map.mp he
    have hne : (mark h false : Side H W) ≠ mark h true := by simp [mark]
    have hs : ({mark h false,mark h true} : Finset (Side H W)) ⊆
        (gridFree V).filter (· ∉ exceptionSet) := by
      intro y hy
      rcases mem_insert.mp hy with rfl|hy
      · exact mem_filter.mpr ⟨marksFree _ _, inl_not_mem_exceptionSet _⟩
      · obtain rfl := mem_singleton.mp hy
        exact mem_filter.mpr ⟨marksFree _ _, inl_not_mem_exceptionSet _⟩
    have mass := sum_le_sum_of_subset_of_nonneg (f := fun y => (exceptionCap d (.inr h) y : ℝ))
      hs (fun y _ _ => Nat.cast_nonneg _)
    have atMark c : exceptionCap d (.inr h) (mark h c : Side H W) = d := by
      rw [exceptionCap, ite_eq_left ⟨h,c,rfl,rfl⟩]
    rw [sum_insert (by simpa using hne), sum_singleton, atMark, atMark] at mass
    simp only [card_univ, Fintype.card_fin, mul_one]
    have dsub : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
    calc
      _ ≤ (d:ℝ)+d := by linarith
      _ ≤ _ := by
        convert mass using 2 <;> first | rfl | exact filter_congr_decidable _ _ _

/-- Any exceptional matching removes exactly one ordinary vertex per
opposite exception. The two internal endpoints are separate from them. -/
theorem grid_missing_ordinary [DecidableEq (Side H W)] (U V : Fin 2 ↪ Ordinary H W)
    (f : ↥(gridFree U ∩ exceptionSet) ↪ ↥(gridFree V \ exceptionSet))
    (g : ↥(gridFree V ∩ exceptionSet) ↪ ↥(gridFree U \ exceptionSet)) :
    ((pullback ordinaryIn (remaining (gridFree U) (pairsOf f ∪ transposePairs (pairsOf g))))ᶜ).card =
      Fintype.card H+2 := by
  classical
  let embed : ↥(gridFree V ∩ exceptionSet) ↪ Side H W :=
    g.trans ⟨Subtype.val, Subtype.val_injective⟩
  let taken := univ.map embed
  have takenOrd : ∀ v ∈ taken, v ∈ Set.range (ordinaryIn : Ordinary H W ↪ Side H W) := by
    intro v hv
    obtain ⟨a,_,rfl⟩ := mem_map.mp hv
    exact ordinary_of_not_exception (mem_sdiff.mp (g a).property).2
  let T := pullback ordinaryIn taken
  have mapT : T.map ordinaryIn = taken := by
    ext v
    constructor
    · intro hv
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
      simpa [T, pullback] using hx
    · intro hv
      obtain ⟨x,rfl⟩ := takenOrd v hv
      exact mem_map.mpr ⟨x,by simpa [T, pullback] using hv,rfl⟩
  have sizeT : T.card = Fintype.card H := by
    rw [← card_map (s := T) ordinaryIn, mapT, card_map, card_univ, Fintype.card_coe,
      gridFree_inter_exception]
    simp [exceptionSet]
  let P := pairsOf f ∪ transposePairs (pairsOf g)
  have hTaken (x : Ordinary H W) : Sum.inl x ∈ P.image Prod.fst ↔ x ∈ T := by
    constructor
    · intro hx
      obtain ⟨⟨u,v⟩,hu,eq⟩ := mem_image.mp hx
      change u = Sum.inl x at eq
      subst u
      rcases mem_union.mp hu with h|h
      · obtain ⟨a,ea,_⟩ := (mem_pairsOf f _ _).mp h
        exact (inl_not_mem_exceptionSet x (ea ▸ (mem_inter.mp a.property).2)).elim
      · obtain ⟨a,_,ea⟩ := (mem_pairsOf g _ _).mp ((mem_transposePairs _ _ _).mp h)
        have hxT : ordinaryIn x ∈ taken := mem_map.mpr ⟨a,mem_univ _,ea⟩
        simpa only [T, pullback, mem_filter, mem_univ, true_and] using hxT
    · intro hx
      have hm : ordinaryIn x ∈ taken := by simpa [T,pullback] using hx
      obtain ⟨a,_,ea⟩ := mem_map.mp hm
      refine mem_image.mpr ⟨(Sum.inl x,a.val),mem_union_right _ ?_,rfl⟩
      exact (mem_transposePairs _ _ _).mpr ((mem_pairsOf g _ _).mpr ⟨a,rfl,ea⟩)
  have sep : Disjoint (univ.map U) T := by
    apply disjoint_left.mpr
    intro x hx hxT
    have hm : ordinaryIn x ∈ taken := by simpa [T,pullback] using hxT
    obtain ⟨a,_,h⟩ := mem_map.mp hm
    have free : Sum.inl x ∈ gridFree U :=
      by rw [show Sum.inl x = (g a).val from h.symm]; exact (mem_sdiff.mp (g a).property).1
    exact (inl_mem_gridFree U x).mp free hx
  have same : (pullback ordinaryIn (remaining (gridFree U) P))ᶜ = univ.map U ∪ T := by
    ext x
    simp only [mem_compl, mem_union, pullback, mem_filter, mem_univ, true_and, remaining,
      mem_sdiff, Function.Embedding.inl_apply, inl_mem_gridFree, not_and_or, not_not]
    apply or_congr Iff.rfl
    simpa only [mem_image] using hTaken x
  change ((pullback ordinaryIn (remaining (gridFree U) P))ᶜ).card = _
  rw [same, card_union_of_disjoint sep, sizeT]
  simp [Nat.add_comm]

theorem grid_remaining_count [DecidableEq (Side H W)] (U V : Fin 2 ↪ Ordinary H W)
    (f : ↥(gridFree U ∩ exceptionSet) ↪ ↥(gridFree V \ exceptionSet))
    (g : ↥(gridFree V ∩ exceptionSet) ↪ ↥(gridFree U \ exceptionSet)) :
    (pullback ordinaryIn (remaining (gridFree U) (pairsOf f ∪ transposePairs (pairsOf g)))).card +
      (Fintype.card H+2) = Fintype.card (Ordinary H W) := by
  let S := pullback ordinaryIn (remaining (gridFree U) (pairsOf f ∪ transposePairs (pairsOf g)))
  have hs : (Sᶜ).card = Fintype.card H+2 := grid_missing_ordinary U V f g
  rw [← hs]
  exact card_add_card_compl S

end WeightedPaper.Repair.Grid
