module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! The incidence weights of several exceptional vertices may share an
ordinary endpoint. Hall counts the total weight in a column once. -/
namespace WeightedPaper.MultiCentreHall

open Finset
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem hall_of_column_budget (X : Finset A) (Y : Finset B) (w : A → B → ℕ)
    (L : ℕ) (hL : 0<L) (hrow : ∀ x∈X, L≤∑ y∈Y,w x y)
    (hcol : ∀ y∈Y, (∑ x∈X,w x y)≤L) (S : Finset A) (hSX : S⊆X) :
    S.card≤(Y.filter fun y => ∃ x∈S,0<w x y).card := by
  let N := Y.filter fun y => ∃ x∈S,0<w x y
  have hNY : N⊆Y := filter_subset _ _
  have hmass : (∑ y∈N,∑ x∈S,w x y)=∑ y∈Y,∑ x∈S,w x y := by
    apply sum_subset hNY
    intro y hy hn
    apply sum_eq_zero
    intro x hx
    exact Nat.eq_zero_of_not_pos (fun h => hn (mem_filter.mpr ⟨hy,x,hx,h⟩))
  have hh : S.card*L≤N.card*L := by
    calc
      _ = ∑ _x∈S,L := by simp
      _ ≤ ∑ x∈S,∑ y∈Y,w x y := sum_le_sum (fun x hx => hrow x (hSX hx))
      _ = ∑ y∈N,∑ x∈S,w x y := by rw [hmass,sum_comm]
      _ ≤ ∑ _y∈N,L := by
        apply sum_le_sum
        intro y hy
        exact (sum_le_sum_of_subset_of_nonneg hSX (fun _ _ _ => Nat.zero_le _)).trans
          (hcol y (hNY hy))
      _ = _ := by simp
  exact Nat.le_of_mul_le_mul_right hh hL

/-- Independent Hall guarantees for the two exceptional sets suffice.
Ordinary vertices on the two sides use complementary degree thresholds. -/
theorem exists_matching_of_exceptional_hall (R : A → B → Prop)
    (X : Finset A) (Y : Finset B) (dA dB : ℕ)
    (heq : Fintype.card A=Fintype.card B) (hd : Fintype.card A≤dA+dB)
    (hA : ∀ a∉X,dA≤(univ.filter fun b => b∉Y ∧ R a b).card)
    (hB : ∀ b∉Y,dB≤(univ.filter fun a => a∉X ∧ R a b).card)
    (hX : ∀ S⊆X,S.card≤(univ.filter fun b => b∉Y ∧ ∃ a∈S,R a b).card)
    (hY : ∀ T⊆Y,T.card≤(univ.filter fun a => a∉X ∧ ∃ b∈T,R a b).card) :
    ∃ f : A ≃ B, ∀ a,R a (f a) := by
  classical
  have hall (S : Finset A) : S.card≤(univ.filter fun b => ∃ a∈S,R a b).card := by
    let N := (univ : Finset B).filter fun b => ∃ a∈S,R a b
    change S.card≤N.card
    by_cases hSX : S⊆X
    · refine (hX S hSX).trans (card_le_card ?_)
      intro b hb
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hb).2.2⟩
    · obtain ⟨a,ha,hax⟩ : ∃ a∈S,a∉X := by
        simpa [subset_iff] using hSX
      by_cases hs : S.card≤dA
      · refine hs.trans ((hA a hax).trans (card_le_card ?_))
        intro b hb
        exact mem_filter.mpr ⟨mem_univ _,a,ha,(mem_filter.mp hb).2.2⟩
      · have hNY : Nᶜ⊆Y := by
          intro b hb
          by_contra hbY
          have hsub : (univ.filter fun a => a∉X ∧ R a b)⊆Sᶜ := by
            intro a ha
            apply mem_compl.mpr
            intro hmem
            exact (mem_compl.mp hb) (mem_filter.mpr
              ⟨mem_univ _,a,hmem,(mem_filter.mp ha).2.2⟩)
          have hh := (hB b hbY).trans (card_le_card hsub)
          have hSsize := card_le_univ S
          rw [card_compl] at hh
          omega
        have hsub : (univ.filter fun a => a∉X ∧ ∃ b∈Nᶜ,R a b)⊆Sᶜ := by
          intro a ha
          obtain ⟨b,hb,hrel⟩ := (mem_filter.mp ha).2.2
          exact mem_compl.mpr (fun hmem =>
            (mem_compl.mp hb) (mem_filter.mpr ⟨mem_univ _,a,hmem,hrel⟩))
        have hh := (hY Nᶜ hNY).trans (card_le_card hsub)
        have hNsize := card_le_univ N
        have hSsize := card_le_univ S
        rw [card_compl,card_compl] at hh
        omega
  obtain ⟨f,hf,hR⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hall
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,heq⟩),hR⟩

theorem exists_matching_of_column_budgets (R : A → B → Prop)
    (X : Finset A) (Y : Finset B) (dA dB LA LB : ℕ)
    (wA : A → B → ℕ) (wB : B → A → ℕ)
    (heq : Fintype.card A=Fintype.card B) (hd : Fintype.card A≤dA+dB)
    (hA : ∀ a∉X,dA≤(univ.filter fun b => b∉Y ∧ R a b).card)
    (hB : ∀ b∉Y,dB≤(univ.filter fun a => a∉X ∧ R a b).card)
    (hLA : 0<LA) (hLB : 0<LB)
    (hrowA : ∀ a∈X, LA≤∑ b∈Yᶜ,wA a b) (hcolA : ∀ b∉Y,(∑ a∈X,wA a b)≤LA)
    (hrowB : ∀ b∈Y, LB≤∑ a∈Xᶜ,wB b a) (hcolB : ∀ a∉X,(∑ b∈Y,wB b a)≤LB)
    (hrelA : ∀ a∈X,∀ b∉Y,0<wA a b → R a b)
    (hrelB : ∀ b∈Y,∀ a∉X,0<wB b a → R a b) :
    ∃ f : A ≃ B, ∀ a,R a (f a) := by
  apply exists_matching_of_exceptional_hall R X Y dA dB heq hd hA hB
  · intro S hS
    refine (hall_of_column_budget X Yᶜ wA LA hLA hrowA
      (fun b hb => hcolA b (mem_compl.mp hb)) S hS).trans (card_le_card ?_)
    intro b hb
    obtain ⟨bY,a,ha,hw⟩ := mem_filter.mp hb
    exact mem_filter.mpr ⟨mem_univ _,mem_compl.mp bY,a,ha,hrelA a (hS ha) b (mem_compl.mp bY) hw⟩
  · intro T hT
    refine (hall_of_column_budget Y Xᶜ wB LB hLB hrowB
      (fun a ha => hcolB a (mem_compl.mp ha)) T hT).trans (card_le_card ?_)
    intro a ha
    obtain ⟨aX,b,hb,hw⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_univ _,mem_compl.mp aX,b,hb,hrelB b (hT hb) a (mem_compl.mp aX) hw⟩

omit [Fintype B] [DecidableEq B] in
/-- A neighbor that is lost consumes at least one unit of the deletion budget. -/
theorem support_loss_under_spending (T : Finset B) (w spent : B → ℕ) :
    (T.filter fun v => 0<w v).card ≤
      (T.filter fun v => 0<w v-spent v).card+∑ v∈T,spent v := by
  classical
  rw [card_eq_sum_ones,card_eq_sum_ones,sum_filter,sum_filter,←sum_add_distrib]
  apply sum_le_sum
  intro v _
  by_cases h : 0<w v <;> by_cases h' : 0<w v-spent v <;> simp [h,h']; omega

omit [Fintype B] [DecidableEq B] in
theorem row_reserve_after_spending (T : Finset B) (w spent : B → ℕ) (L p : ℕ)
    (hrow : L+p≤∑ v∈T,w v) (hspent : (∑ v∈T,spent v)≤p) :
    L≤∑ v∈T,(w v-spent v) := by
  have h := sum_le_sum (s:=T) (fun v _ =>
    show w v≤w v-spent v+spent v by omega)
  rw [sum_add_distrib] at h
  omega

/-- Finish a colour using the actual residual support. Weighted incidence
may have been spent on earlier colours. Row reserves absorb that loss. -/
theorem exists_matching_after_spending (X : Finset A) (Y : Finset B)
    (w spent : A → B → ℕ) (dA dB LA LB pA pB : ℕ)
    (heq : Fintype.card A=Fintype.card B) (hd : Fintype.card A≤dA+dB)
    (hA : ∀ a∉X,dA≤(univ.filter fun b => b∉Y ∧ 0<w a b-spent a b).card)
    (hB : ∀ b∉Y,dB≤(univ.filter fun a => a∉X ∧ 0<w a b-spent a b).card)
    (hLA : 0<LA) (hLB : 0<LB)
    (hrowA : ∀ a∈X, LA+pA≤∑ b∈Yᶜ,w a b) (hcolA : ∀ b∉Y,(∑ a∈X,w a b)≤LA)
    (hrowB : ∀ b∈Y, LB+pB≤∑ a∈Xᶜ,w a b) (hcolB : ∀ a∉X,(∑ b∈Y,w a b)≤LB)
    (hspentA : ∀ a∈X,(∑ b∈Yᶜ,spent a b)≤pA)
    (hspentB : ∀ b∈Y,(∑ a∈Xᶜ,spent a b)≤pB) :
    ∃ f : A ≃ B, ∀ a,0<w a (f a)-spent a (f a) := by
  exact exists_matching_of_column_budgets (fun a b => 0<w a b-spent a b)
    X Y dA dB LA LB (fun a b => w a b-spent a b) (fun b a => w a b-spent a b)
    heq hd
    (fun a ha => by
      convert hA a ha using 1
      congr 1
      ext b
      simp only [mem_filter])
    (fun b hb => by
      convert hB b hb using 1
      congr 1
      ext a
      simp only [mem_filter])
    hLA hLB
    (fun a ha => row_reserve_after_spending Yᶜ _ _ LA pA (hrowA a ha) (hspentA a ha))
    (fun b hb => (sum_le_sum (fun a _ => Nat.sub_le _ _)).trans (hcolA b hb))
    (fun b hb => row_reserve_after_spending Xᶜ _ _ LB pB (hrowB b hb) (hspentB b hb))
    (fun a ha => (sum_le_sum (fun b _ => Nat.sub_le _ _)).trans (hcolB a ha))
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)

omit [Fintype A] [Fintype B] in
/-- Match the ordinary vertices left after fixing the exceptional matches.
The middle regime uses robust crossing neighborhoods from the original cut. -/
theorem exists_matching_of_robust_cut (A₀ U : Finset A) (B₀ W : Finset B)
    (R Q : A → B → Prop) (r t : ℕ)
    (hU : U⊆A₀) (hCard : U.card=W.card) (hLost : (B₀\W).card≤r)
    (hA : ∀ a∈U,t≤(W.filter (Q a)).card)
    (hB : ∀ b∈W,t≤(U.filter (fun a => Q a b)).card)
    (hEdge : ∀ b∈W,(U.filter (fun a => R a b ∧ ¬Q a b)).card<r)
    (hExpand : ∀ S⊆A₀,t≤S.card → S.card+t≤A₀.card →
      S.card+r≤(B₀.filter (fun b => r≤(S.filter (fun a => R a b)).card)).card) :
    ∃ f : U ≃ W,∀ a : U,Q a (f a) := by
  classical
  have hall (S : Finset A) (hS : S⊆U) : S.card≤(W.filter (fun b => ∃ a∈S,Q a b)).card := by
    let N := W.filter (fun b => ∃ a∈S,Q a b)
    change S.card≤N.card
    by_cases hSmall : S.card≤t
    · rcases S.eq_empty_or_nonempty with h|⟨a,ha⟩
      · simp [h]
      · refine hSmall.trans ((hA a (hS ha)).trans (card_le_card ?_))
        intro b hb
        exact mem_filter.mpr ⟨(mem_filter.mp hb).1,a,ha,(mem_filter.mp hb).2⟩
    · by_cases hLarge : A₀.card<S.card+t
      · have hN : N=W := by
          apply Subset.antisymm (filter_subset _ _)
          intro b hb
          by_contra hbn
          have hSub : (U.filter fun a => Q a b)⊆A₀\S := by
            intro a ha
            obtain ⟨hau,hab⟩ := mem_filter.mp ha
            exact mem_sdiff.mpr ⟨hU hau,fun has => hbn (mem_filter.mpr ⟨hb,a,has,hab⟩)⟩
          have hbnd := (hB b hb).trans (card_le_card hSub)
          rw [card_sdiff_of_subset (hS.trans hU)] at hbnd
          have hc := card_le_card (hS.trans hU)
          omega
        rw [hN,←hCard]
        exact card_le_card hS
      · let N₀ := B₀.filter (fun b => r≤(S.filter (fun a => R a b)).card)
        have hExpand' : S.card+r≤N₀.card := hExpand S (hS.trans hU) (by omega) (by omega)
        have hKeep : N₀∩W⊆N := by
          intro b hb
          obtain ⟨hb₀,hbW⟩ := mem_inter.mp hb
          by_contra hn
          have hSub : (S.filter (fun a => R a b))⊆U.filter (fun a => R a b ∧ ¬Q a b) := by
            intro a ha
            obtain ⟨haS,haR⟩ := mem_filter.mp ha
            exact mem_filter.mpr ⟨hS haS,haR,fun haQ => hn (mem_filter.mpr ⟨hbW,a,haS,haQ⟩)⟩
          have hc := ((mem_filter.mp hb₀).2).trans (card_le_card hSub)
          exact (not_lt_of_ge hc) (hEdge b hbW)
        have hCount := card_sdiff_add_card_inter N₀ W
        have hLost' : (N₀\W).card≤r := (card_le_card (sdiff_subset_sdiff
          (filter_subset _ _) (fun _ h => h))).trans hLost
        have hh := card_le_card hKeep
        omega
  have hall' (S : Finset U) :
      S.card≤(univ.filter fun b : W => ∃ a∈S,Q a b).card := by
    let E := S.image Subtype.val
    have hCard' : E.card=S.card :=
      card_image_of_injective S Subtype.val_injective
    have hEU : E⊆U := by
      intro a ha
      obtain ⟨b,_,rfl⟩ := mem_image.mp ha
      exact b.2
    have hh := hall E hEU
    rw [hCard'] at hh
    have hn : (univ.filter (fun b : W => ∃ a∈S,Q a b)).card =
        (W.filter (fun b => ∃ a∈E,Q a b)).card := by
      apply card_bij (fun b _ => b.val)
      · intro b hb
        obtain ⟨a,ha,hab⟩ := (mem_filter.mp hb).2
        exact mem_filter.mpr ⟨b.2,a.val,mem_image_of_mem Subtype.val ha,hab⟩
      · intro b _ c _ hc
        exact Subtype.ext hc
      · intro b hb
        obtain ⟨hbW,a,ha,hab⟩ := mem_filter.mp hb
        obtain ⟨a',ha',rfl⟩ := mem_image.mp ha
        exact ⟨⟨b,hbW⟩,mem_filter.mpr ⟨mem_univ _,a',ha',hab⟩,rfl⟩
    exact hh.trans_eq hn.symm
  obtain ⟨f,hf,hQ⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun a : U => fun b : W => Q a b)).mp hall'
  have heq : Fintype.card U=Fintype.card W := by simpa using hCard
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,heq⟩),hQ⟩

end WeightedPaper.MultiCentreHall

