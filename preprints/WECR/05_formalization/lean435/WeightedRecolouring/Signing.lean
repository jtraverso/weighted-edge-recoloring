module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


namespace WeightedRecolouring
open Finset
open scoped Classical

private theorem choose_direction (x y B : ℝ) (hx : |x| ≤ B) (hy : |y| ≤ B) :
    ∃ t : ℝ, (t = 1 ∨ t = -1) ∧ |x+t*y| ≤ B := by
  by_cases hs : 0 ≤ x*y
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rcases nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg hs with h|h
    all_goals
      have ⟨hx₁,hx₂⟩ := abs_le.mp hx
      have ⟨hy₁,hy₂⟩ := abs_le.mp hy
      exact abs_le.mpr ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩
  · refine ⟨1, Or.inl rfl, ?_⟩
    rcases (mul_neg_iff.mp (lt_of_not_ge hs)) with h|h
    all_goals
      have ⟨hx₁,hx₂⟩ := abs_le.mp hx
      have ⟨hy₁,hy₂⟩ := abs_le.mp hy
      exact abs_le.mpr ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩

private theorem choose_pair {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → ℝ) (S : ℝ) (d : ℕ) (hcard : d+2 ≤ s.card) (hw : ∀ i∈s, |w i| ≤ S) :
    ∃ a∈s, ∃ b∈s, a≠b ∧ |w a-w b| ≤ (if d=0 then 2*S else S) := by
  classical
  have htwo : 1 < s.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp htwo
  by_cases hd : d=0
  · exact ⟨a,ha,b,hb,hab,by simpa [hd] using
      (abs_sub (w a) (w b)).trans (by linarith [hw a ha,hw b hb] : |w a|+|w b| ≤ 2*S)⟩
  · have habc : 0 < (s.erase a |>.erase b).card := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨hab.symm,hb⟩),card_erase_of_mem ha]
      omega
    obtain ⟨c,hc⟩ := card_pos.mp habc
    have hcb := (mem_erase.mp hc).1
    have hca := (mem_erase.mp (mem_erase.mp hc).2).1
    have hcs := (mem_erase.mp (mem_erase.mp hc).2).2
    have hp (i j : ι) (hi : i∈s) (hj : j∈s)
        (h : (0≤w i ∧ 0≤w j) ∨ (w i≤0 ∧ w j≤0)) :
        |w i-w j|≤S := by
      have ⟨hi₁,hi₂⟩ := abs_le.mp (hw i hi)
      have ⟨hj₁,hj₂⟩ := abs_le.mp (hw j hj)
      rcases h with h|h
      all_goals exact abs_le.mpr ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩
    simp only [if_neg hd]
    have hs (i j : ι) (hi : i∈s) (hj : j∈s) (h : (0≤w i) ↔ (0≤w j)) : |w i-w j|≤S := by
      by_cases hi' : 0≤w i
      · exact hp i j hi hj (Or.inl ⟨hi',h.mp hi'⟩)
      · exact hp i j hi hj (Or.inr ⟨le_of_not_ge hi',le_of_not_ge (hi' ∘ h.mpr)⟩)
    by_cases h : (0≤w a) ↔ (0≤w b)
    · exact ⟨a,ha,b,hb,hab,hs a b ha hb h⟩
    by_cases h' : (0≤w a) ↔ (0≤w c)
    · exact ⟨a,ha,c,hcs,hca.symm,hs a c ha hcs h'⟩
    exact ⟨b,hb,c,hcs,hcb.symm,hs b c hb hcs (by tauto)⟩

/-- An orientation of the odd paths, with the exact oriented surplus. -/
theorem exists_odd_signs {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (S : ℝ) (hS : 0≤S) (d n : ℕ) (hcard : s.card=d+2*n) (hw : ∀ i∈s, |w i| ≤ S) :
    ∃ f : ι → ℝ, (∀ i∈s, f i=1 ∨ f i= -1) ∧
      (∑ i∈s,f i)=d ∧ |∑ i∈s,f i*w i| ≤ if d=0 then 2*S else d*S := by
  classical
  let B : ℝ := if d=0 then 2*S else d*S
  change ∃ f : ι → ℝ, _ ∧ _ ∧ |∑ i∈s,f i*w i| ≤ B
  induction n generalizing s with
  | zero =>
    have hd : s.card=d := by omega
    refine ⟨fun _ => 1,fun _ _ => Or.inl rfl,by simp [hd],?_⟩
    have h := (abs_sum_le_sum_abs w s).trans
      (sum_le_sum (fun i hi => hw i hi) : (∑ i∈s,|w i|) ≤ ∑ _i∈s,S)
    simp only [sum_const,nsmul_eq_mul,hd] at h
    simp only [one_mul]
    by_cases hz : d=0
    · simpa [B,hz] using h.trans (show (d:ℝ)*S ≤ 2*S by simp [hz,hS])
    · simpa [B,hz] using h
  | succ n ih =>
    obtain ⟨a,ha,b,hb,hab,hpair⟩ := choose_pair s w S d (by omega) hw
    let t := (s.erase a).erase b
    have hba : b∈s.erase a := mem_erase.mpr ⟨hab.symm,hb⟩
    have ht : t.card=d+2*n := by
      simp only [t,card_erase_of_mem hba,card_erase_of_mem ha]
      omega
    have hex : ∀ i∈t, i≠a ∧ i≠b ∧ i∈s := by
      intro i hi
      have hb' := mem_erase.mp hi
      have ha' := mem_erase.mp hb'.2
      exact ⟨ha'.1,hb'.1,ha'.2⟩
    obtain ⟨f,hf,hsum,hbound⟩ := ih t ht (fun i hi => hw i (hex i hi).2.2)
    have hp : |w a-w b|≤B := by
      by_cases hz : d=0
      · simpa [B,hz] using hpair
      · have hd : (1:ℝ)≤d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        simp only [if_neg hz] at hpair
        simp only [B,if_neg hz]
        exact hpair.trans (by nlinarith)
    obtain ⟨c,hc,hchoice⟩ := choose_direction (∑ i∈t,f i*w i) (w a-w b) B hbound hp
    let g : ι → ℝ := fun i => if i=a then c else if i=b then -c else f i
    have hga : g a=c := by simp [g]
    have hgb : g b= -c := by simp [g,hab.symm]
    have hgt : ∀ i∈t, g i=f i := fun i hi => by simp [g,(hex i hi).1,(hex i hi).2.1]
    have hsplit (v : ι → ℝ) : (∑ i∈s,v i)=(∑ i∈t,v i)+v a+v b := by
      have h₁ := sum_erase_add s v ha
      have h₂ := sum_erase_add (s.erase a) v hba
      change (∑ i∈t,v i)+v b=(∑ i∈s.erase a,v i) at h₂
      linarith
    refine ⟨g,?_,?_,?_⟩
    · intro i hi
      by_cases hia : i=a
      · subst i
        rwa [hga]
      by_cases hib : i=b
      · subst i
        rw [hgb]
        rcases hc with h|h <;> simp [h]
      have hit : i∈t := mem_erase.mpr ⟨hib,mem_erase.mpr ⟨hia,hi⟩⟩
      rw [hgt i hit]
      exact hf i hit
    · rw [hsplit g,sum_congr rfl hgt,hsum,hga,hgb]
      ring
    · rw [hsplit (fun i => g i*w i),hga,hgb,
        sum_congr rfl (fun i hi => congrArg (· * w i) (hgt i hi))]
      convert hchoice using 2 <;> ring

/-- Freely oriented components can be added to a bounded partial sum. -/
theorem exists_free_signs {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (x B : ℝ) (hx : |x|≤B) (hw : ∀ i∈s,|w i|≤B) :
    ∃ f : ι → ℝ, (∀ i∈s,f i=1 ∨ f i= -1) ∧ |x+∑ i∈s,f i*w i|≤B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1,by simp,by simpa using hx⟩
  | insert a s ha ih =>
    obtain ⟨f,hf,hbound⟩ := ih (fun i hi => hw i (mem_insert_of_mem hi))
    obtain ⟨t,ht,hchoice⟩ := choose_direction _ (w a) B hbound (hw a (mem_insert_self _ _))
    let g : ι → ℝ := fun i => if i=a then t else f i
    refine ⟨g,?_,?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl|hi
      · simpa [g] using ht
      · have hne : i≠a := fun h => ha (h ▸ hi)
        simpa [g,hne] using hf i hi
    · rw [sum_insert ha]
      have he : (∑ i∈s,g i*w i)=∑ i∈s,f i*w i := by
        apply sum_congr rfl
        intro i hi
        have hne : i≠a := fun h => ha (h ▸ hi)
        simp [g,hne]
      rw [he,show g a=t by simp [g]]
      convert hchoice using 2 <;> ring

/-- Reorient any collection of components, preserving the total surplus. -/
theorem exists_component_swaps {ι : Type*} [DecidableEq ι] (s : Finset ι) (δ w : ι → ℝ)
    (S : ℝ) (hS : 0≤S) (d : ℕ) (hδ : ∀ i∈s, δ i=0 ∨ δ i=1 ∨ δ i= -1)
    (htotal : (∑ i∈s,δ i)=d) (hw : ∀ i∈s, |w i|≤S) :
    ∃ T ⊆ s, (∑ i∈T,δ i)=0 ∧
      |(∑ i∈s,w i)-2*(∑ i∈T,w i)|≤ if d=0 then 2*S else d*S := by
  classical
  let O := s.filter fun i => δ i≠0
  let E := s.filter fun i => δ i=0
  let N := O.filter fun i => δ i= -1
  let B : ℝ := if d=0 then 2*S else d*S
  have hsplit (f : ι → ℝ) : (∑ i∈O,f i)+(∑ i∈E,f i)=∑ i∈s,f i := by
    simpa [O,E] using sum_filter_add_sum_filter_not s (fun i => δ i≠0) f
  have hO (i : ι) (hi : i∈O) : δ i=1 ∨ δ i= -1 :=
    (hδ i (mem_filter.mp hi).1).resolve_left (mem_filter.mp hi).2
  have hδO : (∑ i∈O,δ i)=d := by
    have he : (∑ i∈E,δ i)=0 := sum_eq_zero (fun i hi => (mem_filter.mp hi).2)
    have hs := hsplit δ
    linarith
  have hcardR : (O.card:ℝ)=d+2*N.card := by
    have hpoint (i : ι) (hi : i∈O) : δ i=1-2*(if δ i= -1 then 1 else 0) := by
      rcases hO i hi with h|h <;> norm_num [h]
    have hsum := sum_congr (s₁:=O) rfl hpoint
    simp only [hδO,sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one] at hsum
    rw [←sum_filter, sum_const,nsmul_eq_mul,mul_one] at hsum
    change (d:ℝ)=(O.card:ℝ)-2*(N.card:ℝ) at hsum
    linarith
  have hcard : O.card=d+2*N.card := by exact_mod_cast hcardR
  obtain ⟨f,hf,hfs,hfb⟩ := exists_odd_signs O (fun i => δ i*w i) S hS d N.card hcard
    (fun i hi => by
      have hh := hw i (mem_filter.mp hi).1
      rcases hO i hi with h|h <;> simp [h,hh])
  have hSB : S≤B := by
    by_cases hd : d=0
    · simp [B,hd]; linarith
    · have hd' : (1:ℝ)≤d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
      simp only [B,if_neg hd]
      nlinarith
  obtain ⟨g,hg,hgb⟩ := exists_free_signs E w _ B hfb
    (fun i hi => (hw i (mem_filter.mp hi).1).trans hSB)
  let q : ι → ℝ := fun i => if δ i=0 then g i else f i*δ i
  have hqO (i : ι) (hi : i∈O) : q i=f i*δ i := by simp [q,(mem_filter.mp hi).2]
  have hqE (i : ι) (hi : i∈E) : q i=g i := by simp [q,(mem_filter.mp hi).2]
  have hq (i : ι) (hi : i∈s) : q i=1 ∨ q i= -1 := by
    by_cases h : δ i=0
    · exact (hqE i (mem_filter.mpr ⟨hi,h⟩)) ▸ hg i (mem_filter.mpr ⟨hi,h⟩)
    · have hiO : i∈O := mem_filter.mpr ⟨hi,h⟩
      rw [hqO i hiO]
      rcases hf i hiO with h₁|h₁ <;> rcases hO i hiO with h₂|h₂ <;> simp [h₁,h₂]
  have hcd : (∑ i∈s,q i*δ i)=d := by
    rw [←hsplit]
    have h1 : (∑ i∈O,q i*δ i)=∑ i∈O,f i := by
      apply sum_congr rfl
      intro i hi
      rw [hqO i hi]
      rcases hO i hi with h|h <;> simp [h]
    have h2 : (∑ i∈E,q i*δ i)=0 := sum_eq_zero (fun i hi => by simp [(mem_filter.mp hi).2])
    rw [h1,h2,hfs,add_zero]
  have hcb : |∑ i∈s,q i*w i|≤B := by
    rw [←hsplit,sum_congr rfl (fun i hi => congrArg (·*w i) (hqE i hi))]
    have h1 : (∑ i∈O,q i*w i)=∑ i∈O,f i*(δ i*w i) := by
      apply sum_congr rfl
      intro i hi
      rw [hqO i hi,mul_assoc]
    rwa [h1]
  let T := s.filter fun i => q i= -1
  have hr (v : ι → ℝ) : (∑ i∈s,q i*v i)=(∑ i∈s,v i)-2*∑ i∈T,v i := by
    rw [show T=s.filter _ from rfl,sum_filter, mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    rcases hq i hi with h|h <;> norm_num [h] <;> ring
  rw [hr,htotal] at hcd
  rw [hr] at hcb
  exact ⟨T, filter_subset _ _,by linarith,hcb⟩

end WeightedRecolouring
