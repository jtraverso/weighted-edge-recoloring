module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section


namespace WeightedPaper.Repair
open Finset

/-- Extend the given matching while pairing missed free vertices with missed
free vertices, and unavailable vertices with unavailable vertices. -/
theorem extend_matching_on_free_sets {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (freeA matchedA : Finset A) (freeB matchedB : Finset B) (ma : matchedA ⊆ freeA) (mb : matchedB ⊆ freeB)
    (same : Fintype.card A = Fintype.card B) (balance : freeA.card = freeB.card) (M : matchedA ≃ matchedB) :
    ∃ π : A ≃ B, (∀ x : matchedA, π x = (M x).val) ∧
      (∀ x, x ∈ matchedA ↔ π x ∈ matchedB) ∧ (∀ x, x ∈ freeA ↔ π x ∈ freeB) := by
  classical
  have mc : matchedA.card = matchedB.card := by simpa using Fintype.card_congr M
  let H : ↥(freeA \ matchedA) ≃ ↥(freeB \ matchedB) := Finset.equivOfCardEq (by
    rw [card_sdiff_of_subset ma, card_sdiff_of_subset mb, balance, mc])
  let U : ↥(univ \ freeA) ≃ ↥(univ \ freeB) := Finset.equivOfCardEq (by
    simp [card_sdiff_of_subset, balance, same])
  let f (x : A) : B := if hm : x ∈ matchedA then M ⟨x,hm⟩ else
    if hf : x ∈ freeA then H ⟨x,mem_sdiff.mpr ⟨hf,hm⟩⟩ else U ⟨x,mem_sdiff.mpr ⟨mem_univ _,hf⟩⟩
  have onto : Function.Surjective f := by
    intro y
    by_cases m : y ∈ matchedB
    · let x := M.symm ⟨y,m⟩
      exact ⟨x,by simp [f,x.property,x]⟩
    by_cases b : y ∈ freeB
    · let x := H.symm ⟨y,mem_sdiff.mpr ⟨b,m⟩⟩
      obtain ⟨ha,hm⟩ := mem_sdiff.mp x.property
      exact ⟨x,by simp [f,ha,hm,x]⟩
    · let x := U.symm ⟨y,mem_sdiff.mpr ⟨mem_univ _,b⟩⟩
      have h := (mem_sdiff.mp x.property).2
      have h' : x.val ∉ matchedA := fun h' => h (ma h')
      exact ⟨x,by simp [f,h,h',x]⟩
  let π := Equiv.ofBijective f ((Fintype.bijective_iff_surjective_and_card _).2 ⟨onto,same⟩)
  have parts (x : A) : (x ∈ matchedA ↔ f x ∈ matchedB) ∧ (x ∈ freeA ↔ f x ∈ freeB) := by
    by_cases hm : x ∈ matchedA
    · have hy := (M ⟨x,hm⟩).property
      simp [f,hm,ma hm,hy,mb hy]
    by_cases hf : x ∈ freeA
    · obtain ⟨hy,hn⟩ := mem_sdiff.mp (H ⟨x,mem_sdiff.mpr ⟨hf,hm⟩⟩).property
      simp [f,hm,hf,hy,hn]
    · have hy := (mem_sdiff.mp (U ⟨x,mem_sdiff.mpr ⟨mem_univ _,hf⟩⟩).property).2
      have hn := fun h => hy (mb h)
      simpa [f,hm,hf,hy] using hn
  exact ⟨π,fun x => by change f x = _; simp [f,x.property],fun x => (parts x).1,fun x => (parts x).2⟩
end WeightedPaper.Repair
