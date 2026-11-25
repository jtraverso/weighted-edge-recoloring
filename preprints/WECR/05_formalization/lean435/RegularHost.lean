import ExceptionalPacking
import PhysicalFactor

namespace WeightedPaper.Repair
open Finset
open scoped Classical

/-- The number of physical copies in a single endpoint pair. -/
abbrev CrossingCopy {A B : Type*} (cap : A → B → ℕ) :=
  Σ p : A × B, Fin (cap p.1 p.2)

variable {I A B E : Type*} [Fintype I] [Fintype A] [Fintype B] [Fintype E]

/-- Realize feasible spending by choosing distinct physical copies. -/
theorem realize_spending (cap : A → B → ℕ) (P : I → Finset (A × B))
    (bound : ∀ a b, spending univ P a b ≤ cap a b) :
    ∃ pick : (Σ p : A × B, ↥(univ.filter fun i => p ∈ P i)) ↪ CrossingCopy cap,
      ∀ p, (pick p).1 = p.1 := by
  classical
  have size (p : A × B) : Fintype.card ↥(univ.filter fun i => p ∈ P i) ≤ cap p.1 p.2 := by
    rcases p with ⟨a,b⟩
    simpa only [Fintype.card_coe,spending] using bound a b
  let emb (p : A × B) := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (size p))
  exact ⟨Function.Embedding.sigmaMap (Function.Embedding.refl _) emb,fun _ => rfl⟩

/-- A physical regular host has a specified set of internal copies and a
crossing pool indexed by its pair capacities. The internal coloring is
completed by a capacity-respecting family of crossing matchings. -/
theorem factorize_regular_host (cap : A → B → ℕ) (l r : E → A ⊕ B) (loopless : ∀ e, l e ≠ r e)
    (seed : E → I) (P : I → Finset (A × B)) (D : ℕ) (kD : Fintype.card I ≤ D)
    (regA : ∀ a, ((univ : Finset E).filter (fun e => l e = .inl a ∨ r e = .inl a)).card +
      ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.1 = a)).card = D)
    (regB : ∀ b, ((univ : Finset E).filter (fun e => l e = .inr b ∨ r e = .inr b)).card +
      ((univ : Finset (CrossingCopy cap)).filter (fun e => e.1.2 = b)).card = D)
    (row : ∀ i a, ((univ : Finset E).filter (fun e => seed e = i ∧ (l e = .inl a ∨ r e = .inl a))).card +
      (univ.filter (fun b => (a,b) ∈ P i)).card = 1)
    (col : ∀ i b, ((univ : Finset E).filter (fun e => seed e = i ∧ (l e = .inr b ∨ r e = .inr b))).card +
      (univ.filter (fun a => (a,b) ∈ P i)).card = 1)
    (bound : ∀ a b, spending univ P a b ≤ cap a b) :
    HasSeededFactorization l r
      (fun e : CrossingCopy cap => e.1.1) (fun e : CrossingCopy cap => e.1.2) seed D := by
  classical
  obtain ⟨pick,pivot⟩ := realize_spending cap P bound
  let J := Σ p : A × B, ↥(univ.filter fun i => p ∈ P i)
  let S := (univ : Finset J).map pick
  let inv (e : S) : J := Classical.choose (mem_map.mp e.property)
  have back (e : S) : pick (inv e) = e.val := (Classical.choose_spec (mem_map.mp e.property)).2
  let c (e : S) : I := (inv e).2.val
  have transport (i : I) (p : A × B → Prop) :
      (S.filter (fun e => ∃ h : e ∈ S, c ⟨e,h⟩ = i ∧ p e.1)).card = ((P i).filter p).card := by
    refine card_bij' (fun e _ => e.1) (fun q h => pick ⟨q,⟨i,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).1⟩⟩⟩) ?_ ?_ ?_ ?_
    · intro e he
      obtain ⟨h,hc,hp⟩ := (mem_filter.mp he).2
      let j := inv ⟨e,h⟩
      have ej : j.1 = e.1 := (pivot j).symm.trans (congrArg Sigma.fst (back ⟨e,h⟩))
      have used : j.1 ∈ P j.2.val := (mem_filter.mp j.2.property).2
      change j.2.val = i at hc
      exact mem_filter.mpr ⟨by simpa only [ej,hc] using used,hp⟩
    · intro q h
      let j : J := ⟨q,⟨i,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).1⟩⟩⟩
      have hs : pick j ∈ S := mem_map.mpr ⟨j,mem_univ _,rfl⟩
      have e : inv ⟨pick j,hs⟩ = j := pick.injective (back _)
      exact mem_filter.mpr ⟨hs,hs,by change (inv ⟨pick j,hs⟩).2.val = i; rw [e],by rw [pivot]; exact (mem_filter.mp h).2⟩
    · intro e he
      obtain ⟨h,hc,_⟩ := (mem_filter.mp he).2
      let j := inv ⟨e,h⟩
      have ej : j.1 = e.1 := (pivot j).symm.trans (congrArg Sigma.fst (back ⟨e,h⟩))
      change j.2.val = i at hc
      apply Eq.trans _ (back ⟨e,h⟩)
      apply congrArg pick
      exact Sigma.subtype_ext ej.symm hc.symm
    · intro q h
      exact pivot _
  have la i a : ((P i).filter (fun p => p.1 = a)).card = (univ.filter (fun b => (a,b) ∈ P i)).card := by
    refine card_bij' (fun p _ => p.2) (fun b _ => (a,b)) ?_ ?_ ?_ ?_
    · rintro ⟨x,y⟩ h
      obtain ⟨hp,e⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨mem_univ _,by simpa only [← e] using hp⟩
    · exact fun b h => mem_filter.mpr ⟨(mem_filter.mp h).2,rfl⟩
    · rintro ⟨x,y⟩ h
      exact Prod.ext (mem_filter.mp h).2.symm rfl
    · intros; rfl
  have lb i b : ((P i).filter (fun p => p.2 = b)).card = (univ.filter (fun a => (a,b) ∈ P i)).card := by
    refine card_bij' (fun p _ => p.1) (fun a _ => (a,b)) ?_ ?_ ?_ ?_
    · rintro ⟨x,y⟩ h
      obtain ⟨hp,e⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨mem_univ _,by simpa only [← e] using hp⟩
    · exact fun a h => mem_filter.mpr ⟨(mem_filter.mp h).2,rfl⟩
    · rintro ⟨x,y⟩ h
      exact Prod.ext rfl (mem_filter.mp h).2.symm
    · intros; rfl
  apply factorize_physical_seed l r (fun e : CrossingCopy cap => e.1.1) (fun e => e.1.2) seed S c D kD regA regB
  · intro i x
    convert row i x using 1
    convert congrArg (_ + ·) ((transport i (fun p => p.1=x)).trans (la i x)) using 2 <;> congr 1 <;> ext <;> simp
  · intro i y
    convert col i y using 1
    convert congrArg (_ + ·) ((transport i (fun p => p.2=y)).trans (lb i y)) using 2 <;> congr 1 <;> ext <;> simp
end WeightedPaper.Repair
