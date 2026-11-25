module

public import GalvinMultigraph.Local.Konig
public import Mathlib.Tactic

@[expose] public section


namespace WeightedPaper.Repair
open Finset
open scoped Classical

variable {I A B E C : Type*} [Fintype I] [Fintype A] [Fintype B] [Fintype E] [Fintype C]

/-- A factorization of identified copies that extends the given seed coloring
after embedding the seed palette in the final palette. -/
def HasSeededFactorization (l r : E → A ⊕ B) (a : C → A) (b : C → B)
    (seed : E → I) (D : ℕ) : Prop :=
  ∃ (rename : I ↪ Fin D) (color : E ⊕ C → Fin D),
    (∀ e, color (.inl e) = rename (seed e)) ∧
    ∀ (v : A ⊕ B) i,
      (univ.filter (fun e => color (.inl e) = i ∧ (l e = v ∨ r e = v))).card +
      (univ.filter (fun e => color (.inr e) = i ∧
        (Sum.inl (a e) = v ∨ Sum.inr (b e) = v))).card = 1

/-- A regular finite multigraph in the edge-copy model. The internal copies
are colored first. A physical subset S of crossing copies completes those
colors, and the complementary crossing copies are factored by Kőnig. -/
theorem factorize_physical_seed (l r : E → A ⊕ B) (a : C → A) (b : C → B)
    (initial : E → I) (S : Finset C) (chosen : S → I) (D : ℕ) (kD : Fintype.card I ≤ D)
    (regA : ∀ x, (univ.filter (fun e => l e = .inl x ∨ r e = .inl x)).card +
      (univ.filter (fun e => a e = x)).card = D)
    (regB : ∀ y, (univ.filter (fun e => l e = .inr y ∨ r e = .inr y)).card +
      (univ.filter (fun e => b e = y)).card = D)
    (row : ∀ i x, (univ.filter (fun e => initial e = i ∧ (l e = .inl x ∨ r e = .inl x))).card +
      (S.filter (fun e => ∃ h : e ∈ S, chosen ⟨e,h⟩ = i ∧ a e = x)).card = 1)
    (col : ∀ i y, (univ.filter (fun e => initial e = i ∧ (l e = .inr y ∨ r e = .inr y))).card +
      (S.filter (fun e => ∃ h : e ∈ S, chosen ⟨e,h⟩ = i ∧ b e = y)).card = 1) :
    HasSeededFactorization l r a b initial D := by
  classical
  let rem := D - Fintype.card I
  have residual (p : E → Prop) (q : C → Prop) (reg : (univ.filter p).card + (univ.filter q).card = D)
      (one : ∀ i, (univ.filter (fun e => initial e = i ∧ p e)).card +
        (S.filter (fun e => ∃ h : e ∈ S, chosen ⟨e,h⟩ = i ∧ q e)).card = 1) :
      (Sᶜ.filter q).card = rem := by
    have e1 : ∑ i, (univ.filter (fun e => initial e = i ∧ p e)).card = (univ.filter p).card := by
      simp_rw [and_comm (a := initial _ = _), ← filter_filter]
      simpa using (sum_card_fiberwise_eq_card_filter (univ.filter p) (univ : Finset I) initial)
    have e2 : ∑ i, (S.filter (fun e => ∃ h : e ∈ S, chosen ⟨e,h⟩ = i ∧ q e)).card =
        (S.filter q).card := by
      simp only [card_eq_sum_ones,sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      by_cases hq : q e
      · simp [he,hq]
      · simp [hq]
    have painted := sum_congr (s₁ := (univ : Finset I)) rfl fun i _ => one i
    rw [sum_add_distrib,e1,e2] at painted
    simp only [sum_const,card_univ,nsmul_one, Nat.cast_id] at painted
    have all : (S.filter q) ∪ (Sᶜ.filter q) = univ.filter q := by ext e; simp; tauto
    have sep : Disjoint (S.filter q) (Sᶜ.filter q) := by
      apply disjoint_left.mpr
      exact fun e he hf => mem_compl.mp (mem_filter.mp hf).1 (mem_filter.mp he).1
    have h := card_union_of_disjoint sep
    rw [all] at h
    dsimp [rem]
    have paintNat : (univ.filter p).card + (S.filter q).card = Fintype.card I := painted
    clear painted
    omega
  have dA (x : A) := residual (fun e => l e = .inl x ∨ r e = .inl x) (fun e => a e = x) (by convert regA x using 2 <;> congr 1 <;> ext <;> simp)
    (fun i => by convert row i x using 2 <;> congr 1 <;> ext <;> simp)
  have dB (y : B) := residual (fun e => l e = .inr y ∨ r e = .inr y) (fun e => b e = y) (by convert regB y using 2 <;> congr 1 <;> ext <;> simp)
    (fun i => by convert col i y using 2 <;> congr 1 <;> ext <;> simp)
  obtain ⟨f,less,proper⟩ := GalvinMultigraph.Local.konig_multigraph a b Sᶜ rem
    (fun x => (dA x).le) (fun y => (dB y).le)
  let rest (e : ↥(Sᶜ)) : Fin rem := ⟨f e,less e e.property⟩
  have rest_count (p : C → Prop) [DecidablePred p]
      (n : (Sᶜ.filter p).card = rem)
      (inj : ∀ u v : ↥(Sᶜ), p u → p v → rest u = rest v → u = v) (j : Fin rem) :
      (Sᶜ.filter (fun e => ∃ (he : e ∈ Sᶜ), rest ⟨e,he⟩ = j ∧ p e)).card = 1 := by
    let F := Sᶜ.filter p
    let g (e : F) := rest ⟨e.val,(mem_filter.mp e.property).1⟩
    have ginj : Function.Injective g := fun u v e => Subtype.ext
      (congrArg (fun z : ↥(Sᶜ) => z.val) (inj ⟨u.val,(mem_filter.mp u.property).1⟩ ⟨v.val,(mem_filter.mp v.property).1⟩
        (mem_filter.mp u.property).2 (mem_filter.mp v.property).2 e))
    have onto := ((Fintype.bijective_iff_injective_and_card g).2 ⟨ginj,by simpa using n⟩).2
    obtain ⟨e,he⟩ := onto j
    have eq : (Sᶜ.filter (fun e => ∃ (he : e ∈ Sᶜ), rest ⟨e,he⟩ = j ∧ p e)) = {e.val} := by
      ext u
      simp only [mem_filter,mem_singleton]
      constructor
      · rintro ⟨hu,_,h,p⟩
        exact congrArg Subtype.val (ginj (show g ⟨u,mem_filter.mpr ⟨hu,p⟩⟩ = g e from h.trans he.symm))
      · rintro rfl
        exact ⟨(mem_filter.mp e.property).1,_,he,(mem_filter.mp e.property).2⟩
    rw [eq,card_singleton]
  let K := I ⊕ Fin rem
  let color : E ⊕ C → K
    | .inl e => .inl (initial e)
    | .inr e => if h : e ∈ S then .inl (chosen ⟨e,h⟩) else .inr (rest ⟨e,mem_compl.mpr h⟩)
  let name : K ≃ Fin D := Fintype.equivFinOfCardEq (by simp [K,rem,Nat.add_sub_of_le kD])
  have selected (p : C → Prop) (i : I) :
      (univ.filter (fun e => color (.inr e) = .inl i ∧ p e)) =
      S.filter (fun e => ∃ h : e ∈ S, chosen ⟨e,h⟩ = i ∧ p e) := by
    ext e
    by_cases h : e ∈ S <;> simp [color,h,K,Sum.inl.injEq,Sum.inr.injEq]
  have unselected (p : C → Prop) (j : Fin rem) :
      (univ.filter (fun e => color (.inr e) = .inr j ∧ p e)) =
      Sᶜ.filter (fun e => ∃ h : e ∈ Sᶜ, rest ⟨e,h⟩ = j ∧ p e) := by
    ext e
    by_cases h : e ∈ S <;> simp [color,h,K,Sum.inl.injEq,Sum.inr.injEq]
  have injA x (u v : ↥(Sᶜ)) (hu : a u = x) (hv : a v = x) (e : rest u = rest v) : u = v := by
    apply Subtype.ext
    by_contra ne
    exact proper _ u.property _ v.property ne (Or.inl (hu.trans hv.symm)) (congrArg Fin.val e)
  have injB y (u v : ↥(Sᶜ)) (hu : b u = y) (hv : b v = y) (e : rest u = rest v) : u = v := by
    apply Subtype.ext
    by_contra ne
    exact proper _ u.property _ v.property ne (Or.inr (hu.trans hv.symm)) (congrArg Fin.val e)
  let rename : I ↪ Fin D := Function.Embedding.inl.trans name.toEmbedding
  refine ⟨rename, name ∘ color, fun _ => rfl, fun v j => ?_⟩
  have e : j = name (name.symm j) := (name.apply_symm_apply j).symm
  rw [e]
  simp only [Function.comp_apply,Equiv.apply_eq_iff_eq]
  rcases v with x|y <;> rcases name.symm j with i|i
  · simpa [color,selected,K,Sum.inl.injEq] using row i x
  · simpa [color,unselected] using rest_count (fun e => a e=x) (dA x) (injA x) i
  · simpa [color,selected,K,Sum.inr.injEq] using col i y
  · simpa [color,unselected] using rest_count (fun e => b e=y) (dB y) (injB y) i
end WeightedPaper.Repair
