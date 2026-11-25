import BulkMatching

namespace WeightedPaper.Repair
open Finset Pseudorandom
variable {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E] [Nonempty A]

private theorem remaining_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (X U : Finset V) (r : V → Prop) [DecidablePred r] (β s d : ℝ) (hd : 0 < d)
    (initial : ((Xᶜ.filter r).card : ℝ) ≤ β*d)
    (missed : (((univ.filter r) ∩ (X \ U)).card : ℝ) ≤ s) :
    ((Uᶜ.filter r).card : ℝ) ≤ (β+s/d)*d := by
  have sub : Uᶜ.filter r ⊆ (Xᶜ.filter r) ∪ ((univ.filter r) ∩ (X \ U)) := by
    intro x hx
    obtain ⟨hu,hr⟩ := mem_filter.mp hx
    by_cases hf : x ∈ X
    · exact mem_union_right _ (mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hr⟩,mem_sdiff.mpr ⟨hf,mem_compl.mp hu⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_compl.mpr hf,hr⟩)
  have card := (card_le_card sub).trans (card_union_le _ _)
  calc
    _ ≤ ((Xᶜ.filter r).card : ℝ) + (((univ.filter r) ∩ (X \ U)).card : ℝ) := by exact_mod_cast card
    _ ≤ β*d+s := add_le_add initial missed
    _ = _ := by rw [add_mul, div_mul_cancel₀ _ hd.ne']

/-- From the degree and codegree of the triple system to simultaneous
ordinary matchings in two disjoint copy pools. A bulk copy has an explicit
identifier e, whereas each reserve copy is the physical pair (a,b). -/
theorem nibble_and_spectral_repair (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ Δ₀ : ℝ, ∀ {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
      [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E] [Nonempty A],
    ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ η : ℝ, 0 ≤ η → η < 1 →
    ∀ (a : E → A) (b : E → B) (pairs : Finset (I × E))
      (X : I → Finset A) (Y : I → Finset B) (R : A → B → Prop) [DecidableRel R]
      (d : ℕ), 0 < d → (∀ x, (univ.filter (R x)).card = d) →
      (∀ y, (univ.filter (fun x => R x y)).card = d) →
      Fintype.card A = Fintype.card B → (∀ i, (X i).card = (Y i).card) →
      (∀ p ∈ pairs, a p.2 ∈ X p.1 ∧ b p.2 ∈ Y p.1) →
      let H := pairs.image (triple a b)
      (∀ v, (degree H v : ℝ) ≤ Δ) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ^(1-δ)) →
      (H.card : ℝ) ≤ Real.exp (Δ^((δ/450)^2)) →
      (Fintype.card (TestIndex I A B) : ℝ) ≤ Real.exp (Δ^((δ/450)^2)) →
      (∀ i x, x ∈ X i → (1-η)*Δ ≤ (degree H (.inl (i,x)) : ℝ)) →
      (∀ i y, y ∈ Y i → (1-η)*Δ ≤ (degree H (.inr (.inl (i,y))) : ℝ)) →
      ∀ σ β : ℝ, 0 ≤ σ → σ ≤ 1 → 0 ≤ β →
      (∀ f : A → ℝ, ∑ x, f x = 0 →
        (∑ y, (∑ x, f x * (if R x y then 1/(d:ℝ) else 0))^2) ≤ σ^2 * ∑ x, (f x)^2) →
      (∀ i x, (((Y i)ᶜ.filter (R x)).card : ℝ) ≤ β*d) →
      (∀ i y, (((X i)ᶜ.filter (fun x => R x y)).card : ℝ) ≤ β*d) →
      let Bnd (z : ℕ) := max ((η+Δ^(-(δ/450)))*z) (3*Δ^δ/(1-η))
      let t := Bnd (Fintype.card I)
      let ρ := β+Bnd d/d
      ∀ h : ℕ, 0 < h → σ^h ≤ 1/(2*(Fintype.card A : ℝ)) → 3*(2*h : ℕ)*ρ ≤ 1/2 →
      (2*(h:ℝ)+1)*(6*(2*t+(2*h-1 : ℕ)*(Fintype.card I : ℝ)*ρ)/d) +
        (2*(h:ℝ))*(6*(2*h : ℕ)*ρ) ≤ 4/27 →
      ∃ (P : Finset (I × E)) (alloc : I → Finset (A × B)) (F : ∀ i, ↥(X i) ≃ ↥(Y i)),
        P ⊆ pairs ∧ validPacking a b P ∧ (∀ i j, i ≠ j → Disjoint (alloc i) (alloc j)) ∧
        ∀ i (u : ↥(X i)), (∃ e, (i,e) ∈ P ∧ a e = u.val ∧ b e = (F i u).val) ∨
          (R u (F i u) ∧ (u.val,(F i u).val) ∈ alloc i) := by
  classical
  obtain ⟨Δ₀,nibble⟩ := exists_packing_with_repair_tests δ hδ hδ'
  refine ⟨max Δ₀ 1,?_⟩
  intro I A B E _ _ _ _ _ _ _ _ _ Δ big η η0 η1 a b pairs X Y R dec d hd degA degB same balance eligible H deg code size count lowA lowB
    σ β s0 s1 β0 op beforeA beforeB Bnd t ρ h hh mix budget1 budget2
  let N x := univ.filter (R x)
  let N' y := univ.filter (fun x => R x y)
  obtain ⟨P,sub,pack,elig,test⟩ := nibble Δ ((le_max_left _ _).trans big) η η0 η1 a b pairs X Y N N' d
    (fun x => (degA x).le) (fun y => (degB y).le) eligible deg code size count lowA lowB
  let C := covered a b P
  let U (i : I) := univ.filter fun x => Sum.inl (i,x) ∈ C
  let W (i : I) := univ.filter fun y => Sum.inr (Sum.inl (i,y)) ∈ C
  obtain ⟨start,stop,nearA,nearB⟩ := physical_test_bounds a b P X Y N N' t (Bnd d) (fun j => by
    rcases j with j|j <;> exact test _)
  choose M old using fun i => matching_of_bulk a b P pack i
  have leftFree i : U i ⊆ X i := by
    intro x hx
    obtain ⟨e,he,hx',_⟩ := old i ⟨x,hx⟩
    change a e = x at hx'
    rw [← hx']; exact (elig _ he).1
  have rightFree i : W i ⊆ Y i := by
    intro y hy
    obtain ⟨x,eq⟩ := (M i).surjective ⟨y,hy⟩
    obtain ⟨e,he,_,ey⟩ := old i x
    rw [eq] at ey
    change b e = y at ey
    rw [← ey]; exact (elig _ he).2
  have D : 0 < (d:ℝ) := by exact_mod_cast hd
  have nonneg (z : ℕ) : 0 ≤ Bnd z := by
    have Δpos : 0 ≤ Δ := zero_le_one.trans ((le_max_right _ _).trans big)
    dsimp only [Bnd]
    exact le_max_of_le_left (by positivity)
  obtain ⟨alloc,F,disj,uses⟩ := repair_in_regular_reserve same R d hd degA degB X U Y W leftFree rightFree
    balance M σ ρ t s0 s1 (add_nonneg β0 (div_nonneg (nonneg d) D.le)) (nonneg _) op
    (fun i x => remaining_neighbors _ _ _ _ _ _ D (beforeA i x) (nearA i x))
    (fun i y => remaining_neighbors _ _ _ _ _ _ D (beforeB i y) (nearB i y))
    start stop h hh mix budget1 budget2
  refine ⟨P,alloc,F,sub,pack,disj,fun i u => ?_⟩
  rcases uses i u with ⟨hu,eq⟩ | reserve
  · obtain ⟨e,he,ae,be⟩ := old i ⟨u.val,hu⟩
    exact Or.inl ⟨e,he,ae,be.trans eq.symm⟩
  · exact Or.inr reserve
end WeightedPaper.Repair
