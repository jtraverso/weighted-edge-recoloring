import RepairSelection

namespace WeightedPaper.Repair
open Finset MeasureTheory

/-- Monotonicity in the set of usable crossing edges. -/
private theorem follows_of_le {V : Type*} [Fintype V] [DecidableEq V] {G K : V → Finset V}
    (h : ∀ x, G x ⊆ K x) (x y : V) (zs : List V) (w : follows G x zs y) : follows K x zs y := by
  induction zs generalizing x with
  | nil => exact h x w
  | cons z zs ih => exact ⟨h x w.1, ih z w.2⟩

/-- Color-specific free coordinates are indexed via the initial matching
on matched vertices and the endpoint pairing on holes. A repair candidate
is a walk in the reserve on these coordinates. The conclusion gives one
permutation per color and disjoint physical copy pools that realize all
its new pairs. The old matching copies are assumed preallocated. -/
theorem pack_palette_from_laws {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    {W : I → Type*} [∀ i,Fintype (W i)] [∀ i,DecidableEq (W i)]
    (holes : ∀ i,Finset (W i))
    (Ω : (q : Σ i, ↥(holes i)) → Type*) [∀ q,Fintype (Ω q)] [∀ q,MeasurableSpace (Ω q)]
    [∀ q,MeasurableSingletonClass (Ω q)] (law : ∀ q,Measure (Ω q)) [∀ q,IsProbabilityMeasure (law q)]
    (edge : ∀ i, W i → W i → Option R)
    (mid : ∀ (q : Σ i, ↥(holes i)), Ω q → List (W q.1))
    (pool : ∀ q, Ω q → Finset R)
    (matched : ∀ q z, ∀ u ∈ mid q z, u ∉ holes q.1)
    (route : ∀ q z, follows (fun u => univ.filter fun v => ∃ r ∈ pool q z, edge q.1 u v = some r)
      q.2.val (mid q z) q.2.val)
    (ℓ μR μM : ℝ) (hR : 0 ≤ μR) (hM : 0 ≤ μM)
    (lenR : ∀ q z, ((pool q z).card : ℝ) ≤ ℓ)
    (lenM : ∀ q z, ((mid q z).length : ℝ) ≤ ℓ-1)
    (loadR : ∀ r, ∑ q, (law q).real {z | r ∈ pool q z} ≤ μR)
    (loadM : ∀ e : Σ i,W i, ∑ q, (law q).real {z | e ∈ (mid q z).toFinset.image (Sigma.mk q.1)} ≤ μM)
    (budget : ℓ*μR + (ℓ-1)*μM ≤ 4/27) :
    ∃ (allocated : I → Finset R) (π : ∀ i, Equiv.Perm (W i)),
      (∀ i j, i ≠ j → Disjoint (allocated i) (allocated j)) ∧
      ∀ i u, (u ∉ holes i ∧ π i u = u) ∨ ∃ r ∈ allocated i, edge i u (π i u) = some r := by
  classical
  let Q := Σ i, ↥(holes i)
  letI : LinearOrder Q := LinearOrder.lift' (Fintype.equivFin Q) (Fintype.equivFin Q).injective
  let used (q : Q) (z : Ω q) := (mid q z).toFinset.image (Sigma.mk q.1)
  have size q z : ((used q z).card : ℝ) ≤ ℓ-1 :=
    (by exact_mod_cast (card_image_le.trans (List.toFinset_card_le (mid q z))) :
      ((used q z).card : ℝ) ≤ (mid q z).length).trans (lenM q z)
  obtain ⟨ω,disj⟩ := select_repairs law pool used ℓ μR μM hR hM lenR size loadR loadM budget
  let allocated (i : I) := univ.biUnion fun h : ↥(holes i) => pool ⟨i,h⟩ (ω ⟨i,h⟩)
  have across i j (neq : i ≠ j) : Disjoint (allocated i) (allocated j) := by
    apply disjoint_left.mpr
    intro r hi hj
    obtain ⟨x,_,hx⟩ := mem_biUnion.mp hi
    obtain ⟨y,_,hy⟩ := mem_biUnion.mp hj
    exact disjoint_left.mp (disj ⟨i,x⟩ ⟨j,y⟩ (fun eq => neq (congrArg Sigma.fst eq))).1 hx hy
  let G (i : I) (u : W i) := univ.filter fun v =>
    (u ∉ holes i ∧ v = u) ∨ ∃ r ∈ allocated i, edge i u v = some r
  have get (i) : ∃ π : Equiv.Perm (W i), ∀ u, π u ∈ G i u := by
    let m (x : W i) : List (W i) := if hx : x ∈ holes i then mid ⟨i,⟨x,hx⟩⟩ (ω ⟨i,⟨x,hx⟩⟩) else []
    apply matching_of_routed_walks (G i) (holes i) (fun u hu => by simp [G,hu]) m
    · intro x hx
      let q : Q := ⟨i,⟨x,hx⟩⟩
      rw [show m x = mid q (ω q) from dif_pos hx]
      refine follows_of_le (fun u v hv => ?_) _ _ _ (route q (ω q))
      obtain ⟨r,hr,h⟩ := (mem_filter.mp hv).2
      exact mem_filter.mpr ⟨mem_univ _, Or.inr ⟨r, mem_biUnion.mpr ⟨⟨x,hx⟩,mem_univ _,hr⟩,h⟩⟩
    · intro x hx y hy neq z hz hz'
      let q : Q := ⟨i,⟨x,hx⟩⟩
      let t : Q := ⟨i,⟨y,hy⟩⟩
      rw [show m x = mid q (ω q) from dif_pos hx] at hz
      rw [show m y = mid t (ω t) from dif_pos hy] at hz'
      simp only [List.mem_append, List.mem_singleton] at hz hz'
      rcases hz with h | rfl <;> rcases hz' with h' | rfl
      · have ne : q ≠ t := by
          intro eq
          have eq' : (⟨x,hx⟩ : ↥(holes i)) = ⟨y,hy⟩ := eq_of_heq (Sigma.mk.inj eq).2
          exact neq (congrArg Subtype.val eq')
        have hq : (⟨i,z⟩ : Σ i,W i) ∈ used q (ω q) :=
          mem_image_of_mem (Sigma.mk i) (List.mem_toFinset.mpr h)
        have ht : (⟨i,z⟩ : Σ i,W i) ∈ used t (ω t) :=
          mem_image_of_mem (Sigma.mk i) (List.mem_toFinset.mpr h')
        exact disjoint_left.mp (disj q t ne).2 hq ht
      · exact matched q _ _ h hy
      · exact matched t _ _ h' hx
      · exact neq rfl
  choose π hπ using get
  exact ⟨allocated,π,across,fun i u => (mem_filter.mp (hπ i u)).2⟩
end WeightedPaper.Repair
