import ConditionedPalette
import PaletteAssembly
import MatchingCoordinates

namespace WeightedPaper.Repair
open Finset MeasureTheory Matrix

private theorem finite_event {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (ev : Ω → Prop) [DecidablePred ev] :
    p.toMeasure.real {z | ev z} = ∑ z, if ev z then (p z).toReal else 0 := by
  classical
  change (p.toMeasure {z | ev z}).toReal = _
  rw [p.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply sum_congr rfl
    intro z _
    by_cases h : ev z <;> simp [Set.indicator, h]
  · intro z _
    by_cases h : ev z <;> simp [Set.indicator,h,p.apply_ne_top]

private theorem arcs_length {V : Type*} (x y : V) (l : List V) : (arcs x l y).length = l.length+1 := by
  induction l generalizing x with
  | nil => rfl
  | cons z l ih => simp [arcs,ih]

private theorem route_of_arcs {V : Type*} [DecidableEq V] (G : V → Finset V) (x y : V) (l : List V)
    (edges : ∀ e ∈ arcs x l y, e.2 ∈ G e.1) : follows G x l y := by
  induction l generalizing x with
  | nil => exact edges (x,y) (by simp [arcs])
  | cons z l ih =>
    exact ⟨edges (x,z) (by simp [arcs]),ih z (fun e he => edges e (List.mem_cons_of_mem _ he))⟩

theorem arc_valid {V : Type*} [Fintype V] [DecidableEq V] (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y)
    (free : Finset V) (x y : V) (l : List V) (hx : x ∈ free) (hy : y ∈ free)
    (middle : ∀ z ∈ l, z ∈ free) (pos : 0 < pathWeight K x l y) :
    ∀ e ∈ arcs x l y, e.1 ∈ free ∧ e.2 ∈ free ∧ 0 < K e.1 e.2 := by
  induction l generalizing x with
  | nil => intro e he; obtain rfl := List.mem_singleton.mp he; exact ⟨hx,hy,pos⟩
  | cons z l ih =>
    have p : 0 < K x z ∧ 0 < pathWeight K z l y :=
      ⟨pos_of_mul_pos_left pos (pathWeight_nonneg K hn z y l), pos_of_mul_pos_right pos (hn x z)⟩
    have hz := middle z (by simp)
    intro e he
    rcases List.mem_cons.mp he with rfl | tail
    · exact ⟨hx,hz,p.1⟩
    · exact ih z hz (fun a h => middle a (List.mem_cons_of_mem _ h)) p.2 e tail

/-- Convert laws on contracted walks to matchings on the actual free subsets.
Physical edges carry their left and right endpoints, so the disjointness
conclusion is meaningful across different color bijections. -/
theorem pack_free_sets_from_paths {I V B : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    [Fintype B] [DecidableEq B] (π : I → V ≃ B) (free holes : I → Finset V)
    (inside : ∀ i, holes i ⊆ free i) (R : V → B → Prop) [DecidableRel R]
    (Ω : (q : Σ i, ↥(holes i)) → Type*) [∀ q,Fintype (Ω q)]
    (p : ∀ q, PMF (Ω q)) (mid : ∀ q, Ω q → List V)
    (matched : ∀ q z a, a ∈ mid q z → a ∈ free q.1 ∧ a ∉ holes q.1)
    (valid : ∀ q z e, e ∈ arcs q.2.val (mid q z) q.2.val → R e.1 (π q.1 e.2))
    (ℓ μR μM : ℝ) (hR : 0 ≤ μR) (hM : 0 ≤ μM)
    (len : ∀ q z, ((mid q z).length : ℝ) + 1 ≤ ℓ)
    (loadR : ∀ (e : V × B), (∑ q, ∑ z, if (e.1,(π q.1).symm e.2) ∈ arcs q.2.val (mid q z) q.2.val
      then (p q z).toReal else 0) ≤ μR)
    (loadM : ∀ i a, (∑ j : ↥(holes i), ∑ z, if a ∈ mid ⟨i,j⟩ z then (p ⟨i,j⟩ z).toReal else 0) ≤ μM)
    (budget : ℓ*μR+(ℓ-1)*μM ≤ 4/27) :
    ∃ (alloc : I → Finset (V × B)) (perm : ∀ i, Equiv.Perm ↥(free i)),
      (∀ i j, i ≠ j → Disjoint (alloc i) (alloc j)) ∧ ∀ i (u : ↥(free i)),
      (u.val ∉ holes i ∧ perm i u = u) ∨ (R u (π i (perm i u).val) ∧ (u.val,π i (perm i u).val) ∈ alloc i) := by
  classical
  let ms : ∀ q, MeasurableSpace (Ω q) := fun _ => ⊤
  let singles : ∀ q, MeasurableSingletonClass (Ω q) := fun _ => ⟨fun _ => trivial⟩
  let tag (i : I) (e : V × V) := (e.1,π i e.2)
  let pool (q : Σ i, ↥(holes i)) (z : Ω q) := (arcs q.2.val (mid q z) q.2.val).toFinset.image (tag q.1)
  let edge (i : I) (a b : V) := if a ∈ free i ∧ b ∈ free i ∧ R a (π i b) then some (a,π i b) else none
  have route q z : follows (fun a => univ.filter fun b => ∃ r ∈ pool q z, edge q.1 a b = some r)
      q.2.val (mid q z) q.2.val := by
    apply route_of_arcs
    intro e he
    obtain ⟨a,b⟩ := e
    have loc (x y : V) (l : List V) (hx : x ∈ free q.1) (hy : y ∈ free q.1)
        (middle : ∀ a ∈ l, a ∈ free q.1) : ∀ e ∈ arcs x l y, e.1 ∈ free q.1 ∧ e.2 ∈ free q.1 := by
      induction l generalizing x with
      | nil => intro e he; obtain rfl := List.mem_singleton.mp he; exact ⟨hx,hy⟩
      | cons z l ih =>
        have hz := middle z (by simp)
        intro e he
        rcases List.mem_cons.mp he with rfl | tail
        · exact ⟨hx,hz⟩
        · exact ih z hz (fun w hw => middle w (List.mem_cons_of_mem _ hw)) e tail
    have ⟨ha,hb⟩ := loc _ _ _ (inside _ q.2.property) (inside _ q.2.property)
      (fun a ha => (matched q z a ha).1) _ he
    refine mem_filter.mpr ⟨mem_univ _,tag q.1 (a,b),mem_image_of_mem _ (List.mem_toFinset.mpr he),?_⟩
    simp [edge,tag,ha,hb,valid q z _ he]
  have lenR q z : ((pool q z).card : ℝ) ≤ ℓ := by
    have lower := (card_image_le (f := tag q.1) (s := (arcs q.2.val (mid q z) q.2.val).toFinset)).trans
      (List.toFinset_card_le _)
    rw [arcs_length] at lower
    exact (by exact_mod_cast lower : ((pool q z).card : ℝ) ≤ (mid q z).length+1).trans (len q z)
  have r (e : V × B) : ∑ q, (p q).toMeasure.real {z | e ∈ pool q z} ≤ μR := by
    refine le_trans (sum_le_sum (fun q _ => ?_)) (loadR e)
    rw [finite_event]
    apply sum_le_sum
    intro z _
    have iff : e ∈ pool q z ↔ (e.1,(π q.1).symm e.2) ∈ arcs q.2.val (mid q z) q.2.val := by
      constructor
      · rintro h
        obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp h
        simpa [tag] using List.mem_toFinset.mp hab
      · intro h
        exact mem_image.mpr ⟨_,List.mem_toFinset.mpr h,by simp [tag]⟩
    simp [iff]
  have m (e : Σ _ : I,V) : ∑ q, (p q).toMeasure.real {z | e ∈ (mid q z).toFinset.image (Sigma.mk q.1)} ≤ μM := by
    obtain ⟨i,a⟩ := e
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ j, if j = i then (∑ x : ↥(holes j), ∑ z, if a ∈ mid ⟨j,x⟩ z then (p ⟨j,x⟩ z).toReal else 0) else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases h : j=i
        · subst j
          simp only [ite_true]
          apply sum_congr rfl
          intro x _
          rw [finite_event]
          simp
        · simp [h]
      _ ≤ _ := by simpa using loadM i a
  obtain ⟨alloc,per,disj,ok⟩ := pack_palette_from_laws holes Ω (fun q => (p q).toMeasure)
    edge mid pool (fun q z a ha => (matched q z a ha).2) route ℓ μR μM hR hM lenR
    (fun q z => by linarith [len q z]) r m budget
  have classify i a : (a ∉ holes i ∧ per i a = a) ∨
      (a ∈ free i ∧ per i a ∈ free i ∧ R a (π i (per i a)) ∧ (a,π i (per i a)) ∈ alloc i) := by
    rcases ok i a with old | ⟨e,he,h⟩
    · exact Or.inl old
    · dsimp only [edge] at h
      split at h
      · rename_i hg
        cases h
        exact Or.inr ⟨hg.1,hg.2.1,hg.2.2,he⟩
      · contradiction
  have maps i a : a ∈ free i ↔ per i a ∈ free i := by
    rcases classify i a with ⟨_,he⟩ | ⟨ha,hb,_⟩
    · rw [he]
    · exact iff_of_true ha hb
  refine ⟨alloc,fun i => (per i).subtypeEquiv (maps i),disj,?_⟩
  intro i u
  rcases classify i u.val with ⟨hh,he⟩ | ⟨_,_,hR,ha⟩
  · exact Or.inl ⟨hh,Subtype.ext he⟩
  · exact Or.inr ⟨hR,ha⟩
end WeightedPaper.Repair
