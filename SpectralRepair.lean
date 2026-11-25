module

public import PhysicalRepair

@[expose] public section


namespace WeightedPaper.Repair
open Finset Matrix

/-- The two budgets of Lemma 8 suffice for actual simultaneous matchings
in a reserve with physical left/right coordinates. The given bijections
identify matching partners and pair the missed free vertices in each color.
Weights are the entries of the normalized reserve biadjacency matrix. -/
theorem spectral_repair_on_free_sets {I V B : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype B] [DecidableEq B]
    (P : Matrix V B ℝ) (hn : ∀ x y, 0 ≤ P x y) (row : ∀ x, ∑ y, P x y = 1)
    (col : ∀ y, ∑ x, P x y = 1) (σ ρ d t : ℝ) (s0 : 0 ≤ σ) (s1 : σ ≤ 1)
    (r0 : 0 ≤ ρ) (hd : 0 < d) (t0 : 0 ≤ t) (edge : ∀ x y, P x y ≤ 1/d)
    (op : ∀ f : V → ℝ, ∑ x, f x = 0 → ∑ y, (∑ x, f x * P x y)^2 ≤ σ^2 * ∑ x, (f x)^2)
    (π : I → V ≃ B) (free used : I → Finset V) (matchedFree : ∀ i, used i ⊆ free i)
    (fw : ∀ i x, ∑ z ∈ (used i)ᶜ, P x (π i z) ≤ ρ)
    (bw : ∀ i y, ∑ z ∈ (used i)ᶜ, P z y ≤ ρ)
    (startCount : ∀ x : V, ((univ.filter (fun q : Σ i, ↥(free i \ used i) => q.2.val = x)).card : ℝ) ≤ t)
    (endCount : ∀ y : B, ((univ.filter (fun q : Σ i, ↥(free i \ used i) => π q.1 q.2.val = y)).card : ℝ) ≤ t)
    (h : ℕ) (hh : 0 < h) (mix : σ^h ≤ 1/(2*(Fintype.card V : ℝ)))
    (budget1 : 3*(2*h : ℕ)*ρ ≤ 1/2)
    (budget2 : (2*(h:ℝ)+1)*(6*(2*t+(2*h-1 : ℕ)*(Fintype.card I : ℝ)*ρ)/d) +
      (2*(h:ℝ))*(6*(2*h : ℕ)*ρ) ≤ 4/27) :
    ∃ (alloc : I → Finset (V × B)) (perm : ∀ i, Equiv.Perm ↥(free i)),
      (∀ i j, i ≠ j → Disjoint (alloc i) (alloc j)) ∧ ∀ i (u : ↥(free i)),
      (u.val ∈ used i ∧ perm i u = u) ∨
      (0 < P u (π i (perm i u).val) ∧ (u.val,π i (perm i u).val) ∈ alloc i) := by
  classical
  let K (i : I) (a b : V) := P a (π i b)
  let holes (i : I) := free i \ used i
  let bad (i : I) := (used i)ᶜ
  let s (i : I) (q : ↥(holes i)) := q.val
  have inc i : holes i ⊆ bad i := fun x hx => mem_compl.mpr (mem_sdiff.mp hx).2
  have first i v : ∑ q : ↥(holes i), K i (s i q) v ≤ ρ := by
    change (∑ q ∈ (holes i).attach, (fun z => P z (π i v)) q.val) ≤ ρ
    rw [sum_attach (holes i) (fun z => P z (π i v))]
    exact (sum_le_sum_of_subset_of_nonneg (inc i) (fun _ _ _ => hn _ _)).trans (bw i (π i v))
  have last i u : ∑ q : ↥(holes i), K i u (s i q) ≤ ρ := by
    change (∑ q ∈ (holes i).attach, (fun z => P u (π i z)) q.val) ≤ ρ
    rw [sum_attach (holes i) (fun z => P u (π i z))]
    exact (sum_le_sum_of_subset_of_nonneg (inc i) (fun _ _ _ => hn _ _)).trans (fw i u)
  let A (i : I) := (univ : Finset (Fin (2*h) → V)).filter fun f => ∀ j, f j ∉ bad i
  let w (q : Σ i, ↥(holes i)) (f : Fin (2*h) → V) := pathWeight (K q.1) q.2.val (List.ofFn f) q.2.val
  let good (q : Σ i, ↥(holes i)) := (A q.1).filter fun f => 0 < w q f
  have end' (e : V × B) :
      ((univ.filter (fun q : Σ i, ↥(holes i) => s q.1 q.2 = (π q.1).symm e.2)).card : ℝ) ≤ t := by
    simpa [s, Equiv.eq_symm_apply] using endCount e.2
  obtain ⟨p,loadR,loadM⟩ := conditioned_palette_loads (Q := fun i => ↥(holes i)) K (fun _ x y => hn _ _)
    (fun i x => ((π i).sum_comp (P x)).trans (row x)) (fun i y => col (π i y))
    σ ρ d t s0 s1 r0 hd (fun i => permuted_contraction (π i) P σ op)
    s s (fun e _ => (e : V × B).1) (fun e i => (π i).symm e.2) (fun e i => edge _ _)
    bad fw (fun i y => bw i (π i y)) first last (fun e => startCount e.1) end' h hh mix budget1
  let mid (q : Σ i, ↥(holes i)) (z : ↥(good q)) := List.ofFn z.val
  have matched q (z : ↥(good q)) a (ha : a ∈ mid q z) : a ∈ used q.1 := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    have ok := (mem_filter.mp (mem_filter.mp z.property).1).2 j
    simpa [bad] using ok
  have valid q (z : ↥(good q)) e (he : e ∈ arcs q.2.val (mid q z) q.2.val) : 0 < P e.1 (π q.1 e.2) := by
    exact (arc_valid (K q.1) (fun _ _ => hn _ _) (free q.1) _ _ _ (mem_sdiff.mp q.2.property).1
      (mem_sdiff.mp q.2.property).1 (fun a ha => matchedFree _ (matched q z a ha)) (mem_filter.mp z.property).2 e he).2.2
  let μR := 6*(2*t+(2*h-1 : ℕ)*(Fintype.card I : ℝ)*ρ)/d
  let μM := 6*(2*h : ℕ)*ρ
  obtain ⟨alloc,perm,disj,cover⟩ := pack_free_sets_from_paths π free holes (fun _ => sdiff_subset) (fun a b => 0 < P a b)
    (fun q => ↥(good q)) p mid
    (fun q z a ha => ⟨matchedFree _ (matched q z a ha),fun hole => (mem_sdiff.mp hole).2 (matched q z a ha)⟩)
    valid (2*(h:ℝ)+1) μR μM (by dsimp [μR]; positivity) (by dsimp [μM]; positivity)
    (fun q z => by simp [mid]) loadR (fun i a => by simpa only [mid,List.mem_ofFn] using loadM i a)
    (by simpa [μR,μM] using budget2)
  refine ⟨alloc,perm,disj,fun i u => ?_⟩
  rcases cover i u with ⟨h,eq⟩ | newEdge
  · exact Or.inl ⟨by by_contra no; exact h (mem_sdiff.mpr ⟨u.property,no⟩),eq⟩
  · exact Or.inr newEdge
end WeightedPaper.Repair
