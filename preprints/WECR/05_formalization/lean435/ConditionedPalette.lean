import PaletteLoads

namespace WeightedPaper.Repair
open Finset Matrix
variable {I E V : Type*} [Fintype I] [Fintype V] [DecidableEq V] [Nonempty V]
variable {Q : I → Type*} [∀ i, Fintype (Q i)]

/-- The same admissible path law works for every tested physical reserve
edge and every color-specific matched vertex. The endpoint and neighborhood
hypotheses already count actual requests. -/
theorem conditioned_palette_loads (K : I → Matrix V V ℝ) (hn : ∀ i x y, 0 ≤ K i x y)
    (row : ∀ i u, ∑ v, K i u v = 1) (col : ∀ i v, ∑ u, K i u v = 1)
    (σ ρ d t : ℝ) (s0 : 0 ≤ σ) (s1 : σ ≤ 1) (r0 : 0 ≤ ρ) (hd : 0 < d)
    (op : ∀ i (f : V → ℝ), ∑ x, f x = 0 → ∑ y, (advance (K i) f y)^2 ≤ σ^2 * ∑ x, (f x)^2)
    (s y : ∀ i, Q i → V) (u v : E → I → V) (edge : ∀ e i, K i (u e i) (v e i) ≤ 1/d)
    (bad : I → Finset V) (forward : ∀ i x, ∑ z ∈ bad i, K i x z ≤ ρ)
    (backward : ∀ i x, ∑ z ∈ bad i, K i z x ≤ ρ)
    (first : ∀ i v, ∑ j, K i (s i j) v ≤ ρ) (last : ∀ i u, ∑ j, K i u (y i j) ≤ ρ)
    (startCount : ∀ e, ((univ.filter (fun q : Σ i,Q i => s q.1 q.2 = u e q.1)).card : ℝ) ≤ t)
    (endCount : ∀ e, ((univ.filter (fun q : Σ i,Q i => y q.1 q.2 = v e q.1)).card : ℝ) ≤ t)
    (h : ℕ) (hh : 0 < h) (mix : σ^h ≤ 1/(2*(Fintype.card V : ℝ)))
    (budget : 3*(2*h : ℕ)*ρ ≤ 1/2) :
    let A (i : I) := (univ : Finset (Fin (2*h) → V)).filter fun f => ∀ j, f j ∉ bad i
    let w (q : Σ i,Q i) (f : Fin (2*h) → V) := pathWeight (K q.1) (s q.1 q.2) (List.ofFn f) (y q.1 q.2)
    let good (q : Σ i,Q i) := (A q.1).filter fun f => 0 < w q f
    ∃ p : ∀ q, PMF (good q),
      (∀ e, (∑ q, ∑ z : good q, if (u e q.1,v e q.1) ∈ arcs (s q.1 q.2) (List.ofFn z.val) (y q.1 q.2)
           then (p q z).toReal else 0) ≤ 6*(2*t+(2*h-1 : ℕ)*(Fintype.card I : ℝ)*ρ)/d) ∧
      (∀ i a, (∑ j : Q i, ∑ z : good ⟨i,j⟩, if ∃ k, z.val k = a then (p ⟨i,j⟩ z).toReal else 0) ≤ 6*(2*h : ℕ)*ρ) := by
  classical
  intro A w good
  let c : ℝ := 1/(2*(Fintype.card V : ℝ))
  have hc : 0 < c := by dsimp [c]; positivity
  let W (q : Σ i,Q i) := ∑ f ∈ A q.1, w q f
  have laws (q : Σ i,Q i) : ∃ p : PMF (good q), c/2 ≤ W q ∧
      ∀ S : Finset (good q), (∑ f ∈ S, (p f).toReal) = (∑ f ∈ S, w q f.val)/W q :=
    admissible_walk_law (K q.1) (hn _) (row _) (col _) s0 s1 r0 (op _) (bad _)
      (forward _) (backward _) h hh mix budget _ _
  choose p accepted law using laws
  have positive q : 0 < W q := (half_pos hc).trans_le (accepted q)
  have long i n (le : h ≤ n) a b : ((K i)^n) a b ≤ 3*c := by
    refine (long_segment_bounds (K i) (row i) (col i) s0 s1 (op i) le mix a b).2.trans_eq ?_
    dsimp [c]; ring
  let m := 2*h-1
  have eq : m+1 = 2*h := by dsimp [m]; omega
  have weightPos q f : 0 ≤ w q f := pathWeight_nonneg _ (hn _) _ _ _
  refine ⟨p,?_,?_⟩
  · intro e
    apply reserve_load_across_colors K hn row col s y (u e) (v e) m h eq.ge c d t ρ hc hd long
      (edge e) first last (startCount e) (endCount e) W _ accepted
    intro q
    rw [show m+2 = 2*h+1 by omega,eq]
    let event (f : Fin (2*h) → V) := (u e q.1,v e q.1) ∈ arcs (s q.1 q.2) (List.ofFn f) (y q.1 q.2)
    exact (restricted_event_mass (A q.1) (w q) (weightPos q) event (p q) (law q)).le.trans
      (reserve_occupancy (K q.1) (hn _) _ _ _ _ _ (A q.1) (W q) (positive q))
  · intro i a
    let hit (j : Q i) := ∑ z : good ⟨i,j⟩, if ∃ k, z.val k = a then (p ⟨i,j⟩ z).toReal else 0
    have bound (j : Q i) : hit j ≤ ∑ k : Fin (2*h),
        ((K i)^(k.val+1)) (s i j) a * ((K i)^(2*h-k.val)) a (y i j) / W ⟨i,j⟩ := by
      let q : Σ i,Q i := ⟨i,j⟩
      let event (f : Fin (2*h) → V) := ∃ k, f k = a
      apply (restricted_event_mass (A i) (w q) (weightPos q) event (p q) (law q)).le.trans
      suffices aux : ∀ n : ℕ, 0 < n → ∀ B : Finset (Fin n → V),
          (∑ f ∈ B, if ∃ k, f k = a then pathWeight (K i) (s i j) (List.ofFn f) (y i j) else 0)/W q ≤
          ∑ k : Fin n, ((K i)^(k.val+1)) (s i j) a * ((K i)^(n-k.val)) a (y i j)/W q by
        exact aux _ (by omega) (A i)
      intro n pos B
      cases n with
      | zero => omega
      | succ n => exact matched_occupancy _ (hn _) _ _ _ n B _ (positive q)
    change ∑ j, hit j ≤ _
    have per : ∀ n : ℕ, 0 < n → 2*h ≤ n+1 →
        (∀ j, hit j ≤ ∑ k : Fin n, ((K i)^(k.val+1)) (s i j) a * ((K i)^(n-k.val)) a (y i j)/W ⟨i,j⟩) →
        ∑ j, hit j ≤ 6*(n:ℝ)*ρ := by
      intro n pos le useBound
      cases n with
      | zero => omega
      | succ n =>
        simpa only [Nat.cast_succ] using matched_load_in_color (K i) (hn _) (row _) (col _) (s i) (y i) a n h le
          c ρ hc (long _) (first _) (last _) (fun j => W ⟨i,j⟩) hit (fun j => accepted ⟨i,j⟩) useBound
    exact per (2*h) (by omega) (by omega) bound
end WeightedPaper.Repair
