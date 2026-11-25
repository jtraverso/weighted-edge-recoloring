import WalkOccupancy

namespace WeightedPaper.Repair
open Finset Matrix
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
variable {Q : I → Type*} [∀ i, Fintype (Q i)]

/-- Aggregate over the full palette for a fixed physical reserve edge. Its
contracted coordinates u,v can differ for every color. A walk that uses the
edge more than once contributes its use probability only once. -/
theorem reserve_load_across_colors (K : I → Matrix V V ℝ) (hn : ∀ i x y, 0 ≤ K i x y)
    (row : ∀ i u, ∑ v, K i u v = 1) (col : ∀ i v, ∑ u, K i u v = 1)
    (s y : ∀ i, Q i → V) (u v : I → V) (m h : ℕ) (time : 2*h ≤ m+1)
    (c d t ρ : ℝ) (hc : 0 < c) (hd : 0 < d)
    (long : ∀ i n, h ≤ n → ∀ a b, ((K i)^n) a b ≤ 3*c)
    (edge : ∀ i, K i (u i) (v i) ≤ 1/d)
    (first : ∀ i v, ∑ j, K i (s i j) v ≤ ρ) (last : ∀ i u, ∑ j, K i u (y i j) ≤ ρ)
    (startCount : ((univ.filter (fun q : Σ i, Q i => s q.1 q.2 = u q.1)).card : ℝ) ≤ t)
    (endCount : ((univ.filter (fun q : Σ i, Q i => y q.1 q.2 = v q.1)).card : ℝ) ≤ t)
    (keep occ : (Σ i, Q i) → ℝ) (accepted : ∀ q, c/2 ≤ keep q)
    (useBound : ∀ q, occ q ≤ ∑ j ∈ range (m+2),
      stepMass (K q.1) j (m+1-j) (s q.1 q.2) (u q.1) (v q.1) (y q.1 q.2) / keep q) :
    ∑ q, occ q ≤ 6*(2*t+m*(Fintype.card I : ℝ)*ρ)/d := by
  classical
  let mass (a b : ℕ) (q : Σ i, Q i) := stepMass (K q.1) a b (s q.1 q.2) (u q.1) (v q.1) (y q.1 q.2)
  let L (j : ℕ) (q : Σ i, Q i) := mass j (m+1-j) q / keep q
  have firstSlot : ∑ q, L 0 q ≤ 6*t/d := by
    apply endpoint_resource_use _ (mass 0 (m+1)) keep c d t hc hd accepted _ startCount
    intro q
    dsimp [mass,stepMass]
    by_cases e : s q.1 q.2 = u q.1
    · simp only [e, pow_zero, one_apply_eq, one_mul, ite_true]
      calc
        _ ≤ (1/d)*(3*c) := mul_le_mul (edge _) (long _ _ (by omega) _ _)
          (power_nonneg _ (hn _) _ _ _) (by positivity)
        _ = _ := by ring
    · simp [e]
  have lastSlot : ∑ q, L (m+1) q ≤ 6*t/d := by
    simp only [L, Nat.sub_self]
    apply endpoint_resource_use _ (mass (m+1) 0) keep c d t hc hd accepted _ endCount
    intro q
    dsimp [mass,stepMass]
    by_cases e : y q.1 q.2 = v q.1
    · simp only [e, pow_zero, one_apply_eq, mul_one, ite_true]
      calc
        _ ≤ (3*c)*(1/d) := mul_le_mul (long _ _ (by omega) _ _) (edge _) (hn _ _ _) (by positivity)
        _ = _ := by ring
    · simp [e, Ne.symm e]
  have middle (j : ℕ) (hj : j < m) : ∑ q, L (j+1) q ≤ (Fintype.card I : ℝ)*(6*ρ/d) := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ _i : I, 6*ρ/d := by
        apply sum_le_sum
        intro i _
        let b := m-1-j
        have eq : m+1-(j+1) = b+1 := by dsimp [b]; omega
        simp only [L,mass,eq]
        apply interior_edge_use (K i) (hn i) (row i) (col i) (s i) (y i) j b (u i) (v i)
          c d ρ hc hd (edge i) (first i) (last i) _ _ _ (fun q => accepted ⟨i,q⟩) (fun q => le_rfl)
        by_cases hb : h ≤ b+1
        · exact Or.inl (fun q => long _ _ hb _ _)
        · exact Or.inr (fun q => long _ _ (by dsimp [b] at hb; omega) _ _)
      _ = _ := by simp
  calc
    _ ≤ ∑ q, ∑ j ∈ range (m+2), L j q := sum_le_sum fun q _ => useBound q
    _ = (∑ q, L (m+1) q) + ((∑ j ∈ range m, ∑ q, L (j+1) q) + (∑ q, L 0 q)) := by
      rw [sum_comm, sum_range_succ, sum_range_succ']; ring
    _ ≤ 6*t/d + ((∑ _j ∈ range m, (Fintype.card I : ℝ)*(6*ρ/d)) + 6*t/d) :=
      add_le_add lastSlot (add_le_add (sum_le_sum fun j hj => middle j (mem_range.mp hj)) firstSlot)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- A matched resource belongs to one color. Only requests of that color
can occupy it, so the matched-edge budget contains no palette-size factor. -/
theorem matched_load_in_color {T : Type*} [Fintype T]
    (K : Matrix V V ℝ) (hn : ∀ x y, 0 ≤ K x y) (row : ∀ u, ∑ v, K u v = 1)
    (col : ∀ v, ∑ u, K u v = 1) (s y : T → V) (z : V) (m h : ℕ) (time : 2*h ≤ m+2)
    (c ρ : ℝ) (hc : 0 < c) (long : ∀ n, h ≤ n → ∀ a b, (K^n) a b ≤ 3*c)
    (first : ∀ v, ∑ j, K (s j) v ≤ ρ) (last : ∀ u, ∑ j, K u (y j) ≤ ρ)
    (keep occ : T → ℝ) (accepted : ∀ q, c/2 ≤ keep q)
    (useBound : ∀ q, occ q ≤ ∑ j : Fin (m+1),
      (K^(j.val+1)) (s q) z * (K^(m+1-j.val)) z (y q) /keep q) :
    ∑ q, occ q ≤ 6*(m+1)*ρ := by
  calc
    _ ≤ _ := sum_le_sum fun q _ => useBound q
    _ = _ := sum_comm
    _ ≤ ∑ _j : Fin (m+1), 6*ρ := by
      apply sum_le_sum
      intro j _
      let b := m-j.val
      have eq : m+1-j.val = b+1 := by dsimp [b]; omega
      simp only [eq]
      apply interior_matched_use K hn row col s y j.val b z c ρ hc first last _ _ _ accepted (fun _ => le_rfl)
      by_cases hb : h ≤ b+1
      · exact Or.inl (fun q => long _ hb _ _)
      · exact Or.inr (fun q => long _ (by dsimp [b] at hb; omega) _ _)
    _ = _ := by simp; ring

end WeightedPaper.Repair
