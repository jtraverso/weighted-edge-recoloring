import GridDegrees
import GridExceptional
import GridNibble

namespace WeightedPaper.Repair.Grid
open Finset Filter
open scoped Classical

variable {H W : Type} [Fintype H] [Fintype W]

private theorem leftFree_iff (x : Side H W) :
    x ∈ gridFree leftEndpoint ↔ x ∉ Set.range (leftInternal : Fin 2 → Side H W) := by
  rcases x with x|h
  · simp [leftEndpoint, leftInternal, Set.mem_range]
  · simp [leftInternal, Set.mem_range]

private theorem rightFree_iff (x : Side H W) :
    x ∈ gridFree rightEndpoint ↔ x ∉ Set.range (rightInternal : Fin 2 → Side H W) := by
  rcases x with x|h
  · simp [rightEndpoint, rightInternal, Set.mem_range, Function.Embedding.coe_trans]
  · simp [rightInternal, Set.mem_range]

private theorem grid_seed_left (d : ℕ) (i : Fin d) (x : Side H W) :
    (univ.filter (fun e : Fin d × Bool => e.1 = i ∧
      (endpoint 0 e = .inl x ∨ endpoint 1 e = .inl x))).card =
      if x ∈ gridFree leftEndpoint then 0 else 1 := by
  calc
    _ = (if x ∈ Set.range (leftInternal : Fin 2 → Side H W) then 1 else 0) := by
      convert internal_seed_count d i x using 2 <;> congr 1 <;> ext <;> simp
    _ = _ := by
      by_cases e : x ∈ Set.range (leftInternal : Fin 2 → Side H W)
      · have no : x ∉ gridFree leftEndpoint := fun h => (leftFree_iff x).mp h e
        simp only [ite_eq_left e, ite_eq_right no]
      · have yes : x ∈ gridFree leftEndpoint := (leftFree_iff x).mpr e
        simp only [ite_eq_right e, ite_eq_left yes]

private theorem grid_seed_right (d : ℕ) (i : Fin d) (x : Side H W) :
    (univ.filter (fun e : Fin d × Bool => e.1 = i ∧
      (endpoint 0 e = .inr x ∨ endpoint 1 e = .inr x))).card =
      if x ∈ gridFree rightEndpoint then 0 else 1 := by
  calc
    _ = (if x ∈ Set.range (rightInternal : Fin 2 → Side H W) then 1 else 0) := by
      convert internal_seed_count' d i x using 2 <;> congr 1 <;> ext <;> simp
    _ = _ := by
      by_cases e : x ∈ Set.range (rightInternal : Fin 2 → Side H W)
      · have no : x ∉ gridFree rightEndpoint := fun h => (rightFree_iff x).mp h e
        simp only [ite_eq_left e, ite_eq_right no]
      · have yes : x ∈ gridFree rightEndpoint := (rightFree_iff x).mpr e
        simp only [ite_eq_right e, ite_eq_left yes]

private theorem capacity_of_support_copy {A : Type} [Fintype A] [DecidableEq A]
    (R : A → A → Prop) [DecidableRel R]
    (x y : A) : ordinaryCapacity (supportLeft (R := R)) supportRight R x y =
      if R x y then 2 else 0 := by
  unfold ordinaryCapacity
  by_cases good : R x y
  · let e : SupportCopy R := ⟨(x,y),good⟩
    have singleton : (univ.filter fun p : SupportCopy R => supportLeft p = x ∧ supportRight p = y) =
        {e} := by
      ext p
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · exact fun ⟨hx,hy⟩ => Subtype.ext (Prod.ext hx hy)
      · rintro rfl
        exact ⟨rfl,rfl⟩
    simp [singleton, good]
  · have empty : (univ.filter fun p : SupportCopy R => supportLeft p = x ∧ supportRight p = y) =
        ∅ := by
      ext p
      simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨hx,hy⟩
      exact good (by rw [← hx, ← hy]; exact p.property)
    simp [empty, good]

private theorem free_cardinalities [DecidableEq (Side H W)] (U V : Fin 2 ↪ Ordinary H W)
    (P : Finset (Side H W × Side H W))
    (matching : ∃ (f : ↥(gridFree U ∩ exceptionSet) ↪ ↥(gridFree V \ exceptionSet))
      (g : ↥(gridFree V ∩ exceptionSet) ↪ ↥(gridFree U \ exceptionSet)),
      P = pairsOf f ∪ transposePairs (pairsOf g)) :
    let j : Ordinary H W ↪ Side H W := Function.Embedding.inl
    (pullback j (remaining (gridFree U) P)).card + (Fintype.card H+2) =
      Fintype.card (Ordinary H W) ∧
    (pullback j (remaining (gridFree V) (transposePairs P))).card + (Fintype.card H+2) =
      Fintype.card (Ordinary H W) := by
  obtain ⟨f,g,rfl⟩ := matching
  refine ⟨grid_remaining_count U V f g, ?_⟩
  have swapped : transposePairs (pairsOf f ∪ transposePairs (pairsOf g)) =
      pairsOf g ∪ transposePairs (pairsOf f) := by
    ext ⟨x,y⟩
    simp [or_comm]
  rw [swapped]
  exact grid_remaining_count V U g f

set_option maxHeartbeats 600000 in
private theorem grid_host_of_certificates (δ Δ₀ : ℝ) (hybrid : WeightedNibbleAt δ Δ₀)
    [DecidableEq (Ordinary H W)]
    (R : Ordinary H W → Ordinary H W → Prop) [decR : DecidableRel R] (d : ℕ) (hd : 0 < d)
    (regA : ∀ x, (univ.filter (R x)).card = d)
    (regB : ∀ y, (univ.filter (fun x => R x y)).card = d)
    (cert : ∀ (F G : Fin d → Finset (Ordinary H W)), (∀ i, (F i).card = (G i).card) →
      (∀ i, Fintype.card (Ordinary H W) ≤ (F i).card+(Fintype.card H+2)) →
      (∀ i, Fintype.card (Ordinary H W) ≤ (G i).card+(Fintype.card H+2)) →
      Nonempty (HybridCertificate δ Δ₀ (supportLeft (R := R)) supportRight R F G)) :
    let cap := capacity R d
    HasSeededFactorization (A := Side H W) (B := Side H W) (endpoint 0) (endpoint 1)
      (fun e : CrossingCopy cap => e.1.1) (fun e : CrossingCopy cap => e.1.2)
      (Prod.fst : Fin d × Bool → Fin d) (3*d) := by
  intro cap
  let U := fun _ : Fin d => (gridFree leftEndpoint : Finset (Side H W))
  let Y := fun _ : Fin d => (gridFree rightEndpoint : Finset (Side H W))
  let ex : Finset (Side H W) := exceptionSet
  let j : Ordinary H W ↪ Side H W := Function.Embedding.inl
  let exc : Side H W → Side H W → ℕ := exceptionCap d
  let pool (x y : Side H W) : ℕ := if ordinary R x y then 2 else 0
  have deg := grid_degrees R d
    (fun x => by convert regA x using 2; exact filter_congr_decidable _ _ _)
    (fun y => by convert regB y using 2; exact filter_congr_decidable _ _ _)
  have loopless (e : Fin d × Bool) :
      (endpoint (H := H) (W := W) 0 e) ≠ endpoint 1 e := by
    rcases e with ⟨i,c⟩
    cases c <;> simp [endpoint, leftInternal, rightInternal, Side, Ordinary]
  have reserveA : WeightedPaper.RowReserves U Y exc univ ex ex :=
    grid_exception_reserves d hd leftEndpoint rightEndpoint (fun h c => (mark_mem_gridFree h c).2)
  have reserveB : WeightedPaper.RowReserves Y U exc univ ex ex :=
    grid_exception_reserves d hd rightEndpoint leftEndpoint (fun h c => (mark_mem_gridFree h c).1)
  refine hybrid (I := Fin d) (A := Side H W) (B := Side H W) (A₀ := Ordinary H W) (B₀ := Ordinary H W)
    (E := SupportCopy R) (T := Fin d × Bool) cap exc (fun x y => exc y x) pool
    (endpoint 0) (endpoint 1) loopless Prod.fst (3*d) (by simp; omega)
    (grid_exception_capacities R d) U Y ex ex j j (supportLeft (R := R)) supportRight R (decR := decR)
    (fun _ => ordinary_of_not_exception) (fun _ => ordinary_of_not_exception)
    (fun x y => by
      rw [capacity_of_support_copy]
      by_cases h : R x y <;> simp [pool, j, ordinary, h])
    (fun x => by convert deg.1 x using 2 <;> congr 1 <;> ext <;> simp)
    (fun y => by convert deg.2 y using 2 <;> congr 1 <;> ext <;> simp)
    (fun i x => by convert grid_seed_left d i x using 2 <;> congr 1 <;> ext <;> simp)
    (fun i y => by convert grid_seed_right d i y using 2 <;> congr 1 <;> ext <;> simp)
    reserveA reserveB ?_
  intro P _ matchings
  letI : DecidableEq (Side H W) := Classical.decEq _
  let F := fun i => pullback j (remaining (U i) (P i))
  let G := fun i => pullback j (remaining (Y i) (transposePairs (P i)))
  have sizes i :
      (F i).card + (Fintype.card H+2) = Fintype.card (Ordinary H W) ∧
      (G i).card + (Fintype.card H+2) = Fintype.card (Ordinary H W) :=
    free_cardinalities leftEndpoint rightEndpoint (P i) (matchings i)
  have same i : (F i).card = (G i).card :=
    Nat.add_right_cancel ((sizes i).1.trans (sizes i).2.symm)
  exact cert F G same (fun i => (sizes i).1.symm.le) (fun i => (sizes i).2.symm.le)

/-- The explicit grid host satisfies the weighted nibble criterion for all
sufficiently large q at each fixed positive cell size. The seed colors on
the two internal pairs are preserved, up to an injection of palettes. -/
theorem sparse_grid_hybrid_factorization (b : ℕ) (hb : 0 < b) :
    ∀ᶠ q : ℕ in atTop, ∃ hq : 12 ≤ q,
      let m := markedEmbedding q b hq hb
      let d := b*(2*q-1)
      let V := Side (Fin (Nat.sqrt q)) (Intact m)
      let cap := capacity (support m) d
      HasSeededFactorization (A := V) (B := V) (endpoint 0) (endpoint 1)
        (fun e : CrossingCopy cap => e.1.1) (fun e : CrossingCopy cap => e.1.2)
        (Prod.fst : Fin d × Bool → Fin d) (3*d) := by
  obtain ⟨Δ₀, hybrid⟩ := factorization_from_weighted_nibble (δ := 1/4)
    (by norm_num) (by norm_num)
  filter_upwards [grid_hybrid_certificates b hb Δ₀] with q hcert
  obtain ⟨hq,cert⟩ := hcert
  refine ⟨hq, ?_⟩
  let m := markedEmbedding q b hq hb
  let d := b*(2*q-1)
  have hd : 0 < d := Nat.mul_pos hb (by omega)
  have reg := support_degrees m
  letI : DecidableEq (Ordinary (Fin (Nat.sqrt q)) (Intact m)) := Classical.decEq _
  letI : DecidableRel (support m) := fun x y => Classical.propDecidable _
  apply grid_host_of_certificates (1/4) Δ₀ hybrid (support m) d hd reg.1 reg.2
  simpa only [Fintype.card_fin] using cert m

end WeightedPaper.Repair.Grid
