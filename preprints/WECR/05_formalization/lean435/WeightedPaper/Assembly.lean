import WeightedPaper.CrossingPacking
import OverfullWork.InternalEdges
import WeightedRecolouring.Statement

/-! Turn the packed crossing pairs into actual coloured multigraph
copies, then factor the regular bipartite residue. -/
namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def crossingGraph (L : Finset V)
    (P : Finset (L × (Lᶜ : Finset V))) : MultiGraph V where
  mult e := if e ∈ P.image (fun p => s(p.1.val,p.2.val)) then 1 else 0
  loopless e he := by
    apply if_neg
    intro h
    obtain ⟨⟨a,b⟩,_,rfl⟩ := mem_image.mp h
    have hb : b.val ∉ L := mem_compl.mp b.2
    have hEq : a.val = b.val := by simpa using he
    exact hb (hEq ▸ a.2)

private theorem crossingGraph_mult (L : Finset V) (P : Finset (L × (Lᶜ : Finset V)))
    (a : L) (b : (Lᶜ : Finset V)) :
    (crossingGraph L P).mult s(a.val,b.val) = if (a,b) ∈ P then 1 else 0 := by
  change (if s(a.val,b.val) ∈ P.image (fun p => s(p.1.val,p.2.val)) then 1 else 0) = _
  have hmem : s(a.val,b.val) ∈ P.image (fun p => s(p.1.val,p.2.val)) ↔ (a,b) ∈ P := by
    constructor
    · intro he
      obtain ⟨⟨x,y⟩,hxy,h⟩ := mem_image.mp he
      rcases Sym2.eq_iff.mp h with ⟨hx,hy⟩|⟨hx,hy⟩
      · have heq : (x,y) = (a,b) := Prod.ext (Subtype.ext hx) (Subtype.ext hy)
        exact heq ▸ hxy
      · exact ((mem_compl.mp b.2) (hx ▸ x.2)).elim
    · intro hp
      exact mem_image_of_mem _ hp
  rw [if_congr hmem rfl rfl]

private theorem crossingGraph_zero (L : Finset V) (P : Finset (L × (Lᶜ : Finset V)))
    (u v : V) (h : u ∈ L ↔ v ∈ L) : (crossingGraph L P).mult s(u,v) = 0 := by
  apply if_neg
  intro hh
  obtain ⟨⟨x,y⟩,_,he⟩ := mem_image.mp hh
  rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩|⟨hx,hy⟩
  · exact (mem_compl.mp y.2) (hy ▸ (h.mp (hx ▸ x.2)))
  · exact (mem_compl.mp y.2) (hy ▸ (h.mpr (hx ▸ x.2)))

private theorem crossingGraph_left_degree (L : Finset V) (P : Finset (L × (Lᶜ : Finset V)))
    (a : L) :
    (crossingGraph L P).degree a.val = (univ.filter fun b => (a,b) ∈ P).card := by
  rw [MultiGraph.degree_eq_sum_mult]
  calc
    _ = ∑ v ∈ Lᶜ, (crossingGraph L P).mult s(a.val,v) := by
      symm
      apply sum_subset (subset_univ _)
      intro v _ hv
      exact crossingGraph_zero L P _ _ (iff_of_true a.2 (by simpa using hv))
    _ = ∑ b : (Lᶜ : Finset V), (crossingGraph L P).mult s(a.val,b.val) :=
      (sum_attach (Lᶜ : Finset V) (fun v => (crossingGraph L P).mult s(a.val,v))).symm
    _ = _ := by
      simp only [crossingGraph_mult,card_eq_sum_ones,sum_filter]

private theorem crossingGraph_right_degree (L : Finset V) (P : Finset (L × (Lᶜ : Finset V)))
    (b : (Lᶜ : Finset V)) :
    (crossingGraph L P).degree b.val = (univ.filter fun a => (a,b) ∈ P).card := by
  rw [MultiGraph.degree_eq_sum_mult]
  calc
    _ = ∑ v ∈ L, (crossingGraph L P).mult s(b.val,v) := by
      symm
      apply sum_subset (subset_univ _)
      intro v _ hv
      exact crossingGraph_zero L P _ _ (iff_of_false (mem_compl.mp b.2) hv)
    _ = ∑ a : L, (crossingGraph L P).mult s(b.val,a.val) :=
      (sum_attach L (fun v => (crossingGraph L P).mult s(b.val,v))).symm
    _ = _ := by
      rw [card_eq_sum_ones,sum_filter]
      apply sum_congr rfl
      intro a _
      rw [Sym2.eq_swap,crossingGraph_mult]

noncomputable def missingOn {M : MultiGraph V} {k : ℕ} (C : M.EdgeColoring k)
    (L : Finset V) (i : Fin k) : Finset L :=
  univ.filter (fun a : L => (C.colourGraph i).degree a.val = 0)

/-- A capacity-respecting packing completes the given internal seed to
perfect matchings and leaves a bipartite residue. -/
theorem exists_factorization_of_crossing_packing (M : MultiGraph V) (L : Finset V)
    (D k : ℕ) (hk : k ≤ D) (hreg : M.IsRegularOfDegree D)
    (C : (M.internalPart L).EdgeColoring k)
    (P : CrossingPacking (missingOn C L) (missingOn C Lᶜ)
      (fun (a : L) (b : (Lᶜ : Finset V)) => M.mult s(a.val,b.val)) univ) :
    ∃ F : M.EdgeColoring D, F.IsFactorization := by
  classical
  let Q (i : Fin k) := crossingGraph L (P.pairs i)
  let H : MultiGraph V := {
    mult e := ∑ i, (C.col e i + (Q i).mult e)
    loopless e he := sum_eq_zero (fun i _ => by
      have hc : C.col e i ≤ (M.internalPart L).mult e := by
        rw [← C.sum_col e]
        exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
      rw [(M.internalPart L).loopless e he] at hc
      rw [(Q i).loopless e he, Nat.add_zero]
      omega) }
  have hdegree (v : V) (i : Fin k) : (C.colourGraph i).degree v + (Q i).degree v = 1 := by
    have hC := C.colourGraph_degree_le_one i v
    by_cases hv : v ∈ L
    · let a : L := ⟨v,hv⟩
      have hp := P.row i (mem_univ i) a
      have h : (Q i).degree v = if a ∈ missingOn C L i then 1 else 0 := by
        rw [show (Q i).degree v = (crossingGraph L (P.pairs i)).degree a.val from rfl,
          crossingGraph_left_degree]
        convert hp using 1 <;> first | (apply congrArg Finset.card; ext x; simp) | (split_ifs <;> rfl)
      rw [h]
      by_cases hz : (C.colourGraph i).degree v = 0 <;> simp [missingOn,hz,a] <;> omega
    · let b : (Lᶜ : Finset V) := ⟨v,mem_compl.mpr hv⟩
      have hp := P.col i (mem_univ i) b
      have h : (Q i).degree v = if b ∈ missingOn C Lᶜ i then 1 else 0 := by
        rw [show (Q i).degree v = (crossingGraph L (P.pairs i)).degree b.val from rfl,
          crossingGraph_right_degree]
        convert hp using 1 <;> first | (apply congrArg Finset.card; ext x; simp) | (split_ifs <;> rfl)
      rw [h]
      by_cases hz : (C.colourGraph i).degree v = 0 <;> simp [missingOn,hz,b] <;> omega
  let T : H.EdgeColoring k := {
    col e i := C.col e i + (Q i).mult e
    sum_col _ := rfl
    proper v i := by
      rw [sum_add_distrib]
      exact le_of_eq (hdegree v i) }
  have hH : H.IsRegularOfDegree k := by
    intro v
    change (∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e),
      ∑ i, (C.col e i + (Q i).mult e)) = k
    rw [sum_comm]
    calc
      _ = ∑ i : Fin k, 1 := sum_congr rfl (fun i _ => by rw [sum_add_distrib]; exact hdegree v i)
      _ = k := by simp
  have hcover (u v : V) (h : u ∈ L ↔ v ∈ L) : H.mult s(u,v) = M.mult s(u,v) := by
    change (∑ i, (C.col s(u,v) i + (Q i).mult s(u,v))) = _
    simp_rw [Q,crossingGraph_zero L _ u v h,Nat.add_zero,C.sum_col,
      M.internalPart_mult L u v,if_pos h]
  have hsub : ∀ e, H.mult e ≤ M.mult e := by
    intro e
    induction e using Sym2.inductionOn with
    | hf u v =>
      by_cases h : u ∈ L ↔ v ∈ L
      · exact (hcover u v h).le
      · have hcross (a : L) (b : (Lᶜ : Finset V)) :
            H.mult s(a.val,b.val) ≤ M.mult s(a.val,b.val) := by
          change (∑ i, (C.col s(a.val,b.val) i + (Q i).mult s(a.val,b.val))) ≤ _
          rw [sum_add_distrib,C.sum_col,M.internalPart_mult,if_neg (by simp [a.2,mem_compl.mp b.2]),
            zero_add]
          simp only [Q,crossingGraph_mult]
          have hh := P.bounded a b
          simp only [spent,card_eq_sum_ones,sum_filter] at hh
          convert hh using 1
          apply sum_congr rfl
          intro i _
          split_ifs <;> simp_all
        by_cases hu : u ∈ L
        · have hv : v ∉ L := fun hv => h (iff_of_true hu hv)
          exact hcross ⟨u,hu⟩ ⟨v,mem_compl.mpr hv⟩
        · have hv : v ∈ L := by by_contra hn; exact h (iff_of_false hu hn)
          rw [Sym2.eq_swap]
          exact hcross ⟨v,hv⟩ ⟨u,mem_compl.mpr hu⟩
  exact MultiGraph.exists_factorization_of_bipartite_residual M H L D k hk hsub hreg hH
    ⟨T⟩ (MultiGraph.bipartite_residual_of_internal_cover M H L hcover)

end WeightedPaper
