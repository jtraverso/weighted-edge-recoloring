import DesignsIIKahn.NibbleAll
import IncidencePacking

namespace WeightedPaper.Repair
open Finset Pseudorandom

/-- Initial ordinary matchings for all colors, with arbitrary demand-count
tests. The pairs input already encodes eligibility, block and color. A marked
copy can occur in several eligible pairs but in only one chosen pair. -/
theorem exists_nibble_packing (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ η : ℝ, 0 ≤ η → η < 1 →
    ∀ (I A B E J : Type) [Fintype I] [Fintype A] [Fintype B] [Fintype E] [Fintype J]
      [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E]
      (a : E → A) (b : E → B) (pairs : Finset (I × E)) (tests : J → Finset (DemandVertex I A B E)),
      let H := pairs.image (triple a b)
      (∀ v, (degree H v : ℝ) ≤ Δ) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ^(1-δ)) →
      (H.card : ℝ) ≤ Real.exp (Δ^((δ/450)^2)) →
      (Fintype.card J : ℝ) ≤ Real.exp (Δ^((δ/450)^2)) →
      (∀ j, ∀ v ∈ tests j, (1-η)*Δ ≤ (degree H v : ℝ)) →
      ∃ P ⊆ pairs, validPacking a b P ∧ ∀ j,
        (((tests j \ covered a b P).card : ℕ) : ℝ) ≤
        max ((η+Δ^(-(δ/450)))*(tests j).card) (3*Δ^δ/(1-η)) := by
  classical
  obtain ⟨Δ₀,H₀⟩ := DesignsII.nibble_matching_all δ hδ hδ' 3 (by decide)
  refine ⟨Δ₀, ?_⟩
  intro Δ hΔ η hη hη' I A B E J _ _ _ _ _ _ _ _ _ a b pairs tests H deg cod size count dense
  let p (j : J) (v : DemandVertex I A B E) : ℝ := if v ∈ tests j then 1 else 0
  have rank (e) (he : e ∈ H) : e.card ≤ 3 := by
    obtain ⟨z,_,rfl⟩ := mem_image.mp he
    exact (triple_card a b z).le
  obtain ⟨M,sub,hm,leave⟩ := H₀ Δ hΔ η hη hη' _ H rank deg cod
    (by norm_num at *; assumption) J p (fun j v => by dsimp [p]; split <;> norm_num)
    (fun j v => by dsimp [p]; split <;> norm_num) (by norm_num at *; assumption)
  obtain ⟨P,hP,packing,cov⟩ := packing_from_triples a b pairs M sub hm
  refine ⟨P,hP,packing,fun j => ?_⟩
  have h := leave j (fun v hv => dense j v (by by_contra hh; simp [p,hh] at hv))
  have inter : (univ \ M.biUnion id).filter (fun v => v ∈ tests j) = tests j \ M.biUnion id := by
    ext v; simp [and_comm]
  simp only [p, ← sum_filter, inter, sum_const, nsmul_eq_mul, mul_one] at h
  rw [cov]
  norm_num at h ⊢
  simpa using h
end WeightedPaper.Repair
