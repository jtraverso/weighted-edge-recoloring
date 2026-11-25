import WeightedPaper.Assembly
import WeightedPaper.RobustCut
import WeightedPaper.RankOne

namespace WeightedPaper
open Finset SimpleGraph
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Fixed cut hypotheses independent of the exceptional row reserves. -/
def DenseCut (cap : A → B → ℕ) (X : Finset A) (Y : Finset B) (m a k : ℕ) : Prop :=
  ∃ δA δB : ℕ, m + 2*a + 2*(k-1) ≤ δA+δB ∧
    (∀ x ∉ X, δA ≤ (Yᶜ.filter fun y => 0 < cap x y).card) ∧
    (∀ y ∉ Y, δB ≤ (Xᶜ.filter fun x => 0 < cap x y).card)

def RobustCut (cap : A → B → ℕ) (X : Finset A) (Y : Finset B) (a k : ℕ) : Prop :=
  ∃ r t : ℕ, 2*a + max X.card Y.card ≤ r ∧ k ≤ r ∧
    (∀ x ∉ X, t + (2*a + max X.card Y.card) + (k-1) ≤
      (Yᶜ.filter fun y => 0 < cap x y).card) ∧
    (∀ y ∉ Y, t + (2*a + max X.card Y.card) + (k-1) ≤
      (Xᶜ.filter fun x => 0 < cap x y).card) ∧
    (∀ S ⊆ Xᶜ, t ≤ S.card → S.card+t ≤ (Xᶜ : Finset A).card →
      S.card+r ≤ (Yᶜ.filter fun y => r ≤ (S.filter fun x => 0 < cap x y).card).card)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unified cut theorem after reserving the exceptional rows.
The conclusion factors the actual ambient multigraph, including all
parallel copies and every crossing edge between exceptional vertices. -/
theorem exists_factorization_across_cut_of_reserves (M : MultiGraph V) (L : Finset V)
    (D k m a : ℕ) (hk : k ≤ D) (hreg : M.IsRegularOfDegree D)
    (C : (M.internalPart L).EdgeColoring k)
    (X : Finset L) (Y : Finset (Lᶜ : Finset V)) (ai : Fin k → ℕ)
    (hmA : L.card = m) (hmB : (Lᶜ : Finset V).card = m)
    (hsize : ∀ i, (missingOn C L i).card+2*ai i = m ∧
      (missingOn C Lᶜ i).card+2*ai i = m ∧ ai i ≤ a)
    (hrowA : RowReserves (missingOn C L) (missingOn C Lᶜ)
      (fun x y => M.mult s(x.val,y.val)) univ X Y)
    (hrowB : RowReserves (missingOn C Lᶜ) (missingOn C L)
      (fun y x => M.mult s(x.val,y.val)) univ Y X)
    (hcut : DenseCut (fun x y => M.mult s(x.val,y.val)) X Y m a k ∨
      RobustCut (fun x y => M.mult s(x.val,y.val)) X Y a k) :
    ∃ F : M.EdgeColoring D, F.IsFactorization := by
  classical
  let cap := fun (x : L) (y : (Lᶜ : Finset V)) => M.mult s(x.val,y.val)
  let U := missingOn C L
  let W := missingOn C Lᶜ
  let K : Finset (Fin k) := univ
  have hK : K.card = k := by simp [K]
  have hA : Fintype.card L = m := by simpa using hmA
  have hB : Fintype.card (↥(Lᶜ : Finset V)) = m := by simpa only [Fintype.card_coe] using hmB
  have hP : Nonempty (CrossingPacking U W cap K) := by
    rcases hcut with hd|hr
    · obtain ⟨δA, δB, hD, hδA, hδB⟩ := hd
      exact exists_crossing_packing_of_dense_cut U W cap K X Y
        m a δA δB ai hA hB (fun i _ => hsize i) (by rwa [hK]) hδA hδB hrowA hrowB
    · obtain ⟨r,t,hMargin,hPrev,hδA,hδB,hExpand⟩ := hr
      exact exists_crossing_packing_of_robust_cut U W cap K X Y
        m a r t ai hA hB (fun i _ => hsize i) hMargin (by rwa [hK])
        (by rwa [hK]) (by rwa [hK]) hExpand hrowA hrowB
  obtain ⟨P⟩ := hP
  exact exists_factorization_of_crossing_packing M L D k hk hreg C P

end WeightedPaper
