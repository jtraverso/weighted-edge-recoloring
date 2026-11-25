import WeightedPaper.Cut.PairDegreeFactorization
import WeightedPaper.Examples.HostBudget

namespace WeightedPaper.Examples

open Finset SimpleGraph
open scoped Classical

variable {X O : Type*} [Fintype X] [Fintype O] [DecidableEq X] [DecidableEq O]

theorem Host.finishPairDegree (P : Host X O) (D k a : ℕ) (hk : k ≤ D)
    (hreg : P.graph.IsRegularOfDegree D)
    (hcap : (P.graph.restrict (half X O false)).edgeCount ≤ k*a)
    (hA : Nonempty ((P.graph.restrict (half X O false)).EdgeColoring k))
    (hB : Nonempty ((P.graph.restrict (half X O true)).EdgeColoring k))
    (budget : HostBudget P k (equitableGap k (P.graph.restrict (half X O false)).edgeCount))
    (hcut : PairDegreeCondition (P.cap false true) (exSet X O false) (exSet X O true)
      (Fintype.card X + Fintype.card O) a k) :
    ∃ F : P.graph.EdgeColoring D, F.IsFactorization := by
  let L := half X O false
  have hm : L.card = Fintype.card X + Fintype.card O := side_card false
  have hcompl : Lᶜ = half X O true := half_compl false
  have bw : (fun (y : half X O true) (x : L) => P.graph.mult s(x.val,y.val)) = P.cap true false := by
    funext y x
    rw [Host.cap,Sym2.eq_swap]
  have hgo (T : Finset (Vertex X O)) (hT : T = Lᶜ)
      (Y : Finset T) (hB : Nonempty ((P.graph.restrict T).EdgeColoring k))
      (hTsize : T.card = Fintype.card X + Fintype.card O)
      (A : ExactIncidenceBudget P.graph T (fun (x : L) y => P.graph.mult s(x.val,y.val)) (exSet X O false) Y
        k (equitableGap k (P.graph.restrict L).edgeCount))
      (B : ExactIncidenceBudget P.graph L (fun (y : T) x => P.graph.mult s(x.val,y.val)) Y (exSet X O false)
        k (equitableGap k (P.graph.restrict L).edgeCount))
      (cut : PairDegreeCondition (fun (x : L) (y : T) => P.graph.mult s(x.val,y.val)) (exSet X O false) Y
        (Fintype.card X + Fintype.card O) a k) :
      ∃ F : P.graph.EdgeColoring D, F.IsFactorization := by
    subst T
    exact exists_factorization_of_pair_degree_cut P.graph L D k _ a hk hreg (exSet X O false)
      Y hm hTsize hcap hA hB A B cut
  exact hgo _ hcompl.symm _ hB (side_card true) (budget.lift Bool.false_ne_true).toExact
    (bw.symm ▸ (budget.lift (by decide : true ≠ false)).toExact) hcut

end WeightedPaper.Examples
