module

public import CopyCapacity
public import ExceptionalHost

@[expose] public section


namespace WeightedPaper.Repair
open Finset Pseudorandom
open scoped Classical
variable {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E] [Nonempty A]

noncomputable def demandError (δ Δ η : ℝ) (z : ℕ) :=
  max ((η+Δ^(-(δ/450)))*z) (3*Δ^δ/(1-η))

/-- The quantitative data and hypotheses of the nibble and spectral repair
on the ordinary sets left by a feasible choice of exceptional matches. -/
structure HybridCertificate (δ Δ₀ : ℝ)
    (a : E → A) (b : E → B) (R : A → B → Prop) [DecidableRel R]
    (X : I → Finset A) (Y : I → Finset B) where
  pairs : Finset (I × E)
  Δ : ℝ
  η : ℝ
  d : ℕ
  σ : ℝ
  β : ℝ
  h : ℕ
  large : Δ₀ ≤ Δ
  eta0 : 0 ≤ η
  eta1 : η < 1
  positive : 0 < d
  regA : ∀ x, (univ.filter (R x)).card = d
  regB : ∀ y, (univ.filter (fun x => R x y)).card = d
  sideCard : Fintype.card A = Fintype.card B
  freeCard : ∀ i, (X i).card = (Y i).card
  eligible : ∀ p ∈ pairs, a p.2 ∈ X p.1 ∧ b p.2 ∈ Y p.1
  degree_le : ∀ v, (degree (pairs.image (triple a b)) v : ℝ) ≤ Δ
  codegree_le : ∀ u v, u ≠ v → (codegree (pairs.image (triple a b)) u v : ℝ) ≤ Δ^(1-δ)
  size_le : ((pairs.image (triple a b)).card : ℝ) ≤ Real.exp (Δ^((δ/450)^2))
  test_le : (Fintype.card (TestIndex I A B) : ℝ) ≤ Real.exp (Δ^((δ/450)^2))
  demandA : ∀ i x, x ∈ X i → (1-η)*Δ ≤ (degree (pairs.image (triple a b)) (.inl (i,x)) : ℝ)
  demandB : ∀ i y, y ∈ Y i → (1-η)*Δ ≤ (degree (pairs.image (triple a b)) (.inr (.inl (i,y))) : ℝ)
  sigma0 : 0 ≤ σ
  sigma1 : σ ≤ 1
  beta0 : 0 ≤ β
  spectrum : ∀ f : A → ℝ, ∑ x, f x = 0 →
    (∑ y, (∑ x, f x * (if R x y then 1/(d:ℝ) else 0))^2) ≤ σ^2 * ∑ x, (f x)^2
  missedA : ∀ i x, (((Y i)ᶜ.filter (R x)).card : ℝ) ≤ β*d
  missedB : ∀ i y, (((X i)ᶜ.filter (fun x => R x y)).card : ℝ) ≤ β*d
  length : 0 < h
  mixing : σ^h ≤ 1/(2*(Fintype.card A : ℝ))
  budget1 : 3*(2*h : ℕ)*(β+demandError δ Δ η d/d) ≤ 1/2
  budget2 :
    let t := demandError δ Δ η (Fintype.card I)
    let ρ := β+demandError δ Δ η d/d
    (2*(h:ℝ)+1)*(6*(2*t+(2*h-1 : ℕ)*(Fintype.card I : ℝ)*ρ)/d) +
      (2*(h:ℝ))*(6*(2*h : ℕ)*ρ) ≤ 4/27

/-- Capacity in the two disjoint ordinary pools, including all identified
parallel copies of the bulk pool. -/
noncomputable def ordinaryCapacity (a : E → A) (b : E → B)
    (R : A → B → Prop) [DecidableRel R] (x : A) (y : B) :=
  (univ.filter (fun e => a e = x ∧ b e = y)).card + if R x y then 1 else 0

theorem ordinary_completion_of_hybrid (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ Δ₀ : ℝ, ∀ {I A B E : Type} [Fintype I] [Fintype A] [Fintype B] [Fintype E]
      [DecidableEq I] [DecidableEq A] [DecidableEq B] [DecidableEq E] [Nonempty A],
    ∀ (a : E → A) (b : E → B) (R : A → B → Prop) [DecidableRel R]
      (X : I → Finset A) (Y : I → Finset B), HybridCertificate δ Δ₀ a b R X Y →
      ∃ F : ∀ i, ↥(X i) ≃ ↥(Y i), ∀ x y, spending univ (fun i => pairsOf (F i)) x y ≤ ordinaryCapacity a b R x y := by
  obtain ⟨Δ₀,hybrid⟩ := nibble_and_spectral_repair δ hδ hδ'
  refine ⟨Δ₀,?_⟩
  intro I A B E _ _ _ _ _ _ _ _ _ a b R dec X Y H
  obtain ⟨P,Q,F,_,pack,disj,uses⟩ := hybrid H.Δ H.large H.η H.eta0 H.eta1 a b H.pairs X Y R H.d
    H.positive H.regA H.regB H.sideCard H.freeCard H.eligible H.degree_le H.codegree_le H.size_le
    H.test_le (fun i x hx => H.demandA i x hx) (fun i y hy => H.demandB i y hy)
    H.σ H.β H.sigma0 H.sigma1 H.beta0 H.spectrum H.missedA H.missedB H.h H.length H.mixing H.budget1 H.budget2
  refine ⟨F,fun x y => ?_⟩
  have h := hybrid_spending_le a b R P pack Q disj X Y F uses x y
  simpa only [spending,mem_pairsOf,ordinaryCapacity] using h
end WeightedPaper.Repair
