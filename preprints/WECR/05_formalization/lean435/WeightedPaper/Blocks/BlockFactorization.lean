import WeightedPaper.Blocks.BlockMatching

namespace WeightedPaper.Blocks

open Finset SimpleGraph
open scoped Classical

variable {I J A B : Type*} [Fintype A] [Fintype B]

/-- The rows eligible for a block are certified using only the free
ordinary columns of that block. Weights may differ between blocks. -/
abbrev BlockReserves (U : I → Finset A) (W : I → Finset B) (cap : A → B → ℕ)
    (K : Finset I) (X : Finset A) (Y : Finset B) (right : B → J)
    (eligible : I → A → J → Prop) :=
  ∀ j, RowReserves (fun i => (U i).filter fun x => eligible i x j)
    (fun i => fiber (W i) right j) cap K X Y

/-- A routing keeps every ordinary vertex in its own block and sends
each exceptional vertex to an eligible block. The augmented fibers are
balanced, and their ordinary remainder meets the rectangle threshold. -/
structure Routing (U : Finset A) (W : Finset B) (X : Finset A) (Y : Finset B)
    (left : A → J) (right : B → J) (threshold : J → ℕ)
    (eligibleA : A → J → Prop) (eligibleB : B → J → Prop) where
  assignA : A → J
  assignB : B → J
  ordinaryA : ∀ x ∈ U \ X, assignA x = left x
  ordinaryB : ∀ y ∈ W \ Y, assignB y = right y
  exceptionalA : ∀ x ∈ U ∩ X, eligibleA x (assignA x)
  exceptionalB : ∀ y ∈ W ∩ Y, eligibleB y (assignB y)
  balance : ∀ j, (fiber U assignA j).card = (fiber W assignB j).card
  size : ∀ j, threshold j + (fiber U assignA j ∩ X).card + (fiber W assignB j ∩ Y).card ≤
    (fiber U assignA j).card

theorem packing_of_block_routing (U : I → Finset A) (W : I → Finset B) (cap : A → B → ℕ)
    (K : Finset I) (X : Finset A) (Y : Finset B) (left : A → J) (right : B → J)
    (threshold : J → ℕ) (eligibleA : I → A → J → Prop) (eligibleB : I → B → J → Prop)
    (hrect : ∀ j, Rectangle cap (fiber (ordinary X) left j) (fiber (ordinary Y) right j) (threshold j) K.card)
    (rowsA : BlockReserves U W cap K X Y right eligibleA)
    (rowsB : BlockReserves W U (fun y x => cap x y) K Y X left eligibleB)
    (routes : ∀ i ∈ K, Nonempty (Routing (U i) (W i) X Y left right threshold (eligibleA i) (eligibleB i))) :
    Nonempty (CrossingPacking U W cap K) := by
  classical
  apply exists_crossing_packing U W cap K
  intro i hi loss hLossA hLossB
  obtain ⟨r⟩ := routes i hi
  apply glue_matchings (U i) (W i) r.assignA r.assignB (fun x y => 0 < cap x y - loss x y)
  intro j
  apply matching_of_rectangle (fiber (U i) r.assignA j) (fiber (W i) r.assignB j)
    X _ Y _ cap loss (threshold j) K.card (card_pos.mpr ⟨i,hi⟩) (r.balance j)
    _ _ (r.size j) hLossA hLossB _ _ (hrect j)
  · intro x hx
    obtain ⟨hx₁,hx₂⟩ := mem_sdiff.mp hx
    obtain ⟨hxU,hxj⟩ := mem_fiber.mp hx₁
    exact mem_fiber.mpr ⟨((mem_ordinary X x).mpr hx₂),(r.ordinaryA x (mem_sdiff.mpr ⟨hxU,hx₂⟩)).symm.trans hxj⟩
  · intro y hy
    obtain ⟨hy₁,hy₂⟩ := mem_sdiff.mp hy
    obtain ⟨hyW,hyj⟩ := mem_fiber.mp hy₁
    exact mem_fiber.mpr ⟨((mem_ordinary Y y).mpr hy₂),(r.ordinaryB y (mem_sdiff.mpr ⟨hyW,hy₂⟩)).symm.trans hyj⟩
  · intro Q hQ
    have hsub : Q ⊆ ((U i).filter fun x => eligibleA i x j).filter (· ∈ X) := by
      intro x hx
      obtain ⟨hx₁,hxX⟩ := mem_inter.mp (hQ hx)
      obtain ⟨hxU,hxj⟩ := mem_fiber.mp hx₁
      have he := r.exceptionalA x (mem_inter.mpr ⟨hxU,hxX⟩)
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hxU,hxj ▸ he⟩,hxX⟩
    apply ((rowsA j).hall i hi loss hLossA Q hsub).trans
    apply card_le_card
    intro y hy
    obtain ⟨hy₁,hyY,hyAdj⟩ := mem_filter.mp hy
    obtain ⟨hyW,hyj⟩ := mem_fiber.mp hy₁
    exact mem_filter.mpr ⟨mem_fiber.mpr ⟨hyW,(r.ordinaryB y (mem_sdiff.mpr ⟨hyW,hyY⟩)).trans hyj⟩,hyAdj⟩
  · intro Q hQ
    have hsub : Q ⊆ ((W i).filter fun y => eligibleB i y j).filter (· ∈ Y) := by
      intro y hy
      obtain ⟨hy₁,hyY⟩ := mem_inter.mp (hQ hy)
      obtain ⟨hyW,hyj⟩ := mem_fiber.mp hy₁
      have he := r.exceptionalB y (mem_inter.mpr ⟨hyW,hyY⟩)
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hyW,hyj ▸ he⟩,hyY⟩
    apply ((rowsB j).hall i hi (fun y x => loss x y) hLossB Q hsub).trans
    apply card_le_card
    intro x hx
    obtain ⟨hx₁,hxX,hxAdj⟩ := mem_filter.mp hx
    obtain ⟨hxU,hxj⟩ := mem_fiber.mp hx₁
    exact mem_filter.mpr ⟨mem_fiber.mpr ⟨hxU,(r.ordinaryA x (mem_sdiff.mpr ⟨hxU,hxX⟩)).trans hxj⟩,hxAdj⟩

theorem exists_factorization_of_block_routing {V : Type*} [Fintype V] [DecidableEq V]
    (M : MultiGraph V) (L : Finset V) (D k : ℕ) (hk : k ≤ D) (hreg : M.IsRegularOfDegree D)
    (C : (M.internalPart L).EdgeColoring k) (X : Finset L) (Y : Finset (Lᶜ : Finset V))
    (left : L → J) (right : (Lᶜ : Finset V) → J) (threshold : J → ℕ)
    (eligibleA : Fin k → L → J → Prop) (eligibleB : Fin k → (Lᶜ : Finset V) → J → Prop)
    (hrect : ∀ j, Rectangle (fun x y => M.mult s(x.val,y.val))
      (fiber (ordinary X) left j) (fiber (ordinary Y) right j) (threshold j) k)
    (rowsA : BlockReserves (missingOn C L) (missingOn C Lᶜ) (fun x y => M.mult s(x.val,y.val))
      univ X Y right eligibleA)
    (rowsB : BlockReserves (missingOn C Lᶜ) (missingOn C L) (fun y x => M.mult s(x.val,y.val))
      univ Y X left eligibleB)
    (routes : ∀ i, Nonempty (Routing (missingOn C L i) (missingOn C Lᶜ i)
      X Y left right threshold (eligibleA i) (eligibleB i))) :
    ∃ F : M.EdgeColoring D, F.IsFactorization := by
  classical
  obtain ⟨P⟩ := packing_of_block_routing (missingOn C L) (missingOn C Lᶜ)
    (fun x y => M.mult s(x.val,y.val)) univ X Y left right threshold eligibleA eligibleB
    (by simpa using hrect) rowsA rowsB (fun i _ => routes i)
  exact exists_factorization_of_crossing_packing M L D k hk hreg C P

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.exists_factorization_of_block_routing
