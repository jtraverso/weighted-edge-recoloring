import WeightedPaper.Blocks.BlockDeficit
import WeightedPaper.Blocks.BlockCutCriterion

namespace WeightedPaper.Blocks

open Finset SimpleGraph
open scoped Classical

variable {X Y J : Type*} [Fintype X] [Fintype Y] [Fintype J]

private abbrev Slot (capacity : J → ℕ) := Σ j, Fin (capacity j)

private def leftSlots (capacity : J → ℕ) (eA : X → J → Prop) :
    X ⊕ Slot capacity → J ⊕ J → Prop
  | .inl x, .inl j => eA x j
  | .inl _, .inr _ => False
  | .inr x, .inl j => x.1 = j
  | .inr x, .inr j => x.1 = j

private def rightSlots (eB : Y → J → Prop) (y : Y) : J ⊕ J → Prop
  | .inl _ => False
  | .inr j => eB y j

private def slotDemand (capacity : J → ℕ) (delta : J → ℤ) : J ⊕ J → ℤ
  | .inl j => delta j - capacity j
  | .inr _ => 0

/-- Quotient cuts on two copies of the block index. Each capacity slot
may be assigned to either copy of its own block. -/
def CapacitatedCuts (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (capacity : J → ℕ) : Prop :=
  TransportCuts (leftSlots capacity eA) (rightSlots eB) (slotDemand capacity delta)

/-- The original-block form of the capacitated cuts. A slot can move
capacity across the cut only from a block in `S` that is absent from `T`. -/
def TwoSetCapacityCut (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (capacity : J → ℕ) (S T : Finset J) : Prop :=
  (∑ j ∈ S, delta j) ≤
    ((univ.filter fun y => ∃ j ∈ T, eB y j).card : ℤ) -
    ((univ.filter fun x => ∀ j, eA x j → j ∈ S).card : ℤ) +
      ∑ j ∈ S \ T, (capacity j : ℤ)

def TwoSetCapacityCuts (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (capacity : J → ℕ) : Prop :=
  ∀ S T : Finset J, TwoSetCapacityCut eA eB delta capacity S T

private noncomputable def takeLeft (S : Finset (J ⊕ J)) : Finset J :=
  univ.filter (fun j => Sum.inl j ∈ S)

private noncomputable def takeRight (S : Finset (J ⊕ J)) : Finset J :=
  univ.filter (fun j => Sum.inr j ∈ S)

private theorem in_takeLeft {S : Finset (J ⊕ J)} {j : J} :
    j ∈ takeLeft S ↔ Sum.inl j ∈ S := by simp [takeLeft]

private theorem in_takeRight {S : Finset (J ⊕ J)} {j : J} :
    j ∈ takeRight S ↔ Sum.inr j ∈ S := by simp [takeRight]

private theorem count_slots_of_blocks (capacity : J → ℕ) (S : Finset J) :
    (univ.filter fun q : Slot capacity => q.1 ∈ S).card = ∑ j ∈ S, capacity j := by
  classical
  rw [card_filter,Fintype.sum_sigma]
  calc
    _ = ∑ j, if j ∈ S then capacity j else 0 := by
      apply sum_congr rfl
      intro j _
      by_cases h : j ∈ S <;> simp [h]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext j
      simp

set_option maxHeartbeats 800000 in
private theorem expand_capacitated_cut (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (capacity : J → ℕ) (C : Finset (J ⊕ J)) :
    let S := takeLeft C
    let T := takeRight C
    ((∑ j ∈ C, slotDemand capacity delta j) ≤
      ((univ.filter fun y => ∃ j ∈ C, rightSlots eB y j).card : ℤ) -
      ((univ.filter fun x => ∀ j, leftSlots capacity eA x j → j ∈ C).card : ℤ)) ↔
    TwoSetCapacityCut eA eB delta capacity S T := by
  classical
  intro S T
  unfold TwoSetCapacityCut
  have demand_sum : (∑ j ∈ C, slotDemand capacity delta j) =
      ∑ j ∈ S, (delta j - capacity j) := by
    have hC : C = univ.filter (fun j => j ∈ C) := by ext j; simp
    calc
      _ = ∑ j, if j ∈ C then slotDemand capacity delta j else 0 := by
        rw [← sum_filter]
        exact congrArg (fun P => ∑ j ∈ P, slotDemand capacity delta j) hC
      _ = _ := by
        simp only [Fintype.sum_sum_type,slotDemand,ite_self,sum_const_zero,add_zero]
        exact (sum_filter (s := (univ : Finset J)) (fun j => Sum.inl j ∈ C)
          (fun j => delta j - capacity j)).symm
  have right_count : (univ.filter fun y => ∃ j ∈ C, rightSlots eB y j).card =
      (univ.filter fun y => ∃ j ∈ T, eB y j).card := by
    apply card_filter_congr
    intro y
    constructor
    · rintro ⟨j,hj,h⟩
      cases j with
      | inl j => exact False.elim h
      | inr j => exact ⟨j,in_takeRight.mpr hj,h⟩
    · rintro ⟨j,hj,h⟩
      exact ⟨.inr j,in_takeRight.mp hj,h⟩
  have left_count : (univ.filter fun x => ∀ j, leftSlots capacity eA x j → j ∈ C).card =
      (univ.filter fun x => ∀ j, eA x j → j ∈ S).card + ∑ j ∈ S ∩ T, capacity j := by
    calc
      _ = (univ.filter (Sum.elim (fun x => ∀ j, eA x j → j ∈ S)
          (fun q : Slot capacity => q.1 ∈ S ∩ T))).card := by
        apply card_filter_congr
        intro x
        cases x with
        | inl x =>
          constructor
          · intro h j hj
            exact in_takeLeft.mpr (h (.inl j) hj)
          · intro h j hj
            cases j with
            | inl j => exact in_takeLeft.mp (h j hj)
            | inr j => exact False.elim hj
        | inr q =>
          constructor
          · intro h
            exact mem_inter.mpr ⟨in_takeLeft.mpr (h (.inl q.1) rfl),
              in_takeRight.mpr (h (.inr q.1) rfl)⟩
          · intro h j hj
            change _ at hj
            cases j with
            | inl j =>
              change q.1 = j at hj
              subst j
              exact in_takeLeft.mp (mem_inter.mp h).1
            | inr j =>
              change q.1 = j at hj
              subst j
              exact in_takeRight.mp (mem_inter.mp h).2
      _ = _ := by rw [card_filter_sum,count_slots_of_blocks]
  have hcap : (∑ j ∈ S \ T, (capacity j : ℤ)) + (∑ j ∈ S ∩ T, (capacity j : ℤ)) =
      ∑ j ∈ S, (capacity j : ℤ) := by
    have hd : Disjoint (S \ T) (S ∩ T) := by
      rw [Finset.disjoint_left]
      exact fun _ hx hy => (mem_sdiff.mp hx).2 (mem_inter.mp hy).2
    rw [← sum_union hd]
    congr 1
    ext j
    by_cases hj : j ∈ T <;> simp [hj]
  rw [demand_sum,right_count,left_count,sum_sub_distrib,Nat.cast_add,Nat.cast_sum]
  omega

set_option maxHeartbeats 850000 in
/-- The doubled quotient can be tested using two subsets of the original blocks. -/
theorem capacitated_cuts_iff_two_sets (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (capacity : J → ℕ) :
    CapacitatedCuts eA eB delta capacity ↔ TwoSetCapacityCuts eA eB delta capacity := by
  classical
  constructor
  · intro h S T
    let C : Finset (J ⊕ J) := S.map Function.Embedding.inl ∪ T.map Function.Embedding.inr
    have hS : takeLeft C = S := by ext j; simp [C,takeLeft]
    have hT : takeRight C = T := by ext j; simp [C,takeRight]
    have hh : TwoSetCapacityCut eA eB delta capacity (takeLeft C) (takeRight C) := by
      apply (expand_capacitated_cut eA eB delta capacity C).mp
      have hc := h C
      convert hc using 2
      apply congrArg (fun S : Finset (X ⊕ Slot capacity) => (S.card : ℤ))
      ext v
      simp
    rwa [hS,hT] at hh
  · intro h C
    have hh := (expand_capacitated_cut eA eB delta capacity C).mpr (h (takeLeft C) (takeRight C))
    convert hh using 2
    apply congrArg (fun S : Finset (X ⊕ Slot capacity) => (S.card : ℤ))
    ext v
    simp

private theorem count_split {V W Z : Type*} [Fintype V] [Fintype W] (f : V ⊕ W → Z) (z : Z) :
    assignedCount f z = assignedCount (fun v => f (.inl v)) z + assignedCount (fun w => f (.inr w)) z := by
  classical
  simp only [assignedCount,card_filter,Fintype.sum_sum_type]

omit [Fintype J] in
private theorem count_relabel_inl {V : Type*} [Fintype V] (f : V → J) (j : J) :
    assignedCount (J := J ⊕ J) (fun v => Sum.inl (f v)) (.inl j) = assignedCount f j := by
  classical
  unfold assignedCount
  congr 1
  ext v
  simp

omit [Fintype J] in
private theorem count_relabel_inr {V : Type*} [Fintype V] (f : V → J) (j : J) :
    assignedCount (J := J ⊕ J) (fun v => Sum.inr (f v)) (.inr j) = assignedCount f j := by
  classical
  unfold assignedCount
  congr 1
  ext v
  simp

private theorem slots_at (capacity : J → ℕ) (j : J) :
    (univ.filter fun x : Slot capacity => x.1 = j).card = capacity j := by
  classical
  calc
    _ = Fintype.card (Fin (capacity j)) := by
      rw [← card_univ]
      symm
      apply card_bij (fun x _ => (⟨j,x⟩ : Slot capacity))
      · intro x _
        exact mem_filter.mpr ⟨mem_univ _,rfl⟩
      · intro x _ y _ h
        simpa using h
      · intro x hx
        rcases x with ⟨l,x⟩
        have hl := (mem_filter.mp hx).2
        change l = j at hl
        subst l
        exact ⟨x,mem_univ _,rfl⟩
    _ = _ := Fintype.card_fin _

private theorem assigned_slots (capacity : J → ℕ) (f : Slot capacity → J ⊕ J)
    (h : ∀ q, f q = .inl q.1 ∨ f q = .inr q.1) (j : J) :
    assignedCount f (.inl j) + assignedCount f (.inr j) = capacity j := by
  classical
  let L := univ.filter (fun q : Slot capacity => f q = .inl j)
  let R := univ.filter (fun q : Slot capacity => f q = .inr j)
  have hd : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro q hL hR
    have hl := (mem_filter.mp hL).2
    have hr := (mem_filter.mp hR).2
    exact Sum.inl_ne_inr (hl.symm.trans hr)
  have hs : L ∪ R = univ.filter (fun q : Slot capacity => q.1 = j) := by
    ext q
    simp only [L,R,mem_union,mem_filter,mem_univ,true_and]
    rcases h q with hq|hq <;> simp [hq]
  have hl : assignedCount f (.inl j) = L.card := by
    unfold assignedCount
    congr 1
    ext q
    simp [L]
  have hr : assignedCount f (.inr j) = R.card := by
    unfold assignedCount
    congr 1
    ext q
    simp [R]
  rw [hl,hr,← card_union_of_disjoint hd,hs,slots_at]

set_option maxHeartbeats 850000 in
/-- The doubled quotient assigns every exception and enforces the exact
upper bound on the right exceptional vertices sent to each block. -/
theorem assign_of_capacitated_cuts (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (capacity : J → ℕ)
    (hδ : (∑ j, delta j) = (Fintype.card Y : ℤ) - Fintype.card X)
    (cuts : CapacitatedCuts eA eB delta capacity) :
    ∃ a : X → J, ∃ b : Y → J, (∀ x, eA x (a x)) ∧ (∀ y, eB y (b y)) ∧
      ∀ j, ((assignedCount b j : ℤ) - assignedCount a j = delta j) ∧ assignedCount b j ≤ capacity j := by
  classical
  have hTotal : (∑ t : J ⊕ J, slotDemand capacity delta t) =
      (Fintype.card Y : ℤ) - Fintype.card (X ⊕ Slot capacity) := by
    simp only [Fintype.sum_sum_type,slotDemand,sum_sub_distrib,← Nat.cast_sum,sum_const_zero,add_zero,
      Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,hδ,Nat.cast_add]
    omega
  obtain ⟨a',b',ha',hb',hbals⟩ :=
    assign_of_transport_cuts (leftSlots capacity eA) (rightSlots eB) (slotDemand capacity delta) hTotal cuts
  let a (x : X) := (a' (.inl x)).elim id id
  let b (y : Y) := (b' y).elim id id
  let f (q : Slot capacity) := a' (.inr q)
  have hA (x : X) : a' (.inl x) = .inl (a x) ∧ eA x (a x) := by
    have hx := ha' (.inl x)
    cases he : a' (.inl x) <;> simp_all [leftSlots,a]
  have hB (y : Y) : b' y = .inr (b y) ∧ eB y (b y) := by
    have hy := hb' y
    cases he : b' y <;> simp_all [rightSlots,b]
  have hF (q : Slot capacity) : f q = .inl q.1 ∨ f q = .inr q.1 := by
    have hq := ha' (.inr q)
    change leftSlots capacity eA (.inr q) (f q) at hq
    cases he : f q <;> simp_all [leftSlots]
  have eqA : (fun x : X => a' (.inl x)) = fun x => .inl (a x) := funext (fun x => (hA x).1)
  have eqB : b' = fun y => .inr (b y) := funext (fun y => (hB y).1)
  refine ⟨a,b,fun x => (hA x).2,fun y => (hB y).2,fun j => ?_⟩
  have hL : (assignedCount b' (.inl j) : ℤ) - assignedCount a' (.inl j) = delta j - capacity j :=
    hbals (.inl j)
  have hR : (assignedCount b' (.inr j) : ℤ) - assignedCount a' (.inr j) = 0 := hbals (.inr j)
  rw [count_split a' _,eqA,eqB,count_relabel_inl] at hL
  rw [count_split a' _,eqA,eqB,count_relabel_inr] at hR
  have zL : assignedCount (fun y => Sum.inr (b y)) (.inl j) = 0 := by simp [assignedCount]
  have zR : assignedCount (fun x => Sum.inl (a x)) (.inr j) = 0 := by simp [assignedCount]
  rw [zL] at hL
  rw [zR] at hR
  change (0:ℤ) - ((assignedCount a j + assignedCount f (.inl j) : ℕ) : ℤ) = _ at hL
  change (assignedCount b j : ℤ) - ((0 + assignedCount f (.inr j) : ℕ) : ℤ) = _ at hR
  have hCount := assigned_slots capacity f hF j
  omega

set_option maxHeartbeats 650000 in
/-- Place the unused capacity on the left copy of each block and the
used capacity on its right copy to recover the capacitated cuts. -/
theorem capacitated_cuts_of_assignment (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (capacity : J → ℕ) (a : X → J) (b : Y → J)
    (ha : ∀ x, eA x (a x)) (hb : ∀ y, eB y (b y))
    (h : ∀ j, ((assignedCount b j : ℤ) - assignedCount a j = delta j) ∧
      assignedCount b j ≤ capacity j) :
    CapacitatedCuts eA eB delta capacity := by
  classical
  have available (j : J) : assignedCount b j ≤ (univ : Finset (Fin (capacity j))).card := by
    simpa only [card_univ,Fintype.card_fin] using (h j).2
  choose T hT hTc using fun j => exists_subset_card_eq (available j)
  let f (q : Slot capacity) : J ⊕ J := if q.2 ∈ T q.1 then .inr q.1 else .inl q.1
  let a' : X ⊕ Slot capacity → J ⊕ J := Sum.elim (fun x => .inl (a x)) f
  let b' : Y → J ⊕ J := fun y => .inr (b y)
  have hdir (q : Slot capacity) : f q = .inl q.1 ∨ f q = .inr q.1 := by
    by_cases hq : q.2 ∈ T q.1 <;> simp [f,hq]
  have hcount (j : J) : assignedCount f (.inr j) = assignedCount b j := by
    rw [← hTc j]
    symm
    unfold assignedCount
    apply card_bij (fun x _ => (⟨j,x⟩ : Slot capacity))
    · intro x hx
      simp [f,hx]
    · intro x _ y _ he
      simpa using he
    · intro q hq
      rcases q with ⟨l,x⟩
      have hq' : f ⟨l,x⟩ = .inr j := by simpa only [mem_filter,mem_univ,true_and] using hq
      by_cases hx : x ∈ T l
      · have hj : l = j := by simpa [f,hx] using hq'
        subst l
        exact ⟨x,hx,rfl⟩
      · simp [f,hx] at hq'
  apply transport_cuts_of_assignment _ _ _ a' b'
  · intro x
    rcases x with x|q
    · exact ha x
    · rcases hdir q with hq|hq <;> simp [a',hq,leftSlots]
  · exact hb
  · intro j
    change (assignedCount b' j : ℤ)-assignedCount a' j = slotDemand capacity delta j
    have zL (j : J) : assignedCount b' (.inl j) = 0 := by simp [assignedCount,b']
    have zR (j : J) : assignedCount (fun x => Sum.inl (a x)) (.inr j) = 0 := by simp [assignedCount]
    cases j with
    | inl j =>
      rw [count_split a' _]
      change (assignedCount b' (.inl j) : ℤ) -
        ((assignedCount (fun x => Sum.inl (a x)) (.inl j) + assignedCount f (.inl j) : ℕ) : ℤ) = _
      rw [zL,count_relabel_inl,slotDemand]
      have hc := assigned_slots capacity f hdir j
      have hd := hcount j
      have he := (h j).1
      omega
    | inr j =>
      rw [count_split a' _]
      change (assignedCount (fun y => Sum.inr (b y)) (.inr j) : ℤ) -
        ((assignedCount (fun x => Sum.inl (a x)) (.inr j) + assignedCount f (.inr j) : ℕ) : ℤ) = _
      rw [zR,count_relabel_inr,hcount,slotDemand]
      simp

theorem capacitated_cuts_iff_assignment (eA : X → J → Prop) (eB : Y → J → Prop)
    (delta : J → ℤ) (capacity : J → ℕ)
    (hδ : (∑ j, delta j) = (Fintype.card Y : ℤ) - Fintype.card X) :
    CapacitatedCuts eA eB delta capacity ↔
      ∃ a : X → J, ∃ b : Y → J, (∀ x, eA x (a x)) ∧ (∀ y, eB y (b y)) ∧
        ∀ j, ((assignedCount b j : ℤ) - assignedCount a j = delta j) ∧
          assignedCount b j ≤ capacity j := by
  constructor
  · exact assign_of_capacitated_cuts eA eB delta capacity hδ
  · rintro ⟨a,b,ha,hb,h⟩
    exact capacitated_cuts_of_assignment eA eB delta capacity a b ha hb h

section Multigraph

variable {A B : Type*}

/-- Each block offers as many slots as its actual free ordinary
count allows after retaining the matching threshold. -/
def BlockCapacityCuts (U : Finset A) (W : Finset B) (E : Finset A) (F : Finset B)
    (left : A → J) (right : B → J) (threshold : J → ℕ)
    (eA : A → J → Prop) (eB : B → J → Prop) : Prop :=
  U.card = W.card ∧
  (∀ j, threshold j ≤ (fiber (U \ E) left j).card) ∧
  TwoSetCapacityCuts (fun (x : ↥(U ∩ E)) j => eA x j) (fun (y : ↥(W ∩ F)) j => eB y j)
    (imbalance U W E F left right) (fun j => (fiber (U \ E) left j).card-threshold j)

set_option maxHeartbeats 650000 in
theorem route_of_block_capacity_cuts (U : Finset A) (W : Finset B) (E : Finset A) (F : Finset B)
    (left : A → J) (right : B → J) (threshold : J → ℕ)
    (eA : A → J → Prop) (eB : B → J → Prop)
    (cuts : BlockCapacityCuts U W E F left right threshold eA eB) :
    Nonempty (Routing U W E F left right threshold eA eB) := by
  classical
  obtain ⟨heq,hwidth,hcuts⟩ := cuts
  obtain ⟨a,b,ha,hb,h⟩ := assign_of_capacitated_cuts _ _ _ _
    (sum_imbalance U W E F left right heq) ((capacitated_cuts_iff_two_sets _ _ _ _).mpr hcuts)
  let a' := extendAssignment U E left a
  let b' := extendAssignment W F right b
  refine ⟨⟨a',b',?_,?_,?_,?_,?_,?_⟩⟩
  · intro x hx
    simp [a',extendAssignment,(mem_sdiff.mp hx).2]
  · intro y hy
    simp [b',extendAssignment,(mem_sdiff.mp hy).2]
  · intro x hx
    simpa [a',extendAssignment,hx] using ha ⟨x,hx⟩
  · intro y hy
    simpa [b',extendAssignment,hy] using hb ⟨y,hy⟩
  · intro j
    have hA := card_sdiff_add_card_inter (fiber U a' j) E
    have hB := card_sdiff_add_card_inter (fiber W b' j) F
    rw [routed_ordinary,routed_exceptional] at hA hB
    have hh := (h j).1
    simp only [imbalance,assignedCount,Finset.univ_eq_attach] at hh hA hB
    omega
  · intro j
    have hA := card_sdiff_add_card_inter (fiber U a' j) E
    rw [routed_ordinary] at hA
    have hc := routed_exceptional W F right b j
    have hh := (h j).2
    have hw := hwidth j
    change (fiber W b' j ∩ F).card = _ at hc
    simp only [assignedCount,Finset.univ_eq_attach] at hh hc
    omega

/-- Factorization under the exact block capacities from the ordinary threshold. -/
theorem exists_factorization_of_block_capacity_cuts {V : Type*} [Fintype V] [DecidableEq V]
    (M : MultiGraph V) (L : Finset V) (D k : ℕ) (hk : k ≤ D) (hreg : M.IsRegularOfDegree D)
    (C : (M.internalPart L).EdgeColoring k) (E : Finset L) (F : Finset (Lᶜ : Finset V))
    (left : L → J) (right : (Lᶜ : Finset V) → J) (threshold : J → ℕ)
    (eligibleA : Fin k → L → J → Prop) (eligibleB : Fin k → (Lᶜ : Finset V) → J → Prop)
    (hrect : ∀ j, Rectangle (fun x y => M.mult s(x.val,y.val))
      (fiber (ordinary E) left j) (fiber (ordinary F) right j) (threshold j) k)
    (rowsA : BlockReserves (missingOn C L) (missingOn C Lᶜ) (fun x y => M.mult s(x.val,y.val))
      univ E F right eligibleA)
    (rowsB : BlockReserves (missingOn C Lᶜ) (missingOn C L) (fun y x => M.mult s(x.val,y.val))
      univ F E left eligibleB)
    (cuts : ∀ i, BlockCapacityCuts (missingOn C L i) (missingOn C Lᶜ i)
      E F left right threshold (eligibleA i) (eligibleB i)) :
    ∃ P : M.EdgeColoring D, P.IsFactorization :=
  exists_factorization_of_block_routing M L D k hk hreg C E F left right threshold eligibleA eligibleB
    hrect rowsA rowsB (fun i => route_of_block_capacity_cuts _ _ E F left right threshold _ _ (cuts i))

end Multigraph

end WeightedPaper.Blocks

#print axioms WeightedPaper.Blocks.capacitated_cuts_iff_two_sets
#print axioms WeightedPaper.Blocks.capacitated_cuts_iff_assignment
#print axioms WeightedPaper.Blocks.exists_factorization_of_block_capacity_cuts
