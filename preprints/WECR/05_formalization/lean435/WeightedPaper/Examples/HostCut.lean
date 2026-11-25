import WeightedPaper.Examples.Host

namespace WeightedPaper.Examples

open Finset SimpleGraph
open scoped Classical

variable {X O : Type*} [Fintype X] [Fintype O] [DecidableEq X] [DecidableEq O]

def exEmb (b : Bool) : X ↪ half X O b :=
  ⟨fun x => sideEquiv b (.inl x), fun _ _ h => Sum.inl.inj ((sideEquiv b).injective h)⟩

def ordEmb (b : Bool) : O ↪ half X O b :=
  ⟨fun o => sideEquiv b (.inr o), fun _ _ h => Sum.inr.inj ((sideEquiv b).injective h)⟩

def exSet (X O : Type*) [Fintype X] [Fintype O] [DecidableEq X] [DecidableEq O] (b : Bool) :
    Finset (half X O b) := univ.map (exEmb b)

def ordSet (X O : Type*) [Fintype X] [Fintype O] [DecidableEq X] [DecidableEq O] (b : Bool) :
    Finset (half X O b) := univ.map (ordEmb b)

@[simp] theorem exEmb_val (b : Bool) (x : X) :
    ((exEmb (O:=O) b x : half X O b) : Vertex X O) = (b,.inl x) := rfl

@[simp] theorem ordEmb_val (b : Bool) (o : O) :
    ((ordEmb (X:=X) b o : half X O b) : Vertex X O) = (b,.inr o) := rfl

theorem exSet_compl (b : Bool) : (exSet X O b)ᶜ = ordSet X O b := by
  ext v
  obtain ⟨x|o,rfl⟩ := (sideEquiv (X:=X) (O:=O) b).surjective v
  · constructor
    · intro h
      exact ((mem_compl.mp h) (mem_map.mpr ⟨x,mem_univ _,rfl⟩)).elim
    · intro h
      obtain ⟨y,_,hy⟩ := mem_map.mp h
      have hf : (Sum.inr y : X ⊕ O) = Sum.inl x := congrArg (fun v : half X O b => v.val.2) hy
      cases hf
  · constructor
    · intro _
      exact mem_map.mpr ⟨o,mem_univ _,rfl⟩
    · intro _
      apply mem_compl.mpr
      intro h
      obtain ⟨x,_,hx⟩ := mem_map.mp h
      have hf : (Sum.inl x : X ⊕ O) = Sum.inr o := congrArg (fun v : half X O b => v.val.2) hx
      cases hf

@[simp] theorem card_exSet (b : Bool) : (exSet X O b).card = Fintype.card X := by
  simp [exSet]

@[simp] theorem card_ordSet (b : Bool) : (ordSet X O b).card = Fintype.card O := by
  simp [ordSet]

theorem exists_ord_of_not_ex {b : Bool} {v : half X O b} (hv : v ∉ exSet X O b) :
    ∃ o, ordEmb b o = v := by
  have h := mem_compl.mpr hv
  rw [exSet_compl] at h
  obtain ⟨o,_,he⟩ := mem_map.mp h
  exact ⟨o,he⟩

def Host.cap (P : Host X O) (b c : Bool) (x : half X O b) (y : half X O c) : ℕ :=
  P.graph.mult s(x.val,y.val)

@[simp] theorem Host.capOrd (P : Host X O) {b c : Bool} (hbc : b ≠ c) (x y : O) :
    P.cap b c (ordEmb b x) (ordEmb c y) = P.ordinary x y := by simp [Host.cap,Host.adj,hbc,Host.cross]

@[simp] theorem Host.capInc (P : Host X O) {b c : Bool} (hbc : b ≠ c) (x : X) (y : O) :
    P.cap b c (exEmb b x) (ordEmb c y) = P.incidence x y := by simp [Host.cap,Host.adj,hbc,Host.cross]

theorem Host.ordinaryNeighbours (P : Host X O) {b c : Bool} (hbc : b ≠ c) (x : O) :
    ((ordSet X O c).filter (fun y => 0 < P.cap b c (ordEmb b x) y)).card =
      (univ.filter (fun y => 0 < P.ordinary x y)).card := by
  rw [ordSet,filter_map,card_map]
  simp [P.capOrd hbc]

theorem Host.ordinaryNeighbours_compl (P : Host X O) {b c : Bool} (hbc : b ≠ c) (x : O) :
    (((exSet X O c)ᶜ).filter (fun y => 0 < P.cap b c (ordEmb b x) y)).card =
      (univ.filter (fun y => 0 < P.ordinary x y)).card := by
  rw [exSet_compl,P.ordinaryNeighbours hbc]

theorem Host.ordinaryNeighbours_compl' (P : Host X O) {b c : Bool} (hbc : b ≠ c) (x : O) :
    (((exSet X O b)ᶜ).filter (fun y => 0 < P.cap b c y (ordEmb c x))).card =
      (univ.filter (fun y => 0 < P.ordinary x y)).card := by
  have he (y : half X O b) : P.cap b c y (ordEmb c x) = P.cap c b (ordEmb c x) y :=
    congrArg P.graph.mult Sym2.eq_swap
  simp_rw [he]
  exact P.ordinaryNeighbours_compl (Ne.symm hbc) x

theorem Host.dense (P : Host X O) {b c : Bool} (hbc : b ≠ c)
    (a k δ : ℕ) (hm : Fintype.card X + Fintype.card O + 2*a+2*(k-1) ≤ 2*δ)
    (hd : ∀ v, δ ≤ (univ.filter fun w => 0 < P.ordinary v w).card) :
    DenseCut (P.cap b c) (exSet X O b) (exSet X O c) (Fintype.card X+Fintype.card O) a k := by
  refine ⟨δ,δ,by omega,?_,?_⟩
  · intro v hv
    obtain ⟨x,rfl⟩ := exists_ord_of_not_ex hv
    have hh := (hd x).trans_eq (P.ordinaryNeighbours_compl hbc x).symm
    convert hh using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp)
  · intro v hv
    obtain ⟨x,rfl⟩ := exists_ord_of_not_ex hv
    have hh := (hd x).trans_eq (P.ordinaryNeighbours_compl' hbc x).symm
    convert hh using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp)

theorem Host.not_dense_of_ordinary_upper (P : Host X O) {b c : Bool} (hbc : b ≠ c)
    (a k δ : ℕ) (v : O) (hv : (univ.filter fun w => 0 < P.ordinary v w).card ≤ δ)
    (hm : 2*δ < Fintype.card X + Fintype.card O) :
    ¬ DenseCut (P.cap b c) (exSet X O b) (exSet X O c) (Fintype.card X+Fintype.card O) a k := by
  rintro ⟨δA,δB,hcut,hA,hB⟩
  have hOrd (s : Bool) : ordEmb s v ∉ exSet X O s := by
    rw [← mem_compl, exSet_compl]
    exact mem_map.mpr ⟨v,mem_univ _,rfl⟩
  have hleft := hA (ordEmb b v) (hOrd b)
  have hright := hB (ordEmb c v) (hOrd c)
  have hl : δA ≤ δ := by
    refine le_trans ?_ ((P.ordinaryNeighbours_compl hbc v).le.trans hv)
    convert hleft using 1 <;> first | rfl | (apply congrArg Finset.card; ext z; simp)
  have hr : δB ≤ δ := by
    refine le_trans ?_ ((P.ordinaryNeighbours_compl' hbc v).le.trans hv)
    convert hright using 1 <;> first | rfl | (apply congrArg Finset.card; ext z; simp)
  omega

theorem Host.robust (P : Host X O) {b c : Bool} (hbc : b ≠ c)
    (a k r t : ℕ) (hMargin : 2*a + Fintype.card X ≤ r) (hp : k ≤ r)
    (hd : ∀ v, t + (2*a + Fintype.card X) + (k-1) ≤ (univ.filter fun w => 0 < P.ordinary v w).card)
    (hExpand : ∀ S : Finset O, t ≤ S.card → S.card+t ≤ Fintype.card O →
      S.card+r ≤ (univ.filter fun y => r ≤ (S.filter fun x => 0 < P.ordinary x y).card).card) :
    RobustCut (P.cap b c) (exSet X O b) (exSet X O c) a k := by
  refine ⟨r,t,by simpa using hMargin,hp,?_,?_,?_⟩
  · intro v hv
    obtain ⟨x,rfl⟩ := exists_ord_of_not_ex hv
    simp only [card_exSet,max_self]
    have hh := (hd x).trans_eq (P.ordinaryNeighbours_compl hbc x).symm
    convert hh using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp)
  · intro v hv
    obtain ⟨x,rfl⟩ := exists_ord_of_not_ex hv
    simp only [card_exSet,max_self]
    have hh := (hd x).trans_eq (P.ordinaryNeighbours_compl' hbc x).symm
    convert hh using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp)
  · intro S hS hsmall hlarge
    have hSord : S ⊆ ordSet X O b := by
      intro v hv
      have hv' := hS hv
      simp only [mem_compl] at hv'
      obtain ⟨o,rfl⟩ := exists_ord_of_not_ex hv'
      exact mem_map.mpr ⟨o,mem_univ _,rfl⟩
    have hccb : ((exSet X O b)ᶜ).card = Fintype.card O := by rw [exSet_compl,card_ordSet]
    have hlarge' : S.card+t ≤ Fintype.card O := by
      convert hlarge using 1 <;> first | rfl | (rw [← hccb]; apply congrArg Finset.card; ext v; simp)
    let S' := univ.filter (fun v => ordEmb b v ∈ S)
    have hs : S'.map (ordEmb b) = S := by
      ext v
      constructor
      · rintro hv
        obtain ⟨o,ho,rfl⟩ := mem_map.mp hv
        exact (mem_filter.mp ho).2
      · intro hv
        obtain ⟨o,_,rfl⟩ := mem_map.mp (hSord hv)
        exact mem_map.mpr ⟨o,mem_filter.mpr ⟨mem_univ _,hv⟩,rfl⟩
    rw [← hs,card_map] at hsmall hlarge'
    have hb' := hExpand S' hsmall hlarge'
    have he (y : O) : (S.filter (fun x => 0 < P.cap b c x (ordEmb c y))).card =
        (S'.filter fun x => 0 < P.ordinary x y).card := by
      rw [← hs,filter_map,card_map]
      simp [P.capOrd hbc]
    have hN : ((univ.filter (fun y => r ≤ (S'.filter fun x => 0 < P.ordinary x y).card)).map
        (ordEmb c)) = ((exSet X O c)ᶜ).filter
          (fun y => r ≤ (S.filter fun x => 0 < P.cap b c x y).card) := by
      ext y
      rw [exSet_compl]
      constructor
      · intro hy
        obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
        exact mem_filter.mpr ⟨mem_map.mpr ⟨v,mem_univ _,rfl⟩,by simpa [he] using (mem_filter.mp hv).2⟩
      · intro hy
        obtain ⟨v,_,rfl⟩ := mem_map.mp (mem_filter.mp hy).1
        exact mem_map.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,by simpa [he] using (mem_filter.mp hy).2⟩,rfl⟩
    have hcount := congrArg Finset.card hN
    rw [card_map] at hcount
    have hsc := congrArg Finset.card hs
    rw [card_map] at hsc
    rw [hsc,hcount] at hb'
    convert hb' using 1 <;> first | rfl | (apply congrArg Finset.card; ext v; simp)


end WeightedPaper.Examples
