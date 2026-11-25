import HybridCertificate

namespace WeightedPaper.Repair
open Finset Pseudorandom
open scoped Classical

variable {I A B : Type} [Fintype I] [Fintype A] [Fintype B]
  [DecidableEq I] [DecidableEq A] [DecidableEq B]

abbrev SupportCopy (R : A → B → Prop) := {p : A × B // R p.1 p.2}

abbrev supportLeft {R : A → B → Prop} (e : SupportCopy R) := e.val.1
abbrev supportRight {R : A → B → Prop} (e : SupportCopy R) := e.val.2

variable (R : A → B → Prop) (X : I → Finset A) (Y : I → Finset B)

noncomputable def eligibleSupport : Finset (I × SupportCopy R) := by
  exact univ.filter fun p => supportLeft p.2 ∈ X p.1 ∧ supportRight p.2 ∈ Y p.1

noncomputable def supportTriples : Finset (Finset (DemandVertex I A B (SupportCopy R))) := by
  exact (eligibleSupport R X Y).image (triple supportLeft supportRight)

theorem eligibleSupport_mem (p : I × SupportCopy R) :
    p ∈ eligibleSupport R X Y ↔ supportLeft p.2 ∈ X p.1 ∧ supportRight p.2 ∈ Y p.1 := by
  simp [eligibleSupport]

private theorem supportTriple_filter_card (Q : Finset (DemandVertex I A B (SupportCopy R)) → Prop)
    [DecidablePred Q] :
    ((supportTriples R X Y).filter Q).card =
      ((eligibleSupport R X Y).filter fun p => Q (triple supportLeft supportRight p)).card := by
  rw [supportTriples, filter_image, card_image_of_injective _ (triple_injective _ _)]

private theorem leftFiber_card (i : I) (x : A) (hx : x ∈ X i) :
    ((eligibleSupport R X Y).filter fun p => p.1 = i ∧ supportLeft p.2 = x).card =
      ((Y i).filter (R x)).card := by
  refine card_bij' (fun p _ => supportRight p.2)
    (fun y hy => ((i, ⟨(x,y), (mem_filter.mp hy).2⟩) : I × SupportCopy R)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨he,hi,hx'⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨?_, by rw [← hx']; exact p.2.property⟩
    exact hi ▸ ((eligibleSupport_mem R X Y _).mp he).2
  · intro y hy
    exact mem_filter.mpr ⟨(eligibleSupport_mem R X Y _).mpr ⟨hx,(mem_filter.mp hy).1⟩,rfl,rfl⟩
  · intro p hp
    obtain ⟨_,hi,hx'⟩ := mem_filter.mp hp
    exact Prod.ext hi.symm (Subtype.ext (Prod.ext hx'.symm rfl))
  · intro y _
    rfl

private theorem rightFiber_card (i : I) (y : B) (hy : y ∈ Y i) :
    ((eligibleSupport R X Y).filter fun p => p.1 = i ∧ supportRight p.2 = y).card =
      ((X i).filter fun x => R x y).card := by
  refine card_bij' (fun p _ => supportLeft p.2)
    (fun x hx => ((i, ⟨(x,y), (mem_filter.mp hx).2⟩) : I × SupportCopy R)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨he,hi,hy'⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨?_, by rw [← hy']; exact p.2.property⟩
    exact hi ▸ ((eligibleSupport_mem R X Y _).mp he).1
  · intro x hx
    exact mem_filter.mpr ⟨(eligibleSupport_mem R X Y _).mpr ⟨(mem_filter.mp hx).1,hy⟩,rfl,rfl⟩
  · intro p hp
    obtain ⟨_,hi,hy'⟩ := mem_filter.mp hp
    exact Prod.ext hi.symm (Subtype.ext (Prod.ext rfl hy'.symm))
  · intro x _
    rfl

theorem support_degree_left (i : I) (x : A) (hx : x ∈ X i) :
    degree (supportTriples R X Y) (.inl (i,x)) = ((Y i).filter (R x)).card := by
  rw [degree, supportTriple_filter_card R X Y (fun e => _ ∈ e)]
  convert leftFiber_card R X Y i x hx using 2
  ext p
  simp [triple, and_comm, eq_comm]

theorem support_degree_right (i : I) (y : B) (hy : y ∈ Y i) :
    degree (supportTriples R X Y) (.inr (.inl (i,y))) = ((X i).filter fun x => R x y).card := by
  rw [degree, supportTriple_filter_card R X Y (fun e => _ ∈ e)]
  convert rightFiber_card R X Y i y hy using 2
  ext p
  simp [triple, and_comm, eq_comm]

theorem support_degree_upper (d : ℕ)
    (regA : ∀ x, (univ.filter (R x)).card = d)
    (regB : ∀ y, (univ.filter fun x => R x y).card = d)
    (k : Fintype.card I ≤ d) (v : DemandVertex I A B (SupportCopy R)) :
    degree (supportTriples R X Y) v ≤ d := by
  rcases v with ⟨i,x⟩ | (⟨i,y⟩ | e)
  · by_cases hx : x ∈ X i
    · rw [support_degree_left R X Y i x hx, ← regA x]
      exact card_le_card (filter_subset_filter _ (subset_univ _))
    · rw [degree, supportTriple_filter_card R X Y (fun e => _ ∈ e)]
      have empty : ((eligibleSupport R X Y).filter fun p => Sum.inl (i,x) ∈
          triple supportLeft supportRight p) = ∅ := by
        ext p
        simp only [mem_filter, eligibleSupport_mem, notMem_empty, iff_false]
        rintro ⟨⟨hp,_⟩, ht⟩
        simp [triple] at ht
        exact hx (by simpa only [← ht.1, ← ht.2] using hp)
      simp [empty]
  · by_cases hy : y ∈ Y i
    · rw [support_degree_right R X Y i y hy, ← regB y]
      exact card_le_card (filter_subset_filter _ (subset_univ _))
    · rw [degree, supportTriple_filter_card R X Y (fun e => _ ∈ e)]
      have empty : ((eligibleSupport R X Y).filter fun p => Sum.inr (Sum.inl (i,y)) ∈
          triple supportLeft supportRight p) = ∅ := by
        ext p
        simp only [mem_filter, eligibleSupport_mem, notMem_empty, iff_false]
        rintro ⟨⟨_,hp⟩, ht⟩
        simp [triple] at ht
        exact hy (by simpa only [← ht.1, ← ht.2] using hp)
      simp [empty]
  · rw [degree, supportTriple_filter_card R X Y (fun e => _ ∈ e)]
    refine le_trans (card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) ?_) k
    intro p hp q hq same
    have pe : e = p.2 := by simpa [triple] using (mem_filter.mp hp).2
    have qe : e = q.2 := by simpa [triple] using (mem_filter.mp hq).2
    exact Prod.ext same (pe.symm.trans qe)

theorem support_codegree (u v : DemandVertex I A B (SupportCopy R)) (ne : u ≠ v) :
    codegree (supportTriples R X Y) u v ≤ 1 := by
  rw [codegree, supportTriple_filter_card]
  rw [card_le_one]
  rintro ⟨i,e⟩ hp ⟨j,f⟩ hq
  simp only [mem_filter] at hp hq
  obtain ⟨_,hu,hv⟩ := hp
  obtain ⟨_,hu',hv'⟩ := hq
  rcases u with ⟨iu,x⟩ | (⟨iu,y⟩ | g) <;> rcases v with ⟨iv,x'⟩ | (⟨iv,y'⟩ | h) <;>
    simp only [triple, mem_insert, mem_singleton, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, or_false, false_or, Prod.mk.injEq, supportLeft, supportRight] at hu hv hu' hv'
  · exact (ne (congrArg Sum.inl (Prod.ext (hu.1.trans hv.1.symm) (hu.2.trans hv.2.symm)))).elim
  · exact Prod.ext (hu.1.symm.trans hu'.1) (Subtype.ext (Prod.ext
      (hu.2.symm.trans hu'.2) (hv.2.symm.trans hv'.2)))
  · exact Prod.ext (hu.1.symm.trans hu'.1) (hv.symm.trans hv')
  · exact Prod.ext (hu.1.symm.trans hu'.1) (Subtype.ext (Prod.ext
      (hv.2.symm.trans hv'.2) (hu.2.symm.trans hu'.2)))
  · exact (ne (congrArg (Sum.inr ∘ Sum.inl)
      (Prod.ext (hu.1.trans hv.1.symm) (hu.2.trans hv.2.symm)))).elim
  · exact Prod.ext (hu.1.symm.trans hu'.1) (hv.symm.trans hv')
  · exact Prod.ext (hv.1.symm.trans hv'.1) (hu.symm.trans hu')
  · exact Prod.ext (hv.1.symm.trans hv'.1) (hu.symm.trans hu')
  · exact (ne (congrArg (Sum.inr ∘ Sum.inr) (hu.trans hv.symm))).elim

theorem support_triple_count (d : ℕ) (regA : ∀ x, (univ.filter (R x)).card = d) :
    (supportTriples R X Y).card ≤ Fintype.card I * Fintype.card A * d := by
  have e : SupportCopy R ≃ (Σ x : A, ↥((univ : Finset B).filter (R x))) :=
    ⟨fun p => ⟨p.val.1, ⟨p.val.2, mem_filter.mpr ⟨mem_univ _,p.property⟩⟩⟩,
      fun t => ⟨(t.1,t.2.val), (mem_filter.mp t.2.property).2⟩,
      fun p => by cases p; rfl, fun t => by cases t; rfl⟩
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  simp only [Fintype.card_coe, regA, sum_const, card_univ, Nat.nsmul_eq_mul] at h
  calc
    (supportTriples R X Y).card ≤ Fintype.card (I × SupportCopy R) :=
      card_image_le.trans (card_le_univ _)
    _ = _ := by rw [Fintype.card_prod, h, Nat.mul_assoc]

end WeightedPaper.Repair
