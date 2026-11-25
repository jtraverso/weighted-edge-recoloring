module

public import GridDetours
public import RegularHost
public import ExceptionalHost

@[expose] public section


namespace WeightedPaper.Repair.Grid
open Finset
open scoped Classical

abbrev Free (H W : Type) := Fin 2 ⊕ ((H × Bool) ⊕ (H ⊕ W))

variable {H W : Type} [Fintype H] [Fintype W]

def mark (h : H) (anchor : Bool) : Side H W := .inl (.inr (.inr (.inl (h,anchor))))
def ordinaryHelper (w : W) : Side H W := .inl (.inr (.inr (.inr w)))

def active : H ⊕ W ↪ Side H W :=
  ⟨Sum.elim (fun h => mark h false) ordinaryHelper,by
    intro x y e
    cases x <;> cases y <;> simp_all [mark,ordinaryHelper]⟩

def leftFreeFn : Free H W → Side H W
  | .inl f => rightInternal f
  | .inr (.inl (h,false)) => mark h true
  | .inr (.inl (h,true)) => .inr h
  | .inr (.inr u) => active u

def leftFree : Free H W ↪ Side H W :=
  ⟨leftFreeFn,by
    intro x y e
    change leftFreeFn x = leftFreeFn y at e
    rcases x with f | (⟨h,b⟩ | (h|w)) <;> rcases y with g | (⟨j,c⟩ | (j|v)) <;>
      (try cases b) <;> (try cases c) <;> simp_all [Free,Side,Ordinary,leftFreeFn,active,mark,ordinaryHelper,rightInternal]⟩

def rightFreeFn : Free H W → Side H W
  | .inl f => leftInternal f
  | .inr (.inl (h,false)) => .inr h
  | .inr (.inl (h,true)) => mark h true
  | .inr (.inr u) => active u

def rightFree : Free H W ↪ Side H W :=
  ⟨rightFreeFn,by
    intro x y e
    change rightFreeFn x = rightFreeFn y at e
    rcases x with f | (⟨h,b⟩ | (h|w)) <;> rcases y with g | (⟨j,c⟩ | (j|v)) <;>
      (try cases b) <;> (try cases c) <;> simp_all [Free,Side,Ordinary,rightFreeFn,active,mark,ordinaryHelper,leftInternal]⟩

theorem leftFree_range (x : Side H W) :
    x ∈ Set.range (leftFree : Free H W ↪ Side H W) ↔ x ∉ Set.range (leftInternal : Fin 2 → Side H W) := by
  rcases x with (f | (f | (⟨h,b⟩ | w))) | h
  · constructor
    · rintro ⟨u,e⟩
      change leftFreeFn u = leftInternal f at e
      exfalso
      rcases u with f' | (⟨h,b⟩ | (h|w)) <;> (try cases b) <;>
        simp [Free,Side,Ordinary,leftFree,leftFreeFn,active,rightInternal,leftInternal,mark,ordinaryHelper] at e
    · intro no
      exact (no ⟨f,rfl⟩).elim
  · exact ⟨fun _ => by simp [leftInternal,rightInternal],fun _ => ⟨.inl f,rfl⟩⟩
  · cases b
    · exact ⟨fun _ => by simp [mark,leftInternal],fun _ => ⟨.inr (.inr (.inl h)),rfl⟩⟩
    · exact ⟨fun _ => by simp [mark,leftInternal],fun _ => ⟨.inr (.inl (h,false)),rfl⟩⟩
  · exact ⟨fun _ => by simp [ordinaryHelper,leftInternal],fun _ => ⟨.inr (.inr (.inr w)),rfl⟩⟩
  · exact ⟨fun _ => by simp [leftInternal],fun _ => ⟨.inr (.inl (h,true)),rfl⟩⟩

theorem rightFree_range (x : Side H W) :
    x ∈ Set.range (rightFree : Free H W ↪ Side H W) ↔ x ∉ Set.range (rightInternal : Fin 2 → Side H W) := by
  rcases x with (f | (f | (⟨h,b⟩ | w))) | h
  · exact ⟨fun _ => by simp [leftInternal,rightInternal],fun _ => ⟨.inl f,rfl⟩⟩
  · constructor
    · rintro ⟨u,e⟩
      change rightFreeFn u = rightInternal f at e
      exfalso
      rcases u with f' | (⟨h,b⟩ | (h|w)) <;> (try cases b) <;>
        simp [Free,Side,Ordinary,rightFree,rightFreeFn,active,leftInternal,rightInternal,mark,ordinaryHelper] at e
    · intro no
      exact (no ⟨f,rfl⟩).elim
  · cases b
    · exact ⟨fun _ => by simp [mark,rightInternal],fun _ => ⟨.inr (.inr (.inl h)),rfl⟩⟩
    · exact ⟨fun _ => by simp [mark,rightInternal],fun _ => ⟨.inr (.inl (h,true)),rfl⟩⟩
  · exact ⟨fun _ => by simp [ordinaryHelper,rightInternal],fun _ => ⟨.inr (.inr (.inr w)),rfl⟩⟩
  · exact ⟨fun _ => by simp [rightInternal],fun _ => ⟨.inr (.inl (h,false)),rfl⟩⟩

/-- Order the free coordinates on each side so that only holes and helpers
are moved in a detour. -/
def onFree (p : Equiv.Perm (H ⊕ W)) : Equiv.Perm (Free H W) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) p)

noncomputable def roundPairs (p : Equiv.Perm (H ⊕ W)) : Finset (Side H W × Side H W) :=
  univ.image fun u : Free H W => (leftFree u,rightFree (onFree p u))

theorem roundRows (p : Equiv.Perm (H ⊕ W)) (x : Side H W) :
    (univ.filter (fun y => (x,y) ∈ roundPairs p)).card =
      if x ∈ Set.range (leftFree : Free H W ↪ Side H W) then 1 else 0 := by
  classical
  by_cases he : x ∈ Set.range (leftFree : Free H W ↪ Side H W)
  · obtain ⟨u,rfl⟩ := he
    have eq : (univ.filter (fun y => ((leftFree : Free H W ↪ Side H W) u,y) ∈ roundPairs p)) =
        {rightFree (onFree p u)} := by
      ext y; simp only [roundPairs,mem_filter,mem_univ,true_and,mem_image,Prod.mk.injEq,mem_singleton]
      exact ⟨fun ⟨u',e,h⟩ => by simpa only [leftFree.injective e] using h.symm,
        fun h => ⟨u,rfl,h.symm⟩⟩
    simp [eq,Set.mem_range_self]
  · have eq : (univ.filter fun y => (x,y) ∈ roundPairs p) = ∅ := by
      ext y
      simp only [roundPairs,mem_filter,mem_univ,true_and,mem_image,Prod.mk.injEq,notMem_empty,iff_false]
      rintro ⟨u,e,_⟩; exact he ⟨u,e⟩
    simp [eq,he]

theorem roundCols (p : Equiv.Perm (H ⊕ W)) (y : Side H W) :
    (univ.filter (fun x => (x,y) ∈ roundPairs p)).card =
      if y ∈ Set.range (rightFree : Free H W ↪ Side H W) then 1 else 0 := by
  classical
  by_cases he : y ∈ Set.range (rightFree : Free H W ↪ Side H W)
  · obtain ⟨u,rfl⟩ := he
    have eq : (univ.filter (fun x => (x,(rightFree : Free H W ↪ Side H W) u) ∈ roundPairs p)) =
        {leftFree ((onFree p).symm u)} := by
      ext x; simp only [roundPairs,mem_filter,mem_univ,true_and,mem_image,Prod.mk.injEq,mem_singleton]
      exact ⟨fun ⟨v,e,h⟩ => e.symm.trans (congrArg leftFree
        (((onFree p).eq_symm_apply).mpr (rightFree.injective h))),
        fun e => ⟨(onFree p).symm u,e.symm,by simp⟩⟩
    simp [eq,Set.mem_range_self]
  · have eq : (univ.filter fun x => (x,y) ∈ roundPairs p) = ∅ := by
      ext x
      simp only [roundPairs,mem_filter,mem_univ,true_and,mem_image,Prod.mk.injEq,notMem_empty,iff_false]
      rintro ⟨u,_,e⟩; exact he ⟨onFree p u,e⟩
    simp [eq,he]

end WeightedPaper.Repair.Grid
