import Enumerations.ProductF.Defs
import Enumerations.ProductF.Functor
import Enumerations.ProductF.Monad
import Enumerations.ProductF.FilterP

import Enumerations.Predicate

@[simp]
def ListM.valid {α : Type u} (xs : List α) (p : α → Prop) : Prop := ∀ y : α, p y ↔ y ∈ xs

abbrev ListM := ProductF List Predicate ListM.valid
abbrev ListS := @Section List Predicate ListM.valid

namespace ListM

@[simp]
def val {α : Type u} (s : ListM α) : List α := s.fst

@[simp]
def predicate {α : Type u} (s : ListM α) : α → Prop := s.snd

instance : ProductF.MapInvariant List Predicate ListM.valid where
  map_invariant := by
    intro _ _ f x
    have := x.property
    simp only [ListM.valid] at this
    simp only [Functor.map, Predicate.map, ListM.valid]
    aesop

instance : ProductF.PureInvariant List Predicate ListM.valid where
  pure_invariant := by
    intros
    simp only [pure, Predicate.pure, ProductF.mk.injEq, ListM.valid, List.ret]
    aesop

instance : ProductF.BindInvariant List Predicate ListM.valid where
  bind_invariant := by
    intros _ _ f x
    have := x.property
    simp only [ListM.valid] at this
    simp only [bind, Predicate.bind, ProductF.mk.injEq, ListM.valid]
    intro
    apply Iff.intro
    · intro h
      obtain ⟨w, ⟨h₁, h₂⟩⟩ := h
      have := (f w).property
      simp only [ListM.valid] at this
      aesop
    · intro h
      simp_all only [List.mem_bind, Function.comp_apply]
      obtain ⟨w, ⟨h₁, h₂⟩⟩ := h
      have := (f w).property
      simp only [ListM.valid] at this
      aesop

instance : ProductF.FilterPInvariant List Predicate ListM.valid where
  filterP_invariant := by
    simp only [valid, filterP]
    intros _ _ _ x y
    constructor
    · intro h
      apply List.mem_filter_of_mem
      exact x.property y |>.mp h.right
      exact decide_eq_true h.left
    · intro h
      have := x.property y |>.mpr (List.mem_of_mem_filter h)
      have := List.of_mem_filter h
      simp_all only [decide_eq_true_eq, and_self]

def cast {α : Type u} (xs : ListM α) {p : α → Prop} (h : ∀ a, xs.predicate a ↔ p a) : ListS p :=
  Section.mk xs.fst <| by
    have := xs.property
    unfold ListM.valid at *
    aesop

end ListM

def ListS.cast {α : Type u}  {q : α → Prop} (xs : ListS q) {p : α → Prop} (h : ∀ a, q a ↔ p a) : ListS p :=
  Section.mk xs.fst <| by
    have := xs.property
    unfold ListM.valid at *
    aesop
