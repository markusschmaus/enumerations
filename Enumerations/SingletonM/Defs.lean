import Enumerations.ProductF.Defs

import Enumerations.Predicate
import Enumerations.ProductF.Functor
import Enumerations.ProductF.Monad
import Enumerations.ProductF.FilterP

def SingletonM.valid {α : Type u} (x : α) (p : α → Prop) : Prop := ∀ y : α, p y ↔ y = x

abbrev SingletonM := ProductF Id Predicate SingletonM.valid

namespace SingletonM

def val {α : Type u} (s : SingletonM α) : α := s.fst

def predicate {α : Type u} (s : SingletonM α) : α → Prop := s.snd

instance : ProductF.MapInvariant Id Predicate SingletonM.valid where
  map_invariant := by
    intro _ _ f x
    have := x.property
    simp only [SingletonM.valid] at this
    have := this x.fst
    simp only [iff_true] at this
    simp only [Functor.map, Predicate.map, SingletonM.valid]
    intro y
    apply Iff.intro
    · intro h
      simp_all only [exists_eq_left]
    · intro h
      use x.fst

instance : ProductF.PureInvariant Id Predicate SingletonM.valid where
  pure_invariant := by
    intros
    simp only [pure, Predicate.pure, ProductF.mk.injEq, SingletonM.valid]
    intro
    trivial

instance : ProductF.BindInvariant Id Predicate SingletonM.valid where
  bind_invariant := by
    intros _ _ f x
    have := x.property
    simp only [SingletonM.valid] at this
    have := this x.fst
    simp only [iff_true] at this
    have := (f x.fst).property
    simp only [SingletonM.valid] at this
    have := this (f x.fst).fst
    simp only [iff_true] at this
    simp only [bind, Predicate.bind, Function.comp_apply, SingletonM.valid]
    intro y
    apply Iff.intro
    · intro h
      simp_all only [exists_eq_left]
    · intro h
      use x.fst
      simp_all only [and_self]

end SingletonM

abbrev SingletonS := @Section Id Predicate SingletonM.valid
