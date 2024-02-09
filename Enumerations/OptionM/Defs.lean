import Enumerations.ProductF.Defs
import Enumerations.ProductF.Functor
import Enumerations.ProductF.Monad
import Enumerations.ProductF.FilterP

import Enumerations.Predicate

theorem Option.exists_of_some_bind {α β : Type u} {x : Option α} {f : α → Option β}
    {y : β} (h : some y = Option.bind x f) : ∃ z, x = some z ∧ f z = some y := by
  simp [Option.bind] at h
  aesop

@[simp]
def OptionS.valid {α : Type u} (x : Option α) (p : α → Prop) : Prop := ∀ y : α, p y ↔ x = some y

abbrev OptionS := @Section Option Predicate OptionS.valid
abbrev OptionM := ProductF Option Predicate OptionS.valid

namespace OptionM

@[simp]
def val {α : Type u} (s : OptionM α) : Option α := s.fst

@[simp]
def predicate {α : Type u} (s : OptionM α) : α → Prop := s.snd

instance : ProductF.MapInvariant Option Predicate OptionS.valid where
  map_invariant := by
    intro _ _ f x
    have := x.property
    simp only [OptionS.valid] at this
    simp only [Functor.map, Predicate.map, OptionS.valid]
    intro y
    apply Iff.intro
    · intro h
      obtain ⟨w, ⟨h₁, h₂⟩⟩ := h
      aesop
    · intro h
      simp [Option.map] at h
      aesop

instance : ProductF.PureInvariant Option Predicate OptionS.valid where
  pure_invariant := by
    intros
    simp only [pure, Predicate.pure, ProductF.mk.injEq, OptionS.valid]
    aesop

instance : ProductF.BindInvariant Option Predicate OptionS.valid where
  bind_invariant := by
    intros _ _ f x
    have := x.property
    simp only [OptionS.valid] at this
    simp only [bind, Predicate.bind, Function.comp_apply, OptionS.valid]
    intro y
    apply Iff.intro
    · intro h
      obtain ⟨w, ⟨h₁, h₂⟩⟩ := h
      have := (f w).property
      simp only [OptionS.valid] at this
      aesop
    · intro h
      have := Option.exists_of_some_bind h.symm
      obtain ⟨w, ⟨h₁, _⟩⟩ := this
      have := (f w).property
      simp only [OptionS.valid] at this
      aesop
