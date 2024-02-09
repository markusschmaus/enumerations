import Enumerations.ProductF

import Enumerations.Predicate

abbrev SubtypeM := ProductF Id Predicate Function.eval

namespace SubtypeM

def val {α : Type u} (s : SubtypeM α) : α := s.fst

def predicate {α : Type u} (s : SubtypeM α) : α → Prop := s.snd

def run {α : Type u} (s : SubtypeM α) : Subtype s.predicate := ⟨s.val, s.property⟩

instance {α : Type u} {p : α → Prop} : CoeOut (Subtype p) (SubtypeM α) := ⟨fun s => ⟨s.val, p, s.property⟩⟩

instance : ProductF.MapInvariant Id Predicate Function.eval where
  map_invariant := by
    intros _ _ f x
    have := x.property
    simp only [Functor.map, Predicate.map]
    use x.fst

instance : ProductF.PureInvariant Id Predicate Function.eval where
  pure_invariant := by
    intros
    simp only [pure, Predicate.pure, ProductF.mk.injEq, Function.eval]

instance : ProductF.BindInvariant Id Predicate Function.eval where
  bind_invariant := by
    intros _ _ f x
    have := x.property
    have := (f x.fst).property
    simp only [bind, Predicate.bind, Function.comp_apply, Function.eval]
    use x.fst
