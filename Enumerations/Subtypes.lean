import Enumerations.Predicate

structure Subtypes (α : Type u) : Type u where
  predicate : α → Prop
  val : α
  property : predicate val

namespace Subtypes

def toSubtype {α : Type u} (s : Subtypes α) : Subtype s.predicate := ⟨s.val, s.property⟩

def fromSubtype {α : Type u} {p : α → Prop} (s : Subtype p) : Subtypes α := ⟨p, s.val, s.property⟩

instance {α : Type u} {p : α → Prop} : CoeOut (Subtype p) (Subtypes α) := ⟨fromSubtype⟩

def map {α β : Type u} (f : α → β)  (s : Subtypes α) :=
  Subtypes.mk (f <$> s.predicate : Predicate β) (f s.val) <| by
    simp only [Predicate.map_def]
    use s.val
    simp only [s.property, and_self]

instance instFunctor : Functor Subtypes where
  map := map

def map_def {α β : Type u} (f : α → β) (s : Subtypes α) := by
  transform (f <$> s) =>
    simp only [Functor.map]
    unfold map

@[simp]
theorem map_predicate {α β : Type u} (f : α → β) (s : Subtypes α) : (f <$> s).predicate = (f <$> s.predicate : Predicate β) := by
  simp only [map_def]

@[simp]
theorem map_val {α β : Type u} (f : α → β) (s : Subtypes α) : (f <$> s).val = f s.val := by
  simp only [map_def]

instance instFunctor.instLawful : LawfulFunctor Subtypes where
  map_const := by
    intro α β
    rfl
  id_map := by
    intro α a
    simp only [map_def, id_map, id_eq]
  comp_map := by
    intros α β γ g h p
    simp only [map_def, comp_map, Function.comp_apply]

def pure {α : Type u} (a : α) : Subtypes α := Subtypes.mk (Pure.pure a : Predicate α) a <| by
  simp only [Predicate.pure_def]

def bind {α β : Type u} (s : Subtypes α) (f : α → Subtypes β) : Subtypes β :=
  mk (s.predicate >>= fun a => (f a).predicate : Predicate β) (f s.val).val <| by
    simp only [Predicate.bind_def]
    use s.val
    simp only [s.property, (f s.val).property, and_self]

instance instMonad : Monad Subtypes where
  pure := pure
  bind := bind

def pure_def {α : Type u} (a : α) := by
  transform (Pure.pure a : Subtypes α) =>
    simp only [Pure.pure]
    unfold pure

def bind_def {α β : Type u} (f : α → Subtypes β) (s : Subtypes α) := by
  transform s >>= f =>
    simp only [Bind.bind]
    unfold bind

@[simp]
theorem pure_predicate {α : Type u} (a : α) : (pure a).predicate = (Pure.pure a : Predicate α) := rfl

@[simp]
theorem bind_predicate {α β : Type u} (f : α → Subtypes β) (s : Subtypes α) :
    (s >>= f).predicate = (s.predicate >>= fun x => (f x).predicate : Predicate β) := rfl

instance instMonad.instLawful : LawfulMonad Subtypes := by
  apply LawfulMonad.mk'
  · intro α a
    simp only [map_def, id_map, id_eq]
  · intro α β a f
    simp only [pure_def, bind_def, pure_bind]
  · intro α β γ a f g
    simp only [bind_def, bind_assoc]
  · intro α β f p
    rfl
  · intro α β f p
    rfl
  · intro α β f p
    rfl
  · intro α β f p
    simp only [pure_def, bind_def, bind_pure_comp, map_def]
  · intro α β f p
    rfl

end Subtypes
