import Enumerations.MonadContainer
import Enumerations.Predicate

universe u v

structure Enumerations.Property (M : Type u → Type v) [MonadContainer M] [LawfulMonadContainer M]
    {α : Type u} (predicate : α → Prop) (elems : M α) : Prop where
  intro ::
  complete (a : α) : a ∈ elems ↔ predicate a


structure Enumerations (M : Type u → Type v) [MonadContainer M] [LawfulMonadContainer M]
    (α : Type u) : Type (max u v) where
  predicate : α → Prop
  elems : M α
  property : Enumerations.Property M predicate elems

namespace Enumerations

variable {M : Type u → Type v} [MonadContainer M] [LawfulMonadContainer M]

def complete (e : Enumerations M α) (a : α) := e.property.complete a

@[simp]
def elem_iff_predicate (e : Enumerations M α) (a : α) : a ∈ e.elems ↔ e.predicate a := e.property.complete a

def map (f : α → β) (enum : Enumerations M α) : Enumerations M β :=
    Enumerations.mk (f <$> enum.predicate : Predicate β) (f <$> enum.elems) <| by
      constructor
      intro b
      simp only [Predicate.map_def, enum.complete]
      simp only [LawfulMonadContainer.mem_map, elem_iff_predicate]

instance functor : Functor (Enumerations M) where
  map := map

def map_def (f : α → β) (enum : Enumerations M α) := by
  transform (f <$> enum : Enumerations M β) =>
    simp only [Functor.map]
    unfold map

theorem map_predicate (f : α → β) (enum : Enumerations M α) :
    (f <$> enum).predicate = (f <$> enum.predicate : Predicate β) := by
  simp only [map_def]

theorem map_elems (f : α → β) (enum : Enumerations M α) :
    (f <$> enum).elems = (f <$> enum.elems : M β) := by
  simp only [map_def]

instance functor.lawful : LawfulFunctor (Enumerations M) where
  map_const := by
    intro α β
    rfl
  id_map := by
    intro α a
    simp only [map_def, id_map]
  comp_map := by
    intros α β γ g h e
    simp only [map_def, mk.injEq, comp_map, and_self]

def pure (a : α) : Enumerations M α :=
  Enumerations.mk (Pure.pure a : Predicate α) (Pure.pure a) <| by
  constructor
  simp only [LawfulMonadContainer.mem_pure, Predicate.pure_apply, implies_true]

def bind (enum : Enumerations M α) (f : α → Enumerations M β) : Enumerations M β :=
  Enumerations.mk (enum.predicate >>= fun a => (f a).predicate : Predicate β) (enum.elems >>= fun a => (f a).elems) <| by
    constructor
    intro b
    simp only [LawfulMonadContainer.mem_bind, elem_iff_predicate, Predicate.bind_def]

instance monad : Monad (Enumerations M) where
  pure := pure
  bind := bind

def pure_def (a : α) := by
  transform (Pure.pure a : Enumerations M α) =>
    simp only [Pure.pure]
    unfold pure

def bind_def (enum : Enumerations M α) (f : α → Enumerations M β) := by
  transform (enum >>= f : Enumerations M β) =>
    simp only [Bind.bind]
    unfold bind

def seq_def {α β: Type u} (enum : Enumerations M α) (f : Enumerations M (α → β)) := by
    transform f <*> enum =>
      simp only [Seq.seq]
      simp only [bind]
      simp only [←seq_eq_bind_map]
      simp

theorem pure_predicate (a : α) : (Pure.pure a : Enumerations M α).predicate = (Pure.pure a : Predicate α) := by
  simp only [pure_def]

theorem pure_elems (a : α) : (Pure.pure a : Enumerations M α).elems = (Pure.pure a : M α) := by
  simp only [pure_def]

theorem bind_predicate (enum : Enumerations M α) (f : α → Enumerations M β) :
    (enum >>= f).predicate = (enum.predicate >>= fun a => (f a).predicate : Predicate β) := by
  simp only [bind_def]

theorem bind_elems (enum : Enumerations M α) (f : α → Enumerations M β) :
    (enum >>= f).elems = (enum.elems >>= fun a => (f a).elems : M β) := by
  simp only [bind_def]

instance monad.lawful : LawfulMonad (Enumerations M) := by
  apply LawfulMonad.mk'
  · intros
    simp only [map_def, id_map]
  · intros
    simp only [pure_def, bind_def, pure_bind, implies_true]
  · intros
    simp only [bind_def, bind_assoc, implies_true]
  · intro _ _ _ _
    rfl
  · intro _ _ _ _
    rfl
  · intro _ _ _ _
    rfl
  · intro _ _ _ _
    simp only [pure_def, bind_def, map_def, bind_pure_comp]
  · intro _ _ _ _
    rfl

end Enumerations
