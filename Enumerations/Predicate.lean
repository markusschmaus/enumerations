import Mathlib.Data.Set.Functor
import Mathlib.Tactic
import Enumerations.Tactic

def Predicate (α : Type u) := α → Prop

namespace Predicate

def map {α β : Type u} (f : α → β) (p : α → Prop) := fun b : β => ∃ a : α, p a ∧ b = f a

instance functor : Functor Predicate where
  map := map

def map_def {α β : Type u} (f : α → β) (p : α → Prop) := by
  transform (f <$> p : Predicate β) =>
    simp [Functor.map]
    unfold map

instance functor.lawful : LawfulFunctor Predicate where
  map_const := by
    intro α β
    apply Eq.refl
  id_map := by
    intro α a
    simp only [map_def, id_eq, exists_eq_right']
  comp_map := by
    intros α β γ g h p
    funext c
    simp only [map_def, Function.comp_apply, eq_iff_iff]
    constructor
    · intro ⟨a, _⟩
      use g a
      simp_all only [and_true]
      use a
      simp_all only [and_self]
    · intro ⟨b, ⟨a, _⟩, eq⟩
      subst eq
      use a
      simp_all only [and_self]


def pure {α : Type u} (a : α) : Predicate α := fun a' => a' = a

def bind {α : Type u} {β : Type v} (p : Predicate α) (f : α → Predicate β) : Predicate β :=
  fun b => ∃ a : α, p a ∧ f a b

instance monad : Monad Predicate where
  pure := pure
  bind := bind

def pure_def {α : Type u} (a : α) := by
  transform (Pure.pure a : Predicate α) =>
    simp only [Pure.pure]
    unfold pure

def bind_def {α β : Type u} (f : α → Predicate β) (p : Predicate α) := by
  transform p >>= f =>
    simp only [Bind.bind]
    unfold bind

def seq_def {α β : Type u} (f : Predicate (α → β)) (p : Predicate α) := by
  transform f <*> p =>
    simp only [Seq.seq, map_def]
    unfold bind
    simp only

@[simp]
theorem pure_apply {α : Type u} (a a' : α) : (Pure.pure a : Predicate α) a' ↔ a' = a := by rfl

instance monad.lawful : LawfulMonad Predicate := by
  apply LawfulMonad.mk'
  · intro α a
    funext a'
    simp only [map_def, id_eq, exists_eq_right']
  · intro α β a f
    funext b
    simp only [pure_def, bind_def]
    apply propext; apply Iff.intro
    · intro ⟨a', eq, h⟩
      subst eq
      exact h
    · intro h
      use a
  · intros α β γ p f g
    simp only [bind_def]
    funext c
    apply propext; apply Iff.intro
    · intro ⟨b, ⟨a, _, _⟩, _⟩
      use a
      simp_all only [true_and]
      use b
    · intro ⟨a, _, ⟨b, _, _⟩⟩
      use b
      simp_all only [and_true]
      use a
  · intros α β f p
    rfl
  · intros α β p q
    rfl
  · intros α β p q
    rfl
  · intros α β f p
    funext b
    simp only [bind_def, map_def, pure_def]
  · intros α β f p
    simp only [bind_def, map_def, pure_def, seq_def]

end Predicate
