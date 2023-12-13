import Mathlib.Tactic
import Enumerations.Tactic

universe u v

class InfiniteListClass (α : Type u) : Type (u + 1) where
  State : Type
  head : State → α
  tail : State → State

namespace InfiniteListClass

theorem State_eq_of_eq {α : Type u} {as₁ as₂ : InfiniteListClass α} (eq : as₁ = as₂) : as₁.State = as₂.State := by
  subst eq
  rfl

def map {α β : Type u} (f : α → β) (as : InfiniteListClass α) : InfiniteListClass β :=
  ⟨as.State, f ∘ as.head, as.tail⟩

instance functor : Functor InfiniteListClass where
  map := map

def map_def {α β : Type u} (f : α → β) (as : InfiniteListClass α) := by
  transform (f <$> as : InfiniteListClass β) =>
    simp [Functor.map]
    unfold map

instance functor.lawful : LawfulFunctor InfiniteListClass where
  map_const := by
    intro _ _
    rfl
  id_map := by
    intro _
    simp only [map_def, Function.comp.left_id, implies_true]
  comp_map := by
    intro _ _ _
    simp only [map_def, Function.comp.assoc, implies_true]

end InfiniteListClass

structure InfiniteList (α : Type u) : Type (u + 1) where
  inst : InfiniteListClass α
  state : inst.State

attribute [instance] InfiniteList.inst

namespace InfiniteList

def head {α : Type u} (l : InfiniteList α) : α :=
  l.inst.head l.state

def tail {α : Type u} (l : InfiniteList α) : InfiniteList α :=
  { state := l.inst.tail l.state, inst := l.inst }

def map {α β : Type u} (f : α → β) (as : InfiniteList α) : InfiniteList β :=
  { state := as.state, inst := f <$> as.inst }

instance functor : Functor InfiniteList where
  map := map

def map_def {α β : Type u} (f : α → β) (as : InfiniteList α) := by
  transform (f <$> as : InfiniteList β) =>
    simp [Functor.map]
    unfold map

instance functor.lawful : LawfulFunctor InfiniteList where
  map_const := by
    intro _ _
    rfl
  id_map := by
    intro _ x
    let ⟨inst, state⟩ := x
    simp only [map_def, mk.injEq, InfiniteListClass.map_def, Function.comp.left_id, heq_eq_eq,
      and_self]
  comp_map := by
    intro _ _ _ _ _ _
    simp only [map_def, mk.injEq, comp_map, heq_eq_eq, and_true]



end InfiniteList

instance From.inst : InfiniteListClass Nat where
  State := Nat
  head := id
  tail n := n.succ

def From (n : Nat) : InfiniteList Nat := ⟨From.inst, n⟩

structure FibState where
  next : Nat
  prev : Nat

namespace FibState

def head : FibState → Nat := next

def tail (f : FibState) : FibState :=
  { next := f.next + f.prev, prev := f.next }

instance inst : InfiniteListClass Nat where
  head := head
  tail := tail

end FibState

def Fib (state : FibState) : InfiniteList Nat :=
  { state := state }

def fibonacci : InfiniteList Nat := Fib ⟨0, 1⟩

#eval fibonacci.head
