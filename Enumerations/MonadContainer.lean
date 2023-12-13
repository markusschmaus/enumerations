import Mathlib

class MonadContainer (m : Type u → Type v) extends Monad m : Type (max (u + 1) v) where
  membership α : Membership α (m α)

instance (m : Type u → Type v) [MonadContainer m] : Membership α (m α) :=
  MonadContainer.membership α

instance : MonadContainer List where
  membership _ := inferInstance

class LawfulMonadContainer (m : Type u → Type v) [MonadContainer m] extends LawfulMonad m : Prop where
  mem_pure {α : Type u} : ∀ (a a' : α), a' ∈ (Pure.pure a : m α) ↔ a' = a
  mem_bind {α β : Type u} (x : m α) (f : α → m β) : ∀ (b : β), b ∈ (x >>= f) ↔ ∃ (a : α), a ∈ x ∧ b ∈ f a

instance : LawfulMonadContainer List where
  mem_pure := by
    intro α a a'
    simp only [pure, List.ret, List.mem_singleton]
  mem_bind := by
    simp only [bind, List.bind, List.mem_join, List.mem_map, exists_exists_and_eq_and, implies_true,
      forall_const]

namespace LawfulMonadContainer

variable {m : Type u → Type v} [MonadContainer m] [LawfulMonadContainer m] {α β : Type u}

theorem mem_map (f : α → β) (x : m α) : ∀ (b : β), b ∈ (f <$> x) ↔ ∃ (a : α), a ∈ x ∧ b = f a := by
  intro b
  simp only [map_eq_pure_bind, mem_bind, mem_pure]

end LawfulMonadContainer
