import Mathlib

class ContainerMonad (m : Type u → Type v) extends Monad m : Type (max (u + 1) v) where
  membership α : Membership α (m α)

instance (m : Type u → Type v) [ContainerMonad m] : Membership α (m α) :=
  ContainerMonad.membership α

instance : ContainerMonad List where
  membership _ := inferInstance

class LawfulContainerMonad (m : Type u → Type v) [ContainerMonad m] extends LawfulMonad m : Prop where
  mem_pure {α : Type u} : ∀ (a a' : α), a' ∈ (Pure.pure a : m α) ↔ a' = a
  mem_bind {α β : Type u} (x : m α) (f : α → m β) : ∀ (b : β), b ∈ (x >>= f) ↔ ∃ (a : α), a ∈ x ∧ b ∈ f a

instance : LawfulContainerMonad List where
  mem_pure := by
    intro α a a'
    simp only [pure, List.ret, List.mem_singleton]
  mem_bind := by
    simp only [bind, List.bind, List.mem_join, List.mem_map, exists_exists_and_eq_and, implies_true,
      forall_const]

namespace LawfulContainerMonad

variable {m : Type u → Type v} [ContainerMonad m] [LawfulContainerMonad m] {α β : Type u}

theorem mem_map (f : α → β) (x : m α) : ∀ (b : β), b ∈ (f <$> x) ↔ ∃ (a : α), a ∈ x ∧ b = f a := by
  intro b
  simp only [map_eq_pure_bind, mem_bind, mem_pure]

end LawfulContainerMonad
