import Mathlib.Tactic

universe u v

@[inline]
abbrev cast' {α : Type u} (a : α) {β : Type u} (h : α = β) : β :=
  cast h a

theorem or_of_not_imp (a b : Prop) : (¬ a → b) → a ∨ b := by
  have := imp_iff_not_or (a := ¬ a) (b := b)
  simp only [not_not] at this
  exact this.mp
