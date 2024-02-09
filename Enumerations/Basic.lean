import Mathlib.Tactic

universe u v

@[inline]
abbrev cast' {α : Type u} (a : α) {β : Type u} (h : α = β) : β :=
  cast h a

theorem or_of_not_imp (a b : Prop) : (¬ a → b) → a ∨ b := by
  have := imp_iff_not_or (a := ¬ a) (b := b)
  simp only [not_not] at this
  exact this.mp

def Nat.iterateDep {β : Nat → Type v} (op : {i : Nat} → β i → β (i + 1))
    (i : Nat) {j : Nat} (a : β j) : β (i + j) :=
  match i with
    | 0 => cast' a <| by
      simp_all only [zero_add]
    | i' + 1 =>
      let a' := cast' (op a) <| by
        apply congrArg
        linarith
      cast' (iterateDep (β := β) op i' (j := 1 + j) a') <| by
        apply congrArg
        linarith
