import Mathlib.Data.Set.Functor
import Mathlib.Tactic
import Enumerations.Tactic

def Endorelation (α : Type u) := α → α → Prop

namespace Endorelation

def map {α β : Type u} (f : α → β) (r : α → α → Prop) := fun b₁ b₂ : β => ∃ a₁ a₂ : α, r a₁ a₂ ∧ b₁ = f a₁ ∧ b₂ = f a₂

instance instFunctor : Functor Endorelation where
  map := map

def map_def {α β : Type u} (f : α → β) (r : α → α → Prop) := by
  transform (f <$> r : Endorelation β) =>
    simp [Functor.map]
    unfold map


instance instFunctor.instLawful : LawfulFunctor Endorelation where
  map_const := by
    intro α β
    apply Eq.refl
  id_map := by
    intro α a
    simp only [map_def, id_eq, exists_eq_right_right', exists_eq_right']
  comp_map := by
    intros α β γ g h p
    funext
    simp only [map_def, Function.comp_apply, eq_iff_iff]
    constructor
    · intro ⟨a₁, a₂, _⟩
      use g a₁, g a₂
      simp_all only [and_true]
      use a₁, a₂
      simp_all only [and_self]
    · intro ⟨b₁, b₂, ⟨a₁, a₂, _⟩, eq₁, eq₂⟩
      subst eq₁
      subst eq₂
      use a₁, a₂
      simp_all only [and_self]

end Endorelation
