import Enumerations.Endorelation
import Enumerations.Predicate

universe u

structure PredicateEndorelation (α : Type u) where
  predicate : α → Prop
  relation : α → α → Prop
  property : ∀ a₁ a₂ : α, relation a₁ a₂ → predicate a₁ ∧ predicate a₂

namespace PredicateEndorelation

def map {α β : Type u} (f : α → β)  (r : PredicateEndorelation α) :=
  PredicateEndorelation.mk (f <$> r.predicate : Predicate β) (f <$> r.relation : Endorelation β) <| by
    simp only [Endorelation.map_def, Predicate.map_def]
    intro b₁ b₂ h
    obtain ⟨a₁, a₂, hr, hp₁, hp₂⟩ := h
    have ⟨hr₁, hr₂⟩ := r.property a₁ a₂ hr
    constructor
    · use a₁
    · use a₂

instance instFunctor : Functor PredicateEndorelation where
  map := PredicateEndorelation.map

def map_def {α β : Type u} (f : α → β) (r : PredicateEndorelation α) := by
  transform (f <$> r) =>
    simp only [Functor.map]
    unfold map

@[simp]
theorem map_predicate {α β : Type u} (f : α → β) (r : PredicateEndorelation α) : (f <$> r).predicate = (f <$> r.predicate : Predicate β) := by
  simp only [map_def]

@[simp]
theorem map_relation {α β : Type u} (f : α → β) (r : PredicateEndorelation α) : (f <$> r).relation = (f <$> r.relation : Endorelation β) := by
  simp only [map_def]

instance instFunctor.instLawful : LawfulFunctor PredicateEndorelation where
  map_const := by
    intro α β
    rfl
  id_map := by
    intro α a
    simp only [map_def, id_map, id_eq]
  comp_map := by
    intros α β γ g h p
    simp only [map_def, comp_map, Function.comp_apply]

def pure {α : Type u} (a : α) : PredicateEndorelation α := PredicateEndorelation.mk (Pure.pure a : Predicate α)
    (fun _ _ => False) <| by
  simp only [Predicate.pure_apply, IsEmpty.forall_iff, implies_true]

def bind {α β : Type u} (r : PredicateEndorelation α) (f : α → PredicateEndorelation β) : PredicateEndorelation β :=
  mk (r.predicate >>= fun a => (f a).predicate : Predicate β)
    (fun (b₁ b₂ : β) => (∃ a₁ a₂, (f a₁).predicate b₁ ∧ (f a₂).predicate b₂ ∧ r.relation a₁ a₂) ∨
      (∃ a, r.predicate a ∧ (f a).relation b₁ b₂))
    <| by
      simp only [Predicate.bind_def]
      intro b₁ b₂ h
      cases h with
      | inl h =>
        obtain ⟨a₁, a₂, hf₁, hf₂, hr⟩ := h
        have ⟨hr₁, hr₂⟩:= r.property a₁ a₂ hr
        constructor
        use a₁; use a₂
      | inr h =>
        obtain ⟨a, hp, hr⟩ := h
        have ⟨hr₁, hr₂⟩ := (f a).property b₁ b₂ hr
        constructor
        repeat use a

instance instMonad : Monad PredicateEndorelation where
  pure := pure
  bind := bind

def pure_def {α : Type u} (a : α) := by
  transform (Pure.pure a : PredicateEndorelation α) =>
    simp only [Pure.pure]
    unfold pure

def bind_def {α β : Type u} (f : α → PredicateEndorelation β) (s : PredicateEndorelation α) := by
  transform s >>= f =>
    simp only [Bind.bind]
    unfold bind

@[simp]
theorem pure_relation {α : Type u} (a : α) : (Pure.pure a : PredicateEndorelation α).relation = (fun _ _ => False) := rfl

@[simp]
theorem pure_predicate {α : Type u} (a : α) : (Pure.pure a : PredicateEndorelation α).predicate = (Pure.pure a : Predicate α) := rfl

@[simp]
theorem bind_predicate {α β : Type u} (f : α → PredicateEndorelation β) (r : PredicateEndorelation α) :
    (r >>= f).predicate = (r.predicate >>= fun a => (f a).predicate : Predicate β) := rfl

#check mk.injEq

instance instMonad.instLawful : LawfulMonad PredicateEndorelation := by
  apply LawfulMonad.mk'
  · intro α a
    simp only [map_def, id_map, id_eq]
  · intro α β a f
    simp only [pure_def, bind_def, pure_bind]
    rw [mk.injEq]
    simp only [and_false, exists_false, Predicate.pure_apply, exists_eq_left, false_or, and_self]
  · intro α β γ r f g
    simp only [bind_def, bind_assoc]
    rw [mk.injEq]
    simp only [Predicate.bind_def, true_and]
    funext c₁ c₂
    apply propext
    constructor
    · intro h
      cases h with
      | inl h =>
        rcases h with ⟨b₁, b₂, _, _, ⟨a₁, a₂, _, _, _⟩ | ⟨a, _, _⟩⟩
        · apply Or.inl
          use a₁, a₂
          constructor
          · use b₁
          constructor
          · use b₂
          · assumption
        · apply Or.inr
          use a
          constructor
          · assumption
          constructor
          · use b₁, b₂
      | inr h =>
        obtain ⟨b, ⟨a, hp, hf⟩, hr⟩ := h
        apply Or.inr; use a
        constructor; assumption
        apply Or.inr; use b
    · intro h
      cases h with
      | inl h =>
        obtain ⟨a₁, a₂, ⟨b₁, _, _⟩, ⟨b₂, p, _⟩, hr⟩ := h
        apply Or.inl
        use b₁, b₂
        simp_all only [true_and]
        apply Or.inl; use a₁, a₂
      | inr h =>
        rcases h with ⟨a, _, ⟨b₁, b₂, _, _, _⟩ | ⟨b, _, _⟩⟩
        · apply Or.inl; use b₁, b₂
          simp_all only [true_and]
          apply Or.inr; use a
        · apply Or.inr; use b
          simp_all only [and_true]
          use a
  · intro α β f p
    rfl
  · intro α β f p
    rfl
  · intro α β f p
    rfl
  · intro α β f p
    simp only [pure_def, bind_def, bind_pure_comp, map_def]
    simp only [Predicate.pure_apply, and_false, exists_false, or_false, mk.injEq, true_and, Endorelation.map_def]
    funext b₁ b₂
    apply propext
    constructor
    · intro ⟨a₁, a₂, _, _, _⟩
      use a₁, a₂
    · intro ⟨a₁, a₂, _, _, _⟩
      use a₁, a₂
  · intro α β f p
    rfl

end PredicateEndorelation
