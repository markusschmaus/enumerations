import Mathlib.Tactic.Basic
import Aesop

universe u v w

structure Section (F₁ : Type u → Type v) (F₂ : Type u → Type w) (p : {α : Type u} → F₁ α → F₂ α → Prop)
    {α : Type u} (snd : F₂ α) : Type v where
  fst : F₁ α
  property : p fst snd

structure ProductF (F₁ : Type u → Type v) (F₂ : Type u → Type w) (p : {α : Type u} → F₁ α → F₂ α → Prop)
    (α : Type u) : Type (max v w) where
  fst : F₁ α
  snd : F₂ α
  property : p fst snd

instance (F₁ : Type u → Type v) (F₂ : Type u → Type w) (p : {α : Type u} → F₁ α → F₂ α → Prop)
    {α : Type u} (snd : F₂ α) : CoeOut (Section F₁ F₂ p snd) (ProductF F₁ F₂ p α) :=
  ⟨fun x => ⟨x.fst, snd, x.property⟩⟩

namespace ProductF

theorem eq_of_fst_snd_eq {F₁ : Type u → Type v} {F₂ : Type u → Type w} {p : {α : Type u} → F₁ α → F₂ α → Prop}
    {α : Type u} {x y : ProductF F₁ F₂ p α} (h : x.fst = y.fst ∧ x.snd = y.snd) : x = y := by
  induction x
  induction y
  simp only [mk.injEq] at *
  assumption

instance (F₁ : Type u → Type v) (F₂ : Type u → Type w) (p : {α : Type u} → F₁ α → F₂ α → Prop)
    {α : Type u} {snd : F₂ α} : CoeOut (Section F₁ F₂ p snd) (ProductF F₁ F₂ p α) := ⟨fun x => ⟨x.fst, snd, x.property⟩⟩

def run (F₁ : Type u → Type v) (F₂ : Type u → Type w) (p : {α : Type u} → F₁ α → F₂ α → Prop)
    {α : Type u} (x : ProductF F₁ F₂ p α) : (Section F₁ F₂ p x.snd) := ⟨x.fst, x.property⟩
