import Enumerations.ProductF.Defs

namespace ProductF

class PureInvariant (F₁ : Type u → Type v) [Pure F₁] (F₂ : Type u → Type w) [Pure F₂]
  (p : {α : Type u} → F₁ α → F₂ α → Prop) : Prop where
  pure_invariant {α : Type u} (x : α) : p (pure x) (pure x)

class BindInvariant (F₁ : Type u → Type v) [Bind F₁] (F₂ : Type u → Type w) [Bind F₂]
  (p : {α : Type u} → F₁ α → F₂ α → Prop) : Prop where
  bind_invariant {α β : Type u} (f : α → ProductF F₁ F₂ p β) (x : ProductF F₁ F₂ p α) :
    p (x.fst >>= ProductF.fst ∘ f) (x.snd >>= ProductF.snd ∘ f)

instance instMonad (F₁ : Type u → Type v) [Monad F₁] (F₂ : Type u → Type w) [Monad F₂]
    (p : {α : Type u} → F₁ α → F₂ α → Prop)
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p] :
    Monad (ProductF F₁ F₂ p) where
  pure {α : Type u} (x : α) := ⟨pure x, pure x, PureInvariant.pure_invariant x⟩
  bind {α β : Type u} (x : ProductF F₁ F₂ p α) (f : α → ProductF F₁ F₂ p β) :=
    ⟨x.fst >>= ProductF.fst ∘ f, x.snd >>= ProductF.snd ∘ f, BindInvariant.bind_invariant f x⟩

@[simp]
theorem pure_fst_pure {F₁ : Type u → Type v} [Monad F₁]
    {F₂ : Type u → Type w} [Monad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    (x : α) : (pure x : ProductF F₁ F₂ p α).fst = (pure x : F₁ α) := by
  simp only [pure]

@[simp]
theorem pure_snd_pure {F₁ : Type u → Type v} [Monad F₁]
    {F₂ : Type u → Type w} [Monad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    (x : α) : (pure x : ProductF F₁ F₂ p α).snd = (pure x : F₂ α) := by
  simp only [pure]

@[simp]
theorem bind_fst_bind {F₁ : Type u → Type v} [Monad F₁]
    {F₂ : Type u → Type w} [Monad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (x : ProductF F₁ F₂ p α) (f : α → ProductF F₁ F₂ p β) :
    (x >>= f).fst = x.fst >>= ProductF.fst ∘ f := by
  simp only [bind]

@[simp]
theorem bind_snd_bind {F₁ : Type u → Type v} [Monad F₁]
    {F₂ : Type u → Type w} [Monad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (x : ProductF F₁ F₂ p α) (f : α → ProductF F₁ F₂ p β) :
    (x >>= f).snd = x.snd >>= ProductF.snd ∘ f := by
  simp only [bind]

@[simp]
theorem monad_map_fst_map {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (f : α → β) (x : ProductF F₁ F₂ p α) :
    (f <$> x).fst = f <$> x.fst := by
  simp only [←bind_pure_comp]
  rfl

@[simp]
theorem monad_map_snd_map {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (f : α → β) (x : ProductF F₁ F₂ p α) :
    (f <$> x).snd = f <$> x.snd := by
  simp only [←bind_pure_comp]
  rfl

@[simp]
theorem monad_seq_fst_seq {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (f : ProductF F₁ F₂ p (α → β)) (x : ProductF F₁ F₂ p α) :
    (f <*> x).fst = f.fst <*> x.fst := by
  simp only [← bind_map, ← bind_pure_comp]
  rfl

@[simp]
theorem monad_seq_snd_seq {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (f : ProductF F₁ F₂ p (α → β)) (x : ProductF F₁ F₂ p α) :
    (f <*> x).snd = f.snd <*> x.snd := by
  simp only [← bind_map, ← bind_pure_comp]
  rfl

@[simp]
theorem monad_seqLeft_fst_seqLeft {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (x : ProductF F₁ F₂ p α) (y : ProductF F₁ F₂ p β) :
    (x <* y).fst = x.fst <* y.fst := by
  simp only [seqLeft_eq, ← bind_pure_comp, ← bind_map, bind_assoc, pure_bind, Function.const_apply]
  rfl

@[simp]
theorem monad_seqLeft_snd_seqLeft {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (x : ProductF F₁ F₂ p α) (y : ProductF F₁ F₂ p β) :
    (x <* y).snd = x.snd <* y.snd := by
  simp only [seqLeft_eq, ← bind_pure_comp, ← bind_map, bind_assoc, pure_bind, Function.const_apply]
  rfl

@[simp]
theorem monad_seqRight_fst_seqRight {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (x : ProductF F₁ F₂ p α) (y : ProductF F₁ F₂ p β) :
    (x *> y).fst = x.fst *> y.fst := by
  simp only [seqRight_eq, ← bind_pure_comp, Function.const_apply, ← bind_map, bind_assoc, pure_bind,
    id_eq, bind_pure]
  rfl

@[simp]
theorem monad_seqRight_snd_seqRight {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p]
    {α β : Type u} (x : ProductF F₁ F₂ p α) (y : ProductF F₁ F₂ p β) :
    (x *> y).snd = x.snd *> y.snd := by
  simp only [seqRight_eq, ← bind_pure_comp, Function.const_apply, ← bind_map, bind_assoc, pure_bind,
    id_eq, bind_pure]
  rfl

instance instLawfulMonad {F₁ : Type u → Type v} [Monad F₁] [LawfulMonad F₁]
    {F₂ : Type u → Type w} [Monad F₂] [LawfulMonad F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [PureInvariant F₁ F₂ p] [BindInvariant F₁ F₂ p] :
    LawfulMonad (ProductF F₁ F₂ p) where
      id_map := by
        intros
        apply ProductF.eq_of_fst_snd_eq
        simp only [monad_map_fst_map, id_map, monad_map_snd_map, and_self]
      map_const := by
        intros
        rfl
      seqLeft_eq := by
        intros
        apply ProductF.eq_of_fst_snd_eq
        simp only [monad_seqLeft_fst_seqLeft, seqLeft_eq, monad_seq_fst_seq, monad_map_fst_map,
          monad_seqLeft_snd_seqLeft, monad_seq_snd_seq, monad_map_snd_map, and_self]
      seqRight_eq := by
        intros
        apply ProductF.eq_of_fst_snd_eq
        simp only [monad_seqRight_fst_seqRight, seqRight_eq, monad_seq_fst_seq, monad_map_fst_map,
          monad_seqRight_snd_seqRight, monad_seq_snd_seq, monad_map_snd_map, and_self]
      pure_seq := by
        intros
        apply ProductF.eq_of_fst_snd_eq
        simp only [monad_seq_fst_seq, pure_fst_pure, pure_seq, monad_map_fst_map, monad_seq_snd_seq,
          pure_snd_pure, monad_map_snd_map, and_self]
      bind_pure_comp := by
        intros
        apply ProductF.eq_of_fst_snd_eq
        simp only [bind, pure, Function.comp_def, bind_pure_comp, monad_map_fst_map,
          monad_map_snd_map, and_self]
      bind_map := by
        intros
        apply ProductF.eq_of_fst_snd_eq
        simp only [bind, Function.comp_def, monad_map_fst_map, bind_map, monad_map_snd_map,
          monad_seq_fst_seq, monad_seq_snd_seq, and_self]
      pure_bind := by
        intros
        apply ProductF.eq_of_fst_snd_eq
        simp only [bind, pure_fst_pure, Function.comp_def, pure_bind, pure_snd_pure, and_self]
      bind_assoc := by
        intros
        apply ProductF.eq_of_fst_snd_eq
        simp only [bind, Function.comp_def, bind_assoc, and_self]
