import Enumerations.ProductF.Defs

namespace ProductF

class MapInvariant (F₁ : Type u → Type v) [Functor F₁] (F₂ : Type u → Type w) [Functor F₂]
    (p : {α : Type u} → F₁ α → F₂ α → Prop) : Prop where
  map_invariant {α β : Type u} (f : α → β) (x : ProductF F₁ F₂ p α) : p (f <$> x.fst) (f <$> x.snd)

instance instFunctor {F₁ : Type u → Type v} [Functor F₁] {F₂ : Type u → Type w} [Functor F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [MapInvariant F₁ F₂ p] :
    Functor (ProductF F₁ F₂ p) where
  map {α β : Type u} (f : α → β) (x : ProductF F₁ F₂ p α) :=
    ⟨f <$> x.fst, f <$> x.snd, MapInvariant.map_invariant f x⟩

@[simp]
theorem map_fst_map {F₁ : Type u → Type v} [Functor F₁]
    {F₂ : Type u → Type w} [Functor F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [MapInvariant F₁ F₂ p]
    {α β : Type u} (f : α → β) (x : ProductF F₁ F₂ p α) :
    (f <$> x).fst = f <$> x.fst := by
  simp only [Functor.map]

@[simp]
theorem map_snd_map {F₁ : Type u → Type v} [Functor F₁]
    {F₂ : Type u → Type w} [Functor F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [MapInvariant F₁ F₂ p]
    {α β : Type u} (f : α → β) (x : ProductF F₁ F₂ p α) :
    (f <$> x).snd = f <$> x.snd := by
  simp only [Functor.map]

instance instLawfulFunctor {F₁ : Type u → Type v} [Functor F₁] [LawfulFunctor F₁]
    {F₂ : Type u → Type w} [Functor F₂] [LawfulFunctor F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [MapInvariant F₁ F₂ p] :
    LawfulFunctor (ProductF F₁ F₂ p) where
  id_map := by
    simp only [Functor.map, id_map, implies_true, forall_const]
  comp_map := by
    simp only [Functor.map, comp_map, implies_true, forall_const]
  map_const := by
    intros
    rfl
