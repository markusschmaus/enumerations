import Enumerations.ProductF.Defs
import Enumerations.FilterP

namespace ProductF

class FilterPInvariant (F₁ : Type u → Type v) [FilterP F₁] (F₂ : Type u → Type w) [FilterP F₂]
    (p : {α : Type u} → F₁ α → F₂ α → Prop) : Prop where
  filterP_invariant {α : Type u} (q : α → Prop) [DecidablePred q] (x : ProductF F₁ F₂ p α) :
    p (FilterP.filterP q x.fst) (FilterP.filterP q x.snd)

instance instFilterP {F₁ : Type u → Type v} [FilterP F₁] {F₂ : Type u → Type w} [FilterP F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [FilterPInvariant F₁ F₂ p] :
    FilterP (ProductF F₁ F₂ p) where
  filterP {α : Type u} (q : α → Prop) [DecidablePred q] (x : ProductF F₁ F₂ p α) :=
    ⟨FilterP.filterP q x.fst, FilterP.filterP q x.snd, FilterPInvariant.filterP_invariant q x⟩

@[simp]
theorem filterP_fst_filterP {F₁ : Type u → Type v} [FilterP F₁]
    {F₂ : Type u → Type w} [FilterP F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [FilterPInvariant F₁ F₂ p]
    {α : Type u} (q : α → Prop) [DecidablePred q] (x : ProductF F₁ F₂ p α) :
    (FilterP.filterP q x).fst = FilterP.filterP q x.fst := by
  simp only [FilterP.filterP]

@[simp]
theorem filterP_snd_filterP {F₁ : Type u → Type v} [FilterP F₁]
    {F₂ : Type u → Type w} [FilterP F₂]
    {p : {α : Type u} → F₁ α → F₂ α → Prop}
    [FilterPInvariant F₁ F₂ p]
    {α : Type u} (q : α → Prop) [DecidablePred q] (x : ProductF F₁ F₂ p α) :
    (FilterP.filterP q x).snd = FilterP.filterP q x.snd := by
  simp only [FilterP.filterP]
