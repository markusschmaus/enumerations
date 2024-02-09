import Enumerations.Predicate

universe u

class FilterP (F : Type u → Type v) where
  filterP {α : Type u} (p : α → Prop) [DecidablePred p] : F α → F α

instance : FilterP List where
  filterP {α : Type u} (p : α → Prop) [DecidablePred p] := List.filter (fun x => p x)

instance : FilterP Option where
  filterP {α : Type u} (p : α → Prop) [DecidablePred p] := Option.filter (fun x => p x)

instance : FilterP Predicate where
  filterP {α : Type u} (p : α → Prop) [DecidablePred p] (q : α → Prop) (a : α) := p a ∧ q a

export FilterP (filterP)
