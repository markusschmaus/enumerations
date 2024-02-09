import Enumerations.ListM.Defs
import Enumerations.OptionM.Defs

import Mathlib.Data.List.Intervals
import Mathlib.Data.Bool.AllAny

namespace ListM

@[simp]
def anyP {α : Type u} (p : α → Prop) (xs : ListM α) : Prop :=
  ∃ x, p x ∧ xs.predicate x

instance {α : Type u} (p : α → Prop) [DecidablePred p] (xs : ListM α) : Decidable (anyP p xs) :=
  if h : xs.val.any p then
    isTrue <| by
      have := xs.property
      aesop
  else
    isFalse <| by
      have := xs.property
      aesop

def cons {α : Type u} (x : α) (xs : ListM α) : ListS fun x' => x = x' ∨ xs.predicate x' :=
  Section.mk (x :: xs.fst) <| by
    have := xs.property
    simp only [valid, predicate, Bool.not_eq_true, List.mem_cons] at *
    aesop

def consOpt {α : Type u} (x : OptionM α) (xs : ListM α) : ListS fun x' => x.predicate x' ∨ xs.predicate x' :=
  if h : x.val.isSome then
    Section.mk (x.val.get h :: xs.fst) <| by
      have := x.property
      have := xs.property
      simp_all only [OptionS.valid, valid, OptionM.predicate, predicate, OptionM.val,
        Bool.not_eq_true, List.mem_cons]
      aesop
  else
    Section.mk xs.fst <| by
      have := x.property
      have := xs.property
      simp_all only [OptionM.val, Bool.not_eq_true, Option.not_isSome, OptionS.valid, valid,
        OptionM.predicate, predicate, or_iff_right_iff_imp, Option.isSome_iff_exists, not_exists]
      intro y a
      have := h y
      contradiction


@[simp]
def Ico.Property (n m a : Nat) : Prop := n ≤ a ∧ a < m
def Ico (n m : Nat) : ListS (Ico.Property n m)  :=
  Section.mk (List.Ico n m) <| by
    aesop
