import Mathlib.Tactic
import Enumerations.Basic

universe u v w

namespace Data

@[inline]
abbrev EquivType (Class : Type u → Type v) :=  {imp : Type u} → (inst : Class imp) → imp →
    {imp' : Type u} → (inst' : Class imp') → imp' → Prop

class ClassEquiv (Class : Type u → Type v)
    (equiv : EquivType Class) : Prop where
  refl {imp : Type u} (inst : Class imp) (x : imp) :
    equiv inst x inst x
  symm {imp : Type u} (inst : Class imp) (x : imp) {imp' : Type u} (inst' : Class imp') (x' : imp') :
    equiv inst x inst' x' → equiv inst' x' inst x
  trans {imp₁ : Type u} (inst₁ : Class imp₁) (x₁ : imp₁) {imp₂ : Type u} (inst₂ : Class imp₂) (x₂ : imp₂)
    {imp₃ : Type u} (inst₃ : Class imp₃) (x₃ : imp₃) :
    equiv inst₁ x₁ inst₂ x₂ → equiv inst₂ x₂ inst₃ x₃ →
    equiv inst₁ x₁ inst₃ x₃

structure Def where
  Class : Type u → Type v
  equiv : EquivType Class
  refl {imp : Type u} (inst : Class imp) (x : imp) :
    equiv inst x inst x
  symm {imp : Type u} {imp' : Type u} (inst : Class imp) (x : imp) (inst' : Class imp') (x' : imp') :
    equiv inst x inst' x' → equiv inst' x' inst x
  trans {imp₁ : Type u} {imp₂ : Type u} {imp₃ : Type u} (inst₁ : Class imp₁) (x₁ : imp₁) (inst₂ : Class imp₂) (x₂ : imp₂)
    (inst₃ : Class imp₃) (x₃ : imp₃) :
    equiv inst₁ x₁ inst₂ x₂ → equiv inst₂ x₂ inst₃ x₃ →
    equiv inst₁ x₁ inst₃ x₃

structure Imp (Class : Type u → Type v) : Type (max (u + 1) v) where
  imp : Type u
  [inst : Class imp]
  value : imp

instance setoid (d : Def) : Setoid (Imp d.Class) where
  r (x x' : Imp d.Class) := d.equiv x.inst x.value x'.inst x'.value
  iseqv := by
    constructor
    · intro _
      refine' d.refl _ _
    · intro _ _
      refine' d.symm _ _ _ _
    · intro _ _ _
      refine' d.trans _ _ _ _ _ _

end Data

def Data (d : Data.Def.{u, v}) :
    Type (max (u + 1) v) :=
  Quotient (Data.setoid d)

namespace Data

set_option checkBinderAnnotations false in
def lift' (d : Def.{u, v}) {β : Type w}
    (f : {imp : Type u} → [inst : d.Class imp] → imp → β)
    (h : ∀ (imp imp': Type u) (inst : d.Class imp) (inst' : d.Class imp') (x : imp) (x' : imp'),
    d.equiv inst x inst' x' → f (inst := inst) x = f (inst := inst') x') :
    Data d → β :=
  Quotient.lift (fun x : Imp d.Class => f (inst := x.inst) x.value) <| by
    intro x x'
    simp only [HasEquiv.Equiv, Setoid.r]
    apply h

structure lift.Precondition (d : Def.{u, v}) {β : Type w}
    (f : {imp : Type u} → (inst : d.Class imp) → imp → β) : Prop where
  f_equiv {imp imp': Type u} (inst : d.Class imp) (inst' : d.Class imp') (x : imp) (x' : imp') :
    d.equiv inst x inst' x' → f inst x = f inst' x'


def lift (d : Def.{u, v}) {β : {imp : Type u} → imp → Type w}
    (f : {imp : Type u} → (inst : d.Class imp) → (x : imp) → β x)
    (h : lift.Precondition d f) :
    (x : Data d) → β x.value :=
  Quotient.lift (fun x : Imp d.Class => f x.inst x.value) <| by
    intro x x'
    simp only [HasEquiv.Equiv, Setoid.r]
    apply h.f_equiv

end Data







class ListLikeClass (α : Type u) (L : Type v) : Type (max u v) where
  isNil : L → Prop
  head (as : L) : ¬ isNil as → α
  tail : L → L

class FiniteListLikeClass (α : Type u) (L : Type v) extends ListLikeClass α L : Type (max u v) where
  finite (as : L) : ∃ (n : ℕ), isNil (tail^[n] as)

namespace FiniteListLikeClass





structure equivOut {α : Type u} {L : Type v} (inst : FiniteListLikeClass α L) (as : L)
    {L' : Type v} (inst' : FiniteListLikeClass α L') (as' : L') : Prop where
  intro ::
  isNil_eq : inst.isNil as ↔ inst'.isNil as'
  head_eq (not_nil : _) : inst.head as not_nil = inst'.head as' (by
    apply not_iff_not.mpr isNil_eq |>.mp <| not_nil
    done)

namespace equivOut

def not_isNil_eq {α : Type u} {L : Type v} {inst : FiniteListLikeClass α L} {as : L}
    {L' : Type v} {inst' : FiniteListLikeClass α L'} {as' : L'} (h : equivOut inst as inst' as') :
    ¬ inst.isNil as ↔ ¬ inst'.isNil as' := by
  apply not_iff_not.mpr h.isNil_eq

theorem is_refl {α : Type u} {L : Type v} (inst : FiniteListLikeClass α L) (as : L) :
    equivOut inst as inst as := by
  apply equivOut.intro
  all_goals simp only [implies_true]

theorem is_symm {α : Type u} {L : Type v} (inst : FiniteListLikeClass α L) (as : L)
    {L' : Type v} (inst' : FiniteListLikeClass α L') (as' : L')
    (h : equivOut inst as inst' as') : equivOut inst' as' inst as := by
  apply equivOut.intro
  · intro not_nil'
    simp only [h.head_eq <| h.not_isNil_eq.mpr not_nil']
  · simp only [h.isNil_eq]

theorem is_trans {α : Type u} {L₁ : Type v} (inst₁ : FiniteListLikeClass α L₁) (as₁ : L₁)
    {L₂ : Type v} (inst₂ : FiniteListLikeClass α L₂) (as₂ : L₂)
    {L₃ : Type v} (inst₃ : FiniteListLikeClass α L₃) (as₃ : L₃)
    (h : equivOut inst₁ as₁ inst₂ as₂) (h' : equivOut inst₂ as₂ inst₃ as₃) :
    equivOut inst₁ as₁ inst₃ as₃ := by
  apply equivOut.intro
  · intro not_nil₁
    simp only [h.head_eq not_nil₁, h'.head_eq <| h.not_isNil_eq.mp not_nil₁]
  · simp only [h.isNil_eq, h'.isNil_eq]

end equivOut

def equiv {α : Type u} {L : Type v} (inst : FiniteListLikeClass α L) (as : L)
    {L' : Type v} (inst' : FiniteListLikeClass α L') (as' : L') : Prop :=
  ∀ (n : ℕ), equivOut inst (inst.tail^[n] as) inst' (inst'.tail^[n] as')

def Def (α : Type u): Data.Def where
  Class := FiniteListLikeClass α
  equiv := equiv
  refl inst as := by
    unfold equiv
    simp only [equivOut.is_refl, forall_const]
  symm inst as inst' as' := by
    unfold equiv
    intro h n
    have := h n
    apply equivOut.is_symm
    assumption
  trans inst₁ as₁ inst₂ as₂ inst₃ as₃ := by
    unfold equiv
    intro h₁ h₂ n
    have := h₁ n
    have := h₂ n
    apply equivOut.is_trans _ _ inst₂ ((ListLikeClass.tail α)^[n] as₂)
    all_goals assumption

end FiniteListLikeClass

def FiniteListLike (α : Type u) := Data (FiniteListLikeClass.Def α)

namespace FiniteListLike

def isNil {α : Type u} := Data.lift (FiniteListLikeClass.Def α) (·.isNil) <| by
  constructor
  unfold Data.Def.equiv
  unfold FiniteListLikeClass.Def
  unfold FiniteListLikeClass.equiv
  simp only [eq_iff_iff]
  intro _ _ inst inst' x x' h
  have := h 0
  simp only [Function.iterate_zero, id_eq] at this
  exact this.isNil_eq

def head {α : Type u} := Data.lift (FiniteListLikeClass.Def α) (·.head) <| by
  constructor
  unfold Data.Def.equiv
  unfold FiniteListLikeClass.Def
  unfold FiniteListLikeClass.equiv
  simp only
  intro _ _ inst inst' x x' h


end FiniteListLike





instance instListFiniteListLike {α : Type u} : FiniteListLikeClass α (List α) where
  isNil as := as = []
  head := List.head
  tail := List.tail
  finite as := by
    use as.length
    simp only []
    apply List.eq_nil_of_length_eq_zero
    have (n : ℕ) : List.length (List.tail^[n] as) = List.length as - n := by
      revert as
      induction n with
      | zero => intro as; simp only [Nat.zero_eq, Function.iterate_zero, id_eq, ge_iff_le,
        nonpos_iff_eq_zero, tsub_zero]
      | succ n ih =>
        intro as
        simp only [Function.iterate_succ, Function.comp_apply, ih, List.length_tail]
        simp only [Nat.succ_eq_one_add, Nat.sub_add_eq]
    have := this as.length
    simp_all only [le_refl, tsub_eq_zero_of_le]


def as : List ℕ := [1, 2, 3]

#check instListFiniteListLike.tail




def StreamListLike (stream : Type u) (α : Type v) [Stream stream α] := Option (α × stream)

namespace StreamListLike

def isNil {stream : Type u} {α : Type v} [Stream stream α] (as : StreamListLike stream α) : Prop := as = none

def head {stream : Type u} {α : Type v} [Stream stream α] (as : StreamListLike stream α) (h : ¬ isNil as) : α :=
  match as with
  | none => absurd rfl h
  | some (a, _) => a

def tail {stream : Type u} {α : Type v} [Stream stream α] (as : StreamListLike stream α) : StreamListLike stream α :=
  match as with
  | none => none
  | some (_, as) => Stream.next? as

instance {stream : Type u} {α : Type v} [Stream stream α] : ListLikeClass α (StreamListLike stream α) where
  isNil := isNil
  head := head
  tail := tail

end StreamListLike
