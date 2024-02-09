import Enumerations.ListM

@[simp]
def Nat.ltPred (pred : Nat → Prop) (n x : Nat) :=
  x < n ∧ pred x

@[simp]
def Nat.eqPred (pred : Nat → Prop) (n x : Nat) :=
  n = x ∧ pred x

namespace ListM

structure Generator where
  predicate : ℕ → Prop
  checkNext {n : Nat} (xs : ListS (n.ltPred predicate)) : OptionS (n.eqPred predicate)

namespace Generator

def extend (g : Generator) {n : ℕ} (xs : ListS (n.ltPred g.predicate)) : ListS ((n + 1).ltPred g.predicate) :=
  let x : OptionM ℕ := g.checkNext xs
  ListM.consOpt x xs |>.cast <| by
    have p_prop := x.property
    have ps_prop := xs.property
    simp_all only [OptionS.valid, Nat.eqPred, valid, Nat.ltPred, ListM.predicate, OptionM.predicate]
    intro a
    constructor
    · intro h
      obtain h' | h' := h
      · have := p_prop a |>.mpr h'
        simp_all only [Option.some.injEq, and_iff_left_iff_imp, forall_eq', lt_add_iff_pos_right,
          zero_lt_one, and_self]
      · have ⟨lt_succ, _⟩ := ps_prop a |>.mpr h'
        simp_all only [and_true, gt_iff_lt]
        linarith
    · intro h'
      obtain ⟨lt_succ, prime_a⟩ := h'
      by_cases h : a < n
      · have := ps_prop a |>.mp (And.intro h prime_a)
        exact Or.inr this
      · have : n = a := by linarith
        have := p_prop a |>.mp (And.intro this prime_a)
        exact Or.inl this

end Generator

end ListM

-- def PrimesLessThan (n : ℕ) : ListS (isPrimeLessThan n) :=
--   let start : ListS (isPrimeLessThan 0) := Section.mk [] <| by
--     simp_all only [ListM.valid, isPrimeLessThan, not_lt_zero', false_and, List.find?_nil,
--       List.not_mem_nil, forall_const]

--   let result := Nat.iterateDep @ExtendPrimes n start

--   ListS.proof result <| by
--     simp_all only [ListM.predicate, isPrimeLessThan, add_zero, forall_const]


-- #eval PrimesLessThan 1000 |>.fst
