import Enumerations.ListM
import Enumerations.OptionM.Defs
import Enumerations.Basic

@[simp]
def isPrimeLessThan (n p: ℕ) : Prop :=
  p < n ∧ Nat.Prime p

@[simp]
def isPrimeEqualTo (n p: ℕ) : Prop :=
  n = p ∧ Nat.Prime p

def CandidatePrime {n : ℕ} (ps : ListS (isPrimeLessThan n)) : OptionS (isPrimeEqualTo n) :=
  if _2_le : 2 ≤ n then
    if h : ListM.anyP (· ∣ n) ps then
      Section.mk none <| by
        simp_all only [ListM.anyP, Nat.isUnit_iff, ListM.predicate, isPrimeLessThan, OptionS.valid,
          isPrimeEqualTo, iff_false, not_and, forall_eq]
        intro n' n'_eq_n Prime_n
        subst n'_eq_n
        obtain ⟨p, p_dvd_n, p_lt_n, Prime_p⟩ := h
        have := Nat.prime_dvd_prime_iff_eq Prime_p Prime_n |>.mp p_dvd_n
        linarith
    else
      Section.mk (some n) <| by
        simp_all only [ListM.anyP, Nat.isUnit_iff, ListM.predicate, isPrimeLessThan, not_exists,
          not_and, OptionS.valid, isPrimeEqualTo, Option.some.injEq]
        intro y
        simp only [and_iff_left_iff_imp]
        intro n_eq_y; subst n_eq_y
        apply Nat.prime_def_lt.mpr
        by_contra h'
        revert h
        simp_all only [Nat.isUnit_iff, true_and, not_forall, exists_prop, exists_and_left,
          not_exists, not_and, imp_false, not_not, _2_le]
        obtain ⟨m, m_lt_n, m_dvd_n, m_ne_1⟩ := h'
        obtain ⟨p, Prime_p, p_dvd_m⟩ : ∃ (p : ℕ), Nat.Prime p ∧ p ∣ m := Nat.exists_prime_and_dvd m_ne_1
        use p
        have := dvd_trans p_dvd_m m_dvd_n
        simp_all only [Nat.isUnit_iff, and_true, true_and, gt_iff_lt]
        have := Nat.le_of_dvd ?_ p_dvd_m
        · calc
            p ≤ m := by linarith
            _ < n := by linarith
        · by_contra
          simp_all only [Nat.isUnit_iff, not_lt, nonpos_iff_eq_zero, isUnit_zero_iff, zero_dvd_iff,
            zero_ne_one, not_false_eq_true, dvd_zero]
  else
    Section.mk none <| by
      simp only [not_le] at _2_le
      cases _2_le |> Nat.le_of_lt_succ |> Nat.le_or_eq_of_le_succ
      all_goals aesop

def ExtendPrimes {n : ℕ} (ps : ListS (isPrimeLessThan n)) : ListS (isPrimeLessThan (n + 1)) :=
  let p : OptionM ℕ := CandidatePrime ps
  ListM.consOpt p ps |>.cast <| by
    have p_prop := p.property
    have ps_prop := ps.property
    simp_all only [OptionS.valid, isPrimeEqualTo, ListM.valid, isPrimeLessThan, OptionM.predicate,
      ListM.predicate]
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

def PrimesLessThan (n : ℕ) : ListS (isPrimeLessThan n) :=
  let start : ListS (isPrimeLessThan 0) := Section.mk [] <| by
    simp_all only [ListM.valid, isPrimeLessThan, not_lt_zero', false_and, List.find?_nil,
      List.not_mem_nil, forall_const]

  let result := Nat.iterateDep @ExtendPrimes n start

  result.cast <| by
    simp_all only [ListM.predicate, isPrimeLessThan, add_zero, forall_const]


#eval PrimesLessThan 1000 |>.fst
