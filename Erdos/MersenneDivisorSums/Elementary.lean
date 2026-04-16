import Erdos.MersenneDivisorSums.Statement

/- 
# Elementary Facts About Mersenne Divisor Sums

This file records the first structural facts about the partial sums in problem
`#893`: every term is positive, the partial sums satisfy a clean successor
recurrence, they are monotone, and in fact they dominate `n`.
-/
namespace MersenneDivisorSums

theorem mersenneNumber_ne_zero (k : ℕ) : 2 ^ (k + 1) - 1 ≠ 0 := by
  have hpow : 0 < 2 ^ (k + 1) := pow_pos (by decide : 0 < 2) _
  omega

theorem one_le_mersenneDivisorTerm (k : ℕ) : 1 ≤ mersenneDivisorTerm k := by
  unfold mersenneDivisorTerm
  have hmem : 1 ∈ (2 ^ (k + 1) - 1).divisors := by
    exact Nat.one_mem_divisors.mpr (mersenneNumber_ne_zero k)
  exact Finset.one_le_card.mpr ⟨1, hmem⟩

theorem mersenneDivisorTerm_pos (k : ℕ) : 0 < mersenneDivisorTerm k := by
  exact lt_of_lt_of_le Nat.zero_lt_one (one_le_mersenneDivisorTerm k)

@[simp] theorem mersenneDivisorSum_zero : mersenneDivisorSum 0 = 0 := by
  simp [mersenneDivisorSum]

@[simp] theorem mersenneDivisorSum_succ (n : ℕ) :
    mersenneDivisorSum (n + 1) = mersenneDivisorSum n + mersenneDivisorTerm n := by
  unfold mersenneDivisorSum
  rw [Finset.sum_range_succ]

theorem mersenneDivisorSum_le_succ (n : ℕ) :
    mersenneDivisorSum n ≤ mersenneDivisorSum (n + 1) := by
  rw [mersenneDivisorSum_succ]
  exact Nat.le_add_right _ _

theorem mersenneDivisorSum_mono {m n : ℕ} (hmn : m ≤ n) :
    mersenneDivisorSum m ≤ mersenneDivisorSum n := by
  induction hmn with
  | refl => exact le_rfl
  | @step n hmn ih =>
      exact le_trans ih (mersenneDivisorSum_le_succ n)

theorem self_le_mersenneDivisorSum (n : ℕ) : n ≤ mersenneDivisorSum n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [mersenneDivisorSum_succ]
      calc
        n + 1 ≤ mersenneDivisorSum n + 1 := Nat.succ_le_succ ih
        _ ≤ mersenneDivisorSum n + mersenneDivisorTerm n :=
          Nat.add_le_add_left (one_le_mersenneDivisorTerm n) _

theorem mersenneDivisorSum_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneDivisorSum n := by
  exact lt_of_lt_of_le hn (self_le_mersenneDivisorSum n)

theorem mersenneDivisorSum_le_double {n : ℕ} :
    mersenneDivisorSum n ≤ mersenneDivisorSum (2 * n) := by
  apply mersenneDivisorSum_mono
  omega

end MersenneDivisorSums
