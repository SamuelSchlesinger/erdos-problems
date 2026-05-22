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

/-- Once the exponent is at least two, the Mersenne number `2^(k+1)-1` has the
two distinct divisors `1` and itself. This gives the first nontrivial per-term
lower bound for the sum. -/
theorem two_le_mersenneDivisorTerm_of_one_le (k : ℕ) (hk : 1 ≤ k) :
    2 ≤ mersenneDivisorTerm k := by
  unfold mersenneDivisorTerm
  set m : ℕ := 2 ^ (k + 1) - 1 with hm
  have hm_ne_zero : m ≠ 0 := by
    rw [hm]
    exact mersenneNumber_ne_zero k
  have hm_gt_one : 1 < m := by
    rw [hm]
    have hk_two : 2 ≤ k + 1 := by omega
    have hpow : 2 ^ 2 ≤ 2 ^ (k + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hk_two
    omega
  have hmem_one : 1 ∈ m.divisors := by
    exact Nat.one_mem_divisors.mpr hm_ne_zero
  have hmem_self : m ∈ m.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨dvd_rfl, hm_ne_zero⟩
  have hsubset : ({1, m} : Finset ℕ) ⊆ m.divisors := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hmem_one
    · exact hmem_self
  have hnot_mem : (1 : ℕ) ∉ ({m} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    exact ne_of_lt hm_gt_one
  calc
    2 = ({1, m} : Finset ℕ).card := by
      rw [Finset.card_insert_of_notMem hnot_mem, Finset.card_singleton]
    _ ≤ m.divisors.card := Finset.card_le_card hsubset

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

/-- A clean elementary strengthening of positivity: for `n ≥ 1`, every term
after the first contributes at least two divisors, while the first term
contributes at least one. Hence `2 * n - 1 ≤ f(n)`. -/
theorem two_n_sub_one_le_mersenneDivisorSum {n : ℕ} (hn : 1 ≤ n) :
    2 * n - 1 ≤ mersenneDivisorSum n := by
  revert hn
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn
      cases n with
      | zero =>
          simpa [mersenneDivisorSum] using one_le_mersenneDivisorTerm 0
      | succ n =>
          rw [mersenneDivisorSum_succ]
          have hprev : 2 * (n + 1) - 1 ≤ mersenneDivisorSum (n + 1) := by
            exact ih (by omega)
          have hterm : 2 ≤ mersenneDivisorTerm (n + 1) := by
            exact two_le_mersenneDivisorTerm_of_one_le (n + 1) (by omega)
          omega

theorem mersenneDivisorSum_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneDivisorSum n := by
  exact lt_of_lt_of_le hn (self_le_mersenneDivisorSum n)

theorem mersenneDivisorSum_le_double {n : ℕ} :
    mersenneDivisorSum n ≤ mersenneDivisorSum (2 * n) := by
  apply mersenneDivisorSum_mono
  omega

end MersenneDivisorSums
