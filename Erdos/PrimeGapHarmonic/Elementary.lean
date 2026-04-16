import Erdos.PrimeGapHarmonic.Statement

/- 
# Elementary Facts About the Prime-Gap Harmonic Sum

This file records the basic formal infrastructure for problem `#950`: a clean
membership description for the prime set, nonnegativity of every summand and of
the full sum, exact vanishing for `n = 0, 1, 2`, and the first nontrivial lower
bound coming from the prime `2`.
-/
namespace PrimeGapHarmonic

@[simp] theorem mem_primesBelow {n p : ℕ} :
    p ∈ primesBelow n ↔ p < n ∧ Nat.Prime p := by
  simp [primesBelow]

theorem gapSummand_nonneg {n p : ℕ} (hp : p ∈ primesBelow n) :
    0 ≤ 1 / (((n - p : ℕ) : ℝ)) := by
  have hpn : p < n := (mem_primesBelow.mp hp).1
  have hpos : 0 < (((n - p : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hpn
  positivity

theorem gapReciprocalSum_nonneg (n : ℕ) :
    0 ≤ gapReciprocalSum n := by
  unfold gapReciprocalSum
  exact Finset.sum_nonneg fun p hp => gapSummand_nonneg hp

@[simp] theorem primesBelow_zero : primesBelow 0 = ∅ := by
  ext p
  simp [primesBelow]

@[simp] theorem primesBelow_one : primesBelow 1 = ∅ := by
  ext p
  constructor
  · intro hp
    rcases mem_primesBelow.mp hp with ⟨hp1, hprime⟩
    have hp0 : p = 0 := by omega
    subst hp0
    exact (Nat.not_prime_zero hprime).elim
  · simp

@[simp] theorem primesBelow_two : primesBelow 2 = ∅ := by
  ext p
  constructor
  · intro hp
    rcases mem_primesBelow.mp hp with ⟨hp2, hprime⟩
    have hp01 : p = 0 ∨ p = 1 := by omega
    rcases hp01 with rfl | rfl
    · exact (Nat.not_prime_zero hprime).elim
    · exact (Nat.not_prime_one hprime).elim
  · simp

@[simp] theorem gapReciprocalSum_zero : gapReciprocalSum 0 = 0 := by
  simp [gapReciprocalSum]

@[simp] theorem gapReciprocalSum_one : gapReciprocalSum 1 = 0 := by
  simp [gapReciprocalSum]

@[simp] theorem gapReciprocalSum_two : gapReciprocalSum 2 = 0 := by
  simp [gapReciprocalSum]

theorem two_mem_primesBelow {n : ℕ} (hn : 2 < n) :
    2 ∈ primesBelow n := by
  exact mem_primesBelow.mpr ⟨hn, Nat.prime_two⟩

theorem inv_sub_two_le_gapReciprocalSum {n : ℕ} (hn : 2 < n) :
    1 / (((n - 2 : ℕ) : ℝ)) ≤ gapReciprocalSum n := by
  unfold gapReciprocalSum
  refine Finset.single_le_sum (fun p hp => gapSummand_nonneg hp) (two_mem_primesBelow hn)

theorem gapReciprocalSum_pos_of_two_lt {n : ℕ} (hn : 2 < n) :
    0 < gapReciprocalSum n := by
  have hterm : 0 < 1 / (((n - 2 : ℕ) : ℝ)) := by
    have hpos : 0 < (((n - 2 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.sub_pos_of_lt hn
    positivity
  exact lt_of_lt_of_le hterm (inv_sub_two_le_gapReciprocalSum hn)

end PrimeGapHarmonic
