import Erdos.ErdosMoser.KnownCases

/-!
# Erdős-Moser: The Case `k = 8`

This file pushes the exact small-exponent analysis one step further:

1. there are no solutions with `k = 8`;
2. consequently, among `k ≤ 8`, the classical solution `(m, k) = (3, 1)` is
   still the only possibility.
-/

namespace ErdosMoser

/-- Tail inequality used in the `k = 8` contradiction. -/
private theorem pow8_tail_gt {m : ℕ} (hm : 15 ≤ m) :
    m ^ 8 < (m - 3) ^ 8 + (m - 2) ^ 8 + (m - 1) ^ 8 := by
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hmZ : (15 : ℤ) ≤ m := by exact_mod_cast hm
  have hfactor :
      ((m : ℤ) - 3) ^ 8 + ((m : ℤ) - 2) ^ 8 + ((m : ℤ) - 1) ^ 8 - (m : ℤ) ^ 8 =
        2 * ((m : ℤ) - 15) ^ 8 + 192 * ((m : ℤ) - 15) ^ 7 + 7952 * ((m : ℤ) - 15) ^ 6 +
          184464 * ((m : ℤ) - 15) ^ 5 + 2596160 * ((m : ℤ) - 15) ^ 4 +
          22320144 * ((m : ℤ) - 15) ^ 3 + 110647712 * ((m : ℤ) - 15) ^ 2 +
          265075632 * ((m : ℤ) - 15) + 158610848 := by
    ring
  have h015 : 0 ≤ (m : ℤ) - 15 := by nlinarith [hmZ]
  have h8 : 0 ≤ ((m : ℤ) - 15) ^ 8 := by positivity
  have h7 : 0 ≤ ((m : ℤ) - 15) ^ 7 := by positivity
  have h6 : 0 ≤ ((m : ℤ) - 15) ^ 6 := by positivity
  have h5 : 0 ≤ ((m : ℤ) - 15) ^ 5 := by positivity
  have h4 : 0 ≤ ((m : ℤ) - 15) ^ 4 := by positivity
  have h3 : 0 ≤ ((m : ℤ) - 15) ^ 3 := by positivity
  have h2 : 0 ≤ ((m : ℤ) - 15) ^ 2 := by positivity
  have hlin : 0 ≤
      2 * ((m : ℤ) - 15) ^ 8 + 192 * ((m : ℤ) - 15) ^ 7 + 7952 * ((m : ℤ) - 15) ^ 6 +
        184464 * ((m : ℤ) - 15) ^ 5 + 2596160 * ((m : ℤ) - 15) ^ 4 +
        22320144 * ((m : ℤ) - 15) ^ 3 + 110647712 * ((m : ℤ) - 15) ^ 2 +
        265075632 * ((m : ℤ) - 15) := by
    nlinarith [h015, h8, h7, h6, h5, h4, h3, h2]
  have haux : 0 <
      2 * ((m : ℤ) - 15) ^ 8 + 192 * ((m : ℤ) - 15) ^ 7 + 7952 * ((m : ℤ) - 15) ^ 6 +
        184464 * ((m : ℤ) - 15) ^ 5 + 2596160 * ((m : ℤ) - 15) ^ 4 +
        22320144 * ((m : ℤ) - 15) ^ 3 + 110647712 * ((m : ℤ) - 15) ^ 2 +
        265075632 * ((m : ℤ) - 15) + 158610848 := by
    nlinarith [hlin]
  have hgtZ : (m : ℤ) ^ 8 < ((m : ℤ) - 3) ^ 8 + ((m : ℤ) - 2) ^ 8 + ((m : ℤ) - 1) ^ 8 := by
    nlinarith [hfactor, haux]
  have hCast : ((m : ℤ) ^ 8) < (((m - 3 : ℕ) ^ 8 + (m - 2 : ℕ) ^ 8 + (m - 1 : ℕ) ^ 8 : ℕ) : ℤ) := by
    simpa [Nat.cast_sub hm3, Nat.cast_sub hm2, Nat.cast_sub hm1, sub_eq_add_neg, add_assoc,
      add_comm] using hgtZ
  exact_mod_cast hCast

/-- There are no solutions to the Erdős-Moser equation with exponent `k = 8`. -/
theorem no_solution_k_eight (m : ℕ) : ¬IsSolution m 8 := by
  intro hsol
  rcases hsol with ⟨_hmpos, _hkpos, hEq⟩
  by_cases hm14 : m ≤ 14
  · interval_cases m <;> norm_num [powerSum] at hEq
  · have hm15 : 15 ≤ m := by omega
    have hsubset : ({m - 3, m - 2, m - 1} : Finset ℕ) ⊆ Finset.range m := by
      intro x hx
      simp [Finset.mem_range] at hx ⊢
      omega
    have hlow_set : (∑ i ∈ ({m - 3, m - 2, m - 1} : Finset ℕ), i ^ 8) ≤ powerSum m 8 := by
      unfold powerSum
      exact Finset.sum_le_sum_of_subset (f := fun i => i ^ 8) hsubset
    have hset :
        (∑ i ∈ ({m - 3, m - 2, m - 1} : Finset ℕ), i ^ 8) =
          (m - 3) ^ 8 + (m - 2) ^ 8 + (m - 1) ^ 8 := by
      have hne12 : m - 3 ≠ m - 2 := by omega
      have hne23 : m - 2 ≠ m - 1 := by omega
      have hne13 : m - 3 ≠ m - 1 := by omega
      simp [hne12, hne23, hne13, add_comm, add_assoc]
    have hlow : (m - 3) ^ 8 + (m - 2) ^ 8 + (m - 1) ^ 8 ≤ powerSum m 8 := by
      simpa [hset] using hlow_set
    have hgt : m ^ 8 < (m - 3) ^ 8 + (m - 2) ^ 8 + (m - 1) ^ 8 := pow8_tail_gt hm15
    have hlt : m ^ 8 < powerSum m 8 := lt_of_lt_of_le hgt hlow
    have hlt' : m ^ 8 < m ^ 8 := by
      simp [hEq] at hlt
    exact (lt_irrefl _ hlt')

/-- Among `k ≤ 8`, the classical solution `(m, k) = (3, 1)` is the only one. -/
theorem no_solution_k_le_eight {m k : ℕ} (hkpos : 0 < k) (hk : k ≤ 8)
    (hsol : IsSolution m k) : m = 3 ∧ k = 1 := by
  have hk_cases : k ≤ 7 ∨ k = 8 := by omega
  rcases hk_cases with hk7 | rfl
  · exact no_solution_k_le_seven hkpos hk7 hsol
  · exact (no_solution_k_eight m hsol).elim

end ErdosMoser
