/-
# Erdos-Moser Equation: Known Territory

This file pushes the formalization beyond the bare statement:

1. `k = 1` is solved exactly: `IsSolution m 1 ↔ m = 3`.
2. There are no solutions with `k = 2`.
3. There are no solutions with `k = 3`.
4. There are no solutions with `k = 4,5,6,7`.
5. A bounded exhaustive certificate checks `(m, k)` up to `(150, 25)`.
-/
import Erdos.ErdosMoser.Statement

namespace ErdosMoser

open scoped BigOperators

/-- For exponent `k = 1`, the unique positive solution is `m = 3`. -/
theorem solution_k_one_iff (m : ℕ) : IsSolution m 1 ↔ m = 3 := by
  constructor
  · intro hsol
    rcases hsol with ⟨hmpos, _hk, hEq⟩
    have hsum : (∑ i ∈ Finset.range m, i) = m := by
      simpa [powerSum] using hEq
    have hmul : m * (m - 1) = m * 2 := by
      calc
        m * (m - 1) = (∑ i ∈ Finset.range m, i) * 2 := by
          simpa using (Finset.sum_range_id_mul_two m).symm
        _ = m * 2 := by
          simp [hsum]
    have hmminus : m - 1 = 2 := Nat.eq_of_mul_eq_mul_left hmpos hmul
    omega
  · intro hm
    simpa [hm] using solution_three_one

/-- There are no solutions to the Erdos-Moser equation with exponent `k = 2`. -/
theorem no_solution_k_two (m : ℕ) : ¬IsSolution m 2 := by
  intro hsol
  rcases hsol with ⟨hmpos, _hkpos, hEq⟩
  by_cases hm5 : m ≤ 5
  · interval_cases m <;> norm_num [powerSum] at hEq
  · have hm6 : 6 ≤ m := by omega
    have hm0 : 0 < m := by omega
    have hsubset : ({m - 2, m - 1} : Finset ℕ) ⊆ Finset.range m := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact Finset.mem_range.mpr (Nat.sub_lt hm0 (by decide : 0 < 2))
      · have hx'' : x = m - 1 := by simpa using hx'
        rw [hx'']
        exact Finset.mem_range.mpr (Nat.sub_lt hm0 (by decide : 0 < 1))
    have hlow_pair : (∑ i ∈ ({m - 2, m - 1} : Finset ℕ), i ^ 2) ≤ powerSum m 2 := by
      unfold powerSum
      exact Finset.sum_le_sum_of_subset (f := fun i => i ^ 2) hsubset
    have hpair :
        (∑ i ∈ ({m - 2, m - 1} : Finset ℕ), i ^ 2) = (m - 2) ^ 2 + (m - 1) ^ 2 := by
      have hne : m - 2 ≠ m - 1 := by omega
      simp [hne, add_comm]
    have hlow : (m - 2) ^ 2 + (m - 1) ^ 2 ≤ powerSum m 2 := by
      simpa [hpair] using hlow_pair
    have hm1 : 1 ≤ m := by omega
    have hm2 : 2 ≤ m := by omega
    have hmZ : (6 : ℤ) ≤ m := by exact_mod_cast hm6
    have hm1Z : (1 : ℤ) ≤ m := by exact_mod_cast hm1
    have hm2Z : (2 : ℤ) ≤ m := by exact_mod_cast hm2
    have hgtZ : (m : ℤ) ^ 2 < (m - 2) ^ 2 + (m - 1) ^ 2 := by
      nlinarith
    have hgt : m ^ 2 < (m - 2) ^ 2 + (m - 1) ^ 2 := by
      have hCast : ((m : ℤ) ^ 2) < (((m - 2 : ℕ) ^ 2 + (m - 1 : ℕ) ^ 2 : ℕ) : ℤ) := by
        simpa [Nat.cast_sub hm2, Nat.cast_sub hm1] using hgtZ
      exact_mod_cast hCast
    have hlt : m ^ 2 < powerSum m 2 := lt_of_lt_of_le hgt hlow
    have hlt' : m ^ 2 < m ^ 2 := by
      simp [hEq] at hlt
    exact (lt_irrefl _ hlt')

/-- There are no solutions to the Erdos-Moser equation with exponent `k = 3`. -/
theorem no_solution_k_three (m : ℕ) : ¬IsSolution m 3 := by
  intro hsol
  rcases hsol with ⟨_hmpos, _hkpos, hEq⟩
  by_cases hm6 : m ≤ 6
  · interval_cases m <;> norm_num [powerSum] at hEq
  · have hm7 : 7 ≤ m := by omega
    have hsubset : ({m - 3, m - 2, m - 1} : Finset ℕ) ⊆ Finset.range m := by
      intro x hx
      simp [Finset.mem_range] at hx ⊢
      omega
    have hlow_triple : (∑ i ∈ ({m - 3, m - 2, m - 1} : Finset ℕ), i ^ 3) ≤ powerSum m 3 := by
      unfold powerSum
      exact Finset.sum_le_sum_of_subset (f := fun i => i ^ 3) hsubset
    have htriple :
        (∑ i ∈ ({m - 3, m - 2, m - 1} : Finset ℕ), i ^ 3) =
          (m - 3) ^ 3 + (m - 2) ^ 3 + (m - 1) ^ 3 := by
      have hne12 : m - 3 ≠ m - 2 := by omega
      have hne23 : m - 2 ≠ m - 1 := by omega
      have hne13 : m - 3 ≠ m - 1 := by omega
      simp [hne12, hne23, hne13, add_comm, add_assoc]
    have hlow : (m - 3) ^ 3 + (m - 2) ^ 3 + (m - 1) ^ 3 ≤ powerSum m 3 := by
      simpa [htriple] using hlow_triple
    have hm1 : 1 ≤ m := by omega
    have hm2 : 2 ≤ m := by omega
    have hm3 : 3 ≤ m := by omega
    have hmZ : (7 : ℤ) ≤ m := by exact_mod_cast hm7
    have hfactor :
        ((m : ℤ) - 3) ^ 3 + ((m : ℤ) - 2) ^ 3 + ((m : ℤ) - 1) ^ 3 - (m : ℤ) ^ 3 =
          ((m : ℤ) - 6) * (2 * (m : ℤ) ^ 2 - 6 * (m : ℤ) + 6) := by
      ring
    have h1 : 0 < (m : ℤ) - 6 := by nlinarith [hmZ]
    have h2 : 0 < 2 * (m : ℤ) ^ 2 - 6 * (m : ℤ) + 6 := by nlinarith [hmZ]
    have haux : 0 < ((m : ℤ) - 6) * (2 * (m : ℤ) ^ 2 - 6 * (m : ℤ) + 6) := mul_pos h1 h2
    have hgtZ : (m : ℤ) ^ 3 < ((m : ℤ) - 3) ^ 3 + ((m : ℤ) - 2) ^ 3 + ((m : ℤ) - 1) ^ 3 := by
      nlinarith [hfactor, haux]
    have hgt : m ^ 3 < (m - 3) ^ 3 + (m - 2) ^ 3 + (m - 1) ^ 3 := by
      have hCast :
          ((m : ℤ) ^ 3) < (((m - 3 : ℕ) ^ 3 + (m - 2 : ℕ) ^ 3 + (m - 1 : ℕ) ^ 3 : ℕ) : ℤ) := by
        simpa [Nat.cast_sub hm3, Nat.cast_sub hm2, Nat.cast_sub hm1, sub_eq_add_neg, add_assoc,
          add_comm] using hgtZ
      exact_mod_cast hCast
    have hlt : m ^ 3 < powerSum m 3 := lt_of_lt_of_le hgt hlow
    have hlt' : m ^ 3 < m ^ 3 := by
      simp [hEq] at hlt
    exact (lt_irrefl _ hlt')

/-- Tail inequality used in the `k = 4` contradiction. -/
private theorem pow4_tail_gt {m : ℕ} (hm : 8 ≤ m) :
    m ^ 4 < (m - 3) ^ 4 + (m - 2) ^ 4 + (m - 1) ^ 4 := by
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hmZ : (8 : ℤ) ≤ m := by exact_mod_cast hm
  have hfactor :
      ((m : ℤ) - 3) ^ 4 + ((m : ℤ) - 2) ^ 4 + ((m : ℤ) - 1) ^ 4 - (m : ℤ) ^ 4 =
        2 * ((m : ℤ) - 8) ^ 4 + 40 * ((m : ℤ) - 8) ^ 3 + 276 * ((m : ℤ) - 8) ^ 2
          + 688 * ((m : ℤ) - 8) + 226 := by
    ring
  have h08 : 0 ≤ (m : ℤ) - 8 := by nlinarith [hmZ]
  have haux : 0 <
      2 * ((m : ℤ) - 8) ^ 4 + 40 * ((m : ℤ) - 8) ^ 3 + 276 * ((m : ℤ) - 8) ^ 2
        + 688 * ((m : ℤ) - 8) + 226 := by
    nlinarith [h08]
  have hgtZ : (m : ℤ) ^ 4 < ((m : ℤ) - 3) ^ 4 + ((m : ℤ) - 2) ^ 4 + ((m : ℤ) - 1) ^ 4 := by
    nlinarith [hfactor, haux]
  have hCast : ((m : ℤ) ^ 4) < (((m - 3 : ℕ) ^ 4 + (m - 2 : ℕ) ^ 4 + (m - 1 : ℕ) ^ 4 : ℕ) : ℤ) := by
    simpa [Nat.cast_sub hm3, Nat.cast_sub hm2, Nat.cast_sub hm1, sub_eq_add_neg, add_assoc,
      add_comm] using hgtZ
  exact_mod_cast hCast

/-- Tail inequality used in the `k = 5` contradiction. -/
private theorem pow5_tail_gt {m : ℕ} (hm : 9 ≤ m) :
    m ^ 5 < (m - 4) ^ 5 + (m - 3) ^ 5 + (m - 2) ^ 5 + (m - 1) ^ 5 := by
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hmZ : (9 : ℤ) ≤ m := by exact_mod_cast hm
  have hfactor :
      ((m : ℤ) - 4) ^ 5 + ((m : ℤ) - 3) ^ 5 + ((m : ℤ) - 2) ^ 5 + ((m : ℤ) - 1) ^ 5 - (m : ℤ) ^ 5 =
        3 * ((m : ℤ) - 9) ^ 5 + 85 * ((m : ℤ) - 9) ^ 4 + 930 * ((m : ℤ) - 9) ^ 3 +
          4670 * ((m : ℤ) - 9) ^ 2 + 9285 * ((m : ℤ) - 9) + 1427 := by
    ring
  have h09 : 0 ≤ (m : ℤ) - 9 := by nlinarith [hmZ]
  have h5 : 0 ≤ ((m : ℤ) - 9) ^ 5 := by positivity
  have h4 : 0 ≤ ((m : ℤ) - 9) ^ 4 := by positivity
  have h3 : 0 ≤ ((m : ℤ) - 9) ^ 3 := by positivity
  have h2 : 0 ≤ ((m : ℤ) - 9) ^ 2 := by positivity
  have hlin : 0 ≤
      3 * ((m : ℤ) - 9) ^ 5 + 85 * ((m : ℤ) - 9) ^ 4 + 930 * ((m : ℤ) - 9) ^ 3 +
        4670 * ((m : ℤ) - 9) ^ 2 + 9285 * ((m : ℤ) - 9) := by
    nlinarith [h09, h5, h4, h3, h2]
  have haux : 0 <
      3 * ((m : ℤ) - 9) ^ 5 + 85 * ((m : ℤ) - 9) ^ 4 + 930 * ((m : ℤ) - 9) ^ 3 +
        4670 * ((m : ℤ) - 9) ^ 2 + 9285 * ((m : ℤ) - 9) + 1427 := by
    nlinarith [hlin]
  have hgtZ : (m : ℤ) ^ 5 <
      ((m : ℤ) - 4) ^ 5 + ((m : ℤ) - 3) ^ 5 + ((m : ℤ) - 2) ^ 5 + ((m : ℤ) - 1) ^ 5 := by
    nlinarith [hfactor, haux]
  have hCast : ((m : ℤ) ^ 5) <
      (((m - 4 : ℕ) ^ 5 + (m - 3 : ℕ) ^ 5 + (m - 2 : ℕ) ^ 5 + (m - 1 : ℕ) ^ 5 : ℕ) : ℤ) := by
    simpa [Nat.cast_sub hm4, Nat.cast_sub hm3, Nat.cast_sub hm2, Nat.cast_sub hm1, sub_eq_add_neg,
      add_assoc, add_comm] using hgtZ
  exact_mod_cast hCast

/-- Tail inequality used in the `k = 6` contradiction. -/
private theorem pow6_tail_gt {m : ℕ} (hm : 11 ≤ m) :
    m ^ 6 < (m - 3) ^ 6 + (m - 2) ^ 6 + (m - 1) ^ 6 := by
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hmZ : (11 : ℤ) ≤ m := by exact_mod_cast hm
  have hfactor :
      ((m : ℤ) - 3) ^ 6 + ((m : ℤ) - 2) ^ 6 + ((m : ℤ) - 1) ^ 6 - (m : ℤ) ^ 6 =
        2 * ((m : ℤ) - 11) ^ 6 + 96 * ((m : ℤ) - 11) ^ 5 + 1860 * ((m : ℤ) - 11) ^ 4 +
          18200 * ((m : ℤ) - 11) ^ 3 + 90240 * ((m : ℤ) - 11) ^ 2 +
          184596 * ((m : ℤ) - 11) + 22024 := by
    ring
  have h011 : 0 ≤ (m : ℤ) - 11 := by nlinarith [hmZ]
  have h6 : 0 ≤ ((m : ℤ) - 11) ^ 6 := by positivity
  have h5 : 0 ≤ ((m : ℤ) - 11) ^ 5 := by positivity
  have h4 : 0 ≤ ((m : ℤ) - 11) ^ 4 := by positivity
  have h3 : 0 ≤ ((m : ℤ) - 11) ^ 3 := by positivity
  have h2 : 0 ≤ ((m : ℤ) - 11) ^ 2 := by positivity
  have hlin : 0 ≤
      2 * ((m : ℤ) - 11) ^ 6 + 96 * ((m : ℤ) - 11) ^ 5 + 1860 * ((m : ℤ) - 11) ^ 4 +
        18200 * ((m : ℤ) - 11) ^ 3 + 90240 * ((m : ℤ) - 11) ^ 2 + 184596 * ((m : ℤ) - 11) := by
    nlinarith [h011, h6, h5, h4, h3, h2]
  have haux : 0 <
      2 * ((m : ℤ) - 11) ^ 6 + 96 * ((m : ℤ) - 11) ^ 5 + 1860 * ((m : ℤ) - 11) ^ 4 +
        18200 * ((m : ℤ) - 11) ^ 3 + 90240 * ((m : ℤ) - 11) ^ 2 +
        184596 * ((m : ℤ) - 11) + 22024 := by
    nlinarith [hlin]
  have hgtZ : (m : ℤ) ^ 6 < ((m : ℤ) - 3) ^ 6 + ((m : ℤ) - 2) ^ 6 + ((m : ℤ) - 1) ^ 6 := by
    nlinarith [hfactor, haux]
  have hCast : ((m : ℤ) ^ 6) < (((m - 3 : ℕ) ^ 6 + (m - 2 : ℕ) ^ 6 + (m - 1 : ℕ) ^ 6 : ℕ) : ℤ) := by
    simpa [Nat.cast_sub hm3, Nat.cast_sub hm2, Nat.cast_sub hm1, sub_eq_add_neg, add_assoc,
      add_comm] using hgtZ
  exact_mod_cast hCast

/-- Tail inequality used in the `k = 7` contradiction. -/
private theorem pow7_tail_gt {m : ℕ} (hm : 12 ≤ m) :
    m ^ 7 < (m - 4) ^ 7 + (m - 3) ^ 7 + (m - 2) ^ 7 + (m - 1) ^ 7 := by
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hmZ : (12 : ℤ) ≤ m := by exact_mod_cast hm
  have hfactor :
      ((m : ℤ) - 4) ^ 7 + ((m : ℤ) - 3) ^ 7 + ((m : ℤ) - 2) ^ 7 + ((m : ℤ) - 1) ^ 7 - (m : ℤ) ^ 7 =
        3 * ((m : ℤ) - 12) ^ 7 + 182 * ((m : ℤ) - 12) ^ 6 + 4662 * ((m : ℤ) - 12) ^ 5 +
          64540 * ((m : ℤ) - 12) ^ 4 + 509670 * ((m : ℤ) - 12) ^ 3 + 2184756 * ((m : ℤ) - 12) ^ 2 +
          4054134 * ((m : ℤ) - 12) + 535484 := by
    ring
  have h012 : 0 ≤ (m : ℤ) - 12 := by nlinarith [hmZ]
  have h7 : 0 ≤ ((m : ℤ) - 12) ^ 7 := by positivity
  have h6 : 0 ≤ ((m : ℤ) - 12) ^ 6 := by positivity
  have h5 : 0 ≤ ((m : ℤ) - 12) ^ 5 := by positivity
  have h4 : 0 ≤ ((m : ℤ) - 12) ^ 4 := by positivity
  have h3 : 0 ≤ ((m : ℤ) - 12) ^ 3 := by positivity
  have h2 : 0 ≤ ((m : ℤ) - 12) ^ 2 := by positivity
  have hlin : 0 ≤
      3 * ((m : ℤ) - 12) ^ 7 + 182 * ((m : ℤ) - 12) ^ 6 + 4662 * ((m : ℤ) - 12) ^ 5 +
        64540 * ((m : ℤ) - 12) ^ 4 + 509670 * ((m : ℤ) - 12) ^ 3 + 2184756 * ((m : ℤ) - 12) ^ 2 +
        4054134 * ((m : ℤ) - 12) := by
    nlinarith [h012, h7, h6, h5, h4, h3, h2]
  have haux : 0 <
      3 * ((m : ℤ) - 12) ^ 7 + 182 * ((m : ℤ) - 12) ^ 6 + 4662 * ((m : ℤ) - 12) ^ 5 +
        64540 * ((m : ℤ) - 12) ^ 4 + 509670 * ((m : ℤ) - 12) ^ 3 + 2184756 * ((m : ℤ) - 12) ^ 2 +
        4054134 * ((m : ℤ) - 12) + 535484 := by
    nlinarith [hlin]
  have hgtZ : (m : ℤ) ^ 7 <
      ((m : ℤ) - 4) ^ 7 + ((m : ℤ) - 3) ^ 7 + ((m : ℤ) - 2) ^ 7 + ((m : ℤ) - 1) ^ 7 := by
    nlinarith [hfactor, haux]
  have hCast : ((m : ℤ) ^ 7) <
      (((m - 4 : ℕ) ^ 7 + (m - 3 : ℕ) ^ 7 + (m - 2 : ℕ) ^ 7 + (m - 1 : ℕ) ^ 7 : ℕ) : ℤ) := by
    simpa [Nat.cast_sub hm4, Nat.cast_sub hm3, Nat.cast_sub hm2, Nat.cast_sub hm1, sub_eq_add_neg,
      add_assoc, add_comm] using hgtZ
  exact_mod_cast hCast

/-- There are no solutions to the Erdos-Moser equation with exponent `k = 4`. -/
theorem no_solution_k_four (m : ℕ) : ¬IsSolution m 4 := by
  intro hsol
  rcases hsol with ⟨_hmpos, _hkpos, hEq⟩
  by_cases hm7 : m ≤ 7
  · interval_cases m <;> norm_num [powerSum] at hEq
  · have hm8 : 8 ≤ m := by omega
    have hsubset : ({m - 3, m - 2, m - 1} : Finset ℕ) ⊆ Finset.range m := by
      intro x hx
      simp [Finset.mem_range] at hx ⊢
      omega
    have hlow_set : (∑ i ∈ ({m - 3, m - 2, m - 1} : Finset ℕ), i ^ 4) ≤ powerSum m 4 := by
      unfold powerSum
      exact Finset.sum_le_sum_of_subset (f := fun i => i ^ 4) hsubset
    have hset :
        (∑ i ∈ ({m - 3, m - 2, m - 1} : Finset ℕ), i ^ 4) =
          (m - 3) ^ 4 + (m - 2) ^ 4 + (m - 1) ^ 4 := by
      have hne12 : m - 3 ≠ m - 2 := by omega
      have hne23 : m - 2 ≠ m - 1 := by omega
      have hne13 : m - 3 ≠ m - 1 := by omega
      simp [hne12, hne23, hne13, add_comm, add_assoc]
    have hlow : (m - 3) ^ 4 + (m - 2) ^ 4 + (m - 1) ^ 4 ≤ powerSum m 4 := by
      simpa [hset] using hlow_set
    have hgt : m ^ 4 < (m - 3) ^ 4 + (m - 2) ^ 4 + (m - 1) ^ 4 := pow4_tail_gt hm8
    have hlt : m ^ 4 < powerSum m 4 := lt_of_lt_of_le hgt hlow
    have hlt' : m ^ 4 < m ^ 4 := by
      simp [hEq] at hlt
    exact (lt_irrefl _ hlt')

/-- There are no solutions to the Erdos-Moser equation with exponent `k = 5`. -/
theorem no_solution_k_five (m : ℕ) : ¬IsSolution m 5 := by
  intro hsol
  rcases hsol with ⟨_hmpos, _hkpos, hEq⟩
  by_cases hm8 : m ≤ 8
  · interval_cases m <;> norm_num [powerSum] at hEq
  · have hm9 : 9 ≤ m := by omega
    have hsubset : ({m - 4, m - 3, m - 2, m - 1} : Finset ℕ) ⊆ Finset.range m := by
      intro x hx
      simp [Finset.mem_range] at hx ⊢
      omega
    have hlow_set : (∑ i ∈ ({m - 4, m - 3, m - 2, m - 1} : Finset ℕ), i ^ 5) ≤ powerSum m 5 := by
      unfold powerSum
      exact Finset.sum_le_sum_of_subset (f := fun i => i ^ 5) hsubset
    have hset :
        (∑ i ∈ ({m - 4, m - 3, m - 2, m - 1} : Finset ℕ), i ^ 5) =
          (m - 4) ^ 5 + (m - 3) ^ 5 + (m - 2) ^ 5 + (m - 1) ^ 5 := by
      have hne12 : m - 4 ≠ m - 3 := by omega
      have hne13 : m - 4 ≠ m - 2 := by omega
      have hne14 : m - 4 ≠ m - 1 := by omega
      have hne23 : m - 3 ≠ m - 2 := by omega
      have hne24 : m - 3 ≠ m - 1 := by omega
      have hne34 : m - 2 ≠ m - 1 := by omega
      simp [hne12, hne13, hne14, hne23, hne24, hne34, add_comm, add_assoc]
    have hlow : (m - 4) ^ 5 + (m - 3) ^ 5 + (m - 2) ^ 5 + (m - 1) ^ 5 ≤ powerSum m 5 := by
      simpa [hset] using hlow_set
    have hgt : m ^ 5 < (m - 4) ^ 5 + (m - 3) ^ 5 + (m - 2) ^ 5 + (m - 1) ^ 5 := pow5_tail_gt hm9
    have hlt : m ^ 5 < powerSum m 5 := lt_of_lt_of_le hgt hlow
    have hlt' : m ^ 5 < m ^ 5 := by
      simp [hEq] at hlt
    exact (lt_irrefl _ hlt')

/-- There are no solutions to the Erdos-Moser equation with exponent `k = 6`. -/
theorem no_solution_k_six (m : ℕ) : ¬IsSolution m 6 := by
  intro hsol
  rcases hsol with ⟨_hmpos, _hkpos, hEq⟩
  by_cases hm10 : m ≤ 10
  · interval_cases m <;> norm_num [powerSum] at hEq
  · have hm11 : 11 ≤ m := by omega
    have hsubset : ({m - 3, m - 2, m - 1} : Finset ℕ) ⊆ Finset.range m := by
      intro x hx
      simp [Finset.mem_range] at hx ⊢
      omega
    have hlow_set : (∑ i ∈ ({m - 3, m - 2, m - 1} : Finset ℕ), i ^ 6) ≤ powerSum m 6 := by
      unfold powerSum
      exact Finset.sum_le_sum_of_subset (f := fun i => i ^ 6) hsubset
    have hset :
        (∑ i ∈ ({m - 3, m - 2, m - 1} : Finset ℕ), i ^ 6) =
          (m - 3) ^ 6 + (m - 2) ^ 6 + (m - 1) ^ 6 := by
      have hne12 : m - 3 ≠ m - 2 := by omega
      have hne23 : m - 2 ≠ m - 1 := by omega
      have hne13 : m - 3 ≠ m - 1 := by omega
      simp [hne12, hne23, hne13, add_comm, add_assoc]
    have hlow : (m - 3) ^ 6 + (m - 2) ^ 6 + (m - 1) ^ 6 ≤ powerSum m 6 := by
      simpa [hset] using hlow_set
    have hgt : m ^ 6 < (m - 3) ^ 6 + (m - 2) ^ 6 + (m - 1) ^ 6 := pow6_tail_gt hm11
    have hlt : m ^ 6 < powerSum m 6 := lt_of_lt_of_le hgt hlow
    have hlt' : m ^ 6 < m ^ 6 := by
      simp [hEq] at hlt
    exact (lt_irrefl _ hlt')

/-- There are no solutions to the Erdos-Moser equation with exponent `k = 7`. -/
theorem no_solution_k_seven (m : ℕ) : ¬IsSolution m 7 := by
  intro hsol
  rcases hsol with ⟨_hmpos, _hkpos, hEq⟩
  by_cases hm11 : m ≤ 11
  · interval_cases m <;> norm_num [powerSum] at hEq
  · have hm12 : 12 ≤ m := by omega
    have hsubset : ({m - 4, m - 3, m - 2, m - 1} : Finset ℕ) ⊆ Finset.range m := by
      intro x hx
      simp [Finset.mem_range] at hx ⊢
      omega
    have hlow_set : (∑ i ∈ ({m - 4, m - 3, m - 2, m - 1} : Finset ℕ), i ^ 7) ≤ powerSum m 7 := by
      unfold powerSum
      exact Finset.sum_le_sum_of_subset (f := fun i => i ^ 7) hsubset
    have hset :
        (∑ i ∈ ({m - 4, m - 3, m - 2, m - 1} : Finset ℕ), i ^ 7) =
          (m - 4) ^ 7 + (m - 3) ^ 7 + (m - 2) ^ 7 + (m - 1) ^ 7 := by
      have hne12 : m - 4 ≠ m - 3 := by omega
      have hne13 : m - 4 ≠ m - 2 := by omega
      have hne14 : m - 4 ≠ m - 1 := by omega
      have hne23 : m - 3 ≠ m - 2 := by omega
      have hne24 : m - 3 ≠ m - 1 := by omega
      have hne34 : m - 2 ≠ m - 1 := by omega
      simp [hne12, hne13, hne14, hne23, hne24, hne34, add_comm, add_assoc]
    have hlow : (m - 4) ^ 7 + (m - 3) ^ 7 + (m - 2) ^ 7 + (m - 1) ^ 7 ≤ powerSum m 7 := by
      simpa [hset] using hlow_set
    have hgt : m ^ 7 < (m - 4) ^ 7 + (m - 3) ^ 7 + (m - 2) ^ 7 + (m - 1) ^ 7 := pow7_tail_gt hm12
    have hlt : m ^ 7 < powerSum m 7 := lt_of_lt_of_le hgt hlow
    have hlt' : m ^ 7 < m ^ 7 := by
      simp [hEq] at hlt
    exact (lt_irrefl _ hlt')

/-- Combined consequence of the `k = 1,2,3` results: among `k ≤ 3`, only `(m,k)=(3,1)` works. -/
theorem no_solution_k_le_three {m k : ℕ} (hkpos : 0 < k) (hk : k ≤ 3)
    (hsol : IsSolution m k) : m = 3 ∧ k = 1 := by
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · exact ⟨(solution_k_one_iff m).mp hsol, rfl⟩
  · exact (no_solution_k_two m hsol).elim
  · exact (no_solution_k_three m hsol).elim

/-- Extended consequence: among `k ≤ 5`, only `(m,k) = (3,1)` is possible. -/
theorem no_solution_k_le_five {m k : ℕ} (hkpos : 0 < k) (hk : k ≤ 5)
    (hsol : IsSolution m k) : m = 3 ∧ k = 1 := by
  have hk_cases : k ≤ 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hk_cases with hk3 | rfl | rfl
  · exact no_solution_k_le_three hkpos hk3 hsol
  · exact (no_solution_k_four m hsol).elim
  · exact (no_solution_k_five m hsol).elim

/-- Further extension: among `k ≤ 7`, only `(m,k) = (3,1)` is possible. -/
theorem no_solution_k_le_seven {m k : ℕ} (hkpos : 0 < k) (hk : k ≤ 7)
    (hsol : IsSolution m k) : m = 3 ∧ k = 1 := by
  have hk_cases : k ≤ 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk_cases with hk5 | rfl | rfl
  · exact no_solution_k_le_five hkpos hk5 hsol
  · exact (no_solution_k_six m hsol).elim
  · exact (no_solution_k_seven m hsol).elim

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
-- `decide` here performs a large finite verification over `151 × 26` cases.
/-- Bounded exhaustive search certificate in the window `m ≤ 150`, `k ≤ 25`. -/
theorem checked_window_150_25 :
    ∀ m : Fin 151, ∀ k : Fin 26, IsSolution m.1 k.1 → m.1 = 3 ∧ k.1 = 1 := by
  decide

/-- Corollary of `checked_window_150_25` stated with ordinary natural bounds. -/
theorem bounded_certificate_150_25 {m k : ℕ} (hm : m ≤ 150) (hk : k ≤ 25)
    (hsol : IsSolution m k) : m = 3 ∧ k = 1 := by
  have hm' : m < 151 := by omega
  have hk' : k < 26 := by omega
  exact checked_window_150_25 ⟨m, hm'⟩ ⟨k, hk'⟩ hsol

end ErdosMoser
