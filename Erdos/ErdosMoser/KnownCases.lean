/-
# Erdos-Moser Equation: Known Territory

This file pushes the formalization beyond the bare statement:

1. `k = 1` is solved exactly: `IsSolution m 1 ↔ m = 3`.
2. There are no solutions with `k = 2`.
3. There are no solutions with `k = 3`.
4. A bounded exhaustive certificate checks `(m, k)` up to `(150, 25)`.
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

/-- Combined consequence of the `k = 1,2,3` results: among `k ≤ 3`, only `(m,k)=(3,1)` works. -/
theorem no_solution_k_le_three {m k : ℕ} (hkpos : 0 < k) (hk : k ≤ 3)
    (hsol : IsSolution m k) : m = 3 ∧ k = 1 := by
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · exact ⟨(solution_k_one_iff m).mp hsol, rfl⟩
  · exact (no_solution_k_two m hsol).elim
  · exact (no_solution_k_three m hsol).elim

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
