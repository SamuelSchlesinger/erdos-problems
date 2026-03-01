/-
# Erdős-Straus: Partial results for n ≡ 1 (mod 4)

This file covers cases that handle most values of n via mod-3 analysis:
- n ≡ 2 (mod 3): use the identity 4/n = 1/((n+1)/3) + 1/n + 1/(n·(n+1)/3)
- n ≡ 0 (mod 3): use the identity 4/n = 1/(n/3) + 1/(n+1) + 1/(n(n+1)/3)

Together with the even case and the n ≡ 3 mod 4 case, this covers all n > 2
except n ≡ 1 (mod 12).
-/
import Erdos.ErdosStraus.Statement

namespace ErdosStraus

/-! ## Reduction to primes

If the conjecture holds for n, it holds for any multiple of n. -/

/-- If the Erdős-Straus conjecture holds for n, it holds for any multiple kn. -/
theorem of_multiple (n k : ℕ) (hn : 2 < n) (hk : 0 < k)
    (h : ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / (k * n) : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := h
  have hk_pos := hk
  refine ⟨k * x, k * y, k * z, by nlinarith, by nlinarith, by nlinarith, ?_⟩
  have hk_ne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hx_ne : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hy_ne : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hz_ne : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast [Nat.cast_mul]
  field_simp
  -- After field_simp, both sides should be equal as polynomials
  -- given that 4*x*y*z = n*(y*z + x*z + x*y) (from heq)
  have heq' : (4 : ℚ) * x * y * z = n * (y * z + x * z + x * y) := by
    have := heq; field_simp at this; linarith
  nlinarith [heq', mul_pos (show (0 : ℚ) < k from by positivity)
    (show (0 : ℚ) < x * y * z from by positivity)]

/-! ## The n ≡ 2 (mod 3) case

For n ≡ 2 (mod 3), set a = (n+1)/3. Then:
  1/a + 1/n + 1/(na) = (n + a + 1)/(na) = (n + (n+1)/3 + 1)/(na)
  = (3n + n + 1 + 3)/(3na) = (4n + 4)/(3na) = 4(n+1)/(3na) = 4·3a/(3na) = 4/n ✓ -/

/-- For n ≡ 2 (mod 3) with n > 2, the Erdős-Straus conjecture holds.

  Proof: Set a = (n+1)/3. Then 4/n = 1/a + 1/n + 1/(na), with a < n < na. -/
theorem mod3_eq2_case (n : ℕ) (hn : 2 < n) (hmod : n % 3 = 2) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  set a := (n + 1) / 3 with ha_def
  have h_rel : n + 1 = 3 * a := by omega
  have ha_pos : 1 ≤ a := by omega
  have ha_lt_n : a < n := by omega
  have ha_ge2 : 2 ≤ a := by omega
  refine ⟨a, n, n * a, by omega, by omega, by nlinarith, ?_⟩
  -- 1/a + 1/n + 1/(na) = 4/n
  have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ha_ne : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_rel_q : (n : ℚ) + 1 = 3 * (a : ℚ) := by exact_mod_cast h_rel
  push_cast [Nat.cast_mul]
  field_simp
  nlinarith [h_rel_q]

/-! ## The n ≡ 0 (mod 3) case

For n = 3m, we use 4/(3m) = 1/m + 1/(3m+1) + 1/(3m(3m+1)).

This works because 4/(3m) - 1/m = (4-3)/(3m) = 1/(3m), and
1/(3m) = 1/(3m+1) + 1/(3m(3m+1)). -/

/-- For n divisible by 3 with n > 2, the Erdős-Straus conjecture holds.

  Proof: Write n = 3m. Then 4/n = 1/m + 1/(3m+1) + 1/(3m(3m+1)). -/
theorem mod3_eq0_case (n : ℕ) (hn : 2 < n) (hmod : n % 3 = 0) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  set m := n / 3 with hm_def
  have h_rel : n = 3 * m := by omega
  have hm_pos : 1 ≤ m := by omega
  refine ⟨m, 3 * m + 1, 3 * m * (3 * m + 1), by omega, by omega, by nlinarith, ?_⟩
  -- 1/m + 1/(3m+1) + 1/(3m(3m+1)) = 4/(3m)
  have hm_ne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h3m_ne : (3 : ℚ) * (m : ℚ) ≠ 0 := by positivity
  have h3m1_ne : (3 : ℚ) * (m : ℚ) + 1 ≠ 0 := by positivity
  have h_rel_q : (n : ℚ) = 3 * (m : ℚ) := by exact_mod_cast h_rel
  rw [h_rel_q]
  push_cast [Nat.cast_mul, Nat.cast_add]
  field_simp
  ring

end ErdosStraus
