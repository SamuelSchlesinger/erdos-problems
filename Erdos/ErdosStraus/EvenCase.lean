/-
# Erdős-Straus: The Even Case

For even n > 2, writing n = 2m with m ≥ 2, we have the identity:
  2/m = 1/m + 1/(m+1) + 1/(m(m+1))

This is because 1/(m+1) + 1/(m(m+1)) = 1/m (partial fractions).
-/
import Erdos.ErdosStraus.Statement

namespace ErdosStraus

/-- The Erdős-Straus conjecture holds for all even n > 2.

  Proof: Write n = 2m. Then 4/(2m) = 2/m = 1/m + 1/(m+1) + 1/(m(m+1)).
  Since m ≥ 2, we have 1 ≤ m < m+1 < m(m+1). -/
theorem even_case (n : ℕ) (hn : 2 < n) (heven : Even n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨m, rfl⟩ := heven
  -- n = m + m, so m ≥ 2
  have hm : 2 ≤ m := by omega
  refine ⟨m, m + 1, m * (m + 1), by omega, by omega, by nlinarith, ?_⟩
  -- 4/(m+m) = 1/m + 1/(m+1) + 1/(m*(m+1))
  have hm_ne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm1_ne : (m : ℚ) + 1 ≠ 0 := by positivity
  push_cast [Nat.cast_add, Nat.cast_mul]
  field_simp
  ring

end ErdosStraus
