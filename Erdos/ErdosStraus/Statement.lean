/-
# Erdős Problem 242: The Erdős-Straus Conjecture

For every integer n > 2, there exist distinct positive integers 1 ≤ x < y < z
such that 4/n = 1/x + 1/y + 1/z.

Reference: https://www.erdosproblems.com/242
-/
import Mathlib

namespace ErdosStraus

/-- The Erdős-Straus conjecture: for every n > 2, the fraction 4/n can be written
    as a sum of three distinct unit fractions. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 < n →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

/-- A witness for the Erdős-Straus conjecture at a given n: three distinct positive
    integers whose reciprocals sum to 4/n. -/
structure Witness (n : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  hx : 1 ≤ x
  hxy : x < y
  hyz : y < z
  heq : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

/-- The conjecture holds at n if and only if there exists a witness. -/
theorem conjecture_iff_witness :
    Conjecture ↔ ∀ n : ℕ, 2 < n → Nonempty (Witness n) := by
  constructor
  · intro h n hn
    obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := h n hn
    exact ⟨⟨x, y, z, hx, hxy, hyz, heq⟩⟩
  · intro h n hn
    obtain ⟨w⟩ := h n hn
    exact ⟨w.x, w.y, w.z, w.hx, w.hxy, w.hyz, w.heq⟩

end ErdosStraus
