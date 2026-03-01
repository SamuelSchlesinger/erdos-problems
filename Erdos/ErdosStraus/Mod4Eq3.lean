/-
# Erdős-Straus: The case n ≡ 3 (mod 4)

When n ≡ 3 (mod 4), set a = (n+1)/4 (an integer). Then:
  4/n = 1/a + 1/(na+1) + 1/(na(na+1))

This works because 1/(na+1) + 1/(na(na+1)) = 1/(na) (partial fractions),
so 1/a + 1/(na) = (n+1)/(na) = 4a/(na) = 4/n.
-/
import Erdos.ErdosStraus.Statement

namespace ErdosStraus

/-- The Erdős-Straus conjecture holds for all n > 2 with n ≡ 3 (mod 4).

  Proof: Let a = (n+1)/4. Then 4/n = 1/a + 1/(na+1) + 1/(na(na+1)).
  Since n ≥ 3 and a ≥ 1, the three denominators are distinct and increasing. -/
theorem mod4_eq3_case (n : ℕ) (hn : 2 < n) (hmod : n % 4 = 3) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  -- Define a = (n+1)/4
  set a := (n + 1) / 4 with ha_def
  have h_rel : n + 1 = 4 * a := by omega
  have ha_pos : 1 ≤ a := by omega
  have hna_pos : 2 ≤ n * a := by nlinarith
  -- Witnesses: x = a, y = n*a + 1, z = n*a*(n*a + 1)
  refine ⟨a, n * a + 1, n * a * (n * a + 1), by omega, by nlinarith, by nlinarith, ?_⟩
  -- Prove the identity: 4/n = 1/a + 1/(n*a+1) + 1/(n*a*(n*a+1))
  have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ha_ne : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hna_ne : (n : ℚ) * (a : ℚ) ≠ 0 := mul_ne_zero hn_ne ha_ne
  have hna1_ne : (n : ℚ) * (a : ℚ) + 1 ≠ 0 := by positivity
  -- Cast the key relation to ℚ
  have h_rel_q : (n : ℚ) + 1 = 4 * (a : ℚ) := by exact_mod_cast h_rel
  push_cast [Nat.cast_mul, Nat.cast_add]
  field_simp
  nlinarith [h_rel_q, sq_nonneg ((n : ℚ) * (a : ℚ)),
             mul_pos (show (0 : ℚ) < n from by positivity) (show (0 : ℚ) < a from by positivity)]

end ErdosStraus
