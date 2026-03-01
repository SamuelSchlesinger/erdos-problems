/-
# Erdős Problem 302: Unit Fraction Triples

Let f(N) be the maximum size of A ⊆ {1, …, N} such that there are no distinct
a, b, c ∈ A with 1/a = 1/b + 1/c.

Known bounds:
- Lower: f(N) ≥ (5/8 + o(1))N (Cambie: odd numbers up to N/4, plus (N/2, N])
- Upper: f(N) ≤ (9/10 + o(1))N (van Doorn)

Conjecture: f(N) = (1/2 + o(1))N.

Note: the equation 1/a = 1/b + 1/c with a < b, c is equivalent to
a(b + c) = bc, i.e., a divides bc and bc/(b+c) = a. This connects
to the divisibility structure we studied in Erdős-Straus.

Reference: https://www.erdosproblems.com/302
-/
import Mathlib

namespace UnitFractionTriples

/-- Three distinct positive naturals (a, b, c) form a unit fraction triple
    if 1/a = 1/b + 1/c. -/
def IsUnitFractionTriple (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ (1 / a : ℚ) = 1 / b + 1 / c

/-- A set is unit-fraction-triple-free if it contains no distinct a, b, c
    with 1/a = 1/b + 1/c. -/
def TripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    ¬IsUnitFractionTriple a b c

/-- Divisibility characterization: for positive a, b, c with b ≠ c,
    1/a = 1/b + 1/c iff a * (b + c) = b * c. -/
theorem triple_iff_div {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (1 / a : ℚ) = 1 / b + 1 / c ↔ a * (b + c) = b * c := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · intro h
    have h' := h
    field_simp at h'
    -- h' is a ℚ identity; we need a * (b + c) = b * c in ℕ
    have hq : (a : ℚ) * (↑b + ↑c) = ↑b * ↑c := by linarith
    exact_mod_cast hq
  · intro h
    have : (a : ℚ) * (b + c) = b * c := by exact_mod_cast h
    field_simp
    linarith

/-- If 1/a = 1/b + 1/c with a, b, c positive and distinct, then a < b and a < c. -/
theorem triple_lt {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_hab : a ≠ b) (_hac : a ≠ c)
    (h : (1 / a : ℚ) = 1 / b + 1 / c) : a < b ∧ a < c := by
  rw [triple_iff_div ha hb hc] at h
  constructor <;> by_contra hle <;> push_neg at hle <;> nlinarith

end UnitFractionTriples
