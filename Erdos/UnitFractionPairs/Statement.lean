/-
# Erdős Problem 327: Unit Fraction Pairs

Let A ⊆ {1, …, N}. We say A is *unit-fraction-pair-free* if for all distinct
a, b ∈ A, the sum 1/a + 1/b is not a unit fraction — equivalently, (a + b) ∤ ab.

The odd numbers in {1, …, N} form such a set of size ⌈N/2⌉. Erdős and Graham
asked: can A be substantially larger?

Known bounds on f(N) = max |A|:
- Lower: f(N) ≥ ⌈N/2⌉ (odd numbers)
- Upper: f(N) ≤ (25/28 + o(1))N (van Doorn)

Conjecture: f(N) = (1/2 + o(1))N.

Reference: https://www.erdosproblems.com/327
-/
import Mathlib

namespace UnitFractionPairs

/-- The sum 1/a + 1/b is a unit fraction iff (a + b) ∣ ab. This is the divisibility
    formulation: a + b divides ab means there exists k with 1/a + 1/b = 1/k. -/
def IsUnitFractionPair (a b : ℕ) : Prop := (a + b) ∣ (a * b)

/-- A set of positive naturals is unit-fraction-pair-free if no two distinct
    elements form a unit fraction pair. -/
def PairFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬IsUnitFractionPair a b

/-- Algebraic equivalence: for positive a, b, the sum 1/a + 1/b is a unit fraction
    (i.e., equals 1/k for some positive k) if and only if (a + b) ∣ ab. -/
theorem unit_fraction_pair_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (∃ k : ℕ, 0 < k ∧ (1 / a + 1 / b : ℚ) = 1 / k) ↔ IsUnitFractionPair a b := by
  unfold IsUnitFractionPair
  constructor
  · rintro ⟨k, hk, heq⟩
    have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h : (k : ℚ) * (a + b) = a * b := by field_simp at heq; linarith
    have h' : k * (a + b) = a * b := by exact_mod_cast h
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    have hkpos : 0 < k := by
      by_contra h
      push_neg at h
      interval_cases k
      simp at hk; omega
    refine ⟨k, hkpos, ?_⟩
    have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h : (a : ℚ) * b = k * (a + b) := by
      have : a * b = (a + b) * k := hk
      have : (a : ℚ) * b = (a + b) * k := by exact_mod_cast this
      linarith
    field_simp
    linarith

/-- The set of odd numbers in {1, …, N} is unit-fraction-pair-free.

    Proof: if a and b are both odd, then a + b is even, so 2 ∣ (a + b).
    If (a + b) ∣ (a * b), then 2 ∣ (a * b). But a * b is odd
    (product of two odds), contradiction. -/
theorem odd_numbers_pair_free (N : ℕ) :
    PairFree ((Finset.Icc 1 N).filter fun n => n % 2 = 1) := by
  intro a ha b hb _hab hpair
  rw [Finset.mem_filter] at ha hb
  unfold IsUnitFractionPair at hpair
  obtain ⟨k, hk⟩ := hpair
  have ha_odd : ¬ 2 ∣ a := by omega
  have hb_odd : ¬ 2 ∣ b := by omega
  have hab_even : 2 ∣ a + b := by omega
  have hab_not_dvd : ¬ 2 ∣ a * b := by
    rw [Nat.Prime.dvd_mul Nat.prime_two]
    push_neg; exact ⟨ha_odd, hb_odd⟩
  exact hab_not_dvd (dvd_trans hab_even ⟨k, hk⟩)

end UnitFractionPairs
