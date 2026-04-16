/- 
# Erdős Problem 313: Primary Pseudoperfect Numbers

Erdős asked whether there are infinitely many integers `m ≥ 2` of the form

`1 / p₁ + ... + 1 / p_k = 1 - 1 / m`

with `p₁ < ... < p_k` distinct primes. Such integers are known as
primary pseudoperfect numbers.

Reference: https://www.erdosproblems.com/313
-/
import Mathlib

namespace PrimaryPseudoperfect

open scoped BigOperators

/-- A finite set of distinct primes witnessing the primary pseudoperfect
equation for `m`. -/
def PrimeReciprocalWitness (m : ℕ) (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, Nat.Prime p) ∧
    (∏ p ∈ P, p) = m ∧
    (∑ p ∈ P, (1 / (p : ℚ))) = 1 - 1 / (m : ℚ)

/-- `m` is primary pseudoperfect if it has a prime-reciprocal witness and
`m ≥ 2`. -/
def IsPrimaryPseudoperfect (m : ℕ) : Prop :=
  2 ≤ m ∧ ∃ P : Finset ℕ, PrimeReciprocalWitness m P

/-- Erdős problem #313 asks whether there are infinitely many primary
pseudoperfect numbers. -/
def InfinitelyManyPrimaryPseudoperfect : Prop :=
  ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ IsPrimaryPseudoperfect m

end PrimaryPseudoperfect
