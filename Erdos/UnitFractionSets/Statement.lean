/-
# Erdős Problem 301: Unit Fraction Sum-Free Sets

Let f(N) be the maximum size of A ⊆ {1, …, N} such that there are no
distinct a, b₁, …, bₖ ∈ A with 1/a = 1/b₁ + ⋯ + 1/bₖ.

Known bounds:
- Lower: f(N) ≥ N/2 (take A = (N/2, N] ∩ ℕ)
- Upper: f(N) ≤ (25/28 + o(1))N (van Doorn)

Conjecture: f(N) = (1/2 + o(1))N.

This generalizes Problem 302 (which restricts to k = 2).

Reference: https://www.erdosproblems.com/301
-/
import Mathlib

namespace UnitFractionSets

/-- A set is unit-fraction-sum-free if no element's reciprocal equals
    the sum of reciprocals of a nonempty subset of other elements.

    Formally: there is no a ∈ A and nonempty S ⊆ A \ {a} with
    1/a = ∑_{b ∈ S} 1/b. -/
def SumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, S.Nonempty →
    (1 / a : ℚ) ≠ ∑ b ∈ S, (1 / b : ℚ)

end UnitFractionSets
