import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors

/- 
# Erdős Problem 893: Divisors of Mersenne Numbers

Let `τ(n)` denote the number of positive divisors of `n`, and define

`f(n) = ∑_{1 ≤ k ≤ n} τ(2^k - 1)`.

Erdős asked whether the doubling ratio `f(2n) / f(n)` tends to a limit.

We package the sum using a shifted range:
`mersenneDivisorSum n = ∑_{k < n} τ(2^(k+1) - 1)`, which is the same finite sum.

Reference: https://www.erdosproblems.com/893
-/
namespace MersenneDivisorSums

/-- The divisor-count term `τ(2^(k+1)-1)`. -/
def mersenneDivisorTerm (k : ℕ) : ℕ :=
  (2 ^ (k + 1) - 1).divisors.card

/-- The partial sums `f(n) = ∑_{1 ≤ k ≤ n} τ(2^k - 1)`, written as a shifted
range sum. -/
def mersenneDivisorSum (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) mersenneDivisorTerm

/-- The doubling ratio appearing in Erdős problem `#893`. -/
noncomputable def mersenneDoublingRatio (n : ℕ) : ℝ :=
  (mersenneDivisorSum (2 * n) : ℝ) / (mersenneDivisorSum n : ℝ)

/-- Tail-based packaging of convergence of the doubling ratio. -/
def DoublingRatioTendsTo (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
    ∀ ⦃n : ℕ⦄, N ≤ n → |mersenneDoublingRatio n - L| < ε

/-- Erdős's question for problem `#893`. -/
def Erdos893Conjecture : Prop :=
  ∃ L : ℝ, DoublingRatioTendsTo L

end MersenneDivisorSums
