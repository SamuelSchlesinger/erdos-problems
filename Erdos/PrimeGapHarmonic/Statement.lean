import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic

/- 
# Erdős Problem 950: Reciprocal Sums Over Prime Gaps

Erdős asked about the function
`f(n) = ∑_{p < n} 1 / (n - p)`, where the sum runs over primes below `n`.
He conjectured that `liminf f(n) = 1`, `limsup f(n) = ∞`, and also asked
whether `f(n) = o(log log n)`.

We package the problem using the finite prime set `primesBelow n` and the real
sum `gapReciprocalSum n`.

Reference: https://www.erdosproblems.com/950
-/
namespace PrimeGapHarmonic

/-- The primes below `n`. -/
def primesBelow (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter Nat.Prime

/-- The reciprocal prime-gap sum `f(n) = ∑_{p<n} 1 / (n-p)`. -/
noncomputable def gapReciprocalSum (n : ℕ) : ℝ :=
  Finset.sum (primesBelow n) fun p => 1 / ((n - p : ℕ) : ℝ)

/-- A direct tail-based packaging of `liminf f(n) = L`. -/
def LiminfAtTopEq (f : ℕ → ℝ) (L : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n → L - ε < f n) ∧
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ f n < L + ε

/-- A direct tail-based packaging of `limsup f(n) = ∞`. -/
def LimsupAtTopEqTop (f : ℕ → ℝ) : Prop :=
  ∀ R : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ R < f n

/-- Tail-based `f(n) = o(log log n)` packaging, stated only once `log log n`
is safely in its large-`n` regime. -/
def EventuallyLittleOLogLog (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧
    ∀ ⦃n : ℕ⦄, N ≤ n → f n ≤ ε * Real.log (Real.log n)

/-- The full package of Erdős's questions for problem `#950`. -/
def Erdos950Conjecture : Prop :=
  LiminfAtTopEq gapReciprocalSum 1 ∧
    LimsupAtTopEqTop gapReciprocalSum ∧
    EventuallyLittleOLogLog gapReciprocalSum

end PrimeGapHarmonic
