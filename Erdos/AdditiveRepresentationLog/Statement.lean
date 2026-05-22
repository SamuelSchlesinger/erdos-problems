import Mathlib

/-
# Erdős Problem 66: Additive Representation Counts and a Logarithmic Limit

Erdős asked whether there is a set `A ⊆ ℕ` for which the additive convolution
count `(1_A * 1_A)(n)`, normalized by `log n`, tends to a nonzero finite limit.

We count ordered pairs `(a, b)` with `a, b ∈ A` and `a + b = n`. The count is
finite even for infinite `A`, because every such pair has both coordinates at
most `n`.

Reference: https://www.erdosproblems.com/66
-/
namespace AdditiveRepresentationLog

/-- The finite set of ordered pairs from `A` that sum to `n`.

Although `A` may be infinite, any pair with `a + b = n` has `a, b ≤ n`, so it
is enough to search inside `Finset.range (n + 1)`. -/
noncomputable def sumRepPairs (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    fun ab => ab.1 ∈ A ∧ ab.2 ∈ A ∧ ab.1 + ab.2 = n

/-- The ordered additive representation count `(1_A * 1_A)(n)`. -/
noncomputable def sumRep (A : Set ℕ) (n : ℕ) : ℕ :=
  (sumRepPairs A n).card

/-- The normalized representation-count sequence from problem `#66`. -/
noncomputable def logRepresentationRatio (A : Set ℕ) (n : ℕ) : ℝ :=
  (sumRep A n : ℝ) / Real.log (n : ℝ)

/-- `A` has a nonzero logarithmic representation limit when
`sumRep A n / log n` tends to some real number different from `0`. -/
def HasNonzeroLogRepresentationLimit (A : Set ℕ) : Prop :=
  ∃ L : ℝ, L ≠ 0 ∧
    Filter.Tendsto (logRepresentationRatio A) Filter.atTop (nhds L)

/-- Erdős problem `#66`: does some set of natural numbers have a nonzero
limit for `(1_A * 1_A)(n) / log n`? -/
def Erdos66Conjecture : Prop :=
  ∃ A : Set ℕ, HasNonzeroLogRepresentationLimit A

end AdditiveRepresentationLog
