/-
# Erdős Problem 12: Divisibility-Avoiding Sets

Let `A` be an infinite set of positive integers such that there are no distinct
`a, b, c ∈ A` with `a ∣ b + c` and `b, c > a`.

The problem asks three size questions for such sets: whether square-root
growth is possible, whether a uniform power saving occurs infinitely often, and
whether every such set has convergent reciprocal sum.

Reference: https://www.erdosproblems.com/12
-/
import Mathlib

namespace DivisibilityAvoidingSets

/-- `PositiveSet A` means that `A` is a set of positive natural numbers. We keep
the ambient type `ℕ`, since the counting functions in the problem are naturally
phrased as intersections with `{1, ..., N}`. -/
def PositiveSet (A : Set ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄, n ∈ A → 0 < n

/-- A forbidden triple for Erdős problem `#12`: distinct `a, b, c ∈ A` with
`a ∣ b + c` and both larger entries above `a`. -/
def ForbiddenTriple (A : Set ℕ) (a b c : ℕ) : Prop :=
  a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    a ∣ b + c ∧ a < b ∧ a < c

/-- A set avoids the divisibility pattern from Erdős problem `#12`. -/
def AvoidingSet (A : Set ℕ) : Prop :=
  ∀ ⦃a b c : ℕ⦄, ForbiddenTriple A a b c → False

/-- The counting function `|A ∩ {1, ..., N}|`. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter fun n => n ∈ A).card

/-- A tail-based packaging of
`liminf |A ∩ {1, ..., N}| / sqrt N > 0`. -/
def HasPositiveSqrtLiminf (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ ⦃N : ℕ⦄, N₀ ≤ N →
      c ≤ (countUpTo A N : ℝ) / Real.sqrt (N : ℝ)

/-- The first density question in Erdős problem `#12`: existence of an infinite
avoiding set with positive square-root lower density. -/
def Erdos12PositiveSqrtDensityQuestion : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ PositiveSet A ∧ AvoidingSet A ∧
    HasPositiveSqrtLiminf A

/-- The finite-count power saving appearing in the second question of Erdős
problem `#12`: for a fixed exponent saving `c`, the count is below
`N^(1-c)` for infinitely many cutoffs `N`. -/
def HasPowerSavingInfinitelyOften (A : Set ℕ) (c : ℝ) : Prop :=
  {N : ℕ | (countUpTo A N : ℝ) < (N : ℝ) ^ (1 - c)}.Infinite

/-- The second density question in Erdős problem `#12`: is there an absolute
constant `c > 0` forcing the count of every avoiding set below `N^(1-c)` for
infinitely many `N`? -/
def Erdos12PowerSavingQuestion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A : Set ℕ, A.Infinite → PositiveSet A → AvoidingSet A →
    HasPowerSavingInfinitelyOften A c

/-- The reciprocal sum over a set of natural numbers, expressed as summability
over the subtype of its members. -/
def ReciprocalSummable (A : Set ℕ) : Prop :=
  Summable fun n : A => (1 : ℝ) / (n : ℕ)

/-- The summability form of Erdős problem `#12`: every infinite positive
avoiding set should have convergent reciprocal sum. -/
def Erdos12SummabilityQuestion : Prop :=
  ∀ A : Set ℕ, A.Infinite → PositiveSet A → AvoidingSet A →
    ReciprocalSummable A

end DivisibilityAvoidingSets
