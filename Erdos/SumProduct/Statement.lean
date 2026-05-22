/-
# Erdos Problem 52: finite sum-product

Let `A` be a finite set of integers. Problem `#52` asks whether, for every
`epsilon > 0`, the larger of the sumset `A + A` and the product set `A * A`
has size at least a positive `epsilon`-dependent constant times
`|A|^(2 - epsilon)`.

Reference: https://www.erdosproblems.com/52
-/
import Mathlib

namespace SumProduct

/-- The two-fold sumset `A + A` of a finite set of integers. -/
def sumset (A : Finset Int) : Finset Int :=
  (A.product A).image fun p : Int × Int => p.1 + p.2

/-- The two-fold product set `A * A` of a finite set of integers. -/
def productSet (A : Finset Int) : Finset Int :=
  (A.product A).image fun p : Int × Int => p.1 * p.2

/-- The quantity appearing in the finite sum-product conjecture:
`max(|A + A|, |A * A|)`. -/
def sumProductMax (A : Finset Int) : Nat :=
  max (sumset A).card (productSet A).card

/-- Erdős problem `#52`, in epsilon-constant form over finite integer sets.

For every `epsilon` with `0 < epsilon < 1`, there should be a positive constant
depending on `epsilon` such that every finite integer set `A` satisfies
`max(|A + A|, |A * A|) >= C_epsilon |A|^(2 - epsilon)`. -/
def Erdos52Conjecture : Prop :=
  ∀ epsilon : Real, 0 < epsilon → epsilon < 1 →
    ∃ Cepsilon : Real, 0 < Cepsilon ∧
      ∀ A : Finset Int,
        Cepsilon * (A.card : Real) ^ ((2 : Real) - epsilon) ≤
          (sumProductMax A : Real)

end SumProduct
