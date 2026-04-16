import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Prod

/- 
# Erdős Problem 89: Distinct Distances in the Plane

Erdős asked whether every set of `n` distinct points in the Euclidean plane
determines at least `≫ n / sqrt(log n)` distinct distances.

We package the problem in a finite form suitable for basic counting lemmas:
given a finite set `A ⊆ ℝ²`, `distanceSet A` is the set of distances `dist p q`
with `p, q ∈ A` and `p ≠ q`, and `distanceCount A` is its cardinality.

Reference: https://www.erdosproblems.com/89
-/
namespace DistinctDistances

/-- The Euclidean plane `ℝ²`, represented as a product. -/
abbrev Plane := ℝ × ℝ

/-- The ordered pairs of distinct points of `A`. -/
noncomputable def orderedDistinctPairs (A : Finset Plane) : Finset (Plane × Plane) :=
  (A.product A).filter fun pq => pq.1 ≠ pq.2

/-- The set of distances determined by a finite point set `A ⊆ ℝ²`. -/
noncomputable def distanceSet (A : Finset Plane) : Finset ℝ :=
  (orderedDistinctPairs A).image fun pq => dist pq.1 pq.2

/-- The number of distinct distances determined by `A`. -/
noncomputable def distanceCount (A : Finset Plane) : ℕ :=
  (distanceSet A).card

/-- Finite-form packaging of the Erdős distinct distances conjecture. -/
def DistinctDistancesConjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ A : Finset Plane, 2 ≤ A.card →
      C * (A.card : ℝ) / Real.sqrt (Real.log (A.card : ℝ)) ≤ (distanceCount A : ℝ)

end DistinctDistances
