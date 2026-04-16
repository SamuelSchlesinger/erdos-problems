/- 
# Elementary Cubic Bound for Obstruction-Covered Sidon Sets

If a Sidon set `A ⊆ {1, ..., N}` has the property that every outside point is
captured by one of the elementary obstruction families

- midpoint candidates `(a + b) / 2`, or
- sum-difference candidates `a + b - c`,

then the interval `{1, ..., N}` is covered by `A` together with at most
`|A|^2 + |A|^3` further candidates. This gives the coarse bound

`N ≤ |A| + |A|^2 + |A|^3`.

This is the standard easy counting heuristic behind the lower bound
`|A| ≫ N^{1/3}` for maximal Sidon sets.
-/
import Erdos.MaximalSidonSets.Statement

namespace MaximalSidonSets

/-- There are at most `|A|^2` midpoint candidates. -/
theorem card_midpointCandidates_le (A : Finset ℕ) :
    (midpointCandidates A).card ≤ A.card ^ 2 := by
  calc
    (midpointCandidates A).card ≤ (A.product A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product _ _
    _ = A.card ^ 2 := by rw [pow_two]

/-- There are at most `|A|^3` sum-difference candidates. -/
theorem card_sumDiffCandidates_le (A : Finset ℕ) :
    (sumDiffCandidates A).card ≤ A.card ^ 3 := by
  calc
    (sumDiffCandidates A).card ≤ ((A.product A).product A).card := Finset.card_image_le
    _ = (A.product A).card * A.card := Finset.card_product _ _
    _ = (A.card * A.card) * A.card := by simp [Finset.card_product]
    _ = A.card ^ 3 := by
      rw [pow_succ, pow_two]

/-- The obstruction-cover hypothesis places every point of `{1, ..., N}` into
the union of `A` with the elementary candidate sets. -/
theorem ground_subset_allCandidates {A : Finset ℕ} {N : ℕ}
    (hcover : ObstructionCoveredInInterval A N) :
    ground N ⊆ allCandidates A := by
  intro x hx
  by_cases hxa : x ∈ A
  · exact (mem_allCandidates).mpr <| Or.inl hxa
  · exact (mem_allCandidates).mpr <| Or.inr <| Finset.mem_union.mp (hcover.2 hx hxa)

/-- Coarse cardinality bound for the combined candidate family. -/
theorem card_allCandidates_le (A : Finset ℕ) :
    (allCandidates A).card ≤
      A.card + (midpointCandidates A).card + (sumDiffCandidates A).card := by
  calc
    (allCandidates A).card
      ≤ (A ∪ midpointCandidates A).card + (sumDiffCandidates A).card := by
          simpa [allCandidates] using
            Finset.card_union_le (A ∪ midpointCandidates A) (sumDiffCandidates A)
    _ ≤ (A.card + (midpointCandidates A).card) + (sumDiffCandidates A).card := by
          gcongr
          exact Finset.card_union_le A (midpointCandidates A)
    _ = A.card + (midpointCandidates A).card + (sumDiffCandidates A).card := by omega

/-- The easy cubic counting inequality behind the lower bound
`|A| ≫ N^{1/3}`. -/
theorem cubic_counting_bound_of_obstructionCover {A : Finset ℕ} {N : ℕ}
    (hcover : ObstructionCoveredInInterval A N) :
    N ≤ A.card + A.card ^ 2 + A.card ^ 3 := by
  have hground :
      (ground N).card ≤ (allCandidates A).card :=
    Finset.card_le_card (ground_subset_allCandidates hcover)
  have hmid : (midpointCandidates A).card ≤ A.card ^ 2 :=
    card_midpointCandidates_le A
  have hsum : (sumDiffCandidates A).card ≤ A.card ^ 3 :=
    card_sumDiffCandidates_le A
  calc
    N = (ground N).card := by simp [ground]
    _ ≤ (allCandidates A).card := hground
    _ ≤ A.card + (midpointCandidates A).card + (sumDiffCandidates A).card :=
      card_allCandidates_le A
    _ ≤ A.card + A.card ^ 2 + A.card ^ 3 := by omega

end MaximalSidonSets
