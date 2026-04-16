import Erdos.DistinctDistances.Statement

/- 
# Elementary Facts About Distinct Distances

This file records the basic formal infrastructure for problem `#89`. We prove
membership characterizations, monotonicity under enlarging the point set,
vanishing for sets of size at most one, positivity for sets with at least two
points, and the trivial quadratic upper bound.
-/
namespace DistinctDistances

@[simp] theorem mem_orderedDistinctPairs {A : Finset Plane} {p q : Plane} :
    (p, q) ∈ orderedDistinctPairs A ↔ p ∈ A ∧ q ∈ A ∧ p ≠ q := by
  simp [orderedDistinctPairs, and_assoc]

@[simp] theorem mem_distanceSet {A : Finset Plane} {d : ℝ} :
    d ∈ distanceSet A ↔ ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ dist p q = d := by
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pq, hpq, hpqd⟩
    rcases pq with ⟨p, q⟩
    have hpq' : p ∈ A ∧ q ∈ A ∧ p ≠ q := by
      simpa using hpq
    exact ⟨p, hpq'.1, q, hpq'.2.1, hpq'.2.2, hpqd⟩
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    exact Finset.mem_image.mpr ⟨(p, q), by simp [hp, hq, hpq], rfl⟩

/-- Enlarging the point set cannot remove previously occurring distances. -/
theorem distanceSet_mono {A B : Finset Plane} (hAB : A ⊆ B) :
    distanceSet A ⊆ distanceSet B := by
  intro d hd
  rcases mem_distanceSet.mp hd with ⟨p, hp, q, hq, hpq, hdist⟩
  exact mem_distanceSet.mpr ⟨p, hAB hp, q, hAB hq, hpq, hdist⟩

/-- Consequently the number of distinct distances is monotone under inclusion. -/
theorem distanceCount_le_of_subset {A B : Finset Plane} (hAB : A ⊆ B) :
    distanceCount A ≤ distanceCount B := by
  exact Finset.card_le_card (distanceSet_mono hAB)

/-- A finite point set with at most one point determines no distances. -/
theorem distanceSet_eq_empty_of_card_le_one {A : Finset Plane} (hA : A.card ≤ 1) :
    distanceSet A = ∅ := by
  ext d
  constructor
  · intro hd
    rcases mem_distanceSet.mp hd with ⟨p, hp, q, hq, hpq, _⟩
    exact (hpq ((Finset.card_le_one_iff.mp hA) hp hq)).elim
  · simp

/-- Therefore a finite point set with at most one point has zero distinct
distances. -/
theorem distanceCount_eq_zero_of_card_le_one {A : Finset Plane} (hA : A.card ≤ 1) :
    distanceCount A = 0 := by
  simp [distanceCount, distanceSet_eq_empty_of_card_le_one hA]

/-- A finite point set with at least two points determines at least one
distance. -/
theorem distanceSet_nonempty_of_one_lt_card {A : Finset Plane} (hA : 1 < A.card) :
    (distanceSet A).Nonempty := by
  rcases Finset.one_lt_card.mp hA with ⟨p, hp, q, hq, hpq⟩
  exact ⟨dist p q, mem_distanceSet.mpr ⟨p, hp, q, hq, hpq, rfl⟩⟩

/-- Therefore a finite point set with at least two points has positive distinct
distance count. -/
theorem distanceCount_pos_of_one_lt_card {A : Finset Plane} (hA : 1 < A.card) :
    0 < distanceCount A := by
  exact Finset.card_pos.mpr (distanceSet_nonempty_of_one_lt_card hA)

/-- In the natural `2 ≤ |A|` range, the distinct-distance count is at least
one. -/
theorem one_le_distanceCount_of_two_le_card {A : Finset Plane} (hA : 2 ≤ A.card) :
    1 ≤ distanceCount A := by
  exact distanceCount_pos_of_one_lt_card (lt_of_lt_of_le (by decide : 1 < 2) hA)

/-- Trivial quadratic upper bound: there are at most `|A|²` ordered distinct
pairs, so there are at most `|A|²` distinct distances. -/
theorem distanceCount_le_sq (A : Finset Plane) :
    distanceCount A ≤ A.card ^ 2 := by
  unfold distanceCount distanceSet orderedDistinctPairs
  calc
    (((A.product A).filter fun pq => pq.1 ≠ pq.2).image fun pq => dist pq.1 pq.2).card ≤
        ((A.product A).filter fun pq => pq.1 ≠ pq.2).card := Finset.card_image_le
    _ ≤ (A.product A).card := Finset.card_filter_le _ _
    _ = A.card * A.card := Finset.card_product _ _
    _ = A.card ^ 2 := by rw [pow_two]

end DistinctDistances
