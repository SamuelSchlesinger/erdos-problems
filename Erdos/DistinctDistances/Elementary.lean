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

/-! ### One-point lower bound

For any chosen `p ∈ A`, the multiset of distances from `p` to the other points of
`A` injects into the global distance set: each `dist p q` is itself a distance
realised by the ordered pair `(p, q)`. Hence the number of *distinct* such radial
distances is a lower bound for `distanceCount A`. This is the workhorse we use to
obtain a linear bound in the collinear / one-dimensional case below.
-/

/-- The finite set of distances from a fixed point `p` to the other points of
`A`. -/
noncomputable def distancesFromPoint (p : Plane) (A : Finset Plane) : Finset ℝ :=
  (A.erase p).image (fun q => dist p q)

/-- The radial distances from any chosen point sit inside the full distance set. -/
theorem distancesFromPoint_subset (A : Finset Plane) {p : Plane} (hp : p ∈ A) :
    distancesFromPoint p A ⊆ distanceSet A := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨q, hq, hqd⟩
  have hq' : q ∈ A ∧ q ≠ p := by
    refine ⟨?_, ?_⟩
    · exact (Finset.mem_erase.mp hq).2
    · exact (Finset.mem_erase.mp hq).1
  exact mem_distanceSet.mpr ⟨p, hp, q, hq'.1, (Ne.symm hq'.2), hqd⟩

/-- **One-point lower bound.** For any `p ∈ A`, the number of distinct distances
from `p` to the other points of `A` lower-bounds `distanceCount A`. -/
theorem distanceCount_ge_card_distancesFromPoint
    (A : Finset Plane) {p : Plane} (hp : p ∈ A) :
    (distancesFromPoint p A).card ≤ distanceCount A := by
  exact Finset.card_le_card (distancesFromPoint_subset A hp)

/-- **Conditional linear bound.** If there is some `p ∈ A` from which all
radial distances to the other points of `A` are pairwise distinct, then
`distanceCount A ≥ |A| - 1`. The injectivity hypothesis can be checked, for
instance, when `A` is contained in a line through `p`. -/
theorem distanceCount_ge_card_sub_one_of_inj
    (A : Finset Plane) {p : Plane} (hp : p ∈ A)
    (hinj : Set.InjOn (fun q => dist p q) (A.erase p : Set Plane)) :
    A.card - 1 ≤ distanceCount A := by
  have hcard : (distancesFromPoint p A).card = (A.erase p).card := by
    unfold distancesFromPoint
    exact Finset.card_image_of_injOn hinj
  have herase : (A.erase p).card = A.card - 1 := Finset.card_erase_of_mem hp
  have hbound : (distancesFromPoint p A).card ≤ distanceCount A :=
    distanceCount_ge_card_distancesFromPoint A hp
  rw [hcard, herase] at hbound
  exact hbound

/-! ### Linear bound for collinear configurations on a horizontal line

The product metric on `ℝ × ℝ` (used here by `Plane`) is the `L∞` metric:
`dist (a, b) (c, d) = max (|a - c|) (|b - d|)`. For points all sharing the same
second coordinate `c`, this collapses to `|a - c|` on the first coordinate.

Taking `p ∈ A` to be the point of minimum first coordinate, the map
`q ↦ dist p q = q.1 - p.1` is then *injective* on `A \ {p}`, and the conditional
linear bound above unlocks `distanceCount A ≥ |A| - 1`. This is the classical
"sort along the line and read off `n − 1` increasing gaps" argument.
-/

/-- A `Finset` of `Plane` points is contained in the horizontal line `y = c`. -/
def OnHorizontalLine (A : Finset Plane) (c : ℝ) : Prop :=
  ∀ p ∈ A, p.2 = c

/-- For two points on the same horizontal line, the `L∞` distance equals the
absolute difference of their first coordinates. -/
lemma dist_eq_of_onLine {p q : Plane} {c : ℝ} (hp : p.2 = c) (hq : q.2 = c) :
    dist p q = |p.1 - q.1| := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hp, hq, sub_self, abs_zero,
    max_eq_left (abs_nonneg _)]

/-- The radial distance map from a leftmost point of a horizontal configuration is
injective on the other points. -/
lemma injOn_distFrom_leftmost
    {A : Finset Plane} {c : ℝ} (hA : OnHorizontalLine A c)
    {p : Plane} (hp : p ∈ A) (hmin : ∀ q ∈ A, p.1 ≤ q.1) :
    Set.InjOn (fun q => dist p q) (A.erase p : Set Plane) := by
  intro q₁ hq₁ q₂ hq₂ hdist
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe,
    Set.mem_singleton_iff] at hq₁ hq₂
  have hp' : p.2 = c := hA p hp
  have hq₁' : q₁.2 = c := hA q₁ hq₁.1
  have hq₂' : q₂.2 = c := hA q₂ hq₂.1
  have hmin₁ : p.1 ≤ q₁.1 := hmin q₁ hq₁.1
  have hmin₂ : p.1 ≤ q₂.1 := hmin q₂ hq₂.1
  -- Compute both sides via `dist_eq_of_onLine`.
  have h1 : dist p q₁ = q₁.1 - p.1 := by
    rw [dist_eq_of_onLine hp' hq₁', abs_of_nonpos (by linarith), neg_sub]
  have h2 : dist p q₂ = q₂.1 - p.1 := by
    rw [dist_eq_of_onLine hp' hq₂', abs_of_nonpos (by linarith), neg_sub]
  -- Hence `q₁.1 = q₂.1`. Combined with `q₁.2 = q₂.2 = c`, we get `q₁ = q₂`.
  have hx : q₁.1 = q₂.1 := by
    have := hdist
    simp only at this
    rw [h1, h2] at this
    linarith
  have hy : q₁.2 = q₂.2 := by rw [hq₁', hq₂']
  exact Prod.ext hx hy

/-- A nonempty finset of reals has a minimum element. -/
private lemma exists_min_fst (A : Finset Plane) (hA : A.Nonempty) :
    ∃ p ∈ A, ∀ q ∈ A, p.1 ≤ q.1 := by
  classical
  -- Use `Finset.exists_min_image` on `(·).1 : Plane → ℝ`.
  rcases A.exists_min_image (fun p => p.1) hA with ⟨p, hp, hpmin⟩
  exact ⟨p, hp, hpmin⟩

/-- **Linear bound for collinear configurations** (horizontal line). If
`A ⊆ ℝ²` lies on a single horizontal line, then `distanceCount A ≥ |A| − 1`. -/
theorem distanceCount_ge_card_sub_one_of_onHorizontalLine
    {A : Finset Plane} {c : ℝ} (hA : OnHorizontalLine A c) (hcard : 1 ≤ A.card) :
    A.card - 1 ≤ distanceCount A := by
  -- Pick a leftmost point.
  have hne : A.Nonempty := Finset.card_pos.mp hcard
  rcases exists_min_fst A hne with ⟨p, hp, hpmin⟩
  exact distanceCount_ge_card_sub_one_of_inj A hp
    (injOn_distFrom_leftmost hA hp hpmin)

end DistinctDistances
