import Mathlib

/-!
# Erdős–Szekeres cups and caps (the "happy ending" bound)

A finite sequence of points in the plane (in general position, distinct `x`-coordinates) contains
a **`k`-cup** (a convex chain of `k` points — consecutive slopes strictly increasing) or an
**`l`-cap** (a concave chain — consecutive slopes strictly decreasing) as soon as it has more than
`binom(k+l-4, k-2)` points. This is the Erdős–Szekeres (1935) cups-and-caps theorem, the
combinatorial heart of the "happy ending" problem (`ES(n) ≤ binom(2n-4, n-2) + 1`).

We model a cup/cap as a *list* of points sorted by `x`-coordinate with the slope condition on
consecutive triples; extending a cup by one point on the right is then a single slope check.

Reference: P. Erdős, G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935).
https://www.erdosproblems.com (happy-ending / convex-polygon circle)
-/

namespace CupsCaps

/-- The slope of the segment from `p` to `q`. -/
noncomputable def slope (p q : ℝ × ℝ) : ℝ := (q.2 - p.2) / (q.1 - p.1)

/-- `IsCup l`: the list `l` of points is strictly increasing in `x` and its consecutive slopes are
strictly increasing (a convex chain). -/
def IsCup : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | [p, q] => p.1 < q.1
  | p :: q :: r :: l => p.1 < q.1 ∧ slope p q < slope q r ∧ IsCup (q :: r :: l)

/-- `IsCap l`: the list `l` is strictly increasing in `x` with strictly decreasing consecutive
slopes (a concave chain). -/
def IsCap : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | [p, q] => p.1 < q.1
  | p :: q :: r :: l => p.1 < q.1 ∧ slope q r < slope p q ∧ IsCap (q :: r :: l)

/-- A finite point set is in **general position**: distinct `x`-coordinates, and no three points
with one slope equal to the next (no three collinear in the relevant sense). -/
def GenPos (s : Finset (ℝ × ℝ)) : Prop :=
  (∀ p ∈ s, ∀ q ∈ s, p.1 = q.1 → p = q) ∧
  (∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, p.1 < q.1 → q.1 < r.1 → slope p q ≠ slope q r)

/-- `s` contains a `k`-cup: a cup-list of length `k` all of whose points lie in `s`. -/
def HasCup (s : Finset (ℝ × ℝ)) (k : ℕ) : Prop :=
  ∃ l : List (ℝ × ℝ), IsCup l ∧ l.length = k ∧ ∀ p ∈ l, p ∈ s

/-- `s` contains an `l`-cap. -/
def HasCap (s : Finset (ℝ × ℝ)) (k : ℕ) : Prop :=
  ∃ l : List (ℝ × ℝ), IsCap l ∧ l.length = k ∧ ∀ p ∈ l, p ∈ s

end CupsCaps
