/- 
# Erdős Problem 85: Minimum Degree Forcing a Four-Cycle

For `n ≥ 4`, let `f(n)` be the least integer such that every graph on `n`
vertices with minimum degree at least `f(n)` contains a copy of `C₄`. Erdős
asked whether `f(n + 1) ≥ f(n)` for all sufficiently large `n`.

We work with graphs on the labelled vertex set `Fin n`. A `C4Witness` is a
labelled cyclic ordering of four distinct vertices with the four cycle edges.
The forcing threshold is packaged through the predicate `ForceC4 n d`, saying
that minimum degree at least `d` forces such a witness.

Reference: https://www.erdosproblems.com/85
-/
import Mathlib

namespace C4MinDegree

open SimpleGraph

noncomputable section

/-- A labelled witness for a copy of `C₄` in a graph on `Fin n`.

The four vertices are stored in cyclic order. We require all six pairwise
inequalities, not merely adjacent inequalities, so that the witness is a genuine
four-cycle rather than a closed walk with repeated vertices. -/
structure C4Witness {n : ℕ} (G : SimpleGraph (Fin n)) where
  v0 : Fin n
  v1 : Fin n
  v2 : Fin n
  v3 : Fin n
  distinct :
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3
  edge01 : G.Adj v0 v1
  edge12 : G.Adj v1 v2
  edge23 : G.Adj v2 v3
  edge30 : G.Adj v3 v0

/-- A graph contains a `C₄` if it has a labelled four-cycle witness. -/
def HasC4 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  Nonempty (C4Witness G)

/-- The minimum degree of a graph on `Fin n` is at least `d`.

We spell this directly with `neighborFinset.card`: each vertex has at least `d`
neighbours. -/
def MinDegreeAtLeast {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : Prop := by
  classical
  exact ∀ v : Fin n, d ≤ (G.neighborFinset v).card

/-- `ForceC4 n d` says that degree threshold `d` forces a four-cycle in every
graph on `n` labelled vertices. -/
def ForceC4 (n d : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), MinDegreeAtLeast G d → HasC4 G

/-- The extremal threshold `f(n)` from Erdős problem `#85`, defined as the least
degree threshold that forces a `C₄` on `n` vertices. The definition is meaningful
for all `n`; the problem statement starts at `n ≥ 4`. -/
def forceC4Threshold (n : ℕ) : ℕ :=
  sInf {d : ℕ | ForceC4 n d}

/-- Erdős problem `#85`: the minimum-degree threshold forcing a `C₄` is
eventually monotone nondecreasing. -/
def Erdos85Conjecture : Prop :=
  ∃ N : ℕ, 4 ≤ N ∧
    ∀ n : ℕ, N ≤ n → forceC4Threshold n ≤ forceC4Threshold (n + 1)

end

end C4MinDegree
