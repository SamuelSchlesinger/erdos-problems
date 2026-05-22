/-
# Erdős Problem 82: Regular Induced Subgraphs

Let `F(n)` be maximal such that every graph on `n` vertices contains a regular
induced subgraph on at least `F(n)` vertices. Erdős asked whether
`F(n) / log n` tends to infinity.

We model an induced subgraph on a finite vertex set `s` by counting, for each
vertex `v ∈ s`, the neighbors of `v` that also lie in `s`. The set `s` is a
regular induced subgraph when these induced degrees are all equal.

Reference: https://www.erdosproblems.com/82
-/
import Mathlib

namespace RegularInducedSubgraphs

open Filter
open SimpleGraph

variable {α : Type*}

/-- The degree of `v` in the subgraph of `G` induced on the finite set `s`.

Vertices outside `s` can be evaluated too, but the regularity predicate below
only compares this quantity for vertices lying in `s`. -/
noncomputable def inducedDegree (G : SimpleGraph α) (s : Finset α) (v : α) : ℕ := by
  classical
  exact (s.filter fun w => G.Adj v w).card

/-- A finite vertex set witnesses a regular induced subgraph when all selected
vertices have the same number of selected neighbors. -/
def IsRegularOn (G : SimpleGraph α) (s : Finset α) : Prop :=
  ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → inducedDegree G s u = inducedDegree G s v

/-- The graph `G` contains a regular induced subgraph on at least `k` vertices. -/
def HasRegularInducedSubgraph (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∃ s : Finset α, k ≤ s.card ∧ IsRegularOn G s

/-- The finite forcing predicate for Erdős problem `#82`: every graph on `n`
vertices has a regular induced subgraph on at least `k` vertices. -/
def ForcesRegularInducedSubgraph (n k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), HasRegularInducedSubgraph G k

/-- The extremal value `F(n)`: the largest `k ≤ n` forced in every graph on
`n` vertices. If no positive `k` is forced, this returns `0`. -/
noncomputable def FValue (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (ForcesRegularInducedSubgraph n) n

/-- Erdős problem `#82`, in the `F(n)` formulation. -/
def Erdos82Conjecture : Prop :=
  Tendsto (fun n : ℕ => (FValue n : ℝ) / Real.log (n : ℝ)) atTop atTop

end RegularInducedSubgraphs
