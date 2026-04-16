/- 
# Erdős Problem 802: Independent Sets in Clique-Free Graphs

Erdős asked whether every `K_r`-free graph on `n` vertices with average degree
`t` contains an independent set of size `≫_r (log t / t) n`.

We package the problem on graphs with vertex set `Fin n`, define the average
degree from the edge count, and state the conjectural lower bound with an
explicit constant depending on `r`.

Reference: https://www.erdosproblems.com/802
-/
import Mathlib

namespace CliqueFreeIndependence

open SimpleGraph

/-- The average degree of a finite graph on `Fin n`, written via the edge
count as `2|E| / n`. -/
noncomputable def averageDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ := by
  classical
  exact (Nat.cast (R := ℝ) (2 * G.edgeFinset.card)) / (Nat.cast (R := ℝ) n)

/-- The conjectured order of magnitude for the independence number in problem
`#802`. -/
noncomputable def aeksLowerBound (C t n : ℝ) : ℝ :=
  C * Real.log t / t * n

/-- Finite-form packaging of Erdős problem `#802`. We only state the bound once
the average degree is in the regime `t > 1`, so the logarithm has the intended
sign. -/
def Erdos802Conjecture : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
        G.CliqueFree r →
        1 < averageDegree G →
        aeksLowerBound C (averageDegree G) n ≤ (G.indepNum : ℝ)

end CliqueFreeIndependence
