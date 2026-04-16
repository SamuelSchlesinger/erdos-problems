import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Countable
/-
# Erdős Problem 474: Pair-Colorings of the Plane on Uncountable Sets

Erdős asked whether there is a symmetric `3`-coloring of unordered pairs of
points in `ℝ²` such that every uncountable subset of the plane contains a pair
of each color.

We package the problem in a slightly more general form: `PlanePairColoringStatement k`
asks for such a coloring with `k` colors. The original problem is the case `k = 3`.

Reference: https://www.erdosproblems.com/474
-/
namespace PlanePairColorings

/-- The ambient plane `ℝ²`. -/
abbrev Plane := ℝ × ℝ

/-- A `k`-coloring of ordered pairs of plane points. The actual Erdős problem
uses symmetric colorings, so order is irrelevant after imposing symmetry. -/
abbrev PairColoring (k : ℕ) := Plane → Plane → Fin k

/-- Symmetry of a pair-coloring. -/
def IsSymmetricColoring {k : ℕ} (c : PairColoring k) : Prop :=
  ∀ x y, c x y = c y x

/-- A color `i` appears on a distinct pair from `A`. -/
def HasColorOn {k : ℕ} (c : PairColoring k) (A : Set Plane) (i : Fin k) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ c x y = i

/-- Every color appears on some distinct pair from `A`. -/
def HitsAllColorsOn {k : ℕ} (c : PairColoring k) (A : Set Plane) : Prop :=
  ∀ i : Fin k, HasColorOn c A i

/-- Existence of a symmetric `k`-coloring of plane pairs such that every
uncountable subset of the plane sees all `k` colors. -/
def PlanePairColoringStatement (k : ℕ) : Prop :=
  ∃ c : PairColoring k, IsSymmetricColoring c ∧
    ∀ A : Set Plane, ¬ A.Countable → HitsAllColorsOn c A

/-- Problem `#474` is the `k = 3` case of the general plane pair-coloring
statement. -/
def Erdos474Statement : Prop :=
  PlanePairColoringStatement 3

end PlanePairColorings
