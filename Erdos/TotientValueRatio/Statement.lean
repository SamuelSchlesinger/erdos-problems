import Mathlib

/-!
# Erdős Problem 417: Comparing Two Totient Value Counts

Let

* `V'(x) = #{φ(m) : 1 ≤ m ≤ x}`
* `V(x) = #{n ≤ x : n = φ(m) for some m}`.

Erdős asked whether `V(x) / V'(x)` has a limit, and if so whether that limit is
strictly greater than `1`.

Reference: https://www.erdosproblems.com/417
-/

namespace TotientValueRatio

/-! We work with finite sets of totient values so that the two counting
functions become cardinalities of explicit finsets. -/

/-- Distinct totient values achieved by arguments in `[1, x]`. -/
def totientImageUpTo (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).image Nat.totient

/-- Distinct totient values at most `x`, regardless of the size of the
argument. -/
noncomputable def totientValuesAtMost (x : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (x + 1)).filter (fun n => ∃ m : ℕ, Nat.totient m = n)

/-- The quantity `V'(x)` from Erdős problem `#417`. -/
def VPrime (x : ℕ) : ℕ :=
  (totientImageUpTo x).card

/-- The quantity `V(x)` from Erdős problem `#417`. -/
noncomputable def V (x : ℕ) : ℕ :=
  (totientValuesAtMost x).card

/-- The ratio considered in problem `#417`. -/
noncomputable def ratioSeq (x : ℕ) : ℝ :=
  (V x : ℝ) / VPrime x

/-- The first part of Erdős problem `#417`: does the ratio `V(x) / V'(x)`
converge? -/
def RatioConverges : Prop :=
  ∃ l : ℝ, Filter.Tendsto ratioSeq Filter.atTop (nhds l)

/-- The second part of Erdős problem `#417`: if the ratio converges, is the
limit strictly greater than `1`? -/
def RatioConvergesToGtOne : Prop :=
  ∃ l : ℝ, Filter.Tendsto ratioSeq Filter.atTop (nhds l) ∧ 1 < l

end TotientValueRatio
