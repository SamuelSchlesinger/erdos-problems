/-
# Split Optimization: `√x + √(N - x) ≤ √(2N)`

A pure real-number lemma used in the proof of the `√2 · √N` upper bound for
strong almost-Sidon sets. The Cauchy–Schwarz inequality applied to the
two-element sequences `(1, 1)` and `(√x, √y)` gives
`(√x + √y)² ≤ 2·(x + y)`. Specializing to `y = N - x` yields the bound
`√x + √(N - x) ≤ √(2N)`, with equality at `x = N/2`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AlmostSidonSets.UpperBound

open Real

/-- Two-term Cauchy–Schwarz: `(√x + √y)² ≤ 2·(x + y)` for non-negative reals. -/
theorem sqrt_add_sqrt_sq_le_two_mul_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x + Real.sqrt y) ^ 2 ≤ 2 * (x + y) := by
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hsy : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  have hsq_x : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsq_y : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hAMGM : 2 * (Real.sqrt x * Real.sqrt y) ≤ x + y := by
    have := sq_nonneg (Real.sqrt x - Real.sqrt y)
    have hexp : (Real.sqrt x - Real.sqrt y) ^ 2
                = Real.sqrt x ^ 2 - 2 * (Real.sqrt x * Real.sqrt y) + Real.sqrt y ^ 2 := by
      ring
    rw [hexp, hsq_x, hsq_y] at this
    linarith
  have hexp : (Real.sqrt x + Real.sqrt y) ^ 2
              = Real.sqrt x ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) + Real.sqrt y ^ 2 := by
    ring
  rw [hexp, hsq_x, hsq_y]
  linarith

/-- Two-term Cauchy–Schwarz, root form: `√x + √y ≤ √(2·(x + y))`. -/
theorem sqrt_add_sqrt_le_sqrt_two_mul_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x + Real.sqrt y ≤ Real.sqrt (2 * (x + y)) := by
  have hsum_nn : 0 ≤ Real.sqrt x + Real.sqrt y :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpos : 0 ≤ 2 * (x + y) := by positivity
  have hsq := sqrt_add_sqrt_sq_le_two_mul_add hx hy
  -- `(√x + √y)² ≤ 2·(x+y)`; both sides nonneg, take √.
  have hrhs : Real.sqrt (2 * (x + y)) = Real.sqrt ((Real.sqrt (2 * (x + y))) ^ 2) := by
    rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
  have hsqrt2_sq : (Real.sqrt (2 * (x + y))) ^ 2 = 2 * (x + y) :=
    Real.sq_sqrt hpos
  -- From hsq : (√x + √y)^2 ≤ 2·(x+y) = (√(2(x+y)))^2, get √x + √y ≤ √(2(x+y))
  have : (Real.sqrt x + Real.sqrt y) ^ 2 ≤ (Real.sqrt (2 * (x + y))) ^ 2 := by
    rwa [hsqrt2_sq]
  exact abs_le_of_sq_le_sq' this (Real.sqrt_nonneg _) |>.2

/-- The headline split-optimization inequality:
for `0 ≤ x ≤ N`, `√x + √(N - x) ≤ √(2N)`.

This follows from the two-term Cauchy–Schwarz inequality with `y = N - x`,
since then `2·(x + y) = 2N`. Equality holds at `x = N/2`. -/
theorem sqrt_add_sqrt_complement_le {N x : ℝ} (hx : 0 ≤ x) (hxN : x ≤ N) :
    Real.sqrt x + Real.sqrt (N - x) ≤ Real.sqrt (2 * N) := by
  have hNmx_nn : 0 ≤ N - x := sub_nonneg.mpr hxN
  have h := sqrt_add_sqrt_le_sqrt_two_mul_add hx hNmx_nn
  have hsimp : x + (N - x) = N := by ring
  rw [hsimp] at h
  exact h

end AlmostSidonSets.UpperBound
