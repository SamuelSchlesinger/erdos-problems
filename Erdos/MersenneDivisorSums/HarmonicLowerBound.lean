import Erdos.MersenneDivisorSums.DivisibilityLowerBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Cast.Order.Field

/-
# An `n · H_n − n` Lower Bound for Mersenne Divisor Sums

Combining the divisor-injection bound `τ(k) ≤ τ(2^k − 1)` from
`DivisibilityLowerBound.lean` with Dirichlet's hyperbola identity

  `∑_{k=1}^{n} τ(k) = ∑_{d=1}^{n} ⌊n/d⌋`

and the elementary floor bound `⌊n/d⌋ > (n / d) - 1` (as reals), we obtain
the closed-form real lower bound

  `f(n) ≥ n · H_n − n`,

where `H_n = ∑_{d=1}^{n} 1/d` is the `n`-th harmonic number. By the standard
inequality `log(n+1) ≤ H_n` (available as `log_add_one_le_harmonic` in
mathlib), this gives an unconditional `n · log n + O(n)` lower bound on the
Mersenne divisor sum `f(n)`, strictly improving the trivial `f(n) ≥ 2n − 1`
recorded in `Elementary.lean`.

Reference: https://www.erdosproblems.com/893
-/
namespace MersenneDivisorSums

open Finset

/-! ### Reindexing `range n` to `Ioc 0 n` -/

private lemma sum_range_succ_eq_sum_Ioc {α : Type*} [AddCommMonoid α]
    (n : ℕ) (f : ℕ → α) :
    ∑ k ∈ Finset.range n, f (k + 1) = ∑ k ∈ Finset.Ioc 0 n, f k := by
  refine Finset.sum_nbij' (i := fun k => k + 1) (j := fun k => k - 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_range] at ha
    simp only [mem_Ioc]
    omega
  · intro a ha
    simp only [mem_Ioc] at ha
    simp only [mem_range]
    omega
  · intro a ha
    simp only [mem_range] at ha
    change a + 1 - 1 = a
    omega
  · intro a ha
    simp only [mem_Ioc] at ha
    change a - 1 + 1 = a
    omega
  · intro a _; rfl

/-! ### Dirichlet's hyperbola identity in shifted-range form -/

/-- **Dirichlet's hyperbola identity** specialized to the divisor counting
function `τ`. The standard mathlib form
`ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div` is

  `∑ k ∈ Ioc 0 N, σ₀(k) = ∑ k ∈ Ioc 0 N, N / k`.

Here we re-express both sides on `Finset.range n` to match the indexing of
`mersenneDivisorSum`. -/
theorem sum_range_succ_divisors_card_eq_sum_div (n : ℕ) :
    ∑ k ∈ Finset.range n, (k + 1).divisors.card =
      ∑ d ∈ Finset.range n, n / (d + 1) := by
  have h := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div n
  simp only [ArithmeticFunction.sigma_zero_apply] at h
  rw [sum_range_succ_eq_sum_Ioc n (fun k => k.divisors.card)]
  rw [sum_range_succ_eq_sum_Ioc n (fun d => n / d)]
  exact h

/-! ### Real floor bound and the harmonic lower bound -/

/-- For `d ≥ 1`, the natural floor `⌊n/d⌋ ∈ ℕ` cast to `ℝ` is strictly greater
than `(n : ℝ) / d − 1`. -/
lemma cast_div_gt_sub_one {n d : ℕ} (hd : 0 < d) :
    ((n : ℝ) / d) - 1 < ((n / d : ℕ) : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- `n < (n / d + 1) * d` as naturals, hence as reals after casting.
  have hlt_nat : n < (n / d + 1) * d := by
    have hmod : n % d < d := Nat.mod_lt n hd
    have heq : d * (n / d) + n % d = n := Nat.div_add_mod n d
    nlinarith
  have hlt_real : (n : ℝ) < ((n / d : ℕ) + 1) * d := by
    have := (Nat.cast_lt (α := ℝ)).mpr hlt_nat
    push_cast at this
    linarith
  -- Divide by `d > 0` to get `(n : ℝ)/d < (n/d : ℕ) + 1`, hence the claim.
  have hdiv_lt : (n : ℝ) / d < ((n / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hdpos]
    linarith
  linarith

/-- Casting the natural sum `∑_{d=1}^{n} ⌊n/d⌋` into `ℝ`, the real harmonic
formula gives the lower bound

  `∑_{d=1}^{n} ⌊n/d⌋ ≥ n · (∑_{d=1}^{n} 1/d) − n`. -/
theorem sum_div_ge_n_mul_harmonic_sub_n (n : ℕ) :
    (n : ℝ) * (∑ d ∈ Finset.range n, (1 : ℝ) / (d + 1)) - n ≤
      ((∑ d ∈ Finset.range n, n / (d + 1) : ℕ) : ℝ) := by
  -- Push the cast inside the sum.
  rw [show ((∑ d ∈ Finset.range n, n / (d + 1) : ℕ) : ℝ)
        = ∑ d ∈ Finset.range n, ((n / (d + 1) : ℕ) : ℝ) by push_cast; rfl]
  -- Per-summand bound: `(n : ℝ)/(d+1) - 1 ≤ ⌊n/(d+1)⌋`.
  have hterm : ∀ d ∈ Finset.range n,
      ((n : ℝ) / (d + 1) - 1) ≤ ((n / (d + 1) : ℕ) : ℝ) := by
    intro d _
    have hd1 : 0 < d + 1 := Nat.succ_pos d
    have := cast_div_gt_sub_one (n := n) (d := d + 1) hd1
    have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    rw [hcast] at this
    linarith
  -- Sum the per-summand bound.
  have hsum := Finset.sum_le_sum hterm
  -- Rewrite the LHS of `hsum` as `n * ∑ 1/(d+1) - n`.
  have hrange_card : ((Finset.range n).card : ℝ) = n := by
    simp
  have hLHS :
      ∑ d ∈ Finset.range n, ((n : ℝ) / (d + 1) - 1)
        = (n : ℝ) * (∑ d ∈ Finset.range n, (1 : ℝ) / (d + 1)) - n := by
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hrange_card]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hLHS] at hsum
  exact hsum

/-! ### Putting it together: `f(n) ≥ n · H_n − n` -/

/-- **Closed-form harmonic lower bound** for the Mersenne divisor sum:

  `f(n) ≥ n · H_n − n`,

where `H_n = ∑_{d=1}^{n} 1/d`. This strictly improves the trivial bound
`f(n) ≥ 2n − 1` from `Elementary.lean` (`H_n` grows like `log n`, so the
right-hand side is `Θ(n log n)`). -/
theorem n_mul_harmonic_sub_n_le_mersenneDivisorSum (n : ℕ) :
    (n : ℝ) * (∑ d ∈ Finset.range n, (1 : ℝ) / (d + 1)) - n ≤
      ((mersenneDivisorSum n : ℕ) : ℝ) := by
  -- Cast the integer divisor-injection bound to `ℝ`.
  have hInjection :
      ((∑ k ∈ Finset.range n, (k + 1).divisors.card : ℕ) : ℝ) ≤
        ((mersenneDivisorSum n : ℕ) : ℝ) := by
    exact_mod_cast divisor_sum_le_mersenneDivisorSum n
  -- Apply Dirichlet's identity to convert τ-sum to the divisor sum.
  rw [sum_range_succ_divisors_card_eq_sum_div n] at hInjection
  exact le_trans (sum_div_ge_n_mul_harmonic_sub_n n) hInjection

/-- The harmonic factor `∑_{d=1}^{n} 1/d` cast from `ℚ` matches the explicit
real sum used above.  Convenient for downstream use of `harmonic_*` lemmas
from mathlib. -/
theorem real_harmonic_eq_sum_range_one_div (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ d ∈ Finset.range n, (1 : ℝ) / (d + 1) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  -- Reindex the RHS to a sum over `Ioc 0 n`.
  rw [show (∑ d ∈ Finset.range n, (1 : ℝ) / ((d : ℝ) + 1))
        = ∑ k ∈ Finset.Ioc 0 n, (1 : ℝ) / (k : ℝ) from by
        have h := sum_range_succ_eq_sum_Ioc n (fun k => (1 : ℝ) / (k : ℝ))
        simpa using h]
  -- Convert the LHS sum domain from `Icc 1 n` to `Ioc 0 n`, and use `(k : ℝ)⁻¹ = 1 / k`.
  have hdom : (Finset.Icc 1 n : Finset ℕ) = Finset.Ioc 0 n := by
    ext k; simp [Nat.lt_iff_add_one_le]
  rw [hdom]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_div]

/-- Same bound, packaged with the rational `harmonic n` from mathlib. -/
theorem n_mul_harmonic_sub_n_le_mersenneDivisorSum' (n : ℕ) :
    (n : ℝ) * ((harmonic n : ℚ) : ℝ) - n ≤
      ((mersenneDivisorSum n : ℕ) : ℝ) := by
  rw [real_harmonic_eq_sum_range_one_div n]
  exact n_mul_harmonic_sub_n_le_mersenneDivisorSum n

end MersenneDivisorSums
