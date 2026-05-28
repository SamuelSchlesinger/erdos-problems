import Erdos.PrimeGapHarmonic.Elementary
import Mathlib.Data.Nat.Prime.Infinite

/-
# Pointwise Upper Bound and Limsup ≥ 1 for the Prime-Gap Harmonic Sum

This file records two structural improvements on the elementary facts in
`Elementary.lean` for Erdős problem `#950`:

* a pointwise upper bound `f(n) ≤ H_{n-1}` coming from the fact that the gap
  values `{n - p : p < n prime}` are distinct positive integers in
  `[1, n - 1]`, hence their reciprocal sum is dominated by the truncated
  harmonic sum;
* the per-prime lower bound `f(p + 1) ≥ 1` (the term `q = p` contributes
  exactly `1/(p+1-p) = 1`), and the immediate consequence that `f(n) ≥ 1`
  holds for arbitrarily large `n`.

The latter gives `limsup f(n) ≥ 1`, a partial step toward Erdős's full
conjecture `limsup f(n) = ∞`.

Reference: https://www.erdosproblems.com/950
-/
namespace PrimeGapHarmonic

open Finset

/-! ### Pointwise upper bound `f(n) ≤ H_{n-1}` -/

/-- The map sending a prime `p < n` to its gap `n - p` is injective on
`primesBelow n`. -/
lemma injOn_sub_primesBelow (n : ℕ) :
    Set.InjOn (fun p => n - p) (primesBelow n : Set ℕ) := by
  intro p hp q hq hpq
  have hp' : p < n := (mem_primesBelow.mp hp).1
  have hq' : q < n := (mem_primesBelow.mp hq).1
  have heq : n - p = n - q := hpq
  -- From `n - p = n - q` and both `p < n`, `q < n`, conclude `p = q`.
  omega

/-- The gap values `{n - p : p < n prime}` are contained in `Icc 1 (n - 1)`. -/
lemma sub_primesBelow_subset_Icc (n : ℕ) :
    (primesBelow n).image (fun p => n - p) ⊆ Finset.Icc 1 (n - 1) := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
  rcases mem_primesBelow.mp hp with ⟨hpn, _⟩
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · exact Nat.sub_pos_of_lt hpn
  · exact Nat.sub_le_sub_left (by linarith [(mem_primesBelow.mp hp).2.two_le]) n

/-- **Pointwise upper bound**: `f(n) ≤ ∑_{k=1}^{n-1} 1/k = H_{n-1}`.

The proof reindexes the prime-gap sum by its image under `p ↦ n - p`, which
is an injection into `Icc 1 (n - 1)`. -/
theorem gapReciprocalSum_le_truncated_harmonic (n : ℕ) :
    gapReciprocalSum n ≤ ∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℝ) / k := by
  unfold gapReciprocalSum
  -- Reindex: ∑_{p ∈ primesBelow n} 1/(n - p) = ∑_{k ∈ image, p ↦ n-p} 1/k.
  rw [show ∑ p ∈ primesBelow n, (1 : ℝ) / ((n - p : ℕ) : ℝ)
        = ∑ k ∈ (primesBelow n).image (fun p => n - p), (1 : ℝ) / (k : ℝ) from by
        rw [Finset.sum_image]
        intro p hp q hq hpq
        exact injOn_sub_primesBelow n hp hq hpq]
  -- The image sits in Icc 1 (n - 1); summand is nonnegative there.
  refine Finset.sum_le_sum_of_subset_of_nonneg (sub_primesBelow_subset_Icc n) ?_
  intro k hk _
  rcases Finset.mem_Icc.mp hk with ⟨hk1, _⟩
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  positivity

/-! ### Per-prime lower bound and limsup ≥ 1 -/

/-- For any prime `p`, the value `f(p + 1)` is at least `1`: the term
`q = p` contributes exactly `1/(p+1-p) = 1`. -/
theorem one_le_gapReciprocalSum_succ_of_prime {p : ℕ} (hp : Nat.Prime p) :
    (1 : ℝ) ≤ gapReciprocalSum (p + 1) := by
  have h := inv_sub_prime_le_gapReciprocalSum (n := p + 1) (p := p)
    (Nat.lt_succ_self p) hp
  -- `(p + 1) - p = 1`, hence the term equals `1 / (1 : ℝ) = 1`.
  have hcalc : (((p + 1 - p : ℕ) : ℝ)) = 1 := by
    have : (p + 1 - p : ℕ) = 1 := by omega
    simp [this]
  rw [hcalc] at h
  simpa using h

/-- **Infinitude**: for every `N`, there exists `n ≥ N` with
`gapReciprocalSum n ≥ 1`.

Equivalently, `limsup f(n) ≥ 1`. This is a partial step toward Erdős's
conjectured `limsup f(n) = ∞`. -/
theorem exists_ge_one_gapReciprocalSum_above (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (1 : ℝ) ≤ gapReciprocalSum n := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  refine ⟨p + 1, le_trans hpN (Nat.le_succ p), ?_⟩
  exact one_le_gapReciprocalSum_succ_of_prime hp

end PrimeGapHarmonic
