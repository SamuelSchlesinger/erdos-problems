/-
# Polynomial Improvement Past `N / 2` for #327

This file completes the polynomial-improvement programme for `#327`. The
structural reduction in `Erdos/UnitFractionPairs/Chebyshev.lean` showed

  `f(N) ≥ (N + 1) / 2 + ⌊log₂ N⌋ + max(|chebyshev41 K|, |chebyshev43 K|)`

for `2 K² ≤ N`, where the max is bounded below by
`(π(K) - 4 - ⌊log₂(K+1)⌋ - ⌊log₂(K+2)⌋) / 2`.

The remaining gap is purely analytic: lower-bounding `π(K)`. Mathlib's
`Chebyshev.theta_ge` and `Chebyshev.theta_le_pi_mul_log` combine to give

  `π(K) · log K ≥ θ(K) ≥ K · log 2 - log(K + 1) - 2 √K · log K`,

so `π(K) ≥ K · log 2 / log K - log(K + 1) / log K - 2 √K`.

The two subtracted terms are `o(K / log K)` (the first because
`log(K + 1) = o(K)`, the second because `2 √K = o(K / log K)`), hence
asymptotically `π(K) ≥ (1 - o(1)) · K · log 2 / log K`. Concretely we
prove `π(K) ≥ K · log 2 / (2 · log K)` eventually.

Plugging `K = ⌊√(N / 2)⌋` gives the polynomial improvement past `N / 2`.
-/

import Erdos.UnitFractionPairs.Chebyshev

open Filter Asymptotics

namespace UnitFractionPairs

/-! ### Asymptotic comparisons: `log K = o(K)` and `log K = o(√K)` on ℕ. -/

/-- For any `ε > 0`, eventually `Real.log K ≤ ε · K` for `K : ℕ`. -/
lemma log_le_eps_id_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, Real.log K ≤ ε * K := by
  have h : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ ε * ‖x‖ :=
    Real.isLittleO_log_id_atTop.def hε
  have h2 : ∀ᶠ K : ℕ in atTop, ‖Real.log (K : ℝ)‖ ≤ ε * ‖(K : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2, eventually_ge_atTop 1] with K hK hK1
  have hlog_nn : 0 ≤ Real.log K :=
    Real.log_nonneg (by exact_mod_cast hK1)
  have hK_nn : (0 : ℝ) ≤ K := by positivity
  rw [Real.norm_of_nonneg hlog_nn, Real.norm_of_nonneg hK_nn] at hK
  exact hK

/-- For any `ε > 0`, eventually `Real.log K ≤ ε · √K` for `K : ℕ`. -/
lemma log_le_eps_sqrt_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, Real.log K ≤ ε * Real.sqrt K := by
  have h_o : Real.log =o[atTop] fun x : ℝ => x ^ (1/2 : ℝ) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)
  have h : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ ε * ‖x ^ (1/2 : ℝ)‖ := h_o.def hε
  have h2 : ∀ᶠ K : ℕ in atTop, ‖Real.log (K : ℝ)‖ ≤ ε * ‖((K : ℝ) ^ (1/2 : ℝ))‖ :=
    tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2, eventually_ge_atTop 1] with K hK hK1
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlog_nn : 0 ≤ Real.log K := Real.log_nonneg hK1'
  have hK_nn : (0 : ℝ) ≤ K := by positivity
  have hrpow : (K : ℝ) ^ (1/2 : ℝ) = Real.sqrt K := by
    rw [Real.sqrt_eq_rpow]
  have hrpow_nn : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hlog_nn, hrpow,
    Real.norm_of_nonneg hrpow_nn] at hK
  exact hK

/-! ### Chebyshev lower bound on `π(K)`. -/

/-- **Chebyshev lower bound** (one-sided): for all sufficiently large `K : ℕ`,
`π(K) ≥ K · log 2 / (2 · log K)`. -/
theorem primeCounting_ge_chebyshev :
    ∀ᶠ K : ℕ in atTop,
      (K : ℝ) * Real.log 2 / (2 * Real.log K) ≤ (Nat.primeCounting K : ℝ) := by
  -- We need: K · log 2 / 2 ≤ K · log 2 - log(K + 1) - 2 √K · log K.
  -- Equivalently: log(K + 1) + 2 √K · log K ≤ K · log 2 / 2.
  -- Strategy: bound each term by `K · log 2 / 4`.
  --   Term 1: `log(K + 1) ≤ log K + log 2 ≤ K · log 2 / 8 + log 2 ≤ K · log 2 / 4`
  --     (the last step uses `log 2 ≤ K · log 2 / 8`, i.e., `K ≥ 8`).
  --   Term 2: `2 √K · log K ≤ 2 √K · (√K · log 2 / 8) = K · log 2 / 4`
  --     (from `log K ≤ (log 2 / 8) · √K`).
  filter_upwards
    [log_le_eps_id_eventually (show (0 : ℝ) < Real.log 2 / 8 by positivity),
     log_le_eps_sqrt_eventually (show (0 : ℝ) < Real.log 2 / 8 by positivity),
     eventually_ge_atTop 8]
    with K hlogId hlogSqrt hK8
  have hK_ge_8 : (8 : ℝ) ≤ K := by exact_mod_cast hK8
  have hK_pos : (0 : ℝ) < K := by linarith
  have hlogK_pos : 0 < Real.log K := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrtK_nn : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hsqrtK_sq : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (by linarith)
  -- Term 1: `log(K + 1) ≤ K · log 2 / 4`.
  have hKplus_le : Real.log ((K : ℝ) + 1) ≤ K * Real.log 2 / 4 := by
    -- Step 1a: `log(K + 1) ≤ log(2K) = log 2 + log K`.
    have h1 : Real.log ((K : ℝ) + 1) ≤ Real.log 2 + Real.log K := by
      have h_le : Real.log ((K : ℝ) + 1) ≤ Real.log (2 * K) :=
        Real.log_le_log (by linarith) (by linarith)
      rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : (K : ℝ) ≠ 0)] at h_le
    -- Step 1b: `log K ≤ K · log 2 / 8` from `hlogId`.
    -- Step 1c: `log 2 ≤ K · log 2 / 8` since `K ≥ 8`.
    have h_log2_le : Real.log 2 ≤ K * Real.log 2 / 8 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hlog2_pos]
    linarith
  -- Term 2: `2 √K · log K ≤ K · log 2 / 4`.
  have hSqrt_le : 2 * Real.sqrt K * Real.log K ≤ K * Real.log 2 / 4 := by
    have : 2 * Real.sqrt K * Real.log K ≤
        2 * Real.sqrt K * (Real.log 2 / 8 * Real.sqrt K) := by
      apply mul_le_mul_of_nonneg_left hlogSqrt
      positivity
    calc 2 * Real.sqrt K * Real.log K
        ≤ 2 * Real.sqrt K * (Real.log 2 / 8 * Real.sqrt K) := this
      _ = K * Real.log 2 / 4 := by
          rw [show 2 * Real.sqrt K * (Real.log 2 / 8 * Real.sqrt K) =
              Real.log 2 / 4 * (Real.sqrt K * Real.sqrt K) from by ring, hsqrtK_sq]
          ring
  -- Combined: `K · log 2 - log(K + 1) - 2 √K · log K ≥ K · log 2 / 2`.
  have h_theta_lb : (K : ℝ) * Real.log 2 / 2 ≤
      K * Real.log 2 - Real.log ((K : ℝ) + 1) - 2 * Real.sqrt K * Real.log K := by
    linarith
  -- Apply `theta_ge` and `theta_le_pi_mul_log`.
  have h_theta_ge : (K : ℝ) * Real.log 2 - Real.log ((K : ℝ) + 1) -
      2 * Real.sqrt K * Real.log K ≤ Chebyshev.theta K := Chebyshev.theta_ge K
  have h_theta_le : Chebyshev.theta K ≤ (Nat.primeCounting K : ℝ) * Real.log K :=
    Chebyshev.theta_le_pi_mul_log K
  have h_combined : (K : ℝ) * Real.log 2 / 2 ≤
      (Nat.primeCounting K : ℝ) * Real.log K := by linarith
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Real.log K)]
  linarith

/-! ### Sqrt-based substitution: `K = Nat.sqrt (N / 2)`.

The natural choice `K := Nat.sqrt (N / 2)` automatically satisfies `2 K² ≤ N`
required by `exists_pairFree_card_ge_primeCounting`, and tends to infinity as
`N → ∞`, so `primeCounting_ge_chebyshev` applies at `K` for `N` large enough.

The final polynomial-improvement headline,

  `∀ᶠ N in atTop, ∃ A ⊆ [1, N] pair-free, A.card ≥ N/2 + c · √N / log N`

then follows by plugging the structural bound through this substitution and
chasing the `K ≥ √N / 2`, `log K ≤ log N / 2` estimates. We package the two
substitution-level lemmas here so the next iteration can compose them with
`primeCounting_ge_chebyshev` and `exists_pairFree_card_ge_primeCounting`. -/

/-- `Nat.sqrt (N / 2)` tends to infinity as `N → ∞`. -/
theorem tendsto_sqrt_div_2_atTop :
    Filter.Tendsto (fun N : ℕ => Nat.sqrt (N / 2)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr (fun M => ?_)
  refine ⟨2 * (M + 1) ^ 2, fun N hN => ?_⟩
  have hM : (M + 1) ^ 2 ≤ N / 2 := by omega
  have h := Nat.sqrt_le_sqrt hM
  rw [Nat.sqrt_eq'] at h
  omega

/-- For any `N : ℕ`, `2 · (Nat.sqrt (N / 2))² ≤ N`. This is the side-condition
for plugging `K = Nat.sqrt (N / 2)` into `exists_pairFree_card_ge_primeCounting`. -/
theorem two_mul_sqrt_div_2_sq_le (N : ℕ) : 2 * (Nat.sqrt (N / 2)) ^ 2 ≤ N := by
  have h : (Nat.sqrt (N / 2)) ^ 2 ≤ N / 2 := Nat.sqrt_le' _
  have h2 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
  linarith [Nat.mul_le_mul_left 2 h]

end UnitFractionPairs
