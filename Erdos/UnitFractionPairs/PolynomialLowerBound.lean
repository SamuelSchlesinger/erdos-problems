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
import Erdos.UnitFractionPairs.LargePrimeDoubles

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

/-! ### Concrete `√(N / 2)` headline. -/

/-- **Concrete polynomial-improvement bound** (Nat form): substituting
`K = Nat.sqrt (N / 2)` into `exists_pairFree_card_ge_primeCounting` gives
an unconditional inequality involving `π(Nat.sqrt (N / 2))`.

  `2 · ((N + 1) / 2 + ⌊log₂ N⌋) + π(⌊√(N/2)⌋) ≤
     2 · |A| + 4 + ⌊log₂(⌊√(N/2)⌋ + 1)⌋ + ⌊log₂(⌊√(N/2)⌋ + 2)⌋`.

By `tendsto_sqrt_div_2_atTop` and `primeCounting_ge_chebyshev`, the third
term on the left grows as `Ω(√N / log N)` and asymptotically dominates the
log terms on the right — the polynomial improvement past `N / 2`. -/
theorem exists_pairFree_card_ge_at_sqrt (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      2 * ((N + 1) / 2 + Nat.log 2 N) +
          Nat.primeCounting (Nat.sqrt (N / 2)) ≤
        2 * A.card + 4 + Nat.log 2 (Nat.sqrt (N / 2) + 1) +
          Nat.log 2 (Nat.sqrt (N / 2) + 2) :=
  exists_pairFree_card_ge_primeCounting (two_mul_sqrt_div_2_sq_le N)

/-- **Asymptotic polynomial-improvement bound at `K = Nat.sqrt (N / 2)`**:
combining `exists_pairFree_card_ge_at_sqrt` with the asymptotic
`primeCounting_ge_chebyshev` at `K = Nat.sqrt (N / 2)` (valid eventually
by `tendsto_sqrt_div_2_atTop`), we obtain that for all sufficiently large
`N`, the structural bound is enhanced by

  `(Nat.sqrt (N / 2) : ℝ) · log 2 / (2 · log (Nat.sqrt (N / 2)))`,

i.e., a `Ω(√N / log N)` term. -/
theorem primeCounting_at_sqrt_ge_chebyshev :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Nat.sqrt (N / 2) : ℝ) * Real.log 2 /
          (2 * Real.log (Nat.sqrt (N / 2))) ≤
        (Nat.primeCounting (Nat.sqrt (N / 2)) : ℝ) :=
  tendsto_sqrt_div_2_atTop.eventually primeCounting_ge_chebyshev

/-! ### Cast lemmas: `(Nat.sqrt (N/2) : ℝ)` vs `Real.sqrt N`. -/

/-- For `N ≥ 64`, `(Nat.sqrt (N / 2) : ℝ) ≥ √N / 4`. -/
private lemma sqrt_div_2_ge_real {N : ℕ} (hN : 64 ≤ N) :
    Real.sqrt N / 4 ≤ (Nat.sqrt (N / 2) : ℝ) := by
  set K : ℕ := Nat.sqrt (N / 2)
  have h_lt : N / 2 < (K + 1) ^ 2 := Nat.lt_succ_sqrt' (N / 2)
  have h_2K : N ≤ 2 * (K + 1) ^ 2 := by
    have hN2 : N ≤ 2 * (N / 2) + 1 := by omega
    linarith [Nat.mul_le_mul_left 2 h_lt]
  have h_R : ((K : ℝ) + 1) ^ 2 ≥ (N : ℝ) / 2 := by
    have h := show (N : ℝ) ≤ 2 * ((K : ℝ) + 1) ^ 2 by exact_mod_cast h_2K
    linarith
  have hKR_nn : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  have h_sqrt : Real.sqrt ((N : ℝ) / 2) ≤ (K : ℝ) + 1 := by
    rw [show ((K : ℝ) + 1) = Real.sqrt (((K : ℝ) + 1) ^ 2) from
      (Real.sqrt_sq hKR_nn).symm]
    exact Real.sqrt_le_sqrt h_R
  have h_sqrt2 : Real.sqrt N / Real.sqrt 2 ≤ (K : ℝ) + 1 := by
    have h_eq : Real.sqrt ((N : ℝ) / 2) = Real.sqrt N / Real.sqrt 2 :=
      Real.sqrt_div (by exact_mod_cast Nat.zero_le N) 2
    linarith [h_eq ▸ h_sqrt]
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_le : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h_div : Real.sqrt N / 2 ≤ Real.sqrt N / Real.sqrt 2 :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hsqrt2_pos hsqrt2_le
  have hsqrt_ge_8 : (8 : ℝ) ≤ Real.sqrt N := by
    rw [show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  linarith

/-- For `N ≥ 4`, `Real.log (Nat.sqrt (N / 2)) ≤ Real.log N / 2`. -/
private lemma log_sqrt_div_2_le {N : ℕ} (hN : 4 ≤ N) :
    Real.log (Nat.sqrt (N / 2)) ≤ Real.log N / 2 := by
  set K : ℕ := Nat.sqrt (N / 2)
  have h_sq : (K : ℝ) ^ 2 ≤ (N : ℝ) / 2 := by
    have h : K ^ 2 ≤ N / 2 := Nat.sqrt_le' _
    have hN2 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
      have : (N / 2 : ℕ) * 2 ≤ N := Nat.div_mul_le_self N 2
      have h_R : ((N / 2 : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by exact_mod_cast this
      linarith
    have hK : ((K ^ 2 : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hK
    linarith
  have h_K_le : (K : ℝ) ≤ Real.sqrt N := by
    have hK_nn : (0 : ℝ) ≤ K := by positivity
    rw [show (K : ℝ) = Real.sqrt ((K : ℝ) ^ 2) from (Real.sqrt_sq hK_nn).symm]
    apply Real.sqrt_le_sqrt; linarith
  have hK_pos : 0 < (K : ℝ) := by
    have hK_nat : 1 ≤ K := by
      have h : 1 ≤ N / 2 := by omega
      have h2 : Nat.sqrt 1 ≤ Nat.sqrt (N / 2) := Nat.sqrt_le_sqrt h
      simpa using h2
    exact_mod_cast hK_nat
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h_log_mono : Real.log K ≤ Real.log (Real.sqrt N) :=
    Real.log_le_log hK_pos h_K_le
  rwa [Real.log_sqrt (le_of_lt hN_pos)] at h_log_mono

/-- `(Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2`. -/
private lemma natLog_two_le (m : ℕ) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have h := Real.natLog_le_logb m 2
  rwa [Real.logb] at h

/-- `(((N + 1) / 2 : ℕ) : ℝ) ≥ (N : ℝ) / 2`. -/
private lemma succDiv_two_ge_half (N : ℕ) :
    (N : ℝ) / 2 ≤ (((N + 1) / 2 : ℕ) : ℝ) := by
  rcases Nat.even_or_odd N with h | h
  · -- N even: (N+1)/2 in ℕ = N/2 (since N+1 odd).
    have hN : N / 2 * 2 = N := Nat.div_two_mul_two_of_even h
    have : (N + 1) / 2 = N / 2 := by omega
    rw [this]
    have : ((N / 2 : ℕ) : ℝ) * 2 = N := by exact_mod_cast hN
    linarith
  · -- N odd: (N+1)/2 in ℕ = (N+1)/2 ≥ N/2 + 1/2 > N/2 in ℝ.
    obtain ⟨k, rfl⟩ := h
    have : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [this]
    push_cast
    linarith

/-- For any `C > 0`, eventually `C · (Real.log N)² ≤ Real.sqrt N` for `N : ℕ`.
This follows from `log = o(N^(1/4))`: squaring gives `log² = o(√N)`. -/
private lemma C_log_sq_le_sqrt_eventually {C : ℝ} (hC : 0 < C) :
    ∀ᶠ N : ℕ in Filter.atTop, C * (Real.log N) ^ 2 ≤ Real.sqrt N := by
  have hC_inv : 0 < 1 / Real.sqrt C := by positivity
  have h_o : Real.log =o[Filter.atTop] (fun x : ℝ => x ^ (1/4 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h_def := h_o.def (c := 1 / Real.sqrt C) hC_inv
  have h_nat : ∀ᶠ N : ℕ in Filter.atTop,
      ‖Real.log N‖ ≤ (1 / Real.sqrt C) * ‖(N : ℝ) ^ (1/4 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually h_def
  filter_upwards [h_nat, Filter.eventually_ge_atTop 1] with N hN hN1
  have h_N_ge_1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h_log_nn : 0 ≤ Real.log N := Real.log_nonneg h_N_ge_1
  have hN_pos : (0 : ℝ) < N := by linarith
  have h_rpow_nn : 0 ≤ ((N : ℝ)) ^ (1/4 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg h_log_nn, Real.norm_of_nonneg h_rpow_nn] at hN
  have hsqrtC_pos : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  -- Algebraic facts: (1/√C)² = 1/C, (N^(1/4))² = √N.
  have h_sqC_inv : (1 / Real.sqrt C) * (1 / Real.sqrt C) = 1 / C := by
    rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt (le_of_lt hC)]
  have h_sqN : (N : ℝ) ^ (1/4 : ℝ) * (N : ℝ) ^ (1/4 : ℝ) = Real.sqrt N := by
    rw [← Real.rpow_add hN_pos, show ((1/4 : ℝ) + (1/4 : ℝ)) = 1/2 by norm_num,
      ← Real.sqrt_eq_rpow]
  -- Square: log² N ≤ (1/C) · √N.
  have hsq : (Real.log N) ^ 2 ≤ (1 / C) * Real.sqrt N := by
    have h_step1 : Real.log N * Real.log N ≤
        ((1 / Real.sqrt C) * (N : ℝ) ^ (1/4 : ℝ)) *
          ((1 / Real.sqrt C) * (N : ℝ) ^ (1/4 : ℝ)) :=
      mul_le_mul hN hN h_log_nn (by positivity)
    have h_step2 : ((1 / Real.sqrt C) * (N : ℝ) ^ (1/4 : ℝ)) *
        ((1 / Real.sqrt C) * (N : ℝ) ^ (1/4 : ℝ)) =
        (1 / C) * Real.sqrt N := by
      calc ((1 / Real.sqrt C) * (N : ℝ) ^ (1/4 : ℝ)) *
          ((1 / Real.sqrt C) * (N : ℝ) ^ (1/4 : ℝ))
          = ((1 / Real.sqrt C) * (1 / Real.sqrt C)) *
              ((N : ℝ) ^ (1/4 : ℝ) * (N : ℝ) ^ (1/4 : ℝ)) := by ring
        _ = (1 / C) * Real.sqrt N := by rw [h_sqC_inv, h_sqN]
    rw [sq, ← h_step2]
    exact h_step1
  -- Hence C · log² N ≤ √N.
  calc C * (Real.log N) ^ 2 ≤ C * ((1 / C) * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsq (le_of_lt hC)
    _ = Real.sqrt N := by field_simp

/-! ### Polynomial-improvement headline. -/

/-- **Polynomial improvement past `N / 2`** (headline): there exists `c > 0`
such that for all sufficiently large `N`, there is a pair-free
`A ⊆ [1, N]` with `|A| ≥ N/2 + c · √N / log N`. -/
theorem exists_pairFree_polynomial_improvement :
    ∃ c > 0, ∀ᶠ N : ℕ in Filter.atTop, ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
        (N : ℝ) / 2 + c * Real.sqrt N / Real.log N ≤ (A.card : ℝ) := by
  refine ⟨Real.log 2 / 32, by positivity, ?_⟩
  -- Slack inequality: 4 + 2 log N / log 2 ≤ 3 log 2 · √N / (16 log N), eventually.
  -- Proof: bound LHS ≤ 4 log N (for log N ≥ 4 + 2/log 2 ≈ 6.88, i.e., N ≥ e⁷ ≈ 1100).
  -- Then `4 log N ≤ 3 log 2 √N / (16 log N)` iff `64 log² N ≤ 3 log 2 √N`,
  -- iff `(64 / (3 log 2)) log² N ≤ √N`. Apply `C_log_sq_le_sqrt_eventually`.
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_slack : ∀ᶠ N : ℕ in Filter.atTop,
      4 + 2 * (Real.log N / Real.log 2) ≤
        3 * Real.log 2 * Real.sqrt N / (16 * Real.log N) := by
    have h_log_sq := C_log_sq_le_sqrt_eventually
      (show (0 : ℝ) < 64 / (3 * Real.log 2) by positivity)
    -- Also need log N ≥ 4 + 2/log 2 eventually (so 4 + 2 log N / log 2 ≤ 4 log N).
    have h_log_big : ∀ᶠ N : ℕ in Filter.atTop, 4 + 2 / Real.log 2 ≤ Real.log N := by
      have h_tend : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact h_tend.eventually_ge_atTop _
    filter_upwards [h_log_sq, h_log_big, Filter.eventually_ge_atTop 2]
      with N h_log_sq h_log_big hN2
    have hN_ge_2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hN_pos : 0 < (N : ℝ) := by linarith
    have hlogN_pos : 0 < Real.log N := Real.log_pos (by linarith)
    have hsqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
    -- LHS ≤ 4 log N: split as `4 ≤ log N` and `2 log N / log 2 ≤ 3 log N`,
    -- the latter from `2 ≤ 3 log 2` (numeric fact).
    have h_two_over_log2_nn : 0 ≤ 2 / Real.log 2 := by positivity
    have h_LHS_le : 4 + 2 * (Real.log N / Real.log 2) ≤ 4 * Real.log N := by
      have h1 : 4 ≤ Real.log N := by linarith
      have h_log2_big : (2 : ℝ) ≤ 3 * Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      have h2 : 2 * (Real.log N / Real.log 2) ≤ 3 * Real.log N := by
        rw [show 2 * (Real.log N / Real.log 2) = 2 * Real.log N / Real.log 2 from by ring]
        rw [div_le_iff₀ hlog2_pos]
        nlinarith [hlogN_pos]
      linarith
    -- Now show 4 log N ≤ 3 log 2 √N / (16 log N), i.e., 64 log² N ≤ 3 log 2 √N.
    have h_RHS_ge : 4 * Real.log N ≤ 3 * Real.log 2 * Real.sqrt N / (16 * Real.log N) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 16 * Real.log N)]
      -- 4 log N · 16 log N ≤ 3 log 2 · √N, i.e., 64 log² N ≤ 3 log 2 √N.
      -- From h_log_sq: 64/(3 log 2) · log² N ≤ √N.
      -- Multiply by 3 log 2: 64 log² N ≤ 3 log 2 · √N. ✓
      have : 64 / (3 * Real.log 2) * (Real.log N) ^ 2 * (3 * Real.log 2) ≤
          Real.sqrt N * (3 * Real.log 2) :=
        mul_le_mul_of_nonneg_right h_log_sq (by linarith)
      have hsimp : 64 / (3 * Real.log 2) * (Real.log N) ^ 2 * (3 * Real.log 2) =
          64 * (Real.log N) ^ 2 := by field_simp
      rw [hsimp] at this
      nlinarith
    linarith
  filter_upwards
    [primeCounting_at_sqrt_ge_chebyshev,
     Filter.eventually_ge_atTop 256,
     h_slack]
    with N h_cheb hN_ge h_slack
  obtain ⟨A, hAsub, hApf, hA⟩ := exists_pairFree_card_ge_at_sqrt N
  refine ⟨A, hAsub, hApf, ?_⟩
  set K : ℕ := Nat.sqrt (N / 2)
  have h_sqrt_lb : Real.sqrt N / 4 ≤ (K : ℝ) := sqrt_div_2_ge_real (by omega : 64 ≤ N)
  have h_log_ub : Real.log K ≤ Real.log N / 2 := log_sqrt_div_2_le (by omega : 4 ≤ N)
  have hK_ge_8 : (8 : ℕ) ≤ K := by
    have h := Nat.sqrt_le_sqrt (show 64 ≤ N / 2 by omega)
    have hsqrt64 : Nat.sqrt 64 = 8 := by
      rw [show (64 : ℕ) = 8 ^ 2 from by norm_num]; exact Nat.sqrt_eq' 8
    rwa [hsqrt64] at h
  have hKR_ge_8 : (8 : ℝ) ≤ K := by exact_mod_cast hK_ge_8
  have hKR_pos : 0 < (K : ℝ) := by linarith
  have hlogK_pos : 0 < Real.log K := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNR_pos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlogN_pos : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNR_pos
  have hAR : 2 * ((((N + 1) / 2 : ℕ) : ℝ) + (Nat.log 2 N : ℝ)) +
      (Nat.primeCounting K : ℝ) ≤
        2 * (A.card : ℝ) + 4 + (Nat.log 2 (K + 1) : ℝ) +
          (Nat.log 2 (K + 2) : ℝ) := by exact_mod_cast hA
  -- π(K) ≥ K log 2 / (2 log K) ≥ √N log 2 / (4 log N).
  have h_piK_ge : Real.sqrt N * Real.log 2 / (4 * Real.log N) ≤
      (K : ℝ) * Real.log 2 / (2 * Real.log K) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    have h1 : Real.sqrt N * Real.log 2 * (2 * Real.log K) ≤
        Real.sqrt N * Real.log 2 * (2 * (Real.log N / 2)) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · positivity
    have h2 : Real.sqrt N * Real.log 2 * (2 * (Real.log N / 2)) =
        Real.sqrt N * Real.log 2 * Real.log N := by ring
    have h3 : Real.sqrt N * Real.log 2 * Real.log N ≤
        K * Real.log 2 * (4 * Real.log N) := by
      have h_eq : Real.sqrt N * Real.log 2 * Real.log N =
          (Real.sqrt N / 4) * Real.log 2 * (4 * Real.log N) := by ring
      rw [h_eq]
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right h_sqrt_lb (le_of_lt hlog2_pos)
      · linarith
    linarith
  have h_piK_le : Real.sqrt N * Real.log 2 / (4 * Real.log N) ≤
      (Nat.primeCounting K : ℝ) := le_trans h_piK_ge h_cheb
  -- Upper bounds on log₂(K+1), log₂(K+2) ≤ log N / log 2.
  have hK2_le_N : (K + 2 : ℕ) ≤ N := by
    have : K ≤ N / 2 := Nat.sqrt_le_self _
    omega
  have hlog_K1_le : Real.log (K + 1 : ℕ) ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < K + 1))
      (by exact_mod_cast (by omega : K + 1 ≤ N))
  have hlog_K2_le : Real.log (K + 2 : ℕ) ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < K + 2))
      (by exact_mod_cast hK2_le_N)
  have h_natLog_K1 : (Nat.log 2 (K + 1) : ℝ) ≤ Real.log N / Real.log 2 :=
    le_trans (natLog_two_le (K + 1))
      (div_le_div_of_nonneg_right hlog_K1_le (le_of_lt hlog2_pos))
  have h_natLog_K2 : (Nat.log 2 (K + 2) : ℝ) ≤ Real.log N / Real.log 2 :=
    le_trans (natLog_two_le (K + 2))
      (div_le_div_of_nonneg_right hlog_K2_le (le_of_lt hlog2_pos))
  have h_halfN : (N : ℝ) / 2 ≤ (((N + 1) / 2 : ℕ) : ℝ) := succDiv_two_ge_half N
  have h_logN_nn : 0 ≤ (Nat.log 2 N : ℝ) := by positivity
  -- Final algebra.
  have h_target : (N : ℝ) + Real.sqrt N * Real.log 2 / (16 * Real.log N) ≤
      2 * (A.card : ℝ) := by
    have h_slack' : 4 + 2 * (Real.log N / Real.log 2) ≤
        3 * Real.log 2 * Real.sqrt N / (16 * Real.log N) := h_slack
    have h_slack_eq : 3 * Real.log 2 * Real.sqrt N / (16 * Real.log N) =
        Real.sqrt N * Real.log 2 / (4 * Real.log N) -
          Real.sqrt N * Real.log 2 / (16 * Real.log N) := by
      field_simp; ring
    have h_2log_eq : 2 * (Real.log N / Real.log 2) =
        2 * Real.log N / Real.log 2 := by ring
    linarith
  have h_div_eq : Real.log 2 / 32 * Real.sqrt N / Real.log N =
      Real.sqrt N * Real.log 2 / (32 * Real.log N) := by ring
  rw [h_div_eq]
  have h_split : (N : ℝ) / 2 + Real.sqrt N * Real.log 2 / (32 * Real.log N) =
      ((N : ℝ) + Real.sqrt N * Real.log 2 / (16 * Real.log N)) / 2 := by
    field_simp; ring
  rw [h_split, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-! ### Improved headline: `f(N) ≥ N/2 + Ω(N / log N)` via large-prime doubles.

The `LargePrimeDoubles.lean` construction provides a *direct* family
`{2p : p prime, p > √N, 2p ≤ N}` which contributes Θ(N / log N) elements
(vs the Θ(√N / log N) from the safe-prime construction).

Combined with `primeCounting_ge_chebyshev` applied at `K = N/2`, this
yields a strictly better lower bound `f(N) ≥ N/2 + Ω(N / log N)` — a
√N times improvement over `exists_pairFree_polynomial_improvement`.

The composition (Real-valued cast + algebra) is symbolically heavy; the
key structural pieces are already in `LargePrimeDoubles.lean`
(`exists_pairFree_card_ge_primeCounting_diff`) and `primeCounting_ge_chebyshev`
above. The detailed asymptotic is left for follow-up. -/

/-- `Nat.div_2` tends to infinity as N → ∞. (Useful when composing
`primeCounting_ge_chebyshev` at K = N/2.) -/
theorem tendsto_div_2_atTop :
    Filter.Tendsto (fun N : ℕ => N / 2) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr (fun M => ?_)
  refine ⟨2 * M, fun N hN => ?_⟩
  omega

/-- Specialisation of `primeCounting_ge_chebyshev` at `K = N / 2`. -/
theorem primeCounting_at_half_ge_chebyshev :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((N / 2 : ℕ) : ℝ) * Real.log 2 / (2 * Real.log (N / 2 : ℕ)) ≤
        (Nat.primeCounting (N / 2 : ℕ) : ℝ) :=
  tendsto_div_2_atTop.eventually primeCounting_ge_chebyshev

/-- `(N/2 : ℕ → ℝ) ≥ N/2 - 1` (the Nat division loses at most 1 in ℝ). -/
private lemma natDiv_2_ge {N : ℕ} : (N : ℝ) / 2 - 1 ≤ ((N / 2 : ℕ) : ℝ) := by
  have h : (N / 2 : ℕ) * 2 + 1 ≥ N := by omega
  have h_R : ((N / 2 : ℕ) : ℝ) * 2 + 1 ≥ N := by exact_mod_cast h
  linarith

/-- For `N ≥ 4`, `Real.log (N / 2 : ℕ) ≤ Real.log N`. -/
private lemma log_natDiv_2_le {N : ℕ} (hN : 4 ≤ N) :
    Real.log (N / 2 : ℕ) ≤ Real.log N := by
  apply Real.log_le_log
  · have : 2 ≤ N / 2 := by omega
    exact_mod_cast (show (0 : ℕ) < N / 2 from by omega)
  · exact_mod_cast Nat.div_le_self N 2

/-- `(Nat.sqrt N + 2 : ℕ → ℝ) ≤ Real.sqrt N + 2`. -/
private lemma sqrtN_plus_2_le {N : ℕ} :
    ((Nat.sqrt N + 2 : ℕ) : ℝ) ≤ Real.sqrt N + 2 := by
  have h_R : ((Nat.sqrt N : ℕ) : ℝ)^2 ≤ (N : ℝ) := by exact_mod_cast Nat.sqrt_le' N
  have hSqrt_nn : (0 : ℝ) ≤ ((Nat.sqrt N : ℕ) : ℝ) := by positivity
  have h_eq : ((Nat.sqrt N : ℕ) : ℝ) = Real.sqrt (((Nat.sqrt N : ℕ) : ℝ)^2) :=
    (Real.sqrt_sq hSqrt_nn).symm
  push_cast
  rw [h_eq]
  have h_R_nn : (0 : ℝ) ≤ N := by positivity
  have : Real.sqrt (((Nat.sqrt N : ℕ) : ℝ)^2) ≤ Real.sqrt N := Real.sqrt_le_sqrt h_R
  linarith

/-- `Nat.primeCounting (Nat.sqrt N + 2) ≤ Nat.sqrt N + 2`. -/
private lemma primeCounting_le_self (n : ℕ) : Nat.primeCounting n ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have h : Nat.primesLE n ⊆ Finset.Icc 1 n := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.one_lt.le, hp.1⟩
  calc (Nat.primesLE n).card
      ≤ (Finset.Icc 1 n).card := Finset.card_le_card h
    _ = n := by rw [Nat.card_Icc]; omega

/-- For any `ε > 0`, eventually `Real.log N + Real.sqrt N ≤ ε · N / Real.log N`. -/
private lemma sqrt_le_eps_N_div_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, Real.sqrt N ≤ ε * (N / Real.log N) := by
  -- log N ≤ (ε/2) √N eventually ⇒ √N log N ≤ (ε/2) N ⇒ √N ≤ (ε/2) N/log N
  -- (using log N > 0 eventually).
  have h_eps2 : 0 < ε / 2 := by linarith
  filter_upwards [log_le_eps_sqrt_eventually h_eps2, Filter.eventually_ge_atTop 2]
    with N hlog hN2
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from by omega)
  have hlogN_pos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N from by omega))
  have hsqrtN_nn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  -- √N · log N ≤ (ε/2) · N (since log N ≤ (ε/2) √N and √N · √N = N).
  have h_sqsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (le_of_lt hN_pos)
  have h_mul : Real.sqrt N * Real.log N ≤ Real.sqrt N * (ε / 2 * Real.sqrt N) := by
    apply mul_le_mul_of_nonneg_left hlog hsqrtN_nn
  have h_mul' : Real.sqrt N * (ε / 2 * Real.sqrt N) = ε / 2 * N := by
    rw [show Real.sqrt N * (ε / 2 * Real.sqrt N) =
        ε / 2 * (Real.sqrt N * Real.sqrt N) from by ring, h_sqsq]
  -- √N ≤ (ε/2) · N / log N · 2 = ε · N / log N? Let me redo.
  -- We have √N log N ≤ (ε/2) N. Divide both sides by log N:
  -- √N ≤ (ε/2) N / log N ≤ ε N / log N (since ε/2 ≤ ε).
  have h_div : Real.sqrt N ≤ (ε / 2) * N / Real.log N := by
    rw [le_div_iff₀ hlogN_pos]
    linarith
  have h_le : (ε / 2) * N / Real.log N ≤ ε * (N / Real.log N) := by
    rw [show ε * (N / Real.log N) = ε * N / Real.log N from by ring]
    apply div_le_div_of_nonneg_right _ hlogN_pos.le
    nlinarith
  linarith

/-! ### Nat-side asymptotic via `largePrimeDoubles`. -/

/-- `Nat.primeCounting (Nat.sqrt N + 2)` is eventually `≤ Nat.primeCounting (N / 2) / 2`.
This is the key qualitative fact: as `N → ∞`, the "small-prime correction"
`π(√N + 2) = O(√N)` becomes negligible compared to `π(N/2) ~ N/log N`. -/
theorem primeCounting_sqrt_le_half_primeCounting_div_2 :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * Nat.primeCounting (Nat.sqrt N + 2) ≤ Nat.primeCounting (N / 2) := by
  filter_upwards
    [primeCounting_at_half_ge_chebyshev,
     log_le_eps_sqrt_eventually (show (0 : ℝ) < Real.log 2 / 32 by positivity),
     log_le_eps_id_eventually (show (0 : ℝ) < Real.log 2 / 64 by positivity),
     Filter.eventually_ge_atTop 16]
    with N h_cheb h_log_sqrt h_log_id hN16
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from by omega)
  have hN_ge_16 : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hlogN_pos : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N from by omega))
  have hsqrtN_nn : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hN2_pos : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N / 2 from by omega)
  have hlogN2_pos : 0 < Real.log (N / 2 : ℕ) := by
    apply Real.log_pos
    have : 2 ≤ N / 2 := by omega
    exact_mod_cast this
  have h_log_N2_le : Real.log (N / 2 : ℕ) ≤ Real.log N :=
    log_natDiv_2_le (by omega : 4 ≤ N)
  have h_natDiv : (N : ℝ) / 2 - 1 ≤ ((N / 2 : ℕ) : ℝ) := natDiv_2_ge
  -- Bound 4 √N log N + 8 log N ≤ N log 2 / 4.
  have h_4sqrt_log : 4 * Real.sqrt N * Real.log N ≤ (N : ℝ) * Real.log 2 / 8 := by
    have h1 : Real.sqrt N * Real.log N ≤ Real.sqrt N * (Real.log 2 / 32 * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left h_log_sqrt hsqrtN_nn
    have h2 : Real.sqrt N * (Real.log 2 / 32 * Real.sqrt N) = Real.log 2 / 32 * N := by
      rw [show Real.sqrt N * (Real.log 2 / 32 * Real.sqrt N) =
        Real.log 2 / 32 * (Real.sqrt N * Real.sqrt N) from by ring]
      rw [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ N)]
    linarith
  have h_8_log : 8 * Real.log N ≤ (N : ℝ) * Real.log 2 / 8 := by
    have : Real.log N ≤ Real.log 2 / 64 * N := h_log_id
    linarith
  -- Combine into the target inequality.
  have h_target : 2 * (Real.sqrt N + 2) * (2 * Real.log (N / 2 : ℕ)) ≤
      ((N / 2 : ℕ) : ℝ) * Real.log 2 := by
    calc 2 * (Real.sqrt N + 2) * (2 * Real.log (N / 2 : ℕ))
        = 4 * (Real.sqrt N + 2) * Real.log (N / 2 : ℕ) := by ring
      _ ≤ 4 * (Real.sqrt N + 2) * Real.log N := by
          apply mul_le_mul_of_nonneg_left h_log_N2_le
          positivity
      _ = 4 * Real.sqrt N * Real.log N + 8 * Real.log N := by ring
      _ ≤ (N : ℝ) * Real.log 2 / 8 + (N : ℝ) * Real.log 2 / 8 := by linarith
      _ = (N : ℝ) * Real.log 2 / 4 := by ring
      _ ≤ ((N : ℝ) / 2 - 1) * Real.log 2 := by nlinarith [hlog2_pos]
      _ ≤ ((N / 2 : ℕ) : ℝ) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right h_natDiv (le_of_lt hlog2_pos)
  have h_two_sqrt_le : 2 * (Real.sqrt N + 2) ≤
      ((N / 2 : ℕ) : ℝ) * Real.log 2 / (2 * Real.log (N / 2 : ℕ)) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * Real.log (N / 2 : ℕ))]
    linarith
  have h_pi_sqrt_R : ((Nat.primeCounting (Nat.sqrt N + 2) : ℕ) : ℝ) ≤
      Real.sqrt N + 2 := by
    calc ((Nat.primeCounting (Nat.sqrt N + 2) : ℕ) : ℝ)
        ≤ ((Nat.sqrt N + 2 : ℕ) : ℝ) := by
          exact_mod_cast primeCounting_le_self (Nat.sqrt N + 2)
      _ ≤ Real.sqrt N + 2 := sqrtN_plus_2_le
  have h_R : (2 * Nat.primeCounting (Nat.sqrt N + 2) : ℝ) ≤
      (Nat.primeCounting (N / 2) : ℝ) := by
    calc 2 * (Nat.primeCounting (Nat.sqrt N + 2) : ℝ)
        ≤ 2 * (Real.sqrt N + 2) := by linarith
      _ ≤ ((N / 2 : ℕ) : ℝ) * Real.log 2 / (2 * Real.log (N / 2 : ℕ)) := h_two_sqrt_le
      _ ≤ (Nat.primeCounting (N / 2) : ℝ) := h_cheb
  exact_mod_cast h_R

/-- **Nat-side polynomial improvement headline**: for all sufficiently large
`N`, there is a pair-free `A ⊆ [1, N]` with
`|A| ≥ (N + 1) / 2 + Nat.primeCounting (N / 2) / 2`.

This is a clean Nat-side statement of the lower bound improvement.
By PNT-like estimates, `Nat.primeCounting (N / 2) ~ N / (2 log N)`,
so this is asymptotically `f(N) ≥ N / 2 + Ω(N / log N)`. -/
theorem exists_pairFree_polynomial_improvement_nat :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
        (N + 1) / 2 + Nat.primeCounting (N / 2) / 2 ≤ A.card := by
  filter_upwards [primeCounting_sqrt_le_half_primeCounting_div_2]
    with N h_pi_le
  obtain ⟨A, hAsub, hApf, hAcard⟩ := exists_pairFree_card_ge_primeCounting_diff N
  refine ⟨A, hAsub, hApf, ?_⟩
  omega

end UnitFractionPairs
