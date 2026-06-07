import Erdos.DivisibilityAvoidingSets.CoprimeSelection

/-!
# Density zero for avoiding sets with unbounded coprime rank

The Erdős–Sárközy density-zero theorem says every infinite avoiding set `A`
(no distinct `a,b,c` with `a ∣ b+c`, `b,c > a`) has natural density `0`.

This file proves the **conditional** form: if the dyadic coprime rank of `A`
tends to infinity (every target rank is eventually realised by a coprime-LCM
core), then `|A ∩ [1,N]| / N → 0`.  The argument is the assembly the positive
route already supports:

* the geometric shell bound `dyadicShell_mass_le_two_mul_geometric_of_coprime`
  gives, at every dyadic scale `k` carrying a coprime core of rank `r`,
  `|A ∩ [2^k, 2^{k+1})| ≤ 2^{k+1} · (3/4)^r`;
* summing shells, `|A ∩ [1,2^K)| ≤ 2^T + 2·(3/4)^R·2^K` once the rank is `≥ R`
  beyond scale `T`;
* hence `limsup_K |A∩[1,2^K)|/2^K ≤ 2·(3/4)^R` for every `R`, and letting
  `R → ∞` forces density `0`.  No *rate* of growth is needed — only that the
  rank is unbounded.  (The reciprocal-summability question is the strictly
  harder "rank grows at least logarithmically" statement.)
-/

namespace DivisibilityAvoidingSets

open Filter

set_option linter.style.header false

/-- An avoiding set has **unbounded dyadic coprime rank** when every target rank
`r` is eventually realised: there is a scale threshold beyond which every dyadic
scale admits a coprime-LCM selection of rank `r`. -/
def UnboundedDyadicCoprimeRank (A : Set ℕ) : Prop :=
  ∀ r : ℕ, ∃ T : ℕ, CoprimeLCMSelectionThreshold A r T

/-- The number of elements of `A` in `[1, 2^K)` is at most the window length. -/
private lemma ncard_inter_Ico_one_le (A : Set ℕ) (K : ℕ) :
    (A ∩ Set.Ico 1 (2 ^ K)).ncard ≤ 2 ^ K := by
  classical
  calc (A ∩ Set.Ico 1 (2 ^ K)).ncard
      ≤ (Set.Ico 1 (2 ^ K)).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Ico _ _)
    _ = (Finset.Ico 1 (2 ^ K)).card := by
        rw [← Finset.coe_Ico, Set.ncard_coe_finset]
    _ = 2 ^ K - 1 := by rw [Nat.card_Ico]
    _ ≤ 2 ^ K := Nat.sub_le _ _

/-- The number of elements of `A` in the `k`-th dyadic shell is at most `2^k`. -/
private lemma ncard_inter_dyadicShell_le (A : Set ℕ) (k : ℕ) :
    (A ∩ dyadicShell k).ncard ≤ 2 ^ k := by
  classical
  calc (A ∩ dyadicShell k).ncard
      ≤ (dyadicShell k).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right (dyadicShell_finite k)
    _ = (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card := by
        unfold dyadicShell
        rw [← Finset.coe_Ico, Set.ncard_coe_finset]
    _ = 2 ^ (k + 1) - 2 ^ k := by rw [Nat.card_Ico]
    _ = 2 ^ k := by have h := pow_succ 2 k; omega

/-- `[1, 2^K)` is the disjoint union of the first `K` dyadic shells, so the
counts add. -/
private lemma decomp (A : Set ℕ) (K : ℕ) :
    (A ∩ Set.Ico 1 (2 ^ K)).ncard
      = ∑ k ∈ Finset.range K, (A ∩ dyadicShell k).ncard := by
  classical
  induction K with
  | zero => simp
  | succ K ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ K := Nat.one_le_two_pow
      have h2 : (2 : ℕ) ^ K ≤ 2 ^ (K + 1) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)
      have hunion : Set.Ico 1 (2 ^ (K + 1))
          = Set.Ico 1 (2 ^ K) ∪ Set.Ico (2 ^ K) (2 ^ (K + 1)) :=
        (Set.Ico_union_Ico_eq_Ico h1 h2).symm
      have hdisj : Disjoint (A ∩ Set.Ico 1 (2 ^ K)) (A ∩ dyadicShell K) := by
        unfold dyadicShell
        exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
          (Set.Ico_disjoint_Ico_same)
      have hset : A ∩ Set.Ico 1 (2 ^ (K + 1))
          = (A ∩ Set.Ico 1 (2 ^ K)) ∪ (A ∩ dyadicShell K) := by
        have hsh : dyadicShell K = Set.Ico (2 ^ K) (2 ^ (K + 1)) := rfl
        rw [hsh, hunion, Set.inter_union_distrib_left]
      have hfin1 : (A ∩ Set.Ico 1 (2 ^ K)).Finite :=
        (Set.finite_Ico _ _).subset Set.inter_subset_right
      have hfin2 : (A ∩ dyadicShell K).Finite :=
        (dyadicShell_finite K).subset Set.inter_subset_right
      rw [hset, Set.ncard_union_eq hdisj hfin1 hfin2, ih, Finset.sum_range_succ]

/-- Real-valued version of `decomp`. -/
private lemma decomp_real (A : Set ℕ) (K : ℕ) :
    ((A ∩ Set.Ico 1 (2 ^ K)).ncard : ℝ)
      = ∑ k ∈ Finset.range K, ((A ∩ dyadicShell k).ncard : ℝ) := by
  rw [decomp, Nat.cast_sum]

/-- A rank-`R` coprime core at scale `k` makes the `k`-th shell geometrically
small: `|A ∩ [2^k,2^{k+1})| ≤ 2·(3/4)^R·2^k`. -/
private lemma shell_count_le {A : Set ℕ} (hA : AvoidingSet A) {k R : ℕ}
    {J : Finset ℕ} (hJ : CoprimeLCMSelection A k R J) :
    ((A ∩ dyadicShell k).ncard : ℝ) ≤ 2 * (3 / 4 : ℝ) ^ R * 2 ^ k := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hJ
  have hb := hA.dyadicShell_mass_le_two_mul_geometric_of_coprime
    (J := J) (m := fun a : ℕ => a) (k := k)
    h1 (fun a ha => lt_of_lt_of_le (by norm_num) (h5 a ha)) h2 h3 h4 h5
  have hpow : (3 / 4 : ℝ) ^ J.card ≤ (3 / 4 : ℝ) ^ R :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h6
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_iff₀ hk] at hb
  calc ((A ∩ dyadicShell k).ncard : ℝ)
      ≤ 2 * (3 / 4 : ℝ) ^ J.card * 2 ^ k := hb
    _ ≤ 2 * (3 / 4 : ℝ) ^ R * 2 ^ k := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hk)
        exact mul_le_mul_of_nonneg_left hpow (by norm_num)

/-- Summing shells: once every scale `≥ T` carries a rank-`R` coprime core,
`|A ∩ [1,2^K)| ≤ 2^T + 2·(3/4)^R·2^K`. -/
private lemma keyBound {A : Set ℕ} (hA : AvoidingSet A) {R T : ℕ}
    (hT : CoprimeLCMSelectionThreshold A R T) {K : ℕ} (hK : T ≤ K) :
    ((A ∩ Set.Ico 1 (2 ^ K)).ncard : ℝ)
      ≤ 2 ^ T + 2 * (3 / 4 : ℝ) ^ R * 2 ^ K := by
  rw [decomp_real A K, ← Finset.sum_range_add_sum_Ico _ hK]
  have hfirst : ∑ k ∈ Finset.range T, ((A ∩ dyadicShell k).ncard : ℝ) ≤ 2 ^ T := by
    calc ∑ k ∈ Finset.range T, ((A ∩ dyadicShell k).ncard : ℝ)
        = ((A ∩ Set.Ico 1 (2 ^ T)).ncard : ℝ) := (decomp_real A T).symm
      _ ≤ 2 ^ T := by exact_mod_cast ncard_inter_Ico_one_le A T
  have hsecond : ∑ k ∈ Finset.Ico T K, ((A ∩ dyadicShell k).ncard : ℝ)
      ≤ 2 * (3 / 4 : ℝ) ^ R * 2 ^ K := by
    have hle : ∑ k ∈ Finset.Ico T K, ((A ∩ dyadicShell k).ncard : ℝ)
        ≤ ∑ k ∈ Finset.Ico T K, 2 * (3 / 4 : ℝ) ^ R * 2 ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨J, hJ⟩ := hT k (Finset.mem_Ico.mp hk).1
      exact shell_count_le hA hJ
    refine hle.trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ k ∈ Finset.Ico T K, (2 : ℝ) ^ k
        ≤ ∑ k ∈ Finset.range K, (2 : ℝ) ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
          · intro i _ _; positivity
      _ = 2 ^ K - 1 := by
          rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; norm_num
      _ ≤ 2 ^ K := by linarith
  linarith [hfirst, hsecond]

/-- **Conditional Erdős–Sárközy density zero.**  If an avoiding set `A` has
unbounded dyadic coprime rank, then `A` has natural density `0`:
`|A ∩ [1,N)| / N → 0`.

Idea: by `keyBound`, for every target rank `R` the count below `2^K` is
`≤ 2^T + 2·(3/4)^R·2^K`, so the density along powers of two is eventually
`≤ 2·(3/4)^R`; sending `R → ∞` kills it.  General `N` is sandwiched between
consecutive powers of two. -/
theorem AvoidingSet.density_zero_of_unboundedDyadicCoprimeRank
    {A : Set ℕ} (hA : AvoidingSet A) (h : UnboundedDyadicCoprimeRank A) :
    Filter.Tendsto (fun N : ℕ => ((A ∩ Set.Ico 1 N).ncard : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose a rank `R` with `4·(3/4)^R < ε/2`
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 8 by linarith)
    (show (3 / 4 : ℝ) < 1 by norm_num)
  obtain ⟨T, hT⟩ := h R
  -- choose a scale `K₀ ≥ T` with `2^T / 2^{K₀} < ε/2`
  obtain ⟨K₀, hK₀T, hK₀⟩ : ∃ K₀, T ≤ K₀ ∧ (2 : ℝ) ^ T / 2 ^ K₀ < ε / 2 := by
    have hhalf : Filter.Tendsto (fun K : ℕ => (2 : ℝ) ^ T / 2 ^ K)
        Filter.atTop (nhds 0) := by
      have hb : Filter.Tendsto (fun K : ℕ => ((1 : ℝ) / 2) ^ K)
          Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hc := hb.const_mul ((2 : ℝ) ^ T)
      simp only [mul_zero] at hc
      refine hc.congr (fun K => ?_)
      rw [one_div, inv_pow, ← div_eq_mul_inv]
    obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.mp hhalf (ε / 2) (by linarith)
    refine ⟨max T K₁, le_max_left _ _, ?_⟩
    have hd := hK₁ (max T K₁) (le_max_right _ _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd
  refine ⟨2 ^ K₀, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by have : 0 < 2 ^ K₀ := by positivity
                         omega
  have hK0K : K₀ ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by norm_num) hn0).2 hn
  set K := Nat.log 2 n with hKdef
  have hlow : 2 ^ K ≤ n := Nat.pow_log_le_self 2 hn0
  have hhigh : n < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hTK1 : T ≤ K + 1 :=
    le_trans hK₀T (le_trans hK0K (Nat.le_succ K))
  have hkey := keyBound hA hT hTK1
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have h2Kpos : (0 : ℝ) < 2 ^ K := by positivity
  -- count(n) ≤ count(2^{K+1})
  have hcount : ((A ∩ Set.Ico 1 n).ncard : ℝ)
      ≤ ((A ∩ Set.Ico 1 (2 ^ (K + 1))).ncard : ℝ) := by
    have hsub : A ∩ Set.Ico 1 n ⊆ A ∩ Set.Ico 1 (2 ^ (K + 1)) :=
      Set.inter_subset_inter (subset_refl A)
        (Set.Ico_subset_Ico_right (le_of_lt hhigh))
    have hfin : (A ∩ Set.Ico 1 (2 ^ (K + 1))).Finite :=
      (Set.finite_Ico _ _).subset Set.inter_subset_right
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  -- f n ≤ count(2^{K+1}) / 2^K
  have hf1 : ((A ∩ Set.Ico 1 n).ncard : ℝ) / n
      ≤ ((A ∩ Set.Ico 1 (2 ^ (K + 1))).ncard : ℝ) / 2 ^ K := by
    gcongr <;> first | exact hcount | exact_mod_cast hlow
  -- count(2^{K+1}) / 2^K ≤ 2^T/2^K + 4·(3/4)^R
  have hf2 : ((A ∩ Set.Ico 1 (2 ^ (K + 1))).ncard : ℝ) / 2 ^ K
      ≤ 2 ^ T / 2 ^ K + 4 * (3 / 4 : ℝ) ^ R := by
    rw [div_le_iff₀ h2Kpos, add_mul, div_mul_cancel₀ _ (ne_of_gt h2Kpos)]
    have heq : 2 * (3 / 4 : ℝ) ^ R * 2 ^ (K + 1) = 4 * (3 / 4 : ℝ) ^ R * 2 ^ K := by
      rw [pow_succ]; ring
    calc ((A ∩ Set.Ico 1 (2 ^ (K + 1))).ncard : ℝ)
        ≤ 2 ^ T + 2 * (3 / 4 : ℝ) ^ R * 2 ^ (K + 1) := hkey
      _ = 2 ^ T + 4 * (3 / 4 : ℝ) ^ R * 2 ^ K := by rw [heq]
  -- 2^T/2^K ≤ 2^T/2^{K₀}
  have hh1 : (2 : ℝ) ^ T / 2 ^ K ≤ 2 ^ T / 2 ^ K₀ := by
    rw [div_eq_mul_one_div (2 ^ T) (2 ^ K), div_eq_mul_one_div (2 ^ T) (2 ^ K₀)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hK0K)
  have hfinal : ((A ∩ Set.Ico 1 n).ncard : ℝ) / n < ε := by
    calc ((A ∩ Set.Ico 1 n).ncard : ℝ) / n
        ≤ 2 ^ T / 2 ^ K + 4 * (3 / 4 : ℝ) ^ R := le_trans hf1 hf2
      _ ≤ 2 ^ T / 2 ^ K₀ + 4 * (3 / 4 : ℝ) ^ R := by linarith [hh1]
      _ < ε := by
          have hb2 : 4 * (3 / 4 : ℝ) ^ R < ε / 2 := by linarith [hR]
          linarith [hK₀, hb2]
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]

end DivisibilityAvoidingSets
