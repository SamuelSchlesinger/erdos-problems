import Erdos.PrimeTwoPowersExceptional.Statement
import Erdos.PrimeTwoPowersExceptional.Elementary

set_option linter.style.header false

/-!
# Covering systems reduce Erdős Problem 9 to positive density

This file records the *conditional* reduction at the heart of Crocker's 1971
positive-density result for Erdős Problem `#9`.  The full proof of positive
upper density of the exceptional set proceeds by exhibiting a *covering system*:
a finite collection of arithmetic progressions whose union covers `ℤ`, used to
rule out every potential representation `n = p + 2^k + 2^l` along a fixed
residue class `n ≡ a (mod m)`.

We do not formalize the covering system itself here.  Instead, we prove the
*soft direction* that is independent of the arithmetic:

> If some arithmetic progression `{a + k·m : k ∈ ℕ}` (for `m ≥ 1`) consists
> entirely of exceptional numbers from some point onward, then the upper
> density of the exceptional set is positive (in fact at least `1 / (4m)`).

This is the canonical reduction: any covering construction that supplies the
hypothesis of `upperDensityPositive_of_AP_exceptional` immediately closes
Problem `#9`.

Reference: https://www.erdosproblems.com/9
-/

namespace PrimeTwoPowersExceptional

open Finset

/-!
## A.P. counting infrastructure

We work with the explicit arithmetic progression `{a + k·m : 0 ≤ k < L}`,
realised as a `Finset`, and show its cardinality is `L` when `m ≥ 1`.
-/

/-- The first `L` terms of the arithmetic progression `a, a+m, a+2m, …`. -/
def apFinset (a m L : ℕ) : Finset ℕ :=
  (Finset.range L).image (fun k => a + k * m)

lemma apFinset_card {a m L : ℕ} (hm : 1 ≤ m) :
    (apFinset a m L).card = L := by
  have hinj : Function.Injective (fun k => a + k * m) := fun x y hxy => by
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_right hm (by omega)
  rw [apFinset, Finset.card_image_of_injective _ hinj, Finset.card_range]

lemma apFinset_mem {a m L n : ℕ} :
    n ∈ apFinset a m L ↔ ∃ k < L, n = a + k * m := by
  simp [apFinset, Finset.mem_image, Finset.mem_range, eq_comm]

/-!
## The conditional density theorem

The key reduction: if an entire AP (from some point) is exceptional, then the
exceptional set has positive upper density.
-/

/--
**Crocker-style conditional density.**
Suppose there exist `m, a, N₀ ∈ ℕ` with `m ≥ 1` such that every natural number
`n ≥ N₀` with `n ≡ a (mod m)` is exceptional.  Then the upper density of the
exceptional set is positive — in fact at least `1 / (4m)`.

This is the soft (purely combinatorial) half of the Crocker / Erdős covering
argument: once a covering system has produced an arithmetic progression inside
the exceptional set, the density lower bound is automatic.

The proof injects an arithmetic progression of length `≥ 3 M / (4m)` into the
exceptional set inside `[1, M]`, for all sufficiently large `M`.
-/
theorem upperDensityPositive_of_AP_exceptional
    {m a N₀ : ℕ} (hm : 1 ≤ m)
    (hAP : ∀ n : ℕ, N₀ ≤ n → n % m = a % m → Exceptional n) :
    UpperDensityPositive exceptionalSet := by
  refine ⟨(1 : ℝ) / (4 * m), ?_, ?_⟩
  · positivity
  intro N
  -- Pick `M = max N (8 * m * (N₀ + a + m + 1))`, so `M` is large enough.
  set M := max N (8 * m * (N₀ + a + m + 1)) with hM_def
  have hMN : N ≤ M := le_max_left _ _
  have hMlarge : 8 * m * (N₀ + a + m + 1) ≤ M := le_max_right _ _
  have hm_pos : 0 < m := hm
  have hM_pos : 0 < M := by
    have : 1 ≤ 8 * m * (N₀ + a + m + 1) := by nlinarith
    omega
  refine ⟨M, hMN, by omega, ?_⟩
  -- Define a₀ := the first AP element ≥ N₀, with a₀ ≡ a (mod m).
  -- Concretely: a₀ = a + m * ((N₀ + m) / m + 1). This satisfies a₀ ≥ N₀ + 1 ≥ N₀
  -- and a₀ ≡ a (mod m), and a₀ ≤ a + N₀ + 2m.
  set a₀ : ℕ := a + m * ((N₀ + m) / m + 1) with ha₀_def
  have h_eq : (N₀ + m) / m = N₀ / m + 1 := by
    have : N₀ + m = N₀ + 1 * m := by ring
    rw [this, Nat.add_mul_div_right _ _ hm_pos]
  have h_div_le : m * (N₀ / m) ≤ N₀ := by
    have h := Nat.div_mul_le_self N₀ m; nlinarith
  have h_div_gt : N₀ < m * (N₀ / m) + m := by
    have := Nat.div_add_mod N₀ m
    have := Nat.mod_lt N₀ hm_pos
    omega
  have ha₀_lt_bound : a₀ ≤ a + N₀ + 2 * m := by
    rw [ha₀_def, h_eq]; nlinarith
  have ha₀_ge_N₀ : N₀ ≤ a₀ := by
    rw [ha₀_def, h_eq]; nlinarith
  have ha₀_mod : a₀ % m = a % m := by
    rw [ha₀_def, Nat.add_mul_mod_self_left]
  have ha₀_ge_one : 1 ≤ a₀ := by
    rw [ha₀_def]; nlinarith [Nat.le_add_left 1 ((N₀ + m) / m)]
  -- a₀ is small relative to M: 4 * a₀ ≤ M.
  have ha₀_quarter : 4 * a₀ ≤ M := by
    have h_le : 4 * a₀ ≤ 4 * (a + N₀ + 2 * m) := by
      have := ha₀_lt_bound; linarith
    have h_bound : 4 * (a + N₀ + 2 * m) ≤ 8 * m * (N₀ + a + m + 1) := by
      nlinarith
    linarith
  -- Define L = (M - a₀) / m + 1. Element k = 0, …, L-1 maps to a₀ + k*m, all ≤ M.
  set L : ℕ := (M - a₀) / m + 1 with hL_def
  -- All AP elements fit in [1, M].
  set S : Finset ℕ := apFinset a₀ m L with hS_def
  have hS_subset_Icc : ∀ n ∈ S, n ∈ Set.Icc 1 M := by
    intro n hn
    rw [hS_def] at hn
    rcases apFinset_mem.mp hn with ⟨k, hk, rfl⟩
    refine ⟨?_, ?_⟩
    · have : 1 ≤ a₀ := ha₀_ge_one
      omega
    · -- k ≤ L - 1 = (M - a₀)/m, so k * m ≤ (M - a₀)/m * m ≤ M - a₀, so a₀ + k*m ≤ M.
      have hkle : k ≤ (M - a₀) / m := by omega
      have hkm : k * m ≤ (M - a₀) / m * m :=
        Nat.mul_le_mul_right m hkle
      have hdivm : (M - a₀) / m * m ≤ M - a₀ := Nat.div_mul_le_self _ _
      have : k * m ≤ M - a₀ := le_trans hkm hdivm
      omega
  have hS_subset_exc : ∀ n ∈ S, n ∈ exceptionalSet := by
    intro n hn
    rw [hS_def] at hn
    rcases apFinset_mem.mp hn with ⟨k, hk, rfl⟩
    have hge : N₀ ≤ a₀ + k * m := by omega
    have hmod : (a₀ + k * m) % m = a % m := by
      rwa [Nat.add_mul_mod_self_right]
    exact hAP _ hge hmod
  -- Convert to ncard inequality.
  have hfin : (exceptionalSet ∩ Set.Icc 1 M).Finite :=
    (Set.finite_Icc 1 M).subset (fun _ hx => hx.2)
  -- The finset S is contained in `exceptionalSet ∩ Icc 1 M` after coercion.
  have hSsub : (S : Set ℕ) ⊆ exceptionalSet ∩ Set.Icc 1 M := by
    intro n hn
    have : n ∈ S := hn
    exact ⟨hS_subset_exc n this, hS_subset_Icc n this⟩
  have hcard_le : S.card ≤ (exceptionalSet ∩ Set.Icc 1 M).ncard := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hSsub hfin
  have hS_card : S.card = L := apFinset_card hm
  -- Lower bound L.
  have hL_lb : 3 * M ≤ 4 * m * L := by
    have h_div_mod : M - a₀ = m * ((M - a₀) / m) + (M - a₀) % m :=
      (Nat.div_add_mod (M - a₀) m).symm
    have hmod_lt : (M - a₀) % m < m := Nat.mod_lt _ hm_pos
    have hLexp : m * L = m * ((M - a₀) / m) + m := by rw [hL_def]; ring
    have hq := ha₀_quarter
    have h4mL : 4 * m * L = 4 * (m * L) := by ring
    omega
  -- Now translate to reals.
  have hLcard : (L : ℝ) ≤ ((exceptionalSet ∩ Set.Icc 1 M).ncard : ℝ) := by
    have : L ≤ (exceptionalSet ∩ Set.Icc 1 M).ncard := by rwa [← hS_card]
    exact_mod_cast this
  -- Goal: 1/(4m) ≤ countUpTo / M
  unfold countUpTo
  have hMR_pos : (0 : ℝ) < M := by exact_mod_cast hM_pos
  have hmR_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have h_4mL_real : (3 : ℝ) * M ≤ 4 * m * L := by exact_mod_cast hL_lb
  rw [div_le_div_iff₀ (by positivity) hMR_pos, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hLcard (by positivity : (0:ℝ) ≤ 4 * m)]

end PrimeTwoPowersExceptional
