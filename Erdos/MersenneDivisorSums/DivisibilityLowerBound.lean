import Erdos.MersenneDivisorSums.Elementary
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.Divisors

/-
# A Divisibility-Driven Lower Bound for Mersenne Divisor Sums

This file upgrades the trivial lower bound `f(n) ≥ n` from `Elementary.lean` to

`f(n) ≥ ∑_{k=1}^{n} τ(k)`,

using the elementary fact that `d ∣ k` implies `(2^d - 1) ∣ (2^k - 1)` (Mathlib's
`Nat.pow_sub_one_dvd_pow_sub_one`). Since `d ↦ 2^d - 1` is strictly monotone, the
map `d ↦ 2^d - 1` embeds the divisors of `k` injectively into the divisors of
`2^k - 1`, so `τ(k) ≤ τ(2^k - 1)`. Summing yields the main inequality.

Asymptotically `∑_{k=1}^{n} τ(k) = n log n + (2γ − 1) n + O(√n)` (Dirichlet's
divisor theorem), so this replaces the linear lower bound with an `n log n`
bound up to constants. The elementary consequence `f(n) ≥ 2n − 1` for `n ≥ 1`
is packaged separately.

Reference: https://www.erdosproblems.com/893
-/
namespace MersenneDivisorSums

open Finset

/-- The map `d ↦ 2^d - 1` is strictly monotone on `ℕ` (using truncated Nat
subtraction). -/
theorem strictMono_pow_two_sub_one :
    StrictMono (fun d : ℕ => 2 ^ d - 1) := by
  intro a b hab
  change 2 ^ a - 1 < 2 ^ b - 1
  have h : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by decide) hab
  have hle : (1 : ℕ) ≤ 2 ^ a := Nat.one_le_pow _ _ (by decide)
  omega

/-- Injectivity of `d ↦ 2^d - 1`. -/
theorem injective_pow_two_sub_one :
    Function.Injective (fun d : ℕ => 2 ^ d - 1) :=
  strictMono_pow_two_sub_one.injective

/-- If `d ∣ k` and `k ≥ 1`, then `2^d - 1` is a positive divisor of `2^k - 1`. -/
theorem pow_two_sub_one_mem_divisors
    {d k : ℕ} (hk : 1 ≤ k) (hdk : d ∣ k) :
    2 ^ d - 1 ∈ (2 ^ k - 1).divisors := by
  rw [Nat.mem_divisors]
  refine ⟨Nat.pow_sub_one_dvd_pow_sub_one _ hdk, ?_⟩
  have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have : 2 ≤ 2 ^ k := by simpa using h1
  omega

/-- **Divisor injection**: for `k ≥ 1`, each divisor `d` of `k` produces a distinct
divisor `2^d - 1` of `2^k - 1`. Hence `τ(k) ≤ τ(2^k - 1)`. -/
theorem card_divisors_le_card_divisors_mersenne {k : ℕ} (hk : 1 ≤ k) :
    k.divisors.card ≤ (2 ^ k - 1).divisors.card := by
  refine Finset.card_le_card_of_injOn (fun d => 2 ^ d - 1) ?_ ?_
  · intro d hd
    have hdvd : d ∣ k := Nat.dvd_of_mem_divisors hd
    exact pow_two_sub_one_mem_divisors hk hdvd
  · exact injective_pow_two_sub_one.injOn

/-- Per-term bound: `τ(k+1) ≤ τ(2^{k+1} - 1) = mersenneDivisorTerm k`. -/
theorem card_divisors_succ_le_mersenneDivisorTerm (k : ℕ) :
    (k + 1).divisors.card ≤ mersenneDivisorTerm k := by
  unfold mersenneDivisorTerm
  exact card_divisors_le_card_divisors_mersenne (by omega)

/-- **Main structural lower bound**: the partial sum of `τ(2^k − 1)` dominates the
classical partial sum of `τ(k)`. Equivalently,
`f(n) ≥ ∑_{k=1}^{n} τ(k)`. -/
theorem divisor_sum_le_mersenneDivisorSum (n : ℕ) :
    ∑ k ∈ Finset.range n, (k + 1).divisors.card ≤ mersenneDivisorSum n := by
  unfold mersenneDivisorSum
  apply Finset.sum_le_sum
  intro k _
  exact card_divisors_succ_le_mersenneDivisorTerm k

/-- Every `2^k - 1` for `k ≥ 2` has at least two divisors (namely `1` and itself,
which differ because `2^k - 1 > 1`). -/
theorem two_le_mersenneDivisorTerm_of_one_le (k : ℕ) (hk : 1 ≤ k) :
    2 ≤ mersenneDivisorTerm k := by
  have h2 : (k + 1).divisors.card ≥ 2 := by
    have : k + 1 ≥ 2 := by omega
    -- divisors of `m ≥ 2` contain `1` and `m`
    have hmem1 : (1 : ℕ) ∈ (k + 1).divisors := by
      rw [Nat.mem_divisors]; refine ⟨one_dvd _, ?_⟩; omega
    have hmemself : (k + 1) ∈ (k + 1).divisors := by
      rw [Nat.mem_divisors]; refine ⟨dvd_rfl, ?_⟩; omega
    have hne : (1 : ℕ) ≠ k + 1 := by omega
    have hsub : ({1, k + 1} : Finset ℕ) ⊆ (k + 1).divisors := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact hmem1
      · rw [Finset.mem_singleton.mp h]; exact hmemself
    have hnot : (1 : ℕ) ∉ ({k + 1} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      exact hne
    calc 2 = ({1, k + 1} : Finset ℕ).card := by
            rw [Finset.card_insert_of_notMem hnot, Finset.card_singleton]
      _ ≤ (k + 1).divisors.card := Finset.card_le_card hsub
  exact le_trans h2 (card_divisors_succ_le_mersenneDivisorTerm k)

/-- **Explicit linear-factor-of-two improvement**: for every `n ≥ 1`,
`f(n) ≥ 2n − 1`. This is an immediate consequence of the divisor-sum bound
together with `τ(k) ≥ 2` for `k ≥ 2`, and already strictly beats the
`f(n) ≥ n` bound from `Elementary.lean`. -/
theorem two_n_sub_one_le_mersenneDivisorSum {n : ℕ} (hn : 1 ≤ n) :
    2 * n - 1 ≤ mersenneDivisorSum n := by
  -- Sum over k < n of `mersenneDivisorTerm k`, splitting off the k = 0 term.
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn) with ⟨m, rfl⟩
  -- Now goal: 2 * (m+1) - 1 ≤ mersenneDivisorSum (m+1).
  -- mersenneDivisorSum (m+1) = mersenneDivisorSum m + mersenneDivisorTerm m,
  -- and we can recurse / sum bound.
  have hsum : mersenneDivisorSum (m + 1)
      = mersenneDivisorTerm 0 + ∑ k ∈ Finset.range m, mersenneDivisorTerm (k + 1) := by
    unfold mersenneDivisorSum
    rw [Finset.sum_range_succ', Nat.add_comm]
  have hk_bound : ∀ k ∈ Finset.range m, 2 ≤ mersenneDivisorTerm (k + 1) := by
    intro k _
    exact two_le_mersenneDivisorTerm_of_one_le (k + 1) (by omega)
  have hsum_bound :
      2 * m ≤ ∑ k ∈ Finset.range m, mersenneDivisorTerm (k + 1) := by
    calc 2 * m = ∑ _k ∈ Finset.range m, (2 : ℕ) := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hk_bound
  have hterm0 : 1 ≤ mersenneDivisorTerm 0 := one_le_mersenneDivisorTerm 0
  calc 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    _ ≤ mersenneDivisorTerm 0 + ∑ k ∈ Finset.range m, mersenneDivisorTerm (k + 1) := by
        have := Nat.add_le_add hterm0 hsum_bound
        omega
    _ = mersenneDivisorSum (m + 1) := hsum.symm

end MersenneDivisorSums
