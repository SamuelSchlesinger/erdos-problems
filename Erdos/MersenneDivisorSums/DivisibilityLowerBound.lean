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
divisor theorem), so this replaces the linear lower bound from `Elementary.lean`
with an `n log n` bound up to constants.

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

end MersenneDivisorSums
