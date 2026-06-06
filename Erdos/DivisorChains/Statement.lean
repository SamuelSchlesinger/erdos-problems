/-
# Erdős Problem 696: divisor chains with `dᵢ₊₁ ≡ 1 (mod dᵢ)`

For a positive integer `n`, Erdős studies two statistics:

* `h n` — the greatest length of a strictly increasing chain of **primes**
  `p₁ < p₂ < ⋯` all dividing `n`, with `pᵢ₊₁ ≡ 1 (mod pᵢ)`;
* `H n` — the same, but allowing arbitrary **integer** divisors `dᵢ ≥ 2` of `n`.

Erdős asked to estimate `h` and `H`, and in particular whether `H n / h n → ∞`
for almost all `n`.  The answer is **no**: both have normal order `Θ(log_* n)`
(the iterated logarithm), so the ratio stays bounded.

This project formalizes a *parsimonious* resolution: to answer the question one
only needs the two outer bounds `log_* n ≪ h n` and `H n ≪ log_* n`, since
`h n ≤ H n` is trivial.  This file fixes the definitions and proves the trivial
inequality, which needs no analysis: every prime chain is an integer chain.

Reference: https://www.erdosproblems.com/696
-/
import Mathlib

namespace DivisorChains

/-- One step of a divisor chain: `a < b` and `b ≡ 1 (mod a)`. -/
def ChainStep (a b : ℕ) : Prop := a < b ∧ b ≡ 1 [MOD a]

/-- `L` is an admissible **integer** divisor chain for `n`: a list of divisors
of `n`, each at least `2`, whose consecutive entries satisfy `ChainStep`. -/
def IsDivChain (n : ℕ) (L : List ℕ) : Prop :=
  (∀ d ∈ L, d ∣ n) ∧ (∀ d ∈ L, 2 ≤ d) ∧ List.IsChain ChainStep L

/-- `L` is an admissible **prime** divisor chain for `n`. -/
def IsPrimeChain (n : ℕ) (L : List ℕ) : Prop :=
  (∀ d ∈ L, d ∣ n) ∧ (∀ p ∈ L, p.Prime) ∧ List.IsChain ChainStep L

/-- A prime chain is in particular an integer chain. -/
theorem IsDivChain.of_isPrimeChain {n : ℕ} {L : List ℕ}
    (hL : IsPrimeChain n L) : IsDivChain n L :=
  ⟨hL.1, fun d hd => (hL.2.1 d hd).two_le, hL.2.2⟩

/-- The set of achievable integer-chain lengths for `n`. -/
def divChainLengths (n : ℕ) : Set ℕ := {k | ∃ L, IsDivChain n L ∧ L.length = k}

/-- The set of achievable prime-chain lengths for `n`. -/
def primeChainLengths (n : ℕ) : Set ℕ := {k | ∃ L, IsPrimeChain n L ∧ L.length = k}

/-- `H n`: longest integer divisor chain of `n`. -/
noncomputable def H (n : ℕ) : ℕ := sSup (divChainLengths n)

/-- `h n`: longest prime divisor chain of `n`. -/
noncomputable def h (n : ℕ) : ℕ := sSup (primeChainLengths n)

/-- The empty list is always a chain, so `0` is an achievable length. -/
theorem zero_mem_divChainLengths (n : ℕ) : 0 ∈ divChainLengths n :=
  ⟨[], ⟨(by intro d hd; cases hd), (by intro d hd; cases hd), List.isChain_nil⟩, rfl⟩

theorem zero_mem_primeChainLengths (n : ℕ) : 0 ∈ primeChainLengths n :=
  ⟨[], ⟨(by intro d hd; cases hd), (by intro d hd; cases hd), List.isChain_nil⟩, rfl⟩

theorem primeChainLengths_subset (n : ℕ) :
    primeChainLengths n ⊆ divChainLengths n := by
  rintro k ⟨L, hL, rfl⟩
  exact ⟨L, IsDivChain.of_isPrimeChain hL, rfl⟩

/-- A `ChainStep` forces the two entries to be coprime: `b ≡ 1 (mod a)` with
`a ≥ 2` gives `gcd a b = 1`.  (Recorded here for the upper-bound argument.) -/
theorem ChainStep.coprime {a b : ℕ} (ha : 2 ≤ a) (hab : ChainStep a b) :
    Nat.Coprime a b := by
  have hmod : b % a = 1 := by
    have h1 : (1 : ℕ) % a = 1 := Nat.mod_eq_of_lt (by omega)
    have h2 := hab.2
    unfold Nat.ModEq at h2
    omega
  unfold Nat.Coprime
  rw [Nat.gcd_rec, hmod]
  exact Nat.gcd_one_left a

/-- For `n ≥ 1`, every element of an integer chain is a divisor of `n` in the
usual `Nat.divisors` sense, so chain lengths are bounded by `τ(n)`. -/
theorem bddAbove_divChainLengths {n : ℕ} (hn : 1 ≤ n) :
    BddAbove (divChainLengths n) := by
  refine ⟨(n.divisors).card, ?_⟩
  rintro k ⟨L, hL, rfl⟩
  have hlt : List.IsChain (· < ·) L := hL.2.2.imp (fun _ _ h => h.1)
  have hpw : List.Pairwise (· < ·) L := List.isChain_iff_pairwise.1 hlt
  have hnodup : L.Nodup := hpw.imp (fun h => ne_of_lt h)
  have hsub : L.toFinset ⊆ n.divisors := by
    intro d hd
    rw [List.mem_toFinset] at hd
    rw [Nat.mem_divisors]
    exact ⟨hL.1 d hd, by omega⟩
  calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (n.divisors).card := Finset.card_le_card hsub

/-- **Trivial direction.** For every positive `n`, `h n ≤ H n`: a prime chain is
an integer chain, so the longest prime chain is no longer than the longest
integer chain. -/
theorem h_le_H {n : ℕ} (hn : 1 ≤ n) : h n ≤ H n :=
  csSup_le_csSup (bddAbove_divChainLengths hn)
    ⟨0, zero_mem_primeChainLengths n⟩ (primeChainLengths_subset n)

/-! ### The iterated logarithm `log_*`

We use the base-2 iterated logarithm; the choice of base only affects
multiplicative constants, which is all the normal-order statement requires. -/

/-- `iterLog k n` applies `Nat.log 2` to `n` exactly `k` times. -/
def iterLog : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => Nat.log 2 (iterLog k n)

/-- The iterated logarithm: the least number of base-2 logs needed to bring `n`
to `≤ 1`. -/
noncomputable def logStar (n : ℕ) : ℕ := sInf {k | iterLog k n ≤ 1}

end DivisorChains
