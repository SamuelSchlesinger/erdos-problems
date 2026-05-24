/-
# Chebyshev-Bounded Safe Prime Set for #327

This file builds a *concrete* `SafePrimeSet` whose cardinality admits a
Chebyshev-style lower bound. By restricting to primes `p ≡ 3 (mod 4)`,
the pairwise-sum condition `p + q ≠ 2^d` becomes automatic: any two such
primes sum to `≡ 2 (mod 4)`, which is divisible by `2` but not by `4`,
hence cannot equal `2^d` for `d ≥ 2`; and the only `d ∈ {0, 1}` cases are
trivially ruled out by `p + q ≥ 22`.

This *bypasses* the greedy pairwise filter used in `safePrimesUpTo K`,
trading a (potentially) smaller prime set for a count that is directly
amenable to Chebyshev's prime-counting bounds: one only needs to lower
bound `π_{4,3}(K)` (the count of primes `≡ 3 mod 4` up to `K`), minus the
Mersenne exclusions, which is `O(log K)`.

The pairwise lemma `chebyshev_pair_not_pow2` is the technical core; the
SafePrimeSet construction `chebyshevSafePrimeSet K` then composes with
the abstract reduction `exists_pairFree_card_ge_abstract` to give the
quantitative form of the lower bound.
-/

import Erdos.UnitFractionPairs.SafePrimes

namespace UnitFractionPairs

/-! ### The Chebyshev-friendly safe prime set. -/

/-- Decidable form of the non-Mersenne predicate (bounded `d` quantifier). -/
private def NotMersenneBounded (p : ℕ) : Prop :=
  ∀ d ∈ Finset.Ioc 0 (Nat.log 2 (p + 2)), p + 1 ≠ 2 ^ d

instance (p : ℕ) : Decidable (NotMersenneBounded p) := by
  unfold NotMersenneBounded; infer_instance

/-- The Chebyshev-friendly safe prime set: doubly-safe primes `p ∈ [11, K]`
with `p ≡ 3 (mod 4)`. The `≡ 3 (mod 4)` condition automatically secures
the pairwise-sum requirement (any two such primes sum to `≡ 2 mod 4`), so
no greedy filter is needed. -/
def chebyshevSafePrimeSet (K : ℕ) : Finset ℕ :=
  (Finset.Icc 11 K).filter fun p =>
    Nat.Prime p ∧ p % 4 = 3 ∧ NotMersenneBounded p

/-- The Chebyshev-friendly safe prime set is bounded by `K`. -/
theorem chebyshevSafePrimeSet_le (K : ℕ) :
    ∀ p ∈ chebyshevSafePrimeSet K, p ≤ K := by
  intro p hp
  simp only [chebyshevSafePrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  exact hp.1.2

/-! ### Pairwise sums of primes `≡ 3 (mod 4)` are not powers of 2. -/

/-- The key arithmetic fact: if `p ≡ q ≡ 3 (mod 4)` and both are `≥ 11`,
then `p + q ≡ 2 (mod 4)`, so `p + q` is not a power of `2`. -/
private lemma threeMod4_pair_not_pow2 {p q : ℕ}
    (hp : p % 4 = 3) (hq : q % 4 = 3) (hp_ge : 11 ≤ p) (hq_ge : 11 ≤ q)
    (d : ℕ) : p + q ≠ 2 ^ d := by
  intro heq
  -- `p + q ≡ 6 ≡ 2 (mod 4)`.
  have hpq_mod : (p + q) % 4 = 2 := by omega
  match d with
  | 0 => -- `2^0 = 1 < 22 ≤ p + q`.
    simp [pow_zero] at heq; omega
  | 1 => -- `2^1 = 2 < 22 ≤ p + q`.
    simp [pow_one] at heq; omega
  | (k + 2) =>
    -- `2^(k+2) = 4 · 2^k`, so `(p+q) % 4 = 0`, contradicting `2`.
    have hmod0 : (2 ^ (k + 2)) % 4 = 0 := by
      have h : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by ring
      rw [h, Nat.mul_mod_right]
    rw [heq] at hpq_mod
    omega

/-! ### `chebyshevSafePrimeSet K` is a `SafePrimeSet`. -/

/-- For a prime `p ≡ 3 (mod 4)` with `p ≥ 11`, the non-Fermat condition
`1 + 2^d ≠ p` for all `d ≥ 1` holds automatically: `1 + 2^d` is `≡ 1 (mod 4)`
for `d ≥ 2` (so `≠ 3 (mod 4)`), and `1 + 2 = 3 ≠ p` since `p ≥ 11`. -/
private lemma threeMod4_not_fermat {p : ℕ} (hp : p % 4 = 3) (hp_ge : 11 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) : 1 + 2 ^ d ≠ p := by
  intro heq
  match d with
  | 1 => -- `1 + 2 = 3 ≠ p` (since p ≥ 11).
    simp [pow_one] at heq; omega
  | (k + 2) =>
    -- `1 + 2^(k+2) ≡ 1 (mod 4)`, contradicting `p ≡ 3 (mod 4)`.
    have hmod : (1 + 2 ^ (k + 2)) % 4 = 1 := by
      have h : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by ring
      rw [h]; omega
    rw [heq] at hmod
    omega

/-- The Chebyshev-friendly set, with `K ≥ 11`, is a `SafePrimeSet`. -/
theorem chebyshevSafePrimeSet_isSafePrimeSet (K : ℕ) :
    SafePrimeSet (chebyshevSafePrimeSet K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- prime
  · intro p hp
    simp only [chebyshevSafePrimeSet, Finset.mem_filter] at hp
    exact hp.2.1
  -- odd: `p ≡ 3 (mod 4) ⇒ p % 2 = 1`.
  · intro p hp
    simp only [chebyshevSafePrimeSet, Finset.mem_filter] at hp
    have : p % 4 = 3 := hp.2.2.1
    omega
  -- not_fermat: from `threeMod4_not_fermat`.
  · intro p hp d hd
    simp only [chebyshevSafePrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
    exact threeMod4_not_fermat hp.2.2.1 hp.1.1 d hd
  -- not_mersenne: from the bounded `NotMersenneBounded` predicate, extended via
  -- the standard "for large enough `d`, `p + 1 < 2^d`" argument.
  · intro p hp d hd
    simp only [chebyshevSafePrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
    intro heq
    have hp_ge : 11 ≤ p := hp.1.1
    by_cases hd_le : d ≤ Nat.log 2 (p + 2)
    · exact hp.2.2.2 d (Finset.mem_Ioc.mpr ⟨hd, hd_le⟩) heq
    · push_neg at hd_le
      have hN_pos : 0 < p + 2 := by omega
      have h2d_gt : p + 2 < 2 ^ d :=
        (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hN_pos.ne').mp hd_le
      omega
  -- pairwise_sum: from `threeMod4_pair_not_pow2`.
  · intro p hp q hq _ d
    simp only [chebyshevSafePrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp hq
    exact threeMod4_pair_not_pow2 hp.2.2.1 hq.2.2.1 hp.1.1 hq.1.1 d

/-! ### Sanity check and cardinality reduction. -/

/-- `chebyshevSafePrimeSet 50 = {11, 19, 23, 43, 47}`: excluding Mersenne `31`,
the primes `≡ 3 (mod 4)` in `[11, 50]`. -/
example : chebyshevSafePrimeSet 50 = ({11, 19, 23, 43, 47} : Finset ℕ) := by decide

/-- `chebyshevSafePrimeSet 100` has cardinality `10` (primes `≡ 3 mod 4` in
`[11, 100]` are `11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83`; excluding the
Mersenne `31` leaves `10`). -/
example : (chebyshevSafePrimeSet 100).card = 10 := by decide

/-- The set of primes `≡ 3 (mod 4)` in `[11, K]`, without the Mersenne filter.
This is the "raw" set whose cardinality we lower-bound; `chebyshevSafePrimeSet`
sits between this set (with Mersennes excluded) and this set itself. -/
def primesIn43 (K : ℕ) : Finset ℕ :=
  (Finset.Icc 11 K).filter fun p => Nat.Prime p ∧ p % 4 = 3

/-- The (over-)set of Mersenne candidates `≤ K`: numbers of the form `2^d - 1`
for `d ∈ [1, ⌊log₂(K + 2)⌋]`. Its cardinality is at most `⌊log₂(K + 2)⌋`. -/
def mersenneCandidates (K : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (Nat.log 2 (K + 2))).image (fun d => 2 ^ d - 1)

/-- `mersenneCandidates K` has cardinality at most `⌊log₂(K + 2)⌋`. -/
theorem mersenneCandidates_card_le (K : ℕ) :
    (mersenneCandidates K).card ≤ Nat.log 2 (K + 2) := by
  unfold mersenneCandidates
  calc ((Finset.Ioc 0 (Nat.log 2 (K + 2))).image (fun d => 2 ^ d - 1)).card
      ≤ (Finset.Ioc 0 (Nat.log 2 (K + 2))).card := Finset.card_image_le
    _ = Nat.log 2 (K + 2) := by rw [Nat.card_Ioc]; omega

/-- Every Mersenne prime in `primesIn43 K` lies in `mersenneCandidates K`. -/
private lemma mersenne_in_candidates {K p : ℕ} (hp : p ∈ primesIn43 K)
    {d : ℕ} (hd : 1 ≤ d) (hdeq : p + 1 = 2 ^ d) : p ∈ mersenneCandidates K := by
  simp only [primesIn43, Finset.mem_filter, Finset.mem_Icc] at hp
  have hp_le_K : p ≤ K := hp.1.2
  have hp_lt : p < 2 ^ d := by omega
  have hd_le : d ≤ Nat.log 2 (K + 2) := by
    have h_le : 2 ^ d ≤ K + 2 := by omega
    have := Nat.log_mono_right (b := 2) h_le
    rwa [Nat.log_pow (by norm_num : 1 < 2)] at this
  refine Finset.mem_image.mpr ⟨d, Finset.mem_Ioc.mpr ⟨hd, hd_le⟩, ?_⟩
  omega

/-- The cardinality reduction:
`|primesIn43 K| ≤ |chebyshevSafePrimeSet K| + |mersenneCandidates K|`. -/
theorem chebyshevSafePrimeSet_card_ge (K : ℕ) :
    (primesIn43 K).card ≤ (chebyshevSafePrimeSet K).card + (mersenneCandidates K).card := by
  -- Strategy: every prime in `primesIn43 K` is either in `chebyshevSafePrimeSet K`
  -- or is Mersenne (hence in `mersenneCandidates K`).
  have h_split : primesIn43 K ⊆ chebyshevSafePrimeSet K ∪ mersenneCandidates K := by
    intro p hp
    by_cases hMers : ∃ d, 1 ≤ d ∧ p + 1 = 2 ^ d
    · -- Mersenne case.
      obtain ⟨d, hd_pos, hdeq⟩ := hMers
      exact Finset.mem_union.mpr (Or.inr (mersenne_in_candidates hp hd_pos hdeq))
    · -- Non-Mersenne case: `p ∈ chebyshevSafePrimeSet K`.
      simp only [primesIn43, Finset.mem_filter, Finset.mem_Icc] at hp
      refine Finset.mem_union.mpr (Or.inl ?_)
      simp only [chebyshevSafePrimeSet, Finset.mem_filter, Finset.mem_Icc,
        NotMersenneBounded]
      refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
      intro d hd hdeq
      exact hMers ⟨d, (Finset.mem_Ioc.mp hd).1, hdeq⟩
  calc (primesIn43 K).card
      ≤ (chebyshevSafePrimeSet K ∪ mersenneCandidates K).card :=
        Finset.card_le_card h_split
    _ ≤ (chebyshevSafePrimeSet K).card + (mersenneCandidates K).card :=
        Finset.card_union_le _ _

/-- The headline structural bound: subtracting at most `⌊log₂(K + 2)⌋` Mersennes,
`|chebyshevSafePrimeSet K| ≥ |primesIn43 K| - ⌊log₂(K + 2)⌋`. -/
theorem chebyshevSafePrimeSet_card_ge_primesIn43 (K : ℕ) :
    (primesIn43 K).card ≤ (chebyshevSafePrimeSet K).card + Nat.log 2 (K + 2) :=
  le_trans (chebyshevSafePrimeSet_card_ge K)
    (Nat.add_le_add_left (mersenneCandidates_card_le K) _)

end UnitFractionPairs
