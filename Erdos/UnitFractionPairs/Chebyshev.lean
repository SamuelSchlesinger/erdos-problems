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
    · push Not at hd_le
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

/-! ### Headline: lower bound via the Chebyshev-friendly set.

Combining the abstract reduction `exists_pairFree_card_ge_abstract` with
the Chebyshev safe set gives a pair-free family of size
`(N + 1) / 2 + ⌊log₂ N⌋ + |chebyshevSafePrimeSet K|` whenever `2 K² ≤ N`. -/

/-- **Chebyshev-bound headline**: for `2 K² ≤ N`,
`f(N) ≥ (N + 1) / 2 + ⌊log₂ N⌋ + |chebyshevSafePrimeSet K|`. The point is
that `|chebyshevSafePrimeSet K| = |primesIn43 K| - O(log K)` is amenable to
a Chebyshev-style lower bound, unlike `|safePrimesUpTo K|` which depends on
Goldbach-sparseness counts. -/
theorem exists_pairFree_card_ge_chebyshev {K N : ℕ} (hKN : 2 * K ^ 2 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      (N + 1) / 2 + Nat.log 2 N + (chebyshevSafePrimeSet K).card ≤ A.card :=
  exists_pairFree_card_ge_abstract (chebyshevSafePrimeSet_isSafePrimeSet K)
    (chebyshevSafePrimeSet_le K) hKN

/-- **Chebyshev-bound headline, in terms of `primesIn43 K`**: combining the
previous theorem with the Mersenne-subtraction bound, we get
`f(N) ≥ (N + 1) / 2 + ⌊log₂ N⌋ + |primesIn43 K| - ⌊log₂(K + 2)⌋`. -/
theorem exists_pairFree_card_ge_primesIn43 {K N : ℕ} (hKN : 2 * K ^ 2 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      (N + 1) / 2 + Nat.log 2 N + (primesIn43 K).card ≤
        A.card + Nat.log 2 (K + 2) := by
  obtain ⟨A, hAsub, hApf, hAcard⟩ := exists_pairFree_card_ge_chebyshev hKN
  refine ⟨A, hAsub, hApf, ?_⟩
  have := chebyshevSafePrimeSet_card_ge_primesIn43 K
  omega

/-! ### The parallel `≡ 1 (mod 4)` safe set.

For Chebyshev counting we need a residue class. Either `≡ 1 (mod 4)` or
`≡ 3 (mod 4)` works for the pairwise-sum constraint (both give `p + q ≡ 2
(mod 4)` for two elements in the same class), but the *exclusion direction*
differs: `≡ 3 (mod 4)` requires excluding Mersennes (`2^d - 1`), while
`≡ 1 (mod 4)` requires excluding Fermats (`1 + 2^d` for `d ≥ 2`).

The point of having both is that we can take the *bigger* class — by
pigeonhole on `π(K) = π_{4,1}(K) + π_{4,3}(K) + 1`, at least one class
contains `≥ (π(K) - 1) / 2` primes. Combined with Chebyshev's lower
bound on `π(K)`, this delivers the polynomial improvement past `N / 2`. -/

/-- Decidable form of the non-Fermat predicate (bounded `d` quantifier). -/
private def NotFermatBounded (p : ℕ) : Prop :=
  ∀ d ∈ Finset.Ioc 0 (Nat.log 2 (p + 1)), 1 + 2 ^ d ≠ p

instance (p : ℕ) : Decidable (NotFermatBounded p) := by
  unfold NotFermatBounded; infer_instance

/-- The parallel Chebyshev-friendly safe prime set for `≡ 1 (mod 4)`:
doubly-safe primes `p ∈ [11, K]` with `p ≡ 1 (mod 4)`. -/
def chebyshevSafePrimeSet41 (K : ℕ) : Finset ℕ :=
  (Finset.Icc 11 K).filter fun p =>
    Nat.Prime p ∧ p % 4 = 1 ∧ NotFermatBounded p

/-- The `≡ 1 (mod 4)` safe set is bounded by `K`. -/
theorem chebyshevSafePrimeSet41_le (K : ℕ) :
    ∀ p ∈ chebyshevSafePrimeSet41 K, p ≤ K := by
  intro p hp
  simp only [chebyshevSafePrimeSet41, Finset.mem_filter, Finset.mem_Icc] at hp
  exact hp.1.2

/-- Same pairwise lemma: for `p, q ≡ 1 (mod 4)` both `≥ 11`,
`p + q ≡ 2 (mod 4)`, so `p + q ≠ 2^d`. -/
private lemma oneMod4_pair_not_pow2 {p q : ℕ}
    (hp : p % 4 = 1) (hq : q % 4 = 1) (hp_ge : 11 ≤ p) (hq_ge : 11 ≤ q)
    (d : ℕ) : p + q ≠ 2 ^ d := by
  intro heq
  have hpq_mod : (p + q) % 4 = 2 := by omega
  match d with
  | 0 => simp [pow_zero] at heq; omega
  | 1 => simp [pow_one] at heq; omega
  | (k + 2) =>
    have hmod0 : (2 ^ (k + 2)) % 4 = 0 := by
      have h : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by ring
      rw [h, Nat.mul_mod_right]
    rw [heq] at hpq_mod
    omega

/-- For a prime `p ≡ 1 (mod 4)` with `p ≥ 11`, the non-Mersenne condition
`p + 1 ≠ 2^d` for all `d ≥ 1` holds automatically: `p + 1 ≡ 2 (mod 4)`, so
`p + 1 = 2^d` forces `d = 1`, giving `p = 1` which is not prime. -/
private lemma oneMod4_not_mersenne {p : ℕ} (hp : p % 4 = 1) (hp_ge : 11 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) : p + 1 ≠ 2 ^ d := by
  intro heq
  match d with
  | 1 => simp [pow_one] at heq; omega
  | (k + 2) =>
    have hmod0 : (2 ^ (k + 2)) % 4 = 0 := by
      have h : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by ring
      rw [h, Nat.mul_mod_right]
    rw [← heq] at hmod0
    omega

/-- The `≡ 1 (mod 4)` Chebyshev safe set is a `SafePrimeSet`. -/
theorem chebyshevSafePrimeSet41_isSafePrimeSet (K : ℕ) :
    SafePrimeSet (chebyshevSafePrimeSet41 K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- prime
  · intro p hp
    simp only [chebyshevSafePrimeSet41, Finset.mem_filter] at hp
    exact hp.2.1
  -- odd: `p ≡ 1 (mod 4) ⇒ p % 2 = 1`.
  · intro p hp
    simp only [chebyshevSafePrimeSet41, Finset.mem_filter] at hp
    have : p % 4 = 1 := hp.2.2.1
    omega
  -- not_fermat: from the bounded `NotFermatBounded` predicate, extended via
  -- the standard "for large enough `d`, `1 + 2^d > p`" argument.
  · intro p hp d hd
    simp only [chebyshevSafePrimeSet41, Finset.mem_filter, Finset.mem_Icc] at hp
    intro heq
    have hp_ge : 11 ≤ p := hp.1.1
    by_cases hd_le : d ≤ Nat.log 2 (p + 1)
    · exact hp.2.2.2 d (Finset.mem_Ioc.mpr ⟨hd, hd_le⟩) heq
    · push Not at hd_le
      have hN_pos : 0 < p + 1 := by omega
      have h2d_gt : p + 1 < 2 ^ d :=
        (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hN_pos.ne').mp hd_le
      omega
  -- not_mersenne: from `oneMod4_not_mersenne`.
  · intro p hp d hd
    simp only [chebyshevSafePrimeSet41, Finset.mem_filter, Finset.mem_Icc] at hp
    exact oneMod4_not_mersenne hp.2.2.1 hp.1.1 d hd
  -- pairwise_sum: from `oneMod4_pair_not_pow2`.
  · intro p hp q hq _ d
    simp only [chebyshevSafePrimeSet41, Finset.mem_filter, Finset.mem_Icc] at hp hq
    exact oneMod4_pair_not_pow2 hp.2.2.1 hq.2.2.1 hp.1.1 hq.1.1 d

/-- Sanity check: `chebyshevSafePrimeSet41 100 = {13, 29, 37, 41, 53, 61, 73, 89, 97}`
(primes `≡ 1 mod 4` in `[11, 100]`, excluding Fermat `17`). -/
example : chebyshevSafePrimeSet41 100 = ({13, 29, 37, 41, 53, 61, 73, 89, 97} : Finset ℕ) :=
  by decide

/-! ### Pigeonhole: at least one class has `≥ (π(K) - 4) / 2 - O(log K)` primes. -/

/-- The `≡ 1 (mod 4)` primes in `[11, K]`, paralleling `primesIn43`. -/
def primesIn41 (K : ℕ) : Finset ℕ :=
  (Finset.Icc 11 K).filter fun p => Nat.Prime p ∧ p % 4 = 1

/-- The (over-)set of Fermat candidates: numbers of the form `1 + 2^d` for
`d ∈ [1, ⌊log₂(K + 1)⌋]`. -/
def fermatCandidates (K : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (Nat.log 2 (K + 1))).image (fun d => 1 + 2 ^ d)

theorem fermatCandidates_card_le (K : ℕ) :
    (fermatCandidates K).card ≤ Nat.log 2 (K + 1) := by
  unfold fermatCandidates
  calc ((Finset.Ioc 0 (Nat.log 2 (K + 1))).image (fun d => 1 + 2 ^ d)).card
      ≤ (Finset.Ioc 0 (Nat.log 2 (K + 1))).card := Finset.card_image_le
    _ = Nat.log 2 (K + 1) := by rw [Nat.card_Ioc]; omega

/-- Every Fermat prime in `primesIn41 K` lies in `fermatCandidates K`. -/
private lemma fermat_in_candidates {K p : ℕ} (hp : p ∈ primesIn41 K)
    {d : ℕ} (hd : 1 ≤ d) (hdeq : 1 + 2 ^ d = p) : p ∈ fermatCandidates K := by
  simp only [primesIn41, Finset.mem_filter, Finset.mem_Icc] at hp
  have hp_le_K : p ≤ K := hp.1.2
  have hd_le : d ≤ Nat.log 2 (K + 1) := by
    have h_le : 2 ^ d ≤ K + 1 := by omega
    have := Nat.log_mono_right (b := 2) h_le
    rwa [Nat.log_pow (by norm_num : 1 < 2)] at this
  exact Finset.mem_image.mpr ⟨d, Finset.mem_Ioc.mpr ⟨hd, hd_le⟩, hdeq⟩

/-- Parallel of `chebyshevSafePrimeSet_card_ge_primesIn43`: subtracting at most
`⌊log₂(K + 1)⌋` Fermats, `|chebyshevSafePrimeSet41 K| ≥ |primesIn41 K| - ⌊log₂(K + 1)⌋`. -/
theorem chebyshevSafePrimeSet41_card_ge_primesIn41 (K : ℕ) :
    (primesIn41 K).card ≤ (chebyshevSafePrimeSet41 K).card + Nat.log 2 (K + 1) := by
  have h_split : primesIn41 K ⊆ chebyshevSafePrimeSet41 K ∪ fermatCandidates K := by
    intro p hp
    by_cases hFermat : ∃ d, 1 ≤ d ∧ 1 + 2 ^ d = p
    · -- Fermat case.
      obtain ⟨d, hd_pos, hdeq⟩ := hFermat
      exact Finset.mem_union.mpr (Or.inr (fermat_in_candidates hp hd_pos hdeq))
    · -- Non-Fermat case.
      simp only [primesIn41, Finset.mem_filter, Finset.mem_Icc] at hp
      refine Finset.mem_union.mpr (Or.inl ?_)
      simp only [chebyshevSafePrimeSet41, Finset.mem_filter, Finset.mem_Icc,
        NotFermatBounded]
      refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
      intro d hd hdeq
      exact hFermat ⟨d, (Finset.mem_Ioc.mp hd).1, hdeq⟩
  calc (primesIn41 K).card
      ≤ (chebyshevSafePrimeSet41 K ∪ fermatCandidates K).card :=
        Finset.card_le_card h_split
    _ ≤ (chebyshevSafePrimeSet41 K).card + (fermatCandidates K).card :=
        Finset.card_union_le _ _
    _ ≤ (chebyshevSafePrimeSet41 K).card + Nat.log 2 (K + 1) :=
        Nat.add_le_add_left (fermatCandidates_card_le K) _

/-! ### Decomposition of `Nat.primeCounting` into residue classes mod 4. -/

/-- Every prime `p ≤ K` either lies in `[2, 10]` (at most 4 such primes:
`{2, 3, 5, 7}`) or in `primesIn41 K ∪ primesIn43 K`. This gives
`Nat.primeCounting K ≤ (primesIn41 K).card + (primesIn43 K).card + 4`. -/
theorem primeCounting_le_residue_classes (K : ℕ) :
    Nat.primeCounting K ≤ (primesIn41 K).card + (primesIn43 K).card + 4 := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  -- Split `primesLE K` by `(· ≤ 10)`.
  have h_split := Finset.card_filter_add_card_filter_not
    (s := Nat.primesLE K) (p := fun p => p ≤ 10)
  -- The "small" part has card ≤ 4 (it's contained in `primesLE 10`).
  have h_small : ((Nat.primesLE K).filter (fun p => p ≤ 10)).card ≤ 4 := by
    have h_sub : (Nat.primesLE K).filter (fun p => p ≤ 10) ⊆ Nat.primesLE 10 := by
      intro p hp
      simp only [Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
      exact ⟨hp.2, hp.1.2⟩
    calc _ ≤ (Nat.primesLE 10).card := Finset.card_le_card h_sub
      _ = 4 := by decide
  -- The "big" part is ⊆ `primesIn41 K ∪ primesIn43 K`.
  have h_big_sub : {p ∈ Nat.primesLE K | ¬ p ≤ 10} ⊆ primesIn41 K ∪ primesIn43 K := by
    intro p hp
    simp only [Finset.mem_filter, Nat.mem_primesLE] at hp
    obtain ⟨⟨hp_le, hp_prime⟩, hp_gt10⟩ := hp
    push Not at hp_gt10
    have hp_ge11 : 11 ≤ p := hp_gt10
    have hp_odd : p % 2 = 1 := by
      rcases hp_prime.eq_two_or_odd with h | h
      · omega
      · exact h
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with h | h
    · refine Finset.mem_union_left _ ?_
      simp only [primesIn41, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp_ge11, hp_le⟩, hp_prime, h⟩
    · refine Finset.mem_union_right _ ?_
      simp only [primesIn43, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp_ge11, hp_le⟩, hp_prime, h⟩
  have h_big : {p ∈ Nat.primesLE K | ¬ p ≤ 10}.card ≤
      (primesIn41 K).card + (primesIn43 K).card := by
    calc _ ≤ (primesIn41 K ∪ primesIn43 K).card := Finset.card_le_card h_big_sub
      _ ≤ (primesIn41 K).card + (primesIn43 K).card := Finset.card_union_le _ _
  omega

/-! ### Pigeonhole: max of the two Chebyshev safe sets. -/

/-- The combined cardinality bound: the two Chebyshev safe sets together cover
all primes in `[11, K]`, up to Fermat and Mersenne exclusions:
`|chebyshev41| + |chebyshev43| ≥ π(K) - 4 - ⌊log₂(K+1)⌋ - ⌊log₂(K+2)⌋`. -/
theorem chebyshev_combined_card_ge (K : ℕ) :
    Nat.primeCounting K ≤
      (chebyshevSafePrimeSet41 K).card + (chebyshevSafePrimeSet K).card
        + 4 + Nat.log 2 (K + 1) + Nat.log 2 (K + 2) := by
  have h41 := chebyshevSafePrimeSet41_card_ge_primesIn41 K
  have h43 := chebyshevSafePrimeSet_card_ge_primesIn43 K
  have hsum := primeCounting_le_residue_classes K
  omega

/-- **Pigeonhole consequence**: at least one of `chebyshevSafePrimeSet41 K` and
`chebyshevSafePrimeSet K` has cardinality at least
`(π(K) - 4 - ⌊log₂(K+1)⌋ - ⌊log₂(K+2)⌋) / 2`. -/
theorem chebyshev_max_card_ge (K : ℕ) :
    Nat.primeCounting K ≤
      2 * max (chebyshevSafePrimeSet41 K).card (chebyshevSafePrimeSet K).card
        + 4 + Nat.log 2 (K + 1) + Nat.log 2 (K + 2) := by
  have h := chebyshev_combined_card_ge K
  have hmax : (chebyshevSafePrimeSet41 K).card + (chebyshevSafePrimeSet K).card ≤
      2 * max (chebyshevSafePrimeSet41 K).card (chebyshevSafePrimeSet K).card := by
    rcases le_total (chebyshevSafePrimeSet41 K).card (chebyshevSafePrimeSet K).card with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  omega

/-! ### Final structural bound: `f(N) ≥ N/2 + log N + max(|41|, |43|)`. -/

/-- **Polynomial-improvement structural headline**: for `2 K² ≤ N`,
`f(N) ≥ (N + 1) / 2 + ⌊log₂ N⌋ + max(|chebyshev41|, |chebyshev43|)`.

The max is what makes the bound *Chebyshev-friendly*: by pigeonhole on
residue classes mod 4 (Theorem `chebyshev_max_card_ge`), it is at least
`(π(K) - 4 - 2 ⌊log₂(K+2)⌋) / 2 = Ω(K / log K)` for large `K`. With
`K = ⌊√(N/2)⌋`, this yields the polynomial improvement past `N / 2`. -/
theorem exists_pairFree_card_ge_chebyshev_max {K N : ℕ} (hKN : 2 * K ^ 2 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      (N + 1) / 2 + Nat.log 2 N +
        max (chebyshevSafePrimeSet41 K).card (chebyshevSafePrimeSet K).card ≤ A.card := by
  rcases le_total (chebyshevSafePrimeSet41 K).card (chebyshevSafePrimeSet K).card with h | h
  · -- `chebyshev43` is bigger; use it.
    rw [max_eq_right h]
    exact exists_pairFree_card_ge_chebyshev hKN
  · -- `chebyshev41` is bigger; use it.
    rw [max_eq_left h]
    exact exists_pairFree_card_ge_abstract (chebyshevSafePrimeSet41_isSafePrimeSet K)
      (chebyshevSafePrimeSet41_le K) hKN

/-- **Combined `π(K)`-based bound**: combining the residue-class pigeonhole with
the structural bound, for `2 K² ≤ N`,

  `2 · f(N) ≥ N + 1 + 2 ⌊log₂ N⌋ + π(K) - 4 - ⌊log₂(K+1)⌋ - ⌊log₂(K+2)⌋`.

This is the clean form for a Chebyshev application: any lower bound on
`π(K)` of the form `c · K / log K` yields the corresponding polynomial
improvement `c · √N / (2 log N) - O(log N)` past `N / 2` (after `K = ⌊√(N/2)⌋`). -/
theorem exists_pairFree_card_ge_primeCounting {K N : ℕ} (hKN : 2 * K ^ 2 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      2 * ((N + 1) / 2 + Nat.log 2 N) + Nat.primeCounting K ≤
        2 * A.card + 4 + Nat.log 2 (K + 1) + Nat.log 2 (K + 2) := by
  obtain ⟨A, hAsub, hApf, hAcard⟩ := exists_pairFree_card_ge_chebyshev_max hKN
  refine ⟨A, hAsub, hApf, ?_⟩
  have hmax := chebyshev_max_card_ge K
  omega

end UnitFractionPairs
