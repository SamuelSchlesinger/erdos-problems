/-
# Large-prime Doubles: a stronger lower bound for #327

The construction `largePrimeDoubles N := {2p : p prime, p > √N, 2p ≤ N}` is
pair-free and disjoint from `oddNumbersIn N ∪ powersOfTwoIn N`. Combined,
this yields a lower bound

  f(N) ≥ ⌈N/2⌉ + ⌊log₂ N⌋ + |largePrimeDoubles N|.

The size `|largePrimeDoubles N|` is Θ(N / log N) by Chebyshev (`π(N/2) -
π(√N)`), giving f(N) ≥ N/2 + Ω(N / log N) — a √N-times improvement over
the previous `N/2 + Ω(√N / log N)` bound from `PolynomialLowerBound.lean`.

**Key insight.** For a prime `p` with `p(p-2) > N`, the unique odd
"pair partner" of `2p` (which would be `p(p-2)`) lies outside `[1, N]`,
so `2p` cannot pair with any odd number. And for two large primes p, q,
the pair `(2p, 2q)` would require `(p+q) | 2`, impossible since
`p + q ≥ 6`. So the entire family is automatically pair-free — no
greedy filter or Goldbach-sparseness counting is needed.
-/

import Erdos.UnitFractionPairs.Classification
import Erdos.UnitFractionPairs.Density
import Erdos.UnitFractionPairs.LowerBound

namespace UnitFractionPairs

/-! ### Definition and basic properties. -/

/-- The set `{2p : p prime, 2 < p, 2p ≤ N, N < p(p-2)}`.
The last condition ensures the unique odd pair-partner `p(p-2)` lies outside
`[1, N]`. -/
def largePrimeDoubles (N : ℕ) : Finset ℕ :=
  ((Finset.Ioc 2 (N / 2)).filter
    (fun p => Nat.Prime p ∧ N < p * (p - 2))).image (· * 2)

/-- `largePrimeDoubles N ⊆ [1, N]`. -/
theorem largePrimeDoubles_subset_Icc (N : ℕ) :
    largePrimeDoubles N ⊆ Finset.Icc 1 N := by
  intro n hn
  simp only [largePrimeDoubles, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ioc] at hn
  obtain ⟨p, ⟨⟨hp_gt, hp_le⟩, hp_prime, _⟩, rfl⟩ := hn
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · -- 2p ≥ 2·3 = 6 ≥ 1.
    have : 3 ≤ p := by omega
    omega
  · -- 2p ≤ 2 · (N/2) ≤ N.
    have h1 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
    omega

/-! ### Pair-freeness. -/

/-- The key arithmetic: for `p` an odd prime, an odd `a` paired with `2p`
forces `a = p(p-2)`. -/
private lemma odd_partner_of_two_mul_prime {p a : ℕ} (ha : 0 < a)
    (hp_prime : Nat.Prime p) (hp_odd : p % 2 = 1) (ha_odd : a % 2 = 1)
    (hpair : IsUnitFractionPair a (2 * p)) :
    a = p * (p - 2) := by
  -- Set d = gcd(a, 2p). Since a odd, gcd(a, 2) = 1, so d = gcd(a, p) ∈ {1, p}.
  have hp_pos : 0 < p := hp_prime.pos
  have hp_ge : 2 ≤ p := hp_prime.two_le
  have h2p_pos : 0 < 2 * p := by omega
  set d := Nat.gcd a (2 * p) with hd_def
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  -- gcd(a, 2) = 1 (a odd), so d | p.
  have hcop_a2 : Nat.Coprime a 2 := by
    rw [Nat.coprime_two_right]; exact Nat.odd_iff.mpr ha_odd
  have h_d_dvd_p : d ∣ p := by
    have h1 : d ∣ (2 * p) := Nat.gcd_dvd_right a (2 * p)
    -- d | 2p, gcd(d, 2) | gcd(a, 2) = 1, so d odd; hence d | p.
    have h_d_dvd_a : d ∣ a := Nat.gcd_dvd_left a (2 * p)
    have hcop_d2 : Nat.Coprime d 2 :=
      Nat.Coprime.coprime_dvd_left h_d_dvd_a hcop_a2
    have h1' : d ∣ p * 2 := by rw [Nat.mul_comm]; exact h1
    exact hcop_d2.dvd_of_dvd_mul_right h1'
  -- Use sum_dvd_gcd_of_pair: (a/d + 2p/d) | d.
  have h_sum_dvd : (a / d + 2 * p / d) ∣ d :=
    sum_dvd_gcd_of_pair ha h2p_pos hpair
  -- Case on d ∈ {1, p}.
  have h_p_cases : d = 1 ∨ d = p := (Nat.dvd_prime hp_prime).mp h_d_dvd_p
  rcases h_p_cases with hd1 | hdp
  · -- d = 1: then (a + 2p) | 1.
    exfalso
    rw [hd1, Nat.div_one, Nat.div_one] at h_sum_dvd
    have h_le_1 : a + 2 * p ≤ 1 := Nat.le_of_dvd Nat.one_pos h_sum_dvd
    omega
  · -- d = p: then a = p · a' with (a/p + 2) | p.
    rw [hdp] at h_sum_dvd
    have ha_dvd : p ∣ a := hdp ▸ (Nat.gcd_dvd_left a (2 * p))
    obtain ⟨a', rfl⟩ := ha_dvd
    have ha'_pos : 0 < a' := by
      rcases Nat.eq_zero_or_pos a' with h | h
      · subst h; simp at ha
      · exact h
    have h_div_a : p * a' / p = a' := Nat.mul_div_cancel_left a' hp_pos
    have h_div_2p : 2 * p / p = 2 := Nat.mul_div_cancel 2 hp_pos
    rw [h_div_a, h_div_2p] at h_sum_dvd
    -- (a' + 2) | p. Since p prime, a' + 2 = 1 or p. a' + 2 ≥ 3, so a' + 2 = p, a' = p - 2.
    have h_cases : a' + 2 = 1 ∨ a' + 2 = p := (Nat.dvd_prime hp_prime).mp h_sum_dvd
    rcases h_cases with h1 | hp
    · omega
    · -- a' = p - 2, so a = p(p-2).
      have : a' = p - 2 := by omega
      rw [this]

/-- **`largePrimeDoubles N` is pair-free.** -/
theorem pairFree_largePrimeDoubles (N : ℕ) : PairFree (largePrimeDoubles N) := by
  intro x hx y hy hxy hpair
  simp only [largePrimeDoubles, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ioc] at hx hy
  obtain ⟨p, ⟨⟨hp_gt, hp_le⟩, hp_prime, hpN⟩, rfl⟩ := hx
  obtain ⟨q, ⟨⟨hq_gt, hq_le⟩, hq_prime, hqN⟩, rfl⟩ := hy
  have hp_ne_q : p ≠ q := by
    intro h; rw [h] at hxy; exact hxy rfl
  -- (p*2, q*2) for distinct primes p, q > 2. gcd = 2, (p + q) | 2 impossible since p + q ≥ 6.
  have hp_odd : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left (by omega)
  have hq_odd : q % 2 = 1 := hq_prime.eq_two_or_odd.resolve_left (by omega)
  have h_gcd : Nat.gcd (p * 2) (q * 2) = 2 := by
    rw [Nat.gcd_mul_right]
    have : Nat.gcd p q = 1 := (Nat.coprime_primes hp_prime hq_prime).mpr hp_ne_q
    rw [this, Nat.one_mul]
  have h_sum_dvd := sum_dvd_gcd_of_pair (by omega : 0 < p * 2) (by omega : 0 < q * 2) hpair
  rw [h_gcd] at h_sum_dvd
  have h_div_p : p * 2 / 2 = p := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel_left p (by omega : 0 < 2)
  have h_div_q : q * 2 / 2 = q := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel_left q (by omega : 0 < 2)
  rw [h_div_p, h_div_q] at h_sum_dvd
  -- (p + q) | 2 with p, q ≥ 3. So p + q ≥ 6 > 2.
  have h_le_2 : p + q ≤ 2 := Nat.le_of_dvd (by omega) h_sum_dvd
  omega

/-! ### Cross pair-freeness with odd numbers. -/

/-- An odd number cannot pair with `2p` for prime `p > Nat.sqrt N + 1` and `2p ≤ N`,
because the would-be partner `p(p-2)` exceeds `N`. -/
theorem odd_largePrimeDouble_pair_free {N : ℕ} {a : ℕ} (ha : 0 < a) (ha_le : a ≤ N)
    (ha_odd : a % 2 = 1) {x : ℕ} (hx : x ∈ largePrimeDoubles N) :
    ¬IsUnitFractionPair a x := by
  intro hpair
  simp only [largePrimeDoubles, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ioc] at hx
  obtain ⟨p, ⟨⟨hp_gt, hp_le⟩, hp_prime, hpN⟩, rfl⟩ := hx
  have hp_ge : 3 ≤ p := by
    have := hp_prime.two_le; omega
  have hp_odd : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left (by omega)
  -- Use the partner characterization.
  have hpair' : IsUnitFractionPair a (2 * p) := by
    unfold IsUnitFractionPair at *
    obtain ⟨k, hk⟩ := hpair
    refine ⟨k, ?_⟩
    rw [show 2 * p = p * 2 from by ring]; exact hk
  have h_a_eq : a = p * (p - 2) :=
    odd_partner_of_two_mul_prime ha hp_prime hp_odd ha_odd hpair'
  -- a = p(p-2) ≤ N, but hpN: N < p(p-2).
  rw [h_a_eq] at ha_le
  omega

/-! ### Disjointness with odd numbers and powers of 2. -/

theorem disjoint_oddNumbers_largePrimeDoubles (N : ℕ) :
    Disjoint (oddNumbersIn N) (largePrimeDoubles N) := by
  rw [Finset.disjoint_left]
  intro n hn_odd hn_lpd
  simp only [oddNumbersIn, Finset.mem_filter, Finset.mem_Icc] at hn_odd
  simp only [largePrimeDoubles, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ioc] at hn_lpd
  obtain ⟨p, _, rfl⟩ := hn_lpd
  -- p * 2 is even.
  have : (p * 2) % 2 = 0 := by omega
  omega

theorem disjoint_powersOfTwo_largePrimeDoubles (N : ℕ) :
    Disjoint (powersOfTwoIn N) (largePrimeDoubles N) := by
  rw [Finset.disjoint_left]
  intro n hn_pow hn_lpd
  simp only [powersOfTwoIn, Finset.mem_image, Finset.mem_Icc] at hn_pow
  simp only [largePrimeDoubles, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ioc] at hn_lpd
  obtain ⟨k, hk, rfl⟩ := hn_pow
  obtain ⟨p, ⟨⟨hp_gt2, _⟩, hp_prime, _⟩, hpk⟩ := hn_lpd
  -- 2^k = p * 2, so p ∣ 2^k. Since p prime ≥ 3, p ∤ 2^k.
  have hp_dvd_2k : p ∣ 2 ^ k := by
    have : p ∣ p * 2 := ⟨2, rfl⟩
    rw [hpk] at this; exact this
  have h_p_dvd_2 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp_prime hp_dvd_2k
  have : p ≤ 2 := Nat.le_of_dvd (by omega) h_p_dvd_2
  omega

/-! ### Combined construction and cardinality. -/

/-- The combined pair-free set: odd numbers ∪ powers of 2 ∪ `2p` for large primes. -/
def oddPlusPowersOfTwoPlusLargePrimes (N : ℕ) : Finset ℕ :=
  oddPlusPowersOfTwo N ∪ largePrimeDoubles N

/-- The combined set is contained in `[1, N]`. -/
theorem oddPlusPowersOfTwoPlusLargePrimes_subset_Icc (N : ℕ) :
    oddPlusPowersOfTwoPlusLargePrimes N ⊆ Finset.Icc 1 N := by
  intro n hn
  rw [oddPlusPowersOfTwoPlusLargePrimes, Finset.mem_union] at hn
  rcases hn with h | h
  · exact oddPlusPowersOfTwo_subset_Icc N h
  · exact largePrimeDoubles_subset_Icc N h

/-- The combined set is disjoint with itself: oddPlusPowersOfTwo ∩ largePrimeDoubles = ∅. -/
theorem disjoint_oddPlusPowersOfTwo_largePrimeDoubles (N : ℕ) :
    Disjoint (oddPlusPowersOfTwo N) (largePrimeDoubles N) := by
  rw [oddPlusPowersOfTwo, Finset.disjoint_union_left]
  exact ⟨disjoint_oddNumbers_largePrimeDoubles N,
         disjoint_powersOfTwo_largePrimeDoubles N⟩

/-- A power of 2 (with k ≥ 1) cannot pair with `2p` for prime p odd ≥ 3. -/
private theorem powerOfTwo_largePrimeDouble_pair_free {k p : ℕ} (hk : 1 ≤ k)
    (hp_odd : p % 2 = 1) (hp_ge : 3 ≤ p) :
    ¬IsUnitFractionPair (2 ^ k) (p * 2) := by
  intro hpair
  have h_gcd : Nat.gcd (2 ^ k) (p * 2) = 2 := by
    rw [show (2 ^ k : ℕ) = 2 * 2 ^ (k - 1) by rw [← pow_succ']; congr 1; omega]
    rw [show p * 2 = 2 * p from by ring, Nat.gcd_mul_left]
    have h2p_cop : Nat.Coprime 2 p := by
      rw [Nat.coprime_comm, Nat.coprime_two_right]
      exact Nat.odd_iff.mpr hp_odd
    have hcop : Nat.Coprime (2 ^ (k - 1)) p := h2p_cop.pow_left _
    change 2 * Nat.gcd (2 ^ (k - 1)) p = 2
    rw [hcop]
  have h2k_pos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hp2_pos : 0 < p * 2 := by omega
  have h_sum_dvd := sum_dvd_gcd_of_pair h2k_pos hp2_pos hpair
  rw [h_gcd] at h_sum_dvd
  -- 2^k / 2 = 2^(k-1), p * 2 / 2 = p.
  have h_div_2k : 2 ^ k / 2 = 2 ^ (k - 1) := by
    rw [show (2 ^ k : ℕ) = 2 * 2 ^ (k - 1) by rw [← pow_succ']; congr 1; omega]
    rw [Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  have h_div_p2 : p * 2 / 2 = p := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel_left p (by omega : 0 < 2)
  rw [h_div_2k, h_div_p2] at h_sum_dvd
  -- 2^(k-1) + p divides 2. Since 2^(k-1) ≥ 1 and p ≥ 3, sum ≥ 4.
  have h2pow_pos : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  have h_le_2 : 2 ^ (k - 1) + p ≤ 2 := Nat.le_of_dvd (by omega) h_sum_dvd
  omega

/-- **The combined set is pair-free.** -/
theorem pairFree_oddPlusPowersOfTwoPlusLargePrimes (N : ℕ) :
    PairFree (oddPlusPowersOfTwoPlusLargePrimes N) := by
  intro x hx y hy hxy hpair
  rw [oddPlusPowersOfTwoPlusLargePrimes, Finset.mem_union] at hx hy
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · -- both in oddPlusPowersOfTwo
      exact pairFree_oddPlusPowersOfTwo N x hx y hy hxy hpair
    · -- x in oddPlusPowersOfTwo, y in largePrimeDoubles
      rw [oddPlusPowersOfTwo, Finset.mem_union] at hx
      rcases hx with hx_odd | hx_pow
      · -- x odd
        simp only [oddNumbersIn, Finset.mem_filter, Finset.mem_Icc] at hx_odd
        exact odd_largePrimeDouble_pair_free hx_odd.1.1 hx_odd.1.2 hx_odd.2 hy hpair
      · -- x power of 2 paired with 2p
        simp only [powersOfTwoIn, Finset.mem_image, Finset.mem_Icc] at hx_pow
        obtain ⟨k, ⟨hk, _⟩, rfl⟩ := hx_pow
        simp only [largePrimeDoubles, Finset.mem_image, Finset.mem_filter,
          Finset.mem_Ioc] at hy
        obtain ⟨p, ⟨⟨hp_gt2, _⟩, hp_prime, _⟩, rfl⟩ := hy
        have hp_odd : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left (by omega)
        have hp_ge3 : 3 ≤ p := by
          have h2 := hp_prime.two_le
          have : p ≠ 2 := by intro hp_eq2; rw [hp_eq2] at hp_odd; norm_num at hp_odd
          omega
        exact powerOfTwo_largePrimeDouble_pair_free hk hp_odd hp_ge3 hpair
  · rcases hy with hy | hy
    · -- y in oddPlusPowersOfTwo, x in largePrimeDoubles — symmetric.
      rw [oddPlusPowersOfTwo, Finset.mem_union] at hy
      rcases hy with hy_odd | hy_pow
      · simp only [oddNumbersIn, Finset.mem_filter, Finset.mem_Icc] at hy_odd
        exact odd_largePrimeDouble_pair_free hy_odd.1.1 hy_odd.1.2 hy_odd.2 hx
          (pair_symm.mp hpair)
      · simp only [powersOfTwoIn, Finset.mem_image, Finset.mem_Icc] at hy_pow
        obtain ⟨k, ⟨hk, _⟩, rfl⟩ := hy_pow
        simp only [largePrimeDoubles, Finset.mem_image, Finset.mem_filter,
          Finset.mem_Ioc] at hx
        obtain ⟨p, ⟨⟨hp_gt2, _⟩, hp_prime, _⟩, rfl⟩ := hx
        have hp_odd : p % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left (by omega)
        have hp_ge3 : 3 ≤ p := by
          have h2 := hp_prime.two_le
          have : p ≠ 2 := by intro hp_eq2; rw [hp_eq2] at hp_odd; norm_num at hp_odd
          omega
        exact powerOfTwo_largePrimeDouble_pair_free hk hp_odd hp_ge3
          (pair_symm.mp hpair)
    · -- both in largePrimeDoubles
      exact pairFree_largePrimeDoubles N x hx y hy hxy hpair

/-! ### Cardinality. -/

/-- The set of primes in the index: `{p : 2 < p ≤ N/2, p prime, N < p(p-2)}`. -/
def largePrimeIndex (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 2 (N / 2)).filter (fun p => Nat.Prime p ∧ N < p * (p - 2))

/-- `|largePrimeDoubles N| = |largePrimeIndex N|` via the injection `p ↦ 2p`. -/
theorem card_largePrimeDoubles (N : ℕ) :
    (largePrimeDoubles N).card = (largePrimeIndex N).card := by
  unfold largePrimeDoubles largePrimeIndex
  rw [Finset.card_image_of_injOn]
  intro a _ b _ hab
  simp only at hab
  omega

/-- The combined construction has card
`(N + 1) / 2 + ⌊log₂ N⌋ + |largePrimeIndex N|`. -/
theorem card_oddPlusPowersOfTwoPlusLargePrimes (N : ℕ) :
    (oddPlusPowersOfTwoPlusLargePrimes N).card =
      (N + 1) / 2 + Nat.log 2 N + (largePrimeIndex N).card := by
  rw [oddPlusPowersOfTwoPlusLargePrimes,
    Finset.card_union_of_disjoint (disjoint_oddPlusPowersOfTwo_largePrimeDoubles N),
    card_oddPlusPowersOfTwo, card_largePrimeDoubles]

/-- **Headline lower bound**: For every `N`, there is a pair-free `A ⊆ [1, N]`
with `|A| = (N+1)/2 + ⌊log₂ N⌋ + |largePrimeIndex N|`. -/
theorem exists_pairFree_card_ge_largePrime (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      A.card = (N + 1) / 2 + Nat.log 2 N + (largePrimeIndex N).card :=
  ⟨oddPlusPowersOfTwoPlusLargePrimes N,
   oddPlusPowersOfTwoPlusLargePrimes_subset_Icc N,
   pairFree_oddPlusPowersOfTwoPlusLargePrimes N,
   card_oddPlusPowersOfTwoPlusLargePrimes N⟩

/-! ### Sanity check. -/

/-- At `N = 40`, `largePrimeIndex 40 = {11, 13, 17, 19}` — primes in `(2, 20]` with
`N < p(p-2)`. Each of `7·5 = 35 ≤ 40` is excluded; `11·9 = 99 > 40` etc. -/
example : largePrimeIndex 40 = ({11, 13, 17, 19} : Finset ℕ) := by decide

/-- At `N = 40`, the combined construction has card `20 + 5 + 4 = 29`. -/
example : (oddPlusPowersOfTwoPlusLargePrimes 40).card = 29 := by decide

/-! ### `|largePrimeIndex N|` lower bound via `Nat.primeCounting`.

The set `largePrimeIndex N` contains all primes `p` in the dyadic interval
`(Nat.sqrt N + 2, N/2]`, since for `p ≥ Nat.sqrt N + 3` we have
`p(p-2) ≥ (Nat.sqrt N + 1)² + something > N`. This gives the structural bound

  `Nat.primeCounting (N/2) ≤ |largePrimeIndex N| + Nat.primeCounting (Nat.sqrt N + 2)`,

reducing the asymptotic question to standard Chebyshev bounds on `π`. -/

/-- For `p ≥ Nat.sqrt N + 3`, we have `N < p · (p - 2)`. -/
private lemma N_lt_p_mul_p_sub_two {N p : ℕ} (hp : Nat.sqrt N + 3 ≤ p) :
    N < p * (p - 2) := by
  -- (Nat.sqrt N + 1)² > N, so (Nat.sqrt N)² + 2 Nat.sqrt N + 1 > N,
  -- so (Nat.sqrt N)² + 2 Nat.sqrt N ≥ N.
  have h1 : N < (Nat.sqrt N + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have h_lb : (Nat.sqrt N + 3) * (Nat.sqrt N + 1) =
      (Nat.sqrt N + 1) ^ 2 + 2 * (Nat.sqrt N + 1) := by ring
  have h2 : (Nat.sqrt N + 1) ^ 2 + 2 * (Nat.sqrt N + 1) > N := by
    have : (Nat.sqrt N + 1) ^ 2 > N := h1
    omega
  have h3 : (Nat.sqrt N + 3) * (Nat.sqrt N + 1) > N := by rw [h_lb]; exact h2
  have h4 : (Nat.sqrt N + 3) * (Nat.sqrt N + 1) ≤ p * (p - 2) := by
    have hp_ge3 : 3 ≤ p := by omega
    have hp_sub : Nat.sqrt N + 1 ≤ p - 2 := by omega
    exact Nat.mul_le_mul hp hp_sub
  omega

/-- `Nat.primeCounting (N/2) ≤ |largePrimeIndex N| + Nat.primeCounting (Nat.sqrt N + 2)`.

Every prime `p ≤ N/2` is either small (`≤ Nat.sqrt N + 2`, counted by
`primeCounting (Nat.sqrt N + 2)`) or large (`p ≥ Nat.sqrt N + 3 ≥ 3`, so
`2 < p ≤ N/2` and `p(p-2) > N`, i.e., `p ∈ largePrimeIndex N`). -/
theorem primeCounting_le_largePrimeIndex (N : ℕ) :
    Nat.primeCounting (N / 2) ≤
      (largePrimeIndex N).card + Nat.primeCounting (Nat.sqrt N + 2) := by
  -- Use `primesLE` characterization.
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
  -- Show `primesLE (N/2) ⊆ largePrimeIndex N ∪ primesLE (sqrt N + 2)`.
  have h_sub : Nat.primesLE (N / 2) ⊆ largePrimeIndex N ∪ Nat.primesLE (Nat.sqrt N + 2) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    obtain ⟨hp_le, hp_prime⟩ := hp
    by_cases hp_small : p ≤ Nat.sqrt N + 2
    · refine Finset.mem_union_right _ ?_
      rw [Nat.mem_primesLE]
      exact ⟨hp_small, hp_prime⟩
    · push Not at hp_small
      refine Finset.mem_union_left _ ?_
      simp only [largePrimeIndex, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, hp_le⟩, hp_prime, ?_⟩
      · -- 2 < p (since p ≥ Nat.sqrt N + 3 ≥ 3)
        omega
      · exact N_lt_p_mul_p_sub_two (by omega : Nat.sqrt N + 3 ≤ p)
  calc (Nat.primesLE (N / 2)).card
      ≤ (largePrimeIndex N ∪ Nat.primesLE (Nat.sqrt N + 2)).card :=
        Finset.card_le_card h_sub
    _ ≤ (largePrimeIndex N).card + (Nat.primesLE (Nat.sqrt N + 2)).card :=
        Finset.card_union_le _ _

/-- **Asymptotic lower bound via `Nat.primeCounting`**: for every `N`,
`f(N) ≥ (N+1)/2 + ⌊log₂ N⌋ + π(N/2) - π(Nat.sqrt N + 2)`. Combined with
Chebyshev's `π(N/2) ≥ Ω(N/log N)` and the trivial `π(Nat.sqrt N + 2) ≤
Nat.sqrt N + 2 = O(√N)`, this gives `f(N) ≥ N/2 + Ω(N/log N)`. -/
theorem exists_pairFree_card_ge_primeCounting_diff (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      (N + 1) / 2 + Nat.log 2 N + Nat.primeCounting (N / 2) ≤
        A.card + Nat.primeCounting (Nat.sqrt N + 2) := by
  obtain ⟨A, hAsub, hApf, hAcard⟩ := exists_pairFree_card_ge_largePrime N
  refine ⟨A, hAsub, hApf, ?_⟩
  have := primeCounting_le_largePrimeIndex N
  omega

end UnitFractionPairs
