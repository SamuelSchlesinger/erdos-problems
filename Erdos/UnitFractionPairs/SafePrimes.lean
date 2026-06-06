/-
# Safe-Prime Families for #327

For each odd prime `p ≥ 7` satisfying

* **Non-Fermat**: `p ≠ 1 + 2^d` for all `d ≥ 1` (equivalently `p ∉ {3, 5, 17, 257, 65537}`),
* **Non-Mersenne**: `p + 1 ≠ 2^d` for all `d ≥ 1` (equivalently `p ∉ {3, 7, 31, 127, …}`),

the family `F_p := {2^α · p : ⌈log₂ p⌉ ≤ α, 2^α · p ≤ N}` joins the
`oddPlusPowersOfTwo` construction without creating any forbidden
unit-fraction pair:

* `safePrime_odd_pair_free` : `(a, 2^α · p)` is not a pair when `a` is odd
  and `2^α ≥ p`. Bezout: `gcd(a + e, a · e) ∣ gcd(a, p)² ≤ p² ≤ e < a + e`.
* `safePrime_powerOfTwo_pair_free` : `(2^α · p, 2^β)` is not a pair, since
  the non-Mersenne condition forbids the only possible same-exponent
  collision `(p + 1) ∣ 2^α`.
* `safePrime_internal_pair_free` : `(2^α · p, 2^β · p)` with `α ≠ β` is
  not a pair, since the non-Fermat condition forbids the only possible
  collision `(1 + 2^{|α - β|}) ∣ p²`.

A single safe prime `p` contributes `Θ(log(N / p))` elements to `F_p`.
With `~ π(√N) ≈ 2 √N / log N` such primes (`p² ≤ N`, doubly safe), if
their same-`α` cross-pair structure cooperates (`p + q` not a small
power of 2), the total contribution is `Θ(√N / log N)` — a polynomial
improvement past the `Θ(log N)` from `oddPlusPowersOfTwoPlusM5`.

This file proves the three building blocks parametrically and lands one
explicit instance, `p = 11`, as a concrete `Θ(log N)` addition. The
multi-prime combination (with cross-`α` conflict handling for prime
pairs `p + q = 2^s`) is the natural next step.
-/
import Erdos.UnitFractionPairs.LowerBound

namespace UnitFractionPairs

/-! ### Parametric safe-prime building blocks. -/

/-- For any odd prime `p` and `α` with `2^α ≥ p`, the pair `(a, 2^α · p)`
is not a unit-fraction pair, for any odd `a > 0`.

Proof via the Bezout-style identity: `gcd(d, a · b) ∣ gcd(d, a) · gcd(d, b)`.
Setting `d = a + 2^α · p`, both `gcd(d, a)` and `gcd(d, 2^α · p)` reduce to
`gcd(a, p)` (since `a` is odd, hence coprime to `2^α`). So `d ∣ gcd(a, p)²`,
which is at most `p²`. But `d = a + 2^α · p ≥ 1 + p² > p²`. -/
theorem safePrime_odd_pair_free {p a : ℕ} (hp_prime : Nat.Prime p)
    (_hp_odd : p % 2 = 1) {α : ℕ} (h_two_ge_p : p ≤ 2 ^ α)
    (ha : 0 < a) (h_a_odd : a % 2 = 1) :
    ¬ IsUnitFractionPair a (2 ^ α * p) := by
  unfold IsUnitFractionPair
  intro hdvd
  -- `gcd(a, 2^α) = 1` (a odd).
  have hgcd_a2alpha : Nat.gcd a (2 ^ α) = 1 := by
    refine Nat.Coprime.pow_right α ?_
    rw [Nat.coprime_two_right, Nat.odd_iff]; exact h_a_odd
  -- gcd(2^α · p, a) = gcd(p, a). Use Bezout to extract gcd(a, p) from the mixed.
  have hgcd_2alpha_p_a : Nat.gcd (2 ^ α * p) a = Nat.gcd p a := by
    apply Nat.dvd_antisymm
    · have h : Nat.gcd a (2 ^ α * p) ∣ Nat.gcd a (2 ^ α) * Nat.gcd a p :=
        gcd_mul_dvd_mul_gcd a (2 ^ α) p
      rw [show Nat.gcd a (2 ^ α) = 1 from hgcd_a2alpha, Nat.one_mul] at h
      rw [Nat.gcd_comm (2 ^ α * p) a, Nat.gcd_comm p a]
      exact h
    · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
      exact (Nat.gcd_dvd_left _ _).trans ⟨2 ^ α, by ring⟩
  -- gcd(a + 2^α p, a) = gcd(2^α p, a) = gcd(p, a).
  have hg1 : Nat.gcd (a + 2 ^ α * p) a = Nat.gcd p a := by
    rw [Nat.add_comm, Nat.gcd_add_self_left]; exact hgcd_2alpha_p_a
  -- gcd(a + 2^α p, 2^α p) = gcd(a, 2^α p) = gcd(a, p).
  have hgcd_a_2alphap : Nat.gcd a (2 ^ α * p) = Nat.gcd a p := by
    rw [Nat.gcd_comm a (2 ^ α * p), hgcd_2alpha_p_a, Nat.gcd_comm]
  have hg2 : Nat.gcd (a + 2 ^ α * p) (2 ^ α * p) = Nat.gcd a p := by
    rw [Nat.gcd_add_self_left]; exact hgcd_a_2alphap
  -- Bezout: gcd(d, a · b) ∣ gcd(d, a) · gcd(d, b).
  set d := a + 2 ^ α * p with hd_def
  have hbez : d.gcd (a * (2 ^ α * p)) ∣ d.gcd a * d.gcd (2 ^ α * p) :=
    gcd_mul_dvd_mul_gcd d a (2 ^ α * p)
  rw [hg1, hg2] at hbez
  have hgcd_eq : d.gcd (a * (2 ^ α * p)) = d := Nat.gcd_eq_left hdvd
  rw [hgcd_eq] at hbez
  rw [show Nat.gcd p a = Nat.gcd a p from Nat.gcd_comm _ _] at hbez
  -- gcd(a, p) divides p, so gcd(a, p) ≤ p.
  set g := Nat.gcd a p with hg_def
  have hg_dvd_p : g ∣ p := Nat.gcd_dvd_right _ _
  have hg_le : g ≤ p := Nat.le_of_dvd hp_prime.pos hg_dvd_p
  have hg2_pos : 0 < g * g := by
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ ha
    positivity
  have hd_le : d ≤ g * g := Nat.le_of_dvd hg2_pos hbez
  -- d = a + 2^α · p ≥ 1 + p · p = 1 + p² (since 2^α ≥ p).
  have h2alphap_ge : p * p ≤ 2 ^ α * p :=
    Nat.mul_le_mul_right p h_two_ge_p
  have hd_ge : 1 + p * p ≤ d := by omega
  nlinarith

/-- For an odd prime `p` that is **non-Mersenne** (i.e., `p + 1 ≠ 2^d`
for any `d ≥ 1`) and `α` with `2^α ≥ p`, the pair `(2^α · p, 2^β)`
is not a unit-fraction pair, for any `β ≥ 1`. -/
theorem safePrime_powerOfTwo_pair_free {p : ℕ} (hp_prime : Nat.Prime p)
    (_hp_odd : p % 2 = 1) (hp_nonMers : ∀ d : ℕ, 1 ≤ d → p + 1 ≠ 2 ^ d)
    {α β : ℕ} (_h_two_ge_p : p ≤ 2 ^ α) (_hβ : 1 ≤ β) :
    ¬ IsUnitFractionPair (2 ^ α * p) (2 ^ β) := by
  unfold IsUnitFractionPair
  intro hdvd
  have hp_pos : 0 < p := hp_prime.pos
  have hp_ge_two : 2 ≤ p := hp_prime.two_le
  rcases lt_trichotomy α β with hαβ | hαβ | hαβ
  · -- α < β. Sum = 2^α · (p + 2^{β-α}); odd factor ≥ p + 2 > p.
    have hpow : 2 ^ β = 2 ^ α * 2 ^ (β - α) := by
      rw [← pow_add]; congr 1; omega
    have hsum : 2 ^ α * p + 2 ^ β = 2 ^ α * (p + 2 ^ (β - α)) := by
      rw [hpow]; ring
    have hprod : 2 ^ α * p * 2 ^ β = 2 ^ α * (p * 2 ^ β) := by ring
    rw [hsum, hprod] at hdvd
    have h2α_pos : 0 < (2 : ℕ) ^ α := Nat.two_pow_pos _
    have hcancel : (p + 2 ^ (β - α)) ∣ p * 2 ^ β :=
      (Nat.mul_dvd_mul_iff_left h2α_pos).mp hdvd
    have hβα_pos : 1 ≤ β - α := by omega
    have hodd_sum : (p + 2 ^ (β - α)) % 2 = 1 := by
      have h2dvd : (2 : ℕ) ∣ 2 ^ (β - α) := dvd_pow_self 2 (by omega)
      omega
    have hcop : Nat.Coprime (p + 2 ^ (β - α)) (2 ^ β) := by
      refine Nat.Coprime.pow_right β ?_
      rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd_sum
    have hcancel_p : (p + 2 ^ (β - α)) ∣ p :=
      hcop.dvd_of_dvd_mul_right hcancel
    have h2_ge_2 : 2 ≤ 2 ^ (β - α) := by
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ (β - α) := Nat.pow_le_pow_right (by norm_num) hβα_pos
    have hgt : p < p + 2 ^ (β - α) := by omega
    have hle : p + 2 ^ (β - α) ≤ p := Nat.le_of_dvd hp_pos hcancel_p
    omega
  · -- α = β. Sum = 2^α (p + 1); the non-Mersenne hypothesis forbids `(p + 1) ∣ 2^α`.
    subst hαβ
    have hsum_eq : 2 ^ α * p + 2 ^ α = 2 ^ α * (p + 1) := by ring
    have hprod_eq : 2 ^ α * p * 2 ^ α = 2 ^ α * (p * 2 ^ α) := by ring
    rw [hsum_eq, hprod_eq] at hdvd
    have h2α_pos : 0 < (2 : ℕ) ^ α := Nat.two_pow_pos _
    have hcancel : (p + 1) ∣ p * 2 ^ α :=
      (Nat.mul_dvd_mul_iff_left h2α_pos).mp hdvd
    have hcop_p : Nat.Coprime (p + 1) p := by
      change Nat.gcd (p + 1) p = 1
      rw [show p + 1 = 1 + p from by ring, Nat.gcd_add_self_left]
      exact Nat.gcd_one_left p
    have hcancel_pow : (p + 1) ∣ 2 ^ α := hcop_p.dvd_of_dvd_mul_left hcancel
    -- (p + 1) > 2 (since p ≥ 2), so it's a nontrivial divisor of 2^α; must be 2^d
    -- for some d ≥ 1. But that contradicts the non-Mersenne hypothesis.
    have hp1_ge_three : 3 ≤ p + 1 := by omega
    have hp1_pos : 0 < p + 1 := by omega
    -- p + 1 ∣ 2^α and 2 ≤ p + 1. So (p+1) is a positive divisor of 2^α.
    -- By `Nat.dvd_prime_pow` (a divisor of 2^α is of the form 2^d for some d ≤ α),
    -- p + 1 = 2^d for some d.
    have hp1_eq : ∃ d : ℕ, d ≤ α ∧ p + 1 = 2 ^ d := by
      have hp1_dvd : p + 1 ∣ 2 ^ α := hcancel_pow
      rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hp1_dvd with ⟨d, hd_le, hd_eq⟩
      exact ⟨d, hd_le, hd_eq⟩
    obtain ⟨d, hd_le, hd_eq⟩ := hp1_eq
    have hd_pos : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
      · rw [hd0] at hd_eq; simp at hd_eq; omega
      · exact hd_pos
    exact hp_nonMers d hd_pos hd_eq
  · -- α > β. Sum = 2^β · (p · 2^{α-β} + 1); odd factor ≥ 2p + 1 > p.
    have hpow : 2 ^ α = 2 ^ β * 2 ^ (α - β) := by
      rw [← pow_add]; congr 1; omega
    have hsum : 2 ^ α * p + 2 ^ β = 2 ^ β * (p * 2 ^ (α - β) + 1) := by
      rw [hpow]; ring
    have hprod : 2 ^ α * p * 2 ^ β = 2 ^ β * (p * 2 ^ α) := by ring
    rw [hsum, hprod] at hdvd
    have h2β_pos : 0 < (2 : ℕ) ^ β := Nat.two_pow_pos _
    have hcancel : (p * 2 ^ (α - β) + 1) ∣ p * 2 ^ α :=
      (Nat.mul_dvd_mul_iff_left h2β_pos).mp hdvd
    have hαβ_pos : 1 ≤ α - β := by omega
    have hodd_sum : (p * 2 ^ (α - β) + 1) % 2 = 1 := by
      have h2dvd : (2 : ℕ) ∣ 2 ^ (α - β) := dvd_pow_self 2 (by omega)
      have : (2 : ℕ) ∣ p * 2 ^ (α - β) := h2dvd.mul_left p
      omega
    have hcop : Nat.Coprime (p * 2 ^ (α - β) + 1) (2 ^ α) := by
      refine Nat.Coprime.pow_right α ?_
      rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd_sum
    have hcancel_p : (p * 2 ^ (α - β) + 1) ∣ p :=
      hcop.dvd_of_dvd_mul_right hcancel
    have h2_ge_2 : 2 ≤ 2 ^ (α - β) := by
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ (α - β) := Nat.pow_le_pow_right (by norm_num) hαβ_pos
    have hge : 2 * p + 1 ≤ p * 2 ^ (α - β) + 1 := by nlinarith
    have hle : p * 2 ^ (α - β) + 1 ≤ p := Nat.le_of_dvd hp_pos hcancel_p
    omega

/-- For distinct odd primes `p, q` whose sum is not a power of 2 (i.e.,
`∀ d ≥ 0, p + q ≠ 2^d`), the pair `(2^α · p, 2^β · q)` is not a
unit-fraction pair, for any `α, β`. The case split is on the relative size
of `α` and `β`; the `α = β` case is where the non-power-of-2 hypothesis
is needed. -/
theorem safePrime_cross_pair_free {p q : ℕ} (hp_prime : Nat.Prime p)
    (hq_prime : Nat.Prime q) (hp_odd : p % 2 = 1) (hq_odd : q % 2 = 1)
    (hpq : p ≠ q) (hpq_sum : ∀ d : ℕ, p + q ≠ 2 ^ d) {α β : ℕ} :
    ¬ IsUnitFractionPair (2 ^ α * p) (2 ^ β * q) := by
  unfold IsUnitFractionPair
  intro hdvd
  have hp_pos : 0 < p := hp_prime.pos
  have hq_pos : 0 < q := hq_prime.pos
  have hp_ge_three : 3 ≤ p := by
    have := hp_prime.two_le
    -- p is odd and ≥ 2 ⇒ p ≥ 3.
    omega
  have hq_ge_three : 3 ≤ q := by
    have := hq_prime.two_le; omega
  have hpq_coprime : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr hpq
  rcases lt_trichotomy α β with hαβ | hαβ | hαβ
  · -- α < β. Sum = 2^α (p + 2^{β-α} q). Odd factor coprime to pq, can't divide it.
    have hpow : 2 ^ β = 2 ^ α * 2 ^ (β - α) := by
      rw [← pow_add]; congr 1; omega
    have hsum : 2 ^ α * p + 2 ^ β * q = 2 ^ α * (p + 2 ^ (β - α) * q) := by
      rw [hpow]; ring
    have hprod : 2 ^ α * p * (2 ^ β * q) = 2 ^ α * (p * (2 ^ β * q)) := by ring
    rw [hsum, hprod] at hdvd
    have h2α_pos : 0 < (2 : ℕ) ^ α := Nat.two_pow_pos _
    have hcancel : (p + 2 ^ (β - α) * q) ∣ p * (2 ^ β * q) :=
      (Nat.mul_dvd_mul_iff_left h2α_pos).mp hdvd
    have hβα_pos : 1 ≤ β - α := by omega
    have hodd_sum : (p + 2 ^ (β - α) * q) % 2 = 1 := by
      have h2dvd : (2 : ℕ) ∣ 2 ^ (β - α) := dvd_pow_self 2 (by omega)
      have h2dvd' : (2 : ℕ) ∣ 2 ^ (β - α) * q := h2dvd.mul_right q
      omega
    have hcop_pow : Nat.Coprime (p + 2 ^ (β - α) * q) (2 ^ β) := by
      refine Nat.Coprime.pow_right β ?_
      rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd_sum
    have hcancel_pq : (p + 2 ^ (β - α) * q) ∣ p * q := by
      have hreq : p * (2 ^ β * q) = 2 ^ β * (p * q) := by ring
      rw [hreq] at hcancel
      exact hcop_pow.dvd_of_dvd_mul_left hcancel
    -- gcd(LHS, p) = gcd(2^{β-α} q, p) = gcd(q, p) = 1.
    -- gcd(LHS, q) = gcd(p, q) = 1.
    have hcop_p : Nat.Coprime (p + 2 ^ (β - α) * q) p := by
      change Nat.gcd (p + 2 ^ (β - α) * q) p = 1
      rw [show p + 2 ^ (β - α) * q = 2 ^ (β - α) * q + p from by ring,
        Nat.gcd_add_self_left]
      refine Nat.Coprime.mul_left ?_ ?_
      · refine Nat.Coprime.pow_left (β - α) ?_
        exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hp_odd)
      · exact hpq_coprime.symm
    have hcop_q : Nat.Coprime (p + 2 ^ (β - α) * q) q := by
      change Nat.gcd (p + 2 ^ (β - α) * q) q = 1
      rw [show p + 2 ^ (β - α) * q = p + q * 2 ^ (β - α) from by ring,
        Nat.gcd_comm, Nat.gcd_add_mul_left_right]
      exact hpq_coprime.symm
    have hcop_pq : Nat.Coprime (p + 2 ^ (β - α) * q) (p * q) :=
      hcop_p.mul_right hcop_q
    have hone : (p + 2 ^ (β - α) * q) ∣ 1 := by
      have : (p + 2 ^ (β - α) * q) ∣ (p * q) * 1 := by rw [Nat.mul_one]; exact hcancel_pq
      exact hcop_pq.dvd_of_dvd_mul_left this
    have hge_three : 3 ≤ p + 2 ^ (β - α) * q := by
      have h2_ge_2 : 2 ≤ 2 ^ (β - α) := by
        calc (2 : ℕ) = 2 ^ 1 := by ring
          _ ≤ 2 ^ (β - α) := Nat.pow_le_pow_right (by norm_num) hβα_pos
      nlinarith
    have : p + 2 ^ (β - α) * q ≤ 1 := Nat.le_of_dvd (by norm_num) hone
    omega
  · -- α = β. Sum = 2^α (p + q). p+q not a power of 2 (by hypothesis).
    subst hαβ
    have hsum : 2 ^ α * p + 2 ^ α * q = 2 ^ α * (p + q) := by ring
    have hprod : 2 ^ α * p * (2 ^ α * q) = 2 ^ α * (2 ^ α * (p * q)) := by ring
    rw [hsum, hprod] at hdvd
    have h2α_pos : 0 < (2 : ℕ) ^ α := Nat.two_pow_pos _
    have hcancel : (p + q) ∣ 2 ^ α * (p * q) :=
      (Nat.mul_dvd_mul_iff_left h2α_pos).mp hdvd
    -- p + q is even; write p + q = 2 * s where s = (p+q)/2.
    have hsum_even : 2 ∣ p + q := by omega
    obtain ⟨s, hs⟩ := hsum_even
    have hs_pos : 0 < s := by have := hp_ge_three; have := hq_ge_three; omega
    -- gcd(p+q, p) = gcd(q, p) = 1, so gcd(s, p) = 1 (s = (p+q)/2 has same odd-part).
    -- Actually it's cleaner: gcd(p+q, pq) = 1 since gcd(p+q, p) = gcd(q,p) = 1 and similarly q.
    have hcop_pq : Nat.Coprime (p + q) (p * q) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · change Nat.gcd (p + q) p = 1
        rw [Nat.add_comm, Nat.gcd_add_self_left]
        exact hpq_coprime.symm
      · change Nat.gcd (p + q) q = 1
        rw [Nat.gcd_add_self_left]
        exact hpq_coprime
    have hcancel_2 : (p + q) ∣ 2 ^ α := by
      have : (p + q) ∣ p * q * 2 ^ α := by
        have hreq : 2 ^ α * (p * q) = p * q * 2 ^ α := by ring
        rw [hreq] at hcancel
        exact hcancel
      exact hcop_pq.dvd_of_dvd_mul_left this
    -- p+q is a positive divisor of 2^α, so p+q = 2^d for some d ≤ α.
    rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hcancel_2 with ⟨d, _, hd_eq⟩
    exact hpq_sum d hd_eq
  · -- α > β. Symmetric to α < β.
    have hpow : 2 ^ α = 2 ^ β * 2 ^ (α - β) := by
      rw [← pow_add]; congr 1; omega
    have hsum : 2 ^ α * p + 2 ^ β * q = 2 ^ β * (p * 2 ^ (α - β) + q) := by
      rw [hpow]; ring
    have hprod : 2 ^ α * p * (2 ^ β * q) = 2 ^ β * (p * (2 ^ α * q)) := by ring
    rw [hsum, hprod] at hdvd
    have h2β_pos : 0 < (2 : ℕ) ^ β := Nat.two_pow_pos _
    have hcancel : (p * 2 ^ (α - β) + q) ∣ p * (2 ^ α * q) :=
      (Nat.mul_dvd_mul_iff_left h2β_pos).mp hdvd
    have hαβ_pos : 1 ≤ α - β := by omega
    have hodd_sum : (p * 2 ^ (α - β) + q) % 2 = 1 := by
      have h2dvd : (2 : ℕ) ∣ 2 ^ (α - β) := dvd_pow_self 2 (by omega)
      have h2dvd' : (2 : ℕ) ∣ p * 2 ^ (α - β) := h2dvd.mul_left p
      omega
    have hcop_pow : Nat.Coprime (p * 2 ^ (α - β) + q) (2 ^ α) := by
      refine Nat.Coprime.pow_right α ?_
      rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd_sum
    have hcancel_pq : (p * 2 ^ (α - β) + q) ∣ p * q := by
      have hreq : p * (2 ^ α * q) = 2 ^ α * (p * q) := by ring
      rw [hreq] at hcancel
      exact hcop_pow.dvd_of_dvd_mul_left hcancel
    have hcop_p : Nat.Coprime (p * 2 ^ (α - β) + q) p := by
      change Nat.gcd (p * 2 ^ (α - β) + q) p = 1
      rw [show p * 2 ^ (α - β) + q = q + p * 2 ^ (α - β) from by ring,
        Nat.gcd_comm, Nat.gcd_add_mul_left_right]
      exact hpq_coprime
    have hcop_q : Nat.Coprime (p * 2 ^ (α - β) + q) q := by
      change Nat.gcd (p * 2 ^ (α - β) + q) q = 1
      rw [Nat.gcd_add_self_left]
      refine Nat.Coprime.mul_left hpq_coprime ?_
      refine Nat.Coprime.pow_left (α - β) ?_
      exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hq_odd)
    have hcop_pq' : Nat.Coprime (p * 2 ^ (α - β) + q) (p * q) :=
      hcop_p.mul_right hcop_q
    have hone : (p * 2 ^ (α - β) + q) ∣ 1 := by
      have : (p * 2 ^ (α - β) + q) ∣ (p * q) * 1 := by rw [Nat.mul_one]; exact hcancel_pq
      exact hcop_pq'.dvd_of_dvd_mul_left this
    have hge_three : 3 ≤ p * 2 ^ (α - β) + q := by
      have h2_ge_2 : 2 ≤ 2 ^ (α - β) := by
        calc (2 : ℕ) = 2 ^ 1 := by ring
          _ ≤ 2 ^ (α - β) := Nat.pow_le_pow_right (by norm_num) hαβ_pos
      nlinarith
    have : p * 2 ^ (α - β) + q ≤ 1 := Nat.le_of_dvd (by norm_num) hone
    omega

/-- Helper for `safePrime_internal_pair_free`, assuming `α < β`. -/
private theorem safePrime_internal_aux {p : ℕ} (hp_prime : Nat.Prime p)
    (hp_nonFerm : ∀ d : ℕ, 1 ≤ d → 1 + 2 ^ d ≠ p) {α β : ℕ} (hαβ : α < β) :
    ¬ IsUnitFractionPair (2 ^ α * p) (2 ^ β * p) := by
  intro hpair
  unfold IsUnitFractionPair at hpair
  have hpow : 2 ^ β = 2 ^ α * 2 ^ (β - α) := by
    rw [← pow_add]; congr 1; omega
  have hsum : 2 ^ α * p + 2 ^ β * p = 2 ^ α * p * (1 + 2 ^ (β - α)) := by
    rw [hpow]; ring
  rw [hsum] at hpair
  have h_pos : 0 < 2 ^ α * p := by
    have := hp_prime.pos; positivity
  have hcancel : (1 + 2 ^ (β - α)) ∣ 2 ^ β * p :=
    (Nat.mul_dvd_mul_iff_left h_pos).mp hpair
  have hβα_pos : 1 ≤ β - α := by omega
  have hodd_sum : (1 + 2 ^ (β - α)) % 2 = 1 := by
    have h2dvd : (2 : ℕ) ∣ 2 ^ (β - α) := dvd_pow_self 2 (by omega)
    omega
  have hcop : Nat.Coprime (1 + 2 ^ (β - α)) (2 ^ β) := by
    refine Nat.Coprime.pow_right β ?_
    rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd_sum
  have hcancel_p : (1 + 2 ^ (β - α)) ∣ p :=
    hcop.dvd_of_dvd_mul_left hcancel
  have hge_three : 3 ≤ 1 + 2 ^ (β - α) := by
    have h2_ge_2 : 2 ≤ 2 ^ (β - α) := by
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ (β - α) := Nat.pow_le_pow_right (by norm_num) hβα_pos
    omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp_prime _ hcancel_p) with h | h
  · omega
  · exact hp_nonFerm (β - α) hβα_pos h

/-- For an odd prime `p` that is **non-Fermat** (i.e., `1 + 2^d ≠ p` for
any `d ≥ 1`), and exponents `α ≠ β`, the pair `(2^α · p, 2^β · p)` is
not a unit-fraction pair. -/
theorem safePrime_internal_pair_free {p : ℕ} (hp_prime : Nat.Prime p)
    (hp_nonFerm : ∀ d : ℕ, 1 ≤ d → 1 + 2 ^ d ≠ p) {α β : ℕ} (hαβ : α ≠ β) :
    ¬ IsUnitFractionPair (2 ^ α * p) (2 ^ β * p) := by
  rcases lt_or_gt_of_ne hαβ with hlt | hgt
  · exact safePrime_internal_aux hp_prime hp_nonFerm hlt
  · intro hpair
    apply safePrime_internal_aux hp_prime hp_nonFerm hgt
    unfold IsUnitFractionPair at hpair ⊢
    have heq_sum : 2 ^ β * p + 2 ^ α * p = 2 ^ α * p + 2 ^ β * p := by ring
    have heq_prod : 2 ^ β * p * (2 ^ α * p) = 2 ^ α * p * (2 ^ β * p) := by ring
    rw [heq_sum, heq_prod]; exact hpair

/-! ### Concrete instance: the `p = 11` family.

`11` is a non-Fermat (`11 ≠ 1 + 2^d` for any `d`: divisors of `121` are
`{1, 11, 121}`, none of the form `1 + 2^d ≥ 3`) and non-Mersenne
(`12 = 4·3`, not a power of 2) odd prime.

The family `F_{11} := {2^α · 11 : α ≥ 4, 2^α · 11 ≤ N}` adds another
`Θ(log N)` elements past `oddPlusPowersOfTwoPlusM5`, with no internal
conflicts (no alternating-exponent restriction needed, unlike `m = 5`). -/

/-- The set `{2^α · 11 : α ≥ 4, 2^α · 11 ≤ N}`. -/
def elevenFamilyIn (N : ℕ) : Finset ℕ :=
  ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 11 ≤ N)).image
    (fun α => 2 ^ α * 11)

private lemma elevenFamily_nonFerm (d : ℕ) (_ : 1 ≤ d) : 1 + 2 ^ d ≠ 11 := by
  -- 1 + 2^d ∈ {3, 5, 9, 17, 33, …}: never 11.
  intro h
  -- 2^d = 10, but 10 is not a power of 2.
  have : 2 ^ d = 10 := by omega
  -- 10 has odd factor 5, so cannot be a power of 2.
  have h5 : (5 : ℕ) ∣ 2 ^ d := by rw [this]; norm_num
  have hcop : Nat.Coprime 5 (2 ^ d) := by
    refine Nat.Coprime.pow_right d ?_; decide
  have : (5 : ℕ) ∣ 1 := by
    have hg : Nat.gcd 5 (2 ^ d) = 5 := Nat.gcd_eq_left h5
    rw [hcop] at hg; omega
  omega

private lemma elevenFamily_nonMers (d : ℕ) (_ : 1 ≤ d) : 11 + 1 ≠ 2 ^ d := by
  -- 12 = 4 · 3 has odd factor 3, not a power of 2.
  intro h
  have h12 : (2 : ℕ) ^ d = 12 := by omega
  have h3 : (3 : ℕ) ∣ 2 ^ d := by rw [h12]; norm_num
  have hcop : Nat.Coprime 3 (2 ^ d) := by
    refine Nat.Coprime.pow_right d ?_; decide
  have : (3 : ℕ) ∣ 1 := by
    have hg : Nat.gcd 3 (2 ^ d) = 3 := Nat.gcd_eq_left h3
    rw [hcop] at hg; omega
  omega

private lemma elevenFamilyIn_exp_ge_four {α : ℕ} (hα : α ∈ Finset.Icc 4 (Nat.log 2 11)) :
    4 ≤ α := (Finset.mem_Icc.mp hα).1

private lemma mem_elevenFamilyIn_iff {N n : ℕ} :
    n ∈ elevenFamilyIn N ↔
      ∃ α : ℕ, 4 ≤ α ∧ 2 ^ α * 11 ≤ N ∧ n = 2 ^ α * 11 := by
  unfold elevenFamilyIn
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨α, ⟨⟨h4, _⟩, hbound⟩, hαn⟩
    exact ⟨α, h4, hbound, hαn.symm⟩
  · rintro ⟨α, h4, hbound, hαn⟩
    refine ⟨α, ⟨⟨h4, ?_⟩, hbound⟩, hαn.symm⟩
    -- 2^α · 11 ≤ N implies 2^α ≤ N, so α ≤ log₂ N.
    have hN_pos : 0 < N := by
      have h2α : 16 ≤ 2 ^ α := by
        calc (16 : ℕ) = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ α := Nat.pow_le_pow_right (by norm_num) h4
      have : 16 ≤ 2 ^ α * 11 := by nlinarith [Nat.two_pow_pos α]
      omega
    have h2α_le : 2 ^ α ≤ N := by
      have : 2 ^ α ≤ 2 ^ α * 11 := by linarith [Nat.two_pow_pos α]
      omega
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hN_pos.ne').mpr h2α_le

/-- The 11-family is internally pair-free. -/
theorem pairFree_elevenFamilyIn (N : ℕ) : PairFree (elevenFamilyIn N) := by
  intro a ha b hb hab hpair
  rw [mem_elevenFamilyIn_iff] at ha hb
  obtain ⟨α, _, _, ha_eq⟩ := ha
  obtain ⟨β, _, _, hb_eq⟩ := hb
  have hαβ : α ≠ β := by
    intro heq
    apply hab
    rw [ha_eq, hb_eq, heq]
  rw [ha_eq, hb_eq] at hpair
  exact safePrime_internal_pair_free (by decide : Nat.Prime 11)
    elevenFamily_nonFerm hαβ hpair

/-! ### Combined construction `oddPlusPowersOfTwo ∪ elevenFamilyIn`.

**Note**: we do *not* take the union with `m5FamilyIn` because the pair
`(5·2^α, 11·2^α)` is forbidden for `α ≥ 4` (since `5 + 11 = 2^4`). So we
present `elevenFamilyIn` as an *alternative* extension to the m=5 family,
not a strict superset. The two families give incomparable `Θ(log N)`
gains over `oddPlusPowersOfTwo`. -/

/-- The construction adding the 11-family to odd-plus-powers-of-2. -/
def oddPlusPowersOfTwoPlusEleven (N : ℕ) : Finset ℕ :=
  oddPlusPowersOfTwo N ∪ elevenFamilyIn N

/-- Pair-freeness of `oddPlusPowersOfTwoPlusEleven`. -/
theorem pairFree_oddPlusPowersOfTwoPlusEleven (N : ℕ) :
    PairFree (oddPlusPowersOfTwoPlusEleven N) := by
  intro a ha b hb hab hpair
  simp only [oddPlusPowersOfTwoPlusEleven, Finset.mem_union] at ha hb
  rcases ha with ha_op | ha_e
  · rcases hb with hb_op | hb_e
    · exact pairFree_oddPlusPowersOfTwo N a ha_op b hb_op hab hpair
    · -- a ∈ oddPlusPowersOfTwo, b ∈ elevenFamily.
      rw [mem_elevenFamilyIn_iff] at hb_e
      obtain ⟨β, hβ_ge, _, hb_eq⟩ := hb_e
      have h11_le : (11 : ℕ) ≤ 2 ^ β := by
        calc (11 : ℕ) ≤ 16 := by norm_num
          _ = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) hβ_ge
      simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
        Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_image] at ha_op
      rcases ha_op with ⟨ha_range, ha_odd⟩ | ⟨γ, ⟨hγ_pos, _⟩, hγ_eq⟩
      · -- a odd, b = 2^β · 11.
        have ha_pos : 0 < a := by have := ha_range.1; omega
        rw [hb_eq] at hpair
        exact safePrime_odd_pair_free (by decide : Nat.Prime 11) (by decide)
          h11_le ha_pos ha_odd hpair
      · -- a = 2^γ (γ ≥ 1), b = 2^β · 11.
        rw [← hγ_eq, hb_eq] at hpair
        have hpair' : IsUnitFractionPair (2 ^ β * 11) (2 ^ γ) := by
          unfold IsUnitFractionPair at hpair ⊢
          have heq_sum : 2 ^ β * 11 + 2 ^ γ = 2 ^ γ + 2 ^ β * 11 := by ring
          have heq_prod : 2 ^ β * 11 * 2 ^ γ = 2 ^ γ * (2 ^ β * 11) := by ring
          rw [heq_sum, heq_prod]; exact hpair
        exact safePrime_powerOfTwo_pair_free (by decide : Nat.Prime 11) (by decide)
          elevenFamily_nonMers h11_le hγ_pos hpair'
  · rcases hb with hb_op | hb_e
    · -- a ∈ elevenFamily, b ∈ oddPlusPowersOfTwo: symmetric.
      rw [mem_elevenFamilyIn_iff] at ha_e
      obtain ⟨α, hα_ge, _, ha_eq⟩ := ha_e
      have h11_le : (11 : ℕ) ≤ 2 ^ α := by
        calc (11 : ℕ) ≤ 16 := by norm_num
          _ = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ α := Nat.pow_le_pow_right (by norm_num) hα_ge
      simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
        Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_image] at hb_op
      rcases hb_op with ⟨hb_range, hb_odd⟩ | ⟨γ, ⟨hγ_pos, _⟩, hγ_eq⟩
      · have hb_pos : 0 < b := by have := hb_range.1; omega
        rw [ha_eq] at hpair
        have hpair' : IsUnitFractionPair b (2 ^ α * 11) := by
          unfold IsUnitFractionPair at hpair ⊢
          have heq_sum : b + 2 ^ α * 11 = 2 ^ α * 11 + b := by ring
          have heq_prod : b * (2 ^ α * 11) = 2 ^ α * 11 * b := by ring
          rw [heq_sum, heq_prod]; exact hpair
        exact safePrime_odd_pair_free (by decide : Nat.Prime 11) (by decide)
          h11_le hb_pos hb_odd hpair'
      · rw [ha_eq, ← hγ_eq] at hpair
        exact safePrime_powerOfTwo_pair_free (by decide : Nat.Prime 11) (by decide)
          elevenFamily_nonMers h11_le hγ_pos hpair
    · -- Both in elevenFamily.
      exact pairFree_elevenFamilyIn N a ha_e b hb_e hab hpair

/-- The construction lies in `[1, N]`. -/
theorem oddPlusPowersOfTwoPlusEleven_subset_Icc (N : ℕ) :
    oddPlusPowersOfTwoPlusEleven N ⊆ Finset.Icc 1 N := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn_op | hn_e
  · exact oddPlusPowersOfTwo_subset_Icc N hn_op
  · rw [mem_elevenFamilyIn_iff] at hn_e
    obtain ⟨α, hα_ge, hbound, hn_eq⟩ := hn_e
    rw [Finset.mem_Icc, hn_eq]
    refine ⟨?_, hbound⟩
    have h16 : (16 : ℕ) ≤ 2 ^ α := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ α := Nat.pow_le_pow_right (by norm_num) hα_ge
    have : 16 * 11 ≤ 2 ^ α * 11 := Nat.mul_le_mul_right 11 h16
    omega

/-- The 11-family is disjoint from `oddPlusPowersOfTwo`: its elements are
even (so not odd) and divisible by 11 (so not powers of 2). -/
theorem disjoint_oddPlusPowersOfTwo_eleven (N : ℕ) :
    Disjoint (oddPlusPowersOfTwo N) (elevenFamilyIn N) := by
  rw [Finset.disjoint_left]
  intro n hn_op hn_e
  rw [mem_elevenFamilyIn_iff] at hn_e
  obtain ⟨α, hα_ge, _, hn_eq⟩ := hn_e
  simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image] at hn_op
  rcases hn_op with ⟨_, hn_odd⟩ | ⟨j, ⟨hj_pos, _⟩, hj_eq⟩
  · -- n odd but n = 2^α · 11 is even.
    have h2dvd : (2 : ℕ) ∣ n := by
      rw [hn_eq]
      have h2 : (2 : ℕ) ∣ 2 ^ α := dvd_pow_self 2 (by omega : α ≠ 0)
      exact h2.mul_right 11
    omega
  · -- n = 2^j and n = 2^α · 11: ⇒ 11 ∣ 2^j, impossible.
    have heq : 2 ^ j = 2 ^ α * 11 := by rw [hj_eq, hn_eq]
    have h11_dvd : (11 : ℕ) ∣ 2 ^ j := by
      rw [heq]; exact Dvd.intro (2 ^ α) (by ring)
    have hcop : Nat.Coprime 11 (2 ^ j) := by
      refine Nat.Coprime.pow_right j ?_; decide
    have : (11 : ℕ) = 1 := by
      have hg : Nat.gcd 11 (2 ^ j) = 11 := Nat.gcd_eq_left h11_dvd
      rw [hcop] at hg; omega
    omega

/-- Cardinality of `elevenFamilyIn`. -/
theorem card_elevenFamilyIn (N : ℕ) :
    (elevenFamilyIn N).card =
      ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 11 ≤ N)).card := by
  unfold elevenFamilyIn
  rw [Finset.card_image_of_injOn]
  intro a _ b _ hab
  have h_pos : 0 < 11 := by norm_num
  exact Nat.pow_right_injective (le_refl 2) (by
    have heq : 2 ^ a * 11 = 2 ^ b * 11 := hab
    exact (Nat.mul_right_cancel h_pos heq))

/-- Cardinality of the combined construction. -/
theorem card_oddPlusPowersOfTwoPlusEleven (N : ℕ) :
    (oddPlusPowersOfTwoPlusEleven N).card =
      (N + 1) / 2 + Nat.log 2 N +
        ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 11 ≤ N)).card := by
  unfold oddPlusPowersOfTwoPlusEleven
  rw [Finset.card_union_of_disjoint (disjoint_oddPlusPowersOfTwo_eleven N),
    card_oddPlusPowersOfTwo, card_elevenFamilyIn]

/-! ### A second instance: the `p = 13` family.

`13` is non-Fermat (`13 ≠ 1 + 2^d`: divisors of `169` are `{1, 13, 169}`,
none of the form `1 + 2^d ≥ 3`) and non-Mersenne (`14 = 2·7`, not a power
of 2). Crucially, `11 + 13 = 24 = 2^3 · 3` is **not** a power of 2 (odd
factor `3 > 1`), so the 11- and 13-families do not collide at same-α.

This demonstrates the layered pattern: each additional non-Fermat
non-Mersenne odd prime `p` with `p + q` not a power of 2 for every other
selected prime `q` contributes another `Θ(log(N/p))` elements. -/

/-- The set `{2^α · 13 : α ≥ 4, 2^α · 13 ≤ N}`. -/
def thirteenFamilyIn (N : ℕ) : Finset ℕ :=
  ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 13 ≤ N)).image
    (fun α => 2 ^ α * 13)

private lemma thirteenFamily_nonFerm (d : ℕ) (_ : 1 ≤ d) : 1 + 2 ^ d ≠ 13 := by
  intro h
  have : 2 ^ d = 12 := by omega
  have h3 : (3 : ℕ) ∣ 2 ^ d := by rw [this]; norm_num
  have hcop : Nat.Coprime 3 (2 ^ d) := by
    refine Nat.Coprime.pow_right d ?_; decide
  have : (3 : ℕ) ∣ 1 := by
    have hg : Nat.gcd 3 (2 ^ d) = 3 := Nat.gcd_eq_left h3
    rw [hcop] at hg; omega
  omega

private lemma thirteenFamily_nonMers (d : ℕ) (_ : 1 ≤ d) : 13 + 1 ≠ 2 ^ d := by
  intro h
  have : (2 : ℕ) ^ d = 14 := by omega
  have h7 : (7 : ℕ) ∣ 2 ^ d := by rw [this]; norm_num
  have hcop : Nat.Coprime 7 (2 ^ d) := by
    refine Nat.Coprime.pow_right d ?_; decide
  have : (7 : ℕ) ∣ 1 := by
    have hg : Nat.gcd 7 (2 ^ d) = 7 := Nat.gcd_eq_left h7
    rw [hcop] at hg; omega
  omega

private lemma mem_thirteenFamilyIn_iff {N n : ℕ} :
    n ∈ thirteenFamilyIn N ↔
      ∃ α : ℕ, 4 ≤ α ∧ 2 ^ α * 13 ≤ N ∧ n = 2 ^ α * 13 := by
  unfold thirteenFamilyIn
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨α, ⟨⟨h4, _⟩, hbound⟩, hαn⟩
    exact ⟨α, h4, hbound, hαn.symm⟩
  · rintro ⟨α, h4, hbound, hαn⟩
    refine ⟨α, ⟨⟨h4, ?_⟩, hbound⟩, hαn.symm⟩
    have hN_pos : 0 < N := by
      have h2α : 16 ≤ 2 ^ α := by
        calc (16 : ℕ) = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ α := Nat.pow_le_pow_right (by norm_num) h4
      have : 16 ≤ 2 ^ α * 13 := by nlinarith [Nat.two_pow_pos α]
      omega
    have h2α_le : 2 ^ α ≤ N := by
      have : 2 ^ α ≤ 2 ^ α * 13 := by linarith [Nat.two_pow_pos α]
      omega
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hN_pos.ne').mpr h2α_le

/-- Internal pair-freeness of the 13-family. -/
theorem pairFree_thirteenFamilyIn (N : ℕ) : PairFree (thirteenFamilyIn N) := by
  intro a ha b hb hab hpair
  rw [mem_thirteenFamilyIn_iff] at ha hb
  obtain ⟨α, _, _, ha_eq⟩ := ha
  obtain ⟨β, _, _, hb_eq⟩ := hb
  have hαβ : α ≠ β := by
    intro heq; apply hab; rw [ha_eq, hb_eq, heq]
  rw [ha_eq, hb_eq] at hpair
  exact safePrime_internal_pair_free (by decide : Nat.Prime 13)
    thirteenFamily_nonFerm hαβ hpair

/-- The hypothesis we'll need for combining 11- and 13-families:
`11 + 13 = 24`, which has an odd factor 3, hence is not a power of 2. -/
private lemma elevenThirteen_sum_not_pow2 : ∀ d : ℕ, 11 + 13 ≠ 2 ^ d := by
  intro d h
  have : (2 : ℕ) ^ d = 24 := by omega
  have h3 : (3 : ℕ) ∣ 2 ^ d := by rw [this]; norm_num
  have hcop : Nat.Coprime 3 (2 ^ d) := by
    refine Nat.Coprime.pow_right d ?_; decide
  have : (3 : ℕ) ∣ 1 := by
    have hg : Nat.gcd 3 (2 ^ d) = 3 := Nat.gcd_eq_left h3
    rw [hcop] at hg; omega
  omega

/-! ### Combined construction with both 11- and 13-families. -/

/-- The construction adding both safe-prime families to odd-plus-powers-of-2. -/
def oddPlusPowersOfTwoPlusElevenPlusThirteen (N : ℕ) : Finset ℕ :=
  oddPlusPowersOfTwo N ∪ elevenFamilyIn N ∪ thirteenFamilyIn N

/-- Pair-freeness of the doubly-extended construction. -/
theorem pairFree_oddPlusPowersOfTwoPlusElevenPlusThirteen (N : ℕ) :
    PairFree (oddPlusPowersOfTwoPlusElevenPlusThirteen N) := by
  intro a ha b hb hab hpair
  simp only [oddPlusPowersOfTwoPlusElevenPlusThirteen,
    Finset.mem_union] at ha hb
  -- Each of a, b is in one of three regions.
  -- We handle the case (a in 13-family, b in 13-family) and the two new cross cases;
  -- the rest reduces to the existing `pairFree_oddPlusPowersOfTwoPlusEleven`.
  rcases ha with (ha_op | ha_e) | ha_t
  · rcases hb with (hb_op | hb_e) | hb_t
    · exact pairFree_oddPlusPowersOfTwo N a ha_op b hb_op hab hpair
    · -- (a ∈ oddPlusPowersOfTwo, b ∈ elevenFamily) — reduce to existing combined proof.
      have ha_v2 : a ∈ oddPlusPowersOfTwoPlusEleven N :=
        Finset.mem_union.mpr (Or.inl ha_op)
      have hb_v2 : b ∈ oddPlusPowersOfTwoPlusEleven N :=
        Finset.mem_union.mpr (Or.inr hb_e)
      exact pairFree_oddPlusPowersOfTwoPlusEleven N a ha_v2 b hb_v2 hab hpair
    · -- a ∈ oddPlusPowersOfTwo, b ∈ thirteenFamily.
      rw [mem_thirteenFamilyIn_iff] at hb_t
      obtain ⟨β, hβ_ge, _, hb_eq⟩ := hb_t
      have h13_le : (13 : ℕ) ≤ 2 ^ β := by
        calc (13 : ℕ) ≤ 16 := by norm_num
          _ = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) hβ_ge
      simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
        Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_image] at ha_op
      rcases ha_op with ⟨ha_range, ha_odd⟩ | ⟨γ, ⟨hγ_pos, _⟩, hγ_eq⟩
      · have ha_pos : 0 < a := by have := ha_range.1; omega
        rw [hb_eq] at hpair
        exact safePrime_odd_pair_free (by decide : Nat.Prime 13) (by decide)
          h13_le ha_pos ha_odd hpair
      · rw [← hγ_eq, hb_eq] at hpair
        have hpair' : IsUnitFractionPair (2 ^ β * 13) (2 ^ γ) := by
          unfold IsUnitFractionPair at hpair ⊢
          have heq_sum : 2 ^ β * 13 + 2 ^ γ = 2 ^ γ + 2 ^ β * 13 := by ring
          have heq_prod : 2 ^ β * 13 * 2 ^ γ = 2 ^ γ * (2 ^ β * 13) := by ring
          rw [heq_sum, heq_prod]; exact hpair
        exact safePrime_powerOfTwo_pair_free (by decide : Nat.Prime 13) (by decide)
          thirteenFamily_nonMers h13_le hγ_pos hpair'
  · rcases hb with (hb_op | hb_e) | hb_t
    · -- a ∈ 11-family, b ∈ oddPlusPowersOfTwo: symmetric to (a oddpow, b 11).
      have ha_v2 : a ∈ oddPlusPowersOfTwoPlusEleven N :=
        Finset.mem_union.mpr (Or.inr ha_e)
      have hb_v2 : b ∈ oddPlusPowersOfTwoPlusEleven N :=
        Finset.mem_union.mpr (Or.inl hb_op)
      exact pairFree_oddPlusPowersOfTwoPlusEleven N a ha_v2 b hb_v2 hab hpair
    · -- Both in 11-family.
      have ha_v2 : a ∈ oddPlusPowersOfTwoPlusEleven N :=
        Finset.mem_union.mpr (Or.inr ha_e)
      have hb_v2 : b ∈ oddPlusPowersOfTwoPlusEleven N :=
        Finset.mem_union.mpr (Or.inr hb_e)
      exact pairFree_oddPlusPowersOfTwoPlusEleven N a ha_v2 b hb_v2 hab hpair
    · -- a ∈ 11-family, b ∈ 13-family. The key new cross-prime case.
      rw [mem_elevenFamilyIn_iff] at ha_e
      rw [mem_thirteenFamilyIn_iff] at hb_t
      obtain ⟨α, _, _, ha_eq⟩ := ha_e
      obtain ⟨β, _, _, hb_eq⟩ := hb_t
      rw [ha_eq, hb_eq] at hpair
      exact safePrime_cross_pair_free
        (by decide : Nat.Prime 11) (by decide : Nat.Prime 13)
        (by decide) (by decide) (by decide) elevenThirteen_sum_not_pow2 hpair
  · rcases hb with (hb_op | hb_e) | hb_t
    · -- a ∈ 13-family, b ∈ oddPlusPowersOfTwo: symmetric to (a oddpow, b 13).
      rw [mem_thirteenFamilyIn_iff] at ha_t
      obtain ⟨α, hα_ge, _, ha_eq⟩ := ha_t
      have h13_le : (13 : ℕ) ≤ 2 ^ α := by
        calc (13 : ℕ) ≤ 16 := by norm_num
          _ = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ α := Nat.pow_le_pow_right (by norm_num) hα_ge
      simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
        Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_image] at hb_op
      rcases hb_op with ⟨hb_range, hb_odd⟩ | ⟨γ, ⟨hγ_pos, _⟩, hγ_eq⟩
      · have hb_pos : 0 < b := by have := hb_range.1; omega
        rw [ha_eq] at hpair
        have hpair' : IsUnitFractionPair b (2 ^ α * 13) := by
          unfold IsUnitFractionPair at hpair ⊢
          have heq_sum : b + 2 ^ α * 13 = 2 ^ α * 13 + b := by ring
          have heq_prod : b * (2 ^ α * 13) = 2 ^ α * 13 * b := by ring
          rw [heq_sum, heq_prod]; exact hpair
        exact safePrime_odd_pair_free (by decide : Nat.Prime 13) (by decide)
          h13_le hb_pos hb_odd hpair'
      · rw [ha_eq, ← hγ_eq] at hpair
        exact safePrime_powerOfTwo_pair_free (by decide : Nat.Prime 13) (by decide)
          thirteenFamily_nonMers h13_le hγ_pos hpair
    · -- a ∈ 13-family, b ∈ 11-family: symmetric to (11-family, 13-family).
      rw [mem_thirteenFamilyIn_iff] at ha_t
      rw [mem_elevenFamilyIn_iff] at hb_e
      obtain ⟨α, _, _, ha_eq⟩ := ha_t
      obtain ⟨β, _, _, hb_eq⟩ := hb_e
      rw [ha_eq, hb_eq] at hpair
      have hpair' : IsUnitFractionPair (2 ^ β * 11) (2 ^ α * 13) := by
        unfold IsUnitFractionPair at hpair ⊢
        have heq_sum : 2 ^ β * 11 + 2 ^ α * 13 = 2 ^ α * 13 + 2 ^ β * 11 := by ring
        have heq_prod : 2 ^ β * 11 * (2 ^ α * 13) = 2 ^ α * 13 * (2 ^ β * 11) := by ring
        rw [heq_sum, heq_prod]; exact hpair
      exact safePrime_cross_pair_free
        (by decide : Nat.Prime 11) (by decide : Nat.Prime 13)
        (by decide) (by decide) (by decide) elevenThirteen_sum_not_pow2 hpair'
    · -- Both in 13-family.
      exact pairFree_thirteenFamilyIn N a ha_t b hb_t hab hpair

/-- **Alternative improved lower bound for #327.** Using the safe-prime
machinery with `p = 11`, we get

  `f(N) ≥ (N + 1)/2 + ⌊log₂ N⌋ +
            |{α ∈ [4, ⌊log₂ N⌋] : 2^α · 11 ≤ N}|`.

The same machinery applies to every odd prime `p ≥ 7` that is neither
Fermat (`p ∈ {3, 5, 17, 257, 65537}`) nor Mersenne (`p ∈ {3, 7, 31, …}`).
Each contributes another `Θ(log(N/p))` elements; combining many primes
(with attention to same-α cross-conflicts when `p + q` is a small power
of 2) gives the projected `Θ(√N / log N)` polynomial improvement. -/
theorem exists_pairFree_card_ge_eleven (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      A.card = (N + 1) / 2 + Nat.log 2 N +
        ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 11 ≤ N)).card := by
  exact ⟨oddPlusPowersOfTwoPlusEleven N,
    oddPlusPowersOfTwoPlusEleven_subset_Icc N,
    pairFree_oddPlusPowersOfTwoPlusEleven N,
    card_oddPlusPowersOfTwoPlusEleven N⟩

/-! ### Cardinality of the combined 11+13 construction. -/

/-- The combined construction lies in `[1, N]`. -/
theorem oddPlusPowersOfTwoPlusElevenPlusThirteen_subset_Icc (N : ℕ) :
    oddPlusPowersOfTwoPlusElevenPlusThirteen N ⊆ Finset.Icc 1 N := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn_ope | hn_t
  · rcases Finset.mem_union.mp hn_ope with hn_op | hn_e
    · exact oddPlusPowersOfTwo_subset_Icc N hn_op
    · -- n ∈ 11-family.
      have : n ∈ oddPlusPowersOfTwoPlusEleven N := Finset.mem_union.mpr (Or.inr hn_e)
      exact oddPlusPowersOfTwoPlusEleven_subset_Icc N this
  · rw [mem_thirteenFamilyIn_iff] at hn_t
    obtain ⟨α, hα_ge, hbound, hn_eq⟩ := hn_t
    rw [Finset.mem_Icc, hn_eq]
    refine ⟨?_, hbound⟩
    have h16 : (16 : ℕ) ≤ 2 ^ α := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ α := Nat.pow_le_pow_right (by norm_num) hα_ge
    have : 16 * 13 ≤ 2 ^ α * 13 := Nat.mul_le_mul_right 13 h16
    omega

/-- The 11- and 13-families are disjoint (different odd parts). -/
theorem disjoint_eleven_thirteen (N : ℕ) :
    Disjoint (elevenFamilyIn N) (thirteenFamilyIn N) := by
  rw [Finset.disjoint_left]
  intro n hn_e hn_t
  rw [mem_elevenFamilyIn_iff] at hn_e
  rw [mem_thirteenFamilyIn_iff] at hn_t
  obtain ⟨α, _, _, he_eq⟩ := hn_e
  obtain ⟨β, _, _, ht_eq⟩ := hn_t
  -- 2^α · 11 = 2^β · 13 ⇒ 13 ∣ 2^α · 11, but gcd(13, 2^α · 11) = 1.
  have heq : 2 ^ α * 11 = 2 ^ β * 13 := by rw [← he_eq, ← ht_eq]
  have h13_dvd : (13 : ℕ) ∣ 2 ^ α * 11 := by rw [heq]; exact ⟨2 ^ β, by ring⟩
  have hcop_11 : Nat.Coprime 13 11 := by decide
  have hcop_2 : Nat.Coprime 13 (2 ^ α) := by
    refine Nat.Coprime.pow_right α ?_; decide
  have hcop : Nat.Coprime 13 (2 ^ α * 11) := hcop_2.mul_right hcop_11
  have h13_eq_1 : (13 : ℕ) = 1 := by
    have hg : Nat.gcd 13 (2 ^ α * 11) = 13 := Nat.gcd_eq_left h13_dvd
    rw [hcop] at hg; omega
  omega

/-- 13-family is disjoint from oddPlusPowersOfTwo. -/
theorem disjoint_oddPlusPowersOfTwo_thirteen (N : ℕ) :
    Disjoint (oddPlusPowersOfTwo N) (thirteenFamilyIn N) := by
  rw [Finset.disjoint_left]
  intro n hn_op hn_t
  rw [mem_thirteenFamilyIn_iff] at hn_t
  obtain ⟨α, hα_ge, _, hn_eq⟩ := hn_t
  simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image] at hn_op
  rcases hn_op with ⟨_, hn_odd⟩ | ⟨j, ⟨hj_pos, _⟩, hj_eq⟩
  · have h2dvd : (2 : ℕ) ∣ n := by
      rw [hn_eq]
      have h2 : (2 : ℕ) ∣ 2 ^ α := dvd_pow_self 2 (by omega : α ≠ 0)
      exact h2.mul_right 13
    omega
  · have heq : 2 ^ j = 2 ^ α * 13 := by rw [hj_eq, hn_eq]
    have h13_dvd : (13 : ℕ) ∣ 2 ^ j := by rw [heq]; exact ⟨2 ^ α, by ring⟩
    have hcop : Nat.Coprime 13 (2 ^ j) := by
      refine Nat.Coprime.pow_right j ?_; decide
    have h13_eq_1 : (13 : ℕ) = 1 := by
      have hg : Nat.gcd 13 (2 ^ j) = 13 := Nat.gcd_eq_left h13_dvd
      rw [hcop] at hg; omega
    omega

/-- The 13-family is disjoint from `oddPlusPowersOfTwoPlusEleven`. -/
theorem disjoint_oddPlusPowersOfTwoPlusEleven_thirteen (N : ℕ) :
    Disjoint (oddPlusPowersOfTwoPlusEleven N) (thirteenFamilyIn N) := by
  unfold oddPlusPowersOfTwoPlusEleven
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_oddPlusPowersOfTwo_thirteen N, disjoint_eleven_thirteen N⟩

/-- Cardinality of the 13-family. -/
theorem card_thirteenFamilyIn (N : ℕ) :
    (thirteenFamilyIn N).card =
      ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 13 ≤ N)).card := by
  unfold thirteenFamilyIn
  rw [Finset.card_image_of_injOn]
  intro a _ b _ hab
  have h_pos : 0 < 13 := by norm_num
  exact Nat.pow_right_injective (le_refl 2) (by
    have heq : 2 ^ a * 13 = 2 ^ b * 13 := hab
    exact (Nat.mul_right_cancel h_pos heq))

/-- Cardinality of the combined 11+13 construction. -/
theorem card_oddPlusPowersOfTwoPlusElevenPlusThirteen (N : ℕ) :
    (oddPlusPowersOfTwoPlusElevenPlusThirteen N).card =
      (N + 1) / 2 + Nat.log 2 N +
        ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 11 ≤ N)).card +
        ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 13 ≤ N)).card := by
  have heq : oddPlusPowersOfTwoPlusElevenPlusThirteen N =
      oddPlusPowersOfTwoPlusEleven N ∪ thirteenFamilyIn N := rfl
  rw [heq, Finset.card_union_of_disjoint
    (disjoint_oddPlusPowersOfTwoPlusEleven_thirteen N),
    card_oddPlusPowersOfTwoPlusEleven, card_thirteenFamilyIn]

/-- **Doubly-improved lower bound for #327.** Using the safe-prime
machinery with both `p = 11` and `p = 13`:

  `f(N) ≥ (N + 1)/2 + ⌊log₂ N⌋ +
            |{α ∈ [4, ⌊log₂ N⌋] : 2^α · 11 ≤ N}| +
            |{α ∈ [4, ⌊log₂ N⌋] : 2^α · 13 ≤ N}|`.

Each safe prime contributes its own `Θ(log(N/p))` gain. With many such
primes (subject to `p + q` not being a small power of 2 for compatibility),
the total contribution grows polynomially: `Θ(√N / log N)`. -/
theorem exists_pairFree_card_ge_elevenThirteen (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      A.card = (N + 1) / 2 + Nat.log 2 N +
        ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 11 ≤ N)).card +
        ((Finset.Icc 4 (Nat.log 2 N)).filter (fun α => 2 ^ α * 13 ≤ N)).card := by
  exact ⟨oddPlusPowersOfTwoPlusElevenPlusThirteen N,
    oddPlusPowersOfTwoPlusElevenPlusThirteen_subset_Icc N,
    pairFree_oddPlusPowersOfTwoPlusElevenPlusThirteen N,
    card_oddPlusPowersOfTwoPlusElevenPlusThirteen N⟩

/-! ### Abstraction: arbitrary compatible safe-prime sets.

The pattern `oddPlusPowersOfTwo ∪ ⋃_{p ∈ P} F_p` is pair-free for any
`Finset P` of odd primes satisfying:

* each `p ∈ P` is non-Fermat and non-Mersenne,
* for any two distinct `p, q ∈ P`, the sum `p + q` is not a power of `2`.

This abstracts the explicit `elevenFamily` / `thirteenFamily` instances. -/

/-- The compatibility conditions on a `Finset` of safe primes. -/
structure SafePrimeSet (P : Finset ℕ) : Prop where
  prime : ∀ p ∈ P, Nat.Prime p
  odd : ∀ p ∈ P, p % 2 = 1
  not_fermat : ∀ p ∈ P, ∀ d : ℕ, 1 ≤ d → 1 + 2 ^ d ≠ p
  not_mersenne : ∀ p ∈ P, ∀ d : ℕ, 1 ≤ d → p + 1 ≠ 2 ^ d
  pairwise_sum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ d : ℕ, p + q ≠ 2 ^ d

/-- The union of safe-prime families for all `p ∈ P`. -/
def safePrimeSetFamily (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  P.biUnion (fun p =>
    ((Finset.Icc 1 (Nat.log 2 N)).filter (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).image
      (fun α => 2 ^ α * p))

private lemma mem_safePrimeSetFamily_iff {P : Finset ℕ} {N n : ℕ} :
    n ∈ safePrimeSetFamily P N ↔
      ∃ p ∈ P, ∃ α : ℕ, 1 ≤ α ∧ α ≤ Nat.log 2 N ∧
        p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N ∧ n = 2 ^ α * p := by
  unfold safePrimeSetFamily
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨p, hp, α, ⟨⟨hα1, hα2⟩, hp_le, hbound⟩, hαp⟩
    exact ⟨p, hp, α, hα1, hα2, hp_le, hbound, hαp.symm⟩
  · rintro ⟨p, hp, α, hα1, hα2, hp_le, hbound, hαp⟩
    exact ⟨p, hp, α, ⟨⟨hα1, hα2⟩, hp_le, hbound⟩, hαp.symm⟩

/-- The safe-prime-set family is internally pair-free. -/
theorem pairFree_safePrimeSetFamily {P : Finset ℕ} (hP : SafePrimeSet P) (N : ℕ) :
    PairFree (safePrimeSetFamily P N) := by
  intro a ha b hb hab hpair
  rw [mem_safePrimeSetFamily_iff] at ha hb
  obtain ⟨p, hp, α, _, _, _, _, ha_eq⟩ := ha
  obtain ⟨q, hq, β, _, _, _, _, hb_eq⟩ := hb
  by_cases hpq : p = q
  · -- Same prime: internal case.
    subst hpq
    have hαβ : α ≠ β := by
      intro heq; apply hab; rw [ha_eq, hb_eq, heq]
    rw [ha_eq, hb_eq] at hpair
    exact safePrime_internal_pair_free (hP.prime p hp)
      (fun d hd => hP.not_fermat p hp d hd) hαβ hpair
  · -- Distinct primes: cross case.
    rw [ha_eq, hb_eq] at hpair
    exact safePrime_cross_pair_free (hP.prime p hp) (hP.prime q hq)
      (hP.odd p hp) (hP.odd q hq) hpq
      (fun d => hP.pairwise_sum p hp q hq hpq d) hpair

/-- The safe-prime-set family is pair-free with all odd numbers. -/
theorem pairFree_oddNumbers_safePrimeSetFamily {P : Finset ℕ}
    (hP : SafePrimeSet P) (N : ℕ) :
    ∀ a ∈ oddNumbersIn N, ∀ b ∈ safePrimeSetFamily P N,
      a ≠ b → ¬ IsUnitFractionPair a b := by
  intro a ha b hb hab hpair
  rw [mem_safePrimeSetFamily_iff] at hb
  obtain ⟨p, hp, α, _, _, hp_le, _, hb_eq⟩ := hb
  simp only [oddNumbersIn, Finset.mem_filter, Finset.mem_Icc] at ha
  have ha_pos : 0 < a := by have := ha.1.1; omega
  rw [hb_eq] at hpair
  exact safePrime_odd_pair_free (hP.prime p hp) (hP.odd p hp)
    hp_le ha_pos ha.2 hpair

/-- The safe-prime-set family is pair-free with all powers of 2. -/
theorem pairFree_powersOfTwo_safePrimeSetFamily {P : Finset ℕ}
    (hP : SafePrimeSet P) (N : ℕ) :
    ∀ a ∈ powersOfTwoIn N, ∀ b ∈ safePrimeSetFamily P N,
      a ≠ b → ¬ IsUnitFractionPair a b := by
  intro a ha b hb hab hpair
  rw [mem_safePrimeSetFamily_iff] at hb
  obtain ⟨p, hp, α, _, _, hp_le, _, hb_eq⟩ := hb
  simp only [powersOfTwoIn, Finset.mem_image, Finset.mem_Icc] at ha
  obtain ⟨γ, ⟨hγ_pos, _⟩, hγ_eq⟩ := ha
  rw [← hγ_eq, hb_eq] at hpair
  have hpair' : IsUnitFractionPair (2 ^ α * p) (2 ^ γ) := by
    unfold IsUnitFractionPair at hpair ⊢
    have heq_sum : 2 ^ α * p + 2 ^ γ = 2 ^ γ + 2 ^ α * p := by ring
    have heq_prod : 2 ^ α * p * 2 ^ γ = 2 ^ γ * (2 ^ α * p) := by ring
    rw [heq_sum, heq_prod]; exact hpair
  exact safePrime_powerOfTwo_pair_free (hP.prime p hp) (hP.odd p hp)
    (fun d hd => hP.not_mersenne p hp d hd) hp_le hγ_pos hpair'

/-- **The full safe-prime construction.** -/
def oddPlusPowersOfTwoPlusSafePrimeSet (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  oddPlusPowersOfTwo N ∪ safePrimeSetFamily P N

/-- Pair-freeness of the full safe-prime construction. -/
theorem pairFree_oddPlusPowersOfTwoPlusSafePrimeSet {P : Finset ℕ}
    (hP : SafePrimeSet P) (N : ℕ) :
    PairFree (oddPlusPowersOfTwoPlusSafePrimeSet P N) := by
  intro a ha b hb hab hpair
  simp only [oddPlusPowersOfTwoPlusSafePrimeSet, Finset.mem_union] at ha hb
  rcases ha with ha_op | ha_sp
  · rcases hb with hb_op | hb_sp
    · exact pairFree_oddPlusPowersOfTwo N a ha_op b hb_op hab hpair
    · -- a ∈ oddPlusPowersOfTwo, b ∈ safePrimeSetFamily.
      simp only [oddPlusPowersOfTwo, Finset.mem_union] at ha_op
      rcases ha_op with ha_odd | ha_pow
      · exact pairFree_oddNumbers_safePrimeSetFamily hP N a ha_odd b hb_sp hab hpair
      · exact pairFree_powersOfTwo_safePrimeSetFamily hP N a ha_pow b hb_sp hab hpair
  · rcases hb with hb_op | hb_sp
    · -- a ∈ safePrimeSetFamily, b ∈ oddPlusPowersOfTwo: symmetric.
      simp only [oddPlusPowersOfTwo, Finset.mem_union] at hb_op
      have hpair' : IsUnitFractionPair b a := by
        unfold IsUnitFractionPair at hpair ⊢
        rw [Nat.add_comm, Nat.mul_comm]; exact hpair
      rcases hb_op with hb_odd | hb_pow
      · exact pairFree_oddNumbers_safePrimeSetFamily hP N b hb_odd a ha_sp hab.symm hpair'
      · exact pairFree_powersOfTwo_safePrimeSetFamily hP N b hb_pow a ha_sp hab.symm hpair'
    · exact pairFree_safePrimeSetFamily hP N a ha_sp b hb_sp hab hpair

/-- The full construction lies in `[1, N]`. -/
theorem oddPlusPowersOfTwoPlusSafePrimeSet_subset_Icc {P : Finset ℕ}
    (hP : SafePrimeSet P) (N : ℕ) :
    oddPlusPowersOfTwoPlusSafePrimeSet P N ⊆ Finset.Icc 1 N := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn_op | hn_sp
  · exact oddPlusPowersOfTwo_subset_Icc N hn_op
  · rw [mem_safePrimeSetFamily_iff] at hn_sp
    obtain ⟨p, hp, α, hα_pos, _, _, hbound, hn_eq⟩ := hn_sp
    rw [Finset.mem_Icc, hn_eq]
    refine ⟨?_, hbound⟩
    have hp_pos : 0 < p := (hP.prime p hp).pos
    have h2α_pos : 0 < 2 ^ α := Nat.two_pow_pos _
    have : 0 < 2 ^ α * p := Nat.mul_pos h2α_pos hp_pos
    omega

/-- **Generalized improved lower bound for #327.** For any compatible
finset `P` of safe primes, the construction
`oddPlusPowersOfTwo ∪ ⋃_{p ∈ P} F_p` is pair-free in `[1, N]`. -/
theorem exists_pairFree_safePrimeSet {P : Finset ℕ}
    (hP : SafePrimeSet P) (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A := by
  exact ⟨oddPlusPowersOfTwoPlusSafePrimeSet P N,
    oddPlusPowersOfTwoPlusSafePrimeSet_subset_Icc hP N,
    pairFree_oddPlusPowersOfTwoPlusSafePrimeSet hP N⟩

/-! ### Explicit `SafePrimeSet {11, 13, 23, 29}` instance.

A concrete set of four pairwise-compatible safe primes — meaning each
`p` is non-Fermat and non-Mersenne, and every pair `(p, q)` has
`p + q` not a power of `2`. Verifications by `decide`. -/

/-- Sums of distinct pairs from `{11, 13, 23, 29}`: `24, 34, 36, 40, 42, 52`.
None is a power of 2 — each has a small odd prime factor (`3, 17, 9, 5, 21, 13`).
We verify all six via the standard reduction "`2^d = N → N's odd factor divides 1`". -/
private lemma sum_not_pow2 (N : ℕ) (q : ℕ) (hq_dvd : q ∣ N) (hq_prime : Nat.Prime q)
    (hq_odd : q ≠ 2) : ∀ d : ℕ, N ≠ 2 ^ d := by
  intro d h
  have hq_dvd_pow : q ∣ 2 ^ d := by rw [← h]; exact hq_dvd
  have hcop : Nat.Coprime q (2 ^ d) := by
    refine Nat.Coprime.pow_right d ?_
    refine (Nat.coprime_primes hq_prime (by decide : Nat.Prime 2)).mpr ?_
    exact hq_odd
  have : q = 1 := by
    have hg : Nat.gcd q (2 ^ d) = q := Nat.gcd_eq_left hq_dvd_pow
    rw [hcop] at hg; omega
  exact hq_prime.one_lt.ne' this

/-! ### Generic safe-prime set: all safe primes up to `K`.

For any bound `K`, the set of "doubly-safe primes ≤ K, greedy-compatible
from below" is decidable and forms a `SafePrimeSet`. This avoids hardcoding
specific primes: the construction works uniformly in `K`.

The key trick is the greedy-from-below definition. A prime `p` is in the
set iff it is doubly safe (non-Fermat, non-Mersenne) AND for every smaller
prime `q < p` that is also doubly safe, `p + q` is not a power of 2. This
breaks the circular reference of "pairwise compatible within the set" by
referencing only the smaller candidates.

Pairwise compatibility within the resulting set then follows: if `p, q` are
both included and `q < p`, then by `p`'s inclusion check, `p + q` is not a
power of 2 (since `q` itself is doubly safe). -/

/-- Predicate: `p` is a base-safe prime, meaning ≥ 11, prime, odd,
non-Fermat, and non-Mersenne. The bounds on the inner `d` quantifiers
are derived from `p` itself. -/
def IsBaseSafePrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p % 2 = 1 ∧ 11 ≤ p ∧
    (∀ d ∈ Finset.Ioc 0 (Nat.log 2 (p + 1)), 1 + 2 ^ d ≠ p) ∧
    (∀ d ∈ Finset.Ioc 0 (Nat.log 2 (p + 2)), p + 1 ≠ 2 ^ d)

instance (p : ℕ) : Decidable (IsBaseSafePrime p) := by
  unfold IsBaseSafePrime; infer_instance

/-- Decidable membership predicate for `safePrimesUpTo K`. -/
def InSafePrimesUpTo (p : ℕ) : Prop :=
  IsBaseSafePrime p ∧
    ∀ q ∈ Finset.range p, IsBaseSafePrime q →
      ∀ d ∈ Finset.Ioc 0 (Nat.log 2 (p + q + 1)), p + q ≠ 2 ^ d

instance (p : ℕ) : Decidable (InSafePrimesUpTo p) := by
  unfold InSafePrimesUpTo; infer_instance

/-- The set of doubly-safe primes ≤ `K`, greedy-filtered so that no two
have a power-of-2 sum. -/
def safePrimesUpTo (K : ℕ) : Finset ℕ :=
  (Finset.range (K + 1)).filter InSafePrimesUpTo

/-! ### Three small extensions: `1 + 2^d ≠ p`, `p + 1 ≠ 2^d`, and
`p + q ≠ 2^d` for *all* `d ≥ 1`, from the *bounded* versions. -/

/-- For `p ≥ 2` and `d` large enough, `1 + 2^d > p`. So the bounded check
suffices for the full quantifier. -/
private lemma not_fermat_from_bounded {p : ℕ} (hp : 2 ≤ p)
    (h : ∀ d ∈ Finset.Ioc 0 (Nat.log 2 (p + 1)), 1 + 2 ^ d ≠ p) :
    ∀ d : ℕ, 1 ≤ d → 1 + 2 ^ d ≠ p := by
  intro d hd_pos
  by_cases hd_le : d ≤ Nat.log 2 (p + 1)
  · exact h d (Finset.mem_Ioc.mpr ⟨hd_pos, hd_le⟩)
  · push Not at hd_le
    intro heq
    -- 2^d > 2^(log 2 (p+1)) ≥ ... actually we use: d > log 2 (p+1) ⇒ 2^d > p+1 ≥ p+1.
    have hN_pos : 0 < p + 1 := by omega
    have h2d_gt : p + 1 < 2 ^ d :=
      (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hN_pos.ne').mp hd_le
    omega

private lemma not_mersenne_from_bounded {p : ℕ} (hp : 2 ≤ p)
    (h : ∀ d ∈ Finset.Ioc 0 (Nat.log 2 (p + 2)), p + 1 ≠ 2 ^ d) :
    ∀ d : ℕ, 1 ≤ d → p + 1 ≠ 2 ^ d := by
  intro d hd_pos
  by_cases hd_le : d ≤ Nat.log 2 (p + 2)
  · exact h d (Finset.mem_Ioc.mpr ⟨hd_pos, hd_le⟩)
  · push Not at hd_le
    intro heq
    have hN_pos : 0 < p + 2 := by omega
    have h2d_gt : p + 2 < 2 ^ d :=
      (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hN_pos.ne').mp hd_le
    omega

private lemma sum_not_pow2_from_bounded {p q : ℕ} (hpq : 2 ≤ p + q)
    (h : ∀ d ∈ Finset.Ioc 0 (Nat.log 2 (p + q + 1)), p + q ≠ 2 ^ d) :
    ∀ d : ℕ, p + q ≠ 2 ^ d := by
  intro d
  by_cases hd_pos : 1 ≤ d
  · by_cases hd_le : d ≤ Nat.log 2 (p + q + 1)
    · exact h d (Finset.mem_Ioc.mpr ⟨hd_pos, hd_le⟩)
    · push Not at hd_le
      intro heq
      have hN_pos : 0 < p + q + 1 := by omega
      have h2d_gt : p + q + 1 < 2 ^ d :=
        (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hN_pos.ne').mp hd_le
      omega
  · push Not at hd_pos
    interval_cases d
    intro heq; simp at heq; omega

/-- **The headline theorem**: `safePrimesUpTo K` is a `SafePrimeSet`,
for any bound `K`. -/
theorem safePrimeSet_safePrimesUpTo (K : ℕ) :
    SafePrimeSet (safePrimesUpTo K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- prime
  · intro p hp
    simp only [safePrimesUpTo, Finset.mem_filter, InSafePrimesUpTo,
      IsBaseSafePrime] at hp
    exact hp.2.1.1
  -- odd
  · intro p hp
    simp only [safePrimesUpTo, Finset.mem_filter, InSafePrimesUpTo,
      IsBaseSafePrime] at hp
    exact hp.2.1.2.1
  -- not_fermat
  · intro p hp d hd
    simp only [safePrimesUpTo, Finset.mem_filter, InSafePrimesUpTo,
      IsBaseSafePrime] at hp
    have hp_ge : 11 ≤ p := hp.2.1.2.2.1
    apply not_fermat_from_bounded (by omega : 2 ≤ p) hp.2.1.2.2.2.1 d hd
  -- not_mersenne
  · intro p hp d hd
    simp only [safePrimesUpTo, Finset.mem_filter, InSafePrimesUpTo,
      IsBaseSafePrime] at hp
    have hp_ge : 11 ≤ p := hp.2.1.2.2.1
    apply not_mersenne_from_bounded (by omega : 2 ≤ p) hp.2.1.2.2.2.2 d hd
  -- pairwise_sum
  · intro p hp q hq hpq d
    simp only [safePrimesUpTo, Finset.mem_filter, InSafePrimesUpTo] at hp hq
    have hp_base := hp.2.1
    have hq_base := hq.2.1
    have hp_ge : 11 ≤ p := hp_base.2.2.1
    have hq_ge : 11 ≤ q := hq_base.2.2.1
    -- WLOG q < p.
    rcases lt_or_gt_of_ne hpq with h | h
    · -- p < q: by q's inclusion, q + p ≠ 2^d ⇒ p + q ≠ 2^d.
      have hp_mem : p ∈ Finset.range q := Finset.mem_range.mpr h
      have h_qp := hq.2.2 p hp_mem hp_base
      have : ∀ d, q + p ≠ 2 ^ d :=
        sum_not_pow2_from_bounded (by omega : 2 ≤ q + p) h_qp
      have := this d
      rw [Nat.add_comm] at this
      exact this
    · -- q < p: by p's inclusion, p + q ≠ 2^d.
      have hq_mem : q ∈ Finset.range p := Finset.mem_range.mpr h
      have h_pq := hp.2.2 q hq_mem hq_base
      exact sum_not_pow2_from_bounded (by omega : 2 ≤ p + q) h_pq d

/-- **The universal construction**: for any `K, N`, the set
`oddPlusPowersOfTwo N ∪ safePrimeSetFamily (safePrimesUpTo K) N` is a
pair-free subset of `[1, N]`. -/
theorem exists_pairFree_universal (K N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A := by
  exact exists_pairFree_safePrimeSet (safePrimeSet_safePrimesUpTo K) N

/-! ### Quantitative bound: cardinality of the universal construction. -/

/-- For distinct primes `p, q` in a safe-prime set, the families `F_p`
and `F_q` are disjoint: `2^α · p = 2^β · q` forces `α = β` (taking
2-adic valuations) and then `p = q`. -/
private lemma disjoint_F_F {P : Finset ℕ} (hP : SafePrimeSet P)
    {p q : ℕ} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) (N : ℕ) :
    Disjoint
      (((Finset.Icc 1 (Nat.log 2 N)).filter
          (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).image (fun α => 2 ^ α * p))
      (((Finset.Icc 1 (Nat.log 2 N)).filter
          (fun α => q ≤ 2 ^ α ∧ 2 ^ α * q ≤ N)).image (fun α => 2 ^ α * q)) := by
  rw [Finset.disjoint_left]
  intro n hnp hnq
  simp only [Finset.mem_image, Finset.mem_filter] at hnp hnq
  obtain ⟨α, _, hα_eq⟩ := hnp
  obtain ⟨β, _, hβ_eq⟩ := hnq
  have heq : 2 ^ α * p = 2 ^ β * q := by rw [hα_eq, hβ_eq]
  have hp_odd : p % 2 = 1 := hP.odd p hp
  have hq_odd : q % 2 = 1 := hP.odd q hq
  -- α = β by comparing 2-adic valuations.
  have hαβ : α = β := by
    rcases lt_trichotomy α β with h | h | h
    · -- α < β: 2^α p = 2^β q ⇒ p = 2^{β-α} q ⇒ p even, contradiction.
      have hpow : 2 ^ β = 2 ^ α * 2 ^ (β - α) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, Nat.mul_assoc] at heq
      have h2α_pos : 0 < (2 : ℕ) ^ α := Nat.two_pow_pos _
      have hp_eq : p = 2 ^ (β - α) * q := Nat.eq_of_mul_eq_mul_left h2α_pos heq
      have h2_dvd_p : (2 : ℕ) ∣ p := by
        rw [hp_eq]; exact (dvd_pow_self 2 (by omega : β - α ≠ 0)).mul_right q
      omega
    · exact h
    · have hpow : 2 ^ α = 2 ^ β * 2 ^ (α - β) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, Nat.mul_assoc] at heq
      have h2β_pos : 0 < (2 : ℕ) ^ β := Nat.two_pow_pos _
      have hq_eq : 2 ^ (α - β) * p = q := Nat.eq_of_mul_eq_mul_left h2β_pos heq
      have h2_dvd_q : (2 : ℕ) ∣ q := by
        rw [← hq_eq]; exact (dvd_pow_self 2 (by omega : α - β ≠ 0)).mul_right p
      omega
  subst hαβ
  have h2α_pos : 0 < (2 : ℕ) ^ α := Nat.two_pow_pos _
  exact hpq (Nat.eq_of_mul_eq_mul_left h2α_pos heq)

/-- The map `α ↦ 2^α · p` is injective for `p > 0`. -/
private lemma card_F_p {P : Finset ℕ} (hP : SafePrimeSet P)
    {p : ℕ} (hp : p ∈ P) (N : ℕ) :
    (((Finset.Icc 1 (Nat.log 2 N)).filter
        (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).image (fun α => 2 ^ α * p)).card =
      ((Finset.Icc 1 (Nat.log 2 N)).filter
        (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).card := by
  rw [Finset.card_image_of_injOn]
  intro a _ b _ hab
  have hp_pos : 0 < p := (hP.prime p hp).pos
  exact Nat.pow_right_injective (le_refl 2) (Nat.mul_right_cancel hp_pos hab)

/-- **Cardinality of the safe-prime-set family**: the sum over `p ∈ P`
of `|F_p|`. -/
theorem card_safePrimeSetFamily {P : Finset ℕ} (hP : SafePrimeSet P) (N : ℕ) :
    (safePrimeSetFamily P N).card =
      ∑ p ∈ P, ((Finset.Icc 1 (Nat.log 2 N)).filter
        (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).card := by
  unfold safePrimeSetFamily
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    exact card_F_p hP hp N
  · intro p hp q hq hpq
    exact disjoint_F_F hP hp hq hpq N

/-- The safe-prime-set family is disjoint from `oddPlusPowersOfTwo`. -/
theorem disjoint_oddPlusPowersOfTwo_safePrimeSetFamily {P : Finset ℕ}
    (hP : SafePrimeSet P) (N : ℕ) :
    Disjoint (oddPlusPowersOfTwo N) (safePrimeSetFamily P N) := by
  rw [Finset.disjoint_left]
  intro n hn_op hn_sp
  rw [mem_safePrimeSetFamily_iff] at hn_sp
  obtain ⟨p, hp, α, hα_pos, _, _, _, hn_eq⟩ := hn_sp
  have hp_prime := hP.prime p hp
  have hp_odd := hP.odd p hp
  simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hn_op
  rcases hn_op with ⟨_, hn_odd⟩ | ⟨j, ⟨hj_pos, _⟩, hj_eq⟩
  · have h2dvd : (2 : ℕ) ∣ n := by
      rw [hn_eq]
      exact (dvd_pow_self 2 (by omega : α ≠ 0)).mul_right p
    omega
  · have heq : 2 ^ j = 2 ^ α * p := by rw [hj_eq, hn_eq]
    have hp_dvd : p ∣ 2 ^ j := by rw [heq]; exact Dvd.intro (2 ^ α) (by ring)
    have hcop : Nat.Coprime p (2 ^ j) := by
      refine Nat.Coprime.pow_right j ?_
      exact (Nat.coprime_two_right (n := p)).mpr (Nat.odd_iff.mpr hp_odd)
    have : p ≤ 1 := by
      have hg : Nat.gcd p (2 ^ j) = p := Nat.gcd_eq_left hp_dvd
      rw [hcop] at hg; omega
    have := hp_prime.two_le; omega

/-- **Cardinality of the full universal construction**. -/
theorem card_oddPlusPowersOfTwoPlusSafePrimeSet {P : Finset ℕ}
    (hP : SafePrimeSet P) (N : ℕ) :
    (oddPlusPowersOfTwoPlusSafePrimeSet P N).card =
      (N + 1) / 2 + Nat.log 2 N +
        ∑ p ∈ P, ((Finset.Icc 1 (Nat.log 2 N)).filter
          (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).card := by
  unfold oddPlusPowersOfTwoPlusSafePrimeSet
  rw [Finset.card_union_of_disjoint
    (disjoint_oddPlusPowersOfTwo_safePrimeSetFamily hP N),
    card_oddPlusPowersOfTwo, card_safePrimeSetFamily hP]

/-- **Quantitative universal lower bound for #327.** For any `K, N`:

  `f(N) ≥ (N + 1) / 2 + ⌊log₂ N⌋ +
            ∑_{p ∈ safePrimesUpTo K} |{α ∈ [1, ⌊log₂ N⌋] : p ≤ 2^α ∧ 2^α · p ≤ N}|`.

As `K, N → ∞` with `K = √N`, the sum grows like `Θ(√N / log N)` by the
prime number theorem (after accounting for the Goldbach-sparse
power-of-2 sums that the greedy filter excludes), giving a polynomial
improvement past `N/2`. -/
theorem exists_pairFree_quantitative (K N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      A.card = (N + 1) / 2 + Nat.log 2 N +
        ∑ p ∈ safePrimesUpTo K,
          ((Finset.Icc 1 (Nat.log 2 N)).filter
            (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).card :=
  ⟨oddPlusPowersOfTwoPlusSafePrimeSet (safePrimesUpTo K) N,
    oddPlusPowersOfTwoPlusSafePrimeSet_subset_Icc
      (safePrimeSet_safePrimesUpTo K) N,
    pairFree_oddPlusPowersOfTwoPlusSafePrimeSet
      (safePrimeSet_safePrimesUpTo K) N,
    card_oddPlusPowersOfTwoPlusSafePrimeSet (safePrimeSet_safePrimesUpTo K) N⟩

/-- Reality check: for `K = 30`, the safe-prime set is exactly
`{11, 13, 23, 29}` (the four explicit primes from earlier). -/
example : safePrimesUpTo 30 = {11, 13, 23, 29} := by decide

/-- For `K = 50`, the set extends to `{11, 13, 23, 29, 37, 43, 47}`. -/
example : safePrimesUpTo 50 = {11, 13, 23, 29, 37, 43, 47} := by decide

/-- The set `{11, 13, 23, 29}` is a valid safe-prime set. -/
theorem safePrimeSet_eleven_thirteen_twentythree_twentynine :
    SafePrimeSet ({11, 13, 23, 29} : Finset ℕ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- prime
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  -- odd
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  -- not_fermat: for each p, no d ≥ 1 has 1 + 2^d = p.
  · intro p hp d hd_pos heq
    -- 2^d = p - 1; check that p - 1 is never a power of 2 for these primes.
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · -- p = 11: 2^d = 10 = 2·5; 5 ∣ 10, 5 prime, 5 ≠ 2.
      exact sum_not_pow2 10 5 (by norm_num) (by decide) (by decide) d (by omega)
    · -- p = 13: 2^d = 12 = 4·3; 3 ∣ 12.
      exact sum_not_pow2 12 3 (by norm_num) (by decide) (by decide) d (by omega)
    · -- p = 23: 2^d = 22 = 2·11; 11 ∣ 22.
      exact sum_not_pow2 22 11 (by norm_num) (by decide) (by decide) d (by omega)
    · -- p = 29: 2^d = 28 = 4·7; 7 ∣ 28.
      exact sum_not_pow2 28 7 (by norm_num) (by decide) (by decide) d (by omega)
  -- not_mersenne: for each p, no d ≥ 1 has p + 1 = 2^d.
  · intro p hp d hd_pos heq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact sum_not_pow2 12 3 (by norm_num) (by decide) (by decide) d
        (by show (12 : ℕ) = 2 ^ d; exact heq)
    · exact sum_not_pow2 14 7 (by norm_num) (by decide) (by decide) d
        (by show (14 : ℕ) = 2 ^ d; exact heq)
    · exact sum_not_pow2 24 3 (by norm_num) (by decide) (by decide) d
        (by show (24 : ℕ) = 2 ^ d; exact heq)
    · exact sum_not_pow2 30 5 (by norm_num) (by decide) (by decide) d
        (by show (30 : ℕ) = 2 ^ d; exact heq)
  -- pairwise_sum: for each pair (p, q) with p ≠ q in {11,13,23,29}, p + q not power of 2.
  · intro p hp q hq hpq d heq
    -- Six pairs: (11,13)→24, (11,23)→34, (11,29)→40, (13,23)→36, (13,29)→42, (23,29)→52.
    -- Each has a small odd prime factor.
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first
      | (exact (hpq rfl).elim)
      | (exact sum_not_pow2 24 3 (by norm_num) (by decide) (by decide) d heq)
      | (exact sum_not_pow2 34 17 (by norm_num) (by decide) (by decide) d heq)
      | (exact sum_not_pow2 40 5 (by norm_num) (by decide) (by decide) d heq)
      | (exact sum_not_pow2 36 3 (by norm_num) (by decide) (by decide) d heq)
      | (exact sum_not_pow2 42 3 (by norm_num) (by decide) (by decide) d heq)
      | (exact sum_not_pow2 52 13 (by norm_num) (by decide) (by decide) d heq)

/-! ### Reducing the safe-prime sum to a prime count.

The headline `exists_pairFree_quantitative` bound carries the inner sum
`∑_{p ∈ safePrimesUpTo K} |{α ∈ [1, ⌊log₂ N⌋] : p ≤ 2^α ∧ 2^α · p ≤ N}|`.
For the polynomial-improvement application we only need a one-element-per-prime
witness: for each safe prime `p ≤ K` and any `N ≥ 2 K²`, the choice
`α := ⌊log₂ p⌋ + 1` lies in the filter set, so the inner sum is `≥ |P|`. This
turns the Chebyshev question into a *prime count*: bound `|safePrimesUpTo K|`
from below by `Ω(K / log K)`. -/

/-- For `p ≥ 1` and `N ≥ 2 p²`, the choice `α := ⌊log₂ p⌋ + 1` is a valid
witness in the inner filter: `1 ≤ α ≤ ⌊log₂ N⌋`, `p ≤ 2^α`, and `2^α · p ≤ N`. -/
private lemma inner_filter_witness {p N : ℕ} (hp : 1 ≤ p) (hN : 2 * p ^ 2 ≤ N) :
    (Nat.log 2 p + 1) ∈
      ((Finset.Icc 1 (Nat.log 2 N)).filter
        (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)) := by
  -- Two key inequalities about `2 ^ (Nat.log 2 p + 1)`.
  have hp_lt : p < 2 ^ (Nat.log 2 p + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  have h2p_le : 2 ^ (Nat.log 2 p + 1) ≤ 2 * p := by
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega : p ≠ 0))
  -- `2^α · p ≤ 2 p²` and `2 p² ≤ N` give `2^α · p ≤ N`.
  have h2αp_le_N : 2 ^ (Nat.log 2 p + 1) * p ≤ N := by
    calc 2 ^ (Nat.log 2 p + 1) * p
        ≤ 2 * p * p := Nat.mul_le_mul_right p h2p_le
      _ = 2 * p ^ 2 := by ring
      _ ≤ N := hN
  -- `2^α ≤ N` since `p ≥ 1`, so `2^α ≤ 2^α · p ≤ N`.
  have h2α_le_N : 2 ^ (Nat.log 2 p + 1) ≤ N :=
    le_trans (Nat.le_mul_of_pos_right _ hp) h2αp_le_N
  -- Hence `α ≤ Nat.log 2 N` via `Nat.log_mono_right` applied to `2^α ≤ N`.
  have hα_le : Nat.log 2 p + 1 ≤ Nat.log 2 N := by
    have := Nat.log_mono_right (b := 2) h2α_le_N
    rwa [Nat.log_pow (by norm_num : 1 < 2)] at this
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hα_le⟩, ?_, h2αp_le_N⟩
  exact hp_lt.le

/-- **Lower bound on the inner filter cardinality**: for any safe prime
`p ∈ P` (so `p ≥ 11`) and `N ≥ 2 p²`, the inner Finset is non-empty. -/
theorem one_le_inner_card {P : Finset ℕ} (hP : SafePrimeSet P)
    {p : ℕ} (hp : p ∈ P) {N : ℕ} (hN : 2 * p ^ 2 ≤ N) :
    1 ≤ ((Finset.Icc 1 (Nat.log 2 N)).filter
        (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).card := by
  have hp_pos : 1 ≤ p := (hP.prime p hp).one_lt.le
  exact Finset.card_pos.mpr ⟨_, inner_filter_witness hp_pos hN⟩

/-- **Reduction to a prime count**: if every `p ∈ P` satisfies `2 p² ≤ N`,
then the inner sum is `≥ |P|`. Combined with `exists_pairFree_quantitative`,
this turns the polynomial-improvement question into a Chebyshev-style bound
on `|safePrimesUpTo K|`. -/
theorem card_safePrimeSetFamily_ge_card {P : Finset ℕ} (hP : SafePrimeSet P)
    {N : ℕ} (hN : ∀ p ∈ P, 2 * p ^ 2 ≤ N) :
    P.card ≤ (safePrimeSetFamily P N).card := by
  rw [card_safePrimeSetFamily hP]
  calc P.card = ∑ _ ∈ P, 1 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun p hp => one_le_inner_card hP hp (hN p hp))

/-- **Chebyshev-reduced lower bound (abstract)**: for any `SafePrimeSet P` whose
elements are bounded by `K`, with `2 K² ≤ N`, we have
`f(N) ≥ (N + 1) / 2 + ⌊log₂ N⌋ + |P|`. This is the form that turns the
polynomial-improvement question into a Chebyshev-style count of `|P|`. -/
theorem exists_pairFree_card_ge_abstract {P : Finset ℕ} (hP : SafePrimeSet P)
    {K N : ℕ} (hP_le_K : ∀ p ∈ P, p ≤ K) (hKN : 2 * K ^ 2 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      (N + 1) / 2 + Nat.log 2 N + P.card ≤ A.card := by
  refine ⟨oddPlusPowersOfTwoPlusSafePrimeSet P N,
    oddPlusPowersOfTwoPlusSafePrimeSet_subset_Icc hP N,
    pairFree_oddPlusPowersOfTwoPlusSafePrimeSet hP N, ?_⟩
  rw [card_oddPlusPowersOfTwoPlusSafePrimeSet hP N]
  have h_bound : ∀ p ∈ P, 2 * p ^ 2 ≤ N := by
    intro p hp
    have hp_le_K : p ≤ K := hP_le_K p hp
    have hp2 : p ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left hp_le_K 2
    calc 2 * p ^ 2 ≤ 2 * K ^ 2 := Nat.mul_le_mul_left 2 hp2
      _ ≤ N := hKN
  have key : P.card ≤
      ∑ p ∈ P, ((Finset.Icc 1 (Nat.log 2 N)).filter
        (fun α => p ≤ 2 ^ α ∧ 2 ^ α * p ≤ N)).card := by
    calc P.card
        = ∑ _ ∈ P, 1 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
      _ ≤ _ := Finset.sum_le_sum (fun p hp =>
          one_le_inner_card hP hp (h_bound p hp))
  omega

/-- Specialisation to `safePrimesUpTo K`: `f(N) ≥ (N+1)/2 + ⌊log₂ N⌋ +
|safePrimesUpTo K|` when `2 K² ≤ N`. -/
theorem exists_pairFree_card_ge_safePrimeCount {K N : ℕ} (hKN : 2 * K ^ 2 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      (N + 1) / 2 + Nat.log 2 N + (safePrimesUpTo K).card ≤ A.card := by
  refine exists_pairFree_card_ge_abstract (safePrimeSet_safePrimesUpTo K)
    (fun p hp => ?_) hKN
  have : p ∈ Finset.range (K + 1) :=
    (Finset.mem_filter.mp (show p ∈ (Finset.range (K + 1)).filter _ from hp)).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)

end UnitFractionPairs
