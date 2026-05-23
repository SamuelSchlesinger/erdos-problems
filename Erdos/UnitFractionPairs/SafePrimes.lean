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

end UnitFractionPairs
