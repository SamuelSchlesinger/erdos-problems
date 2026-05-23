/-
# Beating the Elementary Lower Bound for #327

The folklore lower bound `f(N) ≥ ⌈N/2⌉` comes from the odd numbers being
pair-free. We strengthen this to

  `f(N) ≥ ⌈N/2⌉ + ⌊log₂ N⌋`

via the explicit construction `A = {odd numbers in [1, N]} ∪ {2^k : 1 ≤ k, 2^k ≤ N}`.

The improvement is `Θ(log N)` — small, but a real first step past the
elementary bound, and the union infrastructure here generalises (more
"odd-conflict-free" even families exist, e.g. `2^k · m` with `m ≤ 2^k`).

## Pair-freeness of the construction

* Odd–odd pairs: already proven in `Statement.lean` (the parity
  obstruction `2 ∣ a + b` with `2 ∤ ab`).
* Odd–power-of-2 pairs: for odd `a` and `e = 2^k`, the sum `a + 2^k` is
  coprime to both `a` and `2^k`, hence to `a · 2^k`, but it is `≥ 3`.
* Power-of-2 / power-of-2 pairs: for `1 ≤ k < l`, `2^k + 2^l = 2^k(1 + 2^{l-k})`
  carries the odd factor `1 + 2^{l-k} ≥ 3`, but `2^k · 2^l = 2^{k+l}` is a
  pure power of 2; no odd `> 1` divides a pure power of 2.
-/
import Erdos.UnitFractionPairs.Statement

namespace UnitFractionPairs

/-- The powers of 2 with exponent `≥ 1` that are at most `N`. -/
def powersOfTwoIn (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.log 2 N)).image (fun k => 2 ^ k)

/-- The odd numbers in `[1, N]`. -/
def oddNumbersIn (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 2 = 1)

/-- The pair-free construction: odd numbers up to `N` together with powers
of `2` up to `N`. -/
def oddPlusPowersOfTwo (N : ℕ) : Finset ℕ :=
  oddNumbersIn N ∪ powersOfTwoIn N

/-! ### Pair-freeness of each component. -/

/-- Two distinct positive powers of 2 form no unit-fraction pair. -/
theorem powerOfTwo_pair_free {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hkl : k ≠ l) : ¬ IsUnitFractionPair (2 ^ k) (2 ^ l) := by
  -- WLOG `k < l`.
  wlog h : k < l with hsym
  · push_neg at h
    have hlt : l < k := lt_of_le_of_ne h hkl.symm
    intro hpair
    apply hsym hl hk hkl.symm hlt
    unfold IsUnitFractionPair at hpair ⊢
    rw [Nat.add_comm, Nat.mul_comm]
    exact hpair
  -- Now `k < l`. Suppose, for contradiction, that the pair is forbidden.
  unfold IsUnitFractionPair
  intro hdvd
  -- Rewrite `2^k + 2^l = 2^k * (1 + 2^(l-k))` and `2^k * 2^l = 2^(k+l)`.
  have hpow_diff : 2 ^ l = 2 ^ k * 2 ^ (l - k) := by
    rw [← pow_add]; congr 1; omega
  have hsum_eq : 2 ^ k + 2 ^ l = 2 ^ k * (1 + 2 ^ (l - k)) := by
    rw [hpow_diff]; ring
  have hprod_eq : 2 ^ k * 2 ^ l = 2 ^ k * 2 ^ l := rfl
  rw [hsum_eq] at hdvd
  -- Cancel `2^k` from both sides of the divisibility.
  have h2k_pos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos _
  have hcancel : (1 + 2 ^ (l - k)) ∣ 2 ^ l :=
    (Nat.mul_dvd_mul_iff_left h2k_pos).mp hdvd
  -- `1 + 2^(l-k)` is odd and `≥ 3`.
  have hodd : (1 + 2 ^ (l - k)) % 2 = 1 := by
    have h2_dvd : (2 : ℕ) ∣ 2 ^ (l - k) := dvd_pow_self 2 (by omega)
    omega
  have hgt : 3 ≤ 1 + 2 ^ (l - k) := by
    have h2le : 2 ≤ 2 ^ (l - k) := by
      have h1le : 1 ≤ l - k := by omega
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ (l - k) := Nat.pow_le_pow_right (by norm_num) h1le
    omega
  -- An odd number `≥ 3` is coprime to any power of 2.
  have hcop : Nat.Coprime (1 + 2 ^ (l - k)) (2 ^ l) := by
    refine Nat.Coprime.pow_right l ?_
    rw [Nat.coprime_two_right, Nat.odd_iff]
    exact hodd
  -- But a coprime divisor of `n` divides `1`.
  have hone : 1 + 2 ^ (l - k) ∣ 1 := by
    have := hcop.dvd_of_dvd_mul_left (show (1 + 2 ^ (l - k)) ∣ 2 ^ l * 1 by
      rw [Nat.mul_one]; exact hcancel)
    exact this
  have hle : 1 + 2 ^ (l - k) ≤ 1 := Nat.le_of_dvd (by norm_num) hone
  omega

/-- An odd number and a positive power of 2 form no unit-fraction pair. -/
theorem odd_powerOfTwo_pair_free {a k : ℕ} (ha : 0 < a) (hodd : a % 2 = 1)
    (hk : 1 ≤ k) : ¬ IsUnitFractionPair a (2 ^ k) := by
  unfold IsUnitFractionPair
  intro hdvd
  -- gcd(a + 2^k, a) = gcd(2^k, a) = 1 (a odd).
  have hgcd_a2k : Nat.gcd a (2 ^ k) = 1 := by
    refine Nat.Coprime.pow_right k ?_
    rw [Nat.coprime_two_right, Nat.odd_iff]
    exact hodd
  have hcop_a : Nat.Coprime (a + 2 ^ k) a := by
    have : Nat.Coprime (2 ^ k + a) a := by
      rw [Nat.coprime_add_self_left]
      rw [Nat.Coprime, Nat.gcd_comm]; exact hgcd_a2k
    rwa [Nat.add_comm] at this
  have hcop_pow : Nat.Coprime (a + 2 ^ k) (2 ^ k) := by
    rw [Nat.coprime_add_self_left]
    exact hgcd_a2k
  have hcop : Nat.Coprime (a + 2 ^ k) (a * 2 ^ k) :=
    hcop_a.mul_right hcop_pow
  -- A coprime divisor must divide 1.
  have hone : (a + 2 ^ k) ∣ 1 := by
    have hdvd' : (a + 2 ^ k) ∣ (a * 2 ^ k) * 1 := by
      rw [Nat.mul_one]; exact hdvd
    exact hcop.dvd_of_dvd_mul_left hdvd'
  have hle : a + 2 ^ k ≤ 1 := Nat.le_of_dvd (by norm_num) hone
  have h2le : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

/-! ### Pair-freeness of the combined construction. -/

/-- **Pair-freeness of the enriched odd-plus-powers-of-2 construction.**

For every `N`, the set `oddPlusPowersOfTwo N ⊆ {1, ..., N}` is
unit-fraction pair-free. -/
theorem pairFree_oddPlusPowersOfTwo (N : ℕ) :
    PairFree (oddPlusPowersOfTwo N) := by
  intro a ha b hb hab hpair
  simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image] at ha hb
  -- Cases by whether `a, b` come from the odd block or the power-of-2 block.
  rcases ha with ha_odd | ⟨ka, hka_range, hka⟩
  · rcases hb with hb_odd | ⟨kb, hkb_range, hkb⟩
    · -- Both odd.
      have hpos_a : 0 < a := by have := ha_odd.1.1; omega
      have hpos_b : 0 < b := by have := hb_odd.1.1; omega
      unfold IsUnitFractionPair at hpair
      obtain ⟨k, hk⟩ := hpair
      have ha_not_two : ¬ 2 ∣ a := by have := ha_odd.2; omega
      have hb_not_two : ¬ 2 ∣ b := by have := hb_odd.2; omega
      have hab_even : 2 ∣ a + b := by
        have := ha_odd.2; have := hb_odd.2; omega
      have hab_not_dvd : ¬ 2 ∣ a * b := by
        rw [Nat.Prime.dvd_mul Nat.prime_two]; push_neg
        exact ⟨ha_not_two, hb_not_two⟩
      exact hab_not_dvd (dvd_trans hab_even ⟨k, hk⟩)
    · -- a odd, b = 2^kb.
      have ha_mod : a % 2 = 1 := ha_odd.2
      have ha_pos : 0 < a := by have := ha_odd.1.1; omega
      have hkb_pos : 1 ≤ kb := hkb_range.1
      rw [← hkb] at hpair
      exact odd_powerOfTwo_pair_free ha_pos ha_mod hkb_pos hpair
  · rcases hb with hb_odd | ⟨kb, hkb_range, hkb⟩
    · -- a = 2^ka, b odd.
      have hb_mod : b % 2 = 1 := hb_odd.2
      have hb_pos : 0 < b := by have := hb_odd.1.1; omega
      have hka_pos : 1 ≤ ka := hka_range.1
      rw [← hka] at hpair
      unfold IsUnitFractionPair at hpair
      rw [Nat.add_comm, Nat.mul_comm] at hpair
      exact odd_powerOfTwo_pair_free hb_pos hb_mod hka_pos hpair
    · -- Both powers of 2.
      have hka_pos : 1 ≤ ka := hka_range.1
      have hkb_pos : 1 ≤ kb := hkb_range.1
      have hkakb : ka ≠ kb := by
        intro heq
        apply hab
        rw [← hka, ← hkb, heq]
      rw [← hka, ← hkb] at hpair
      exact powerOfTwo_pair_free hka_pos hkb_pos hkakb hpair

/-! ### Subset and cardinality of the construction. -/

/-- The construction lies in `[1, N]`. -/
theorem oddPlusPowersOfTwo_subset_Icc (N : ℕ) :
    oddPlusPowersOfTwo N ⊆ Finset.Icc 1 N := by
  intro n hn
  simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image] at hn
  rw [Finset.mem_Icc]
  rcases hn with ⟨⟨h1, h2⟩, _⟩ | ⟨k, ⟨hk_pos, hk_le⟩, hkn⟩
  · exact ⟨h1, h2⟩
  · subst hkn
    refine ⟨?_, ?_⟩
    · -- 2^k ≥ 2 ≥ 1 since k ≥ 1
      have h2le : 2 ≤ 2 ^ k :=
        calc (2 : ℕ) = 2 ^ 1 := by ring
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk_pos
      omega
    · -- 2^k ≤ N because k ≤ Nat.log 2 N
      rcases Nat.eq_zero_or_pos N with hN0 | hN_pos
      · rw [hN0] at hk_le
        simp at hk_le
        omega
      · calc 2 ^ k ≤ 2 ^ Nat.log 2 N :=
              Nat.pow_le_pow_right (by norm_num) hk_le
          _ ≤ N := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hN_pos)

/-- The odd-number block and the power-of-2 block are disjoint
(powers of 2 with exponent ≥ 1 are even). -/
theorem disjoint_oddNumbers_powersOfTwo (N : ℕ) :
    Disjoint (oddNumbersIn N) (powersOfTwoIn N) := by
  rw [Finset.disjoint_left]
  intro n hn_odd hn_pow
  simp only [oddNumbersIn, powersOfTwoIn, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image] at hn_odd hn_pow
  obtain ⟨k, hk_range, hkn⟩ := hn_pow
  have hk_pos : 1 ≤ k := hk_range.1
  -- n = 2^k is even.
  have hn_even : 2 ∣ n := by
    rw [← hkn]
    exact dvd_pow_self 2 (by omega : k ≠ 0)
  -- But n is odd.
  have hn_odd_mod : n % 2 = 1 := hn_odd.2
  omega

/-- Cardinality of the odd-numbers block. -/
theorem card_oddNumbersIn (N : ℕ) : (oddNumbersIn N).card = (N + 1) / 2 := by
  classical
  -- Bijection with Icc 1 ((N+1)/2): k ↦ 2k - 1.
  have hbij : (oddNumbersIn N) = (Finset.Icc 1 ((N + 1) / 2)).image (fun k => 2 * k - 1) := by
    ext n
    simp only [oddNumbersIn, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hnodd⟩
      refine ⟨(n + 1) / 2, ⟨?_, ?_⟩, ?_⟩
      · omega
      · omega
      · omega
    · rintro ⟨k, ⟨hk1, hkN⟩, hkn⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  rw [hbij]
  rw [Finset.card_image_of_injOn]
  · rw [Nat.card_Icc]; omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
    -- hab : (fun k => 2 * k - 1) a = (fun k => 2 * k - 1) b
    have : 2 * a - 1 = 2 * b - 1 := hab
    omega

/-- Cardinality of the powers-of-2 block. -/
theorem card_powersOfTwoIn (N : ℕ) : (powersOfTwoIn N).card = Nat.log 2 N := by
  unfold powersOfTwoIn
  rw [Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
    exact Nat.pow_right_injective (by norm_num) hab

/-- Cardinality of the construction. -/
theorem card_oddPlusPowersOfTwo (N : ℕ) :
    (oddPlusPowersOfTwo N).card = (N + 1) / 2 + Nat.log 2 N := by
  unfold oddPlusPowersOfTwo
  rw [Finset.card_union_of_disjoint (disjoint_oddNumbers_powersOfTwo N),
    card_oddNumbersIn, card_powersOfTwoIn]

/-! ### Final lower bound on the maximum pair-free set size. -/

/-- **Improved lower bound for #327.** The maximum size of a pair-free
subset of `[1, N]` is at least `(N + 1) / 2 + ⌊log₂ N⌋`. This beats the
folklore odd-numbers bound by `Θ(log N)`. -/
theorem exists_pairFree_card_ge (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      A.card = (N + 1) / 2 + Nat.log 2 N := by
  exact ⟨oddPlusPowersOfTwo N,
    oddPlusPowersOfTwo_subset_Icc N,
    pairFree_oddPlusPowersOfTwo N,
    card_oddPlusPowersOfTwo N⟩

/-! ### Pushing further: the `m = 5` family.

The set `T := {2^k · m : k ≥ 1, m odd, m ≤ 2^k}` of *odd-conflict-free*
even numbers has cardinality `Θ(√N)` in `[1, N]`. After pruning internal
conflicts, one could hope to extract a pair-free subset of `T` of
comparable size, giving a polynomial improvement past `N/2`.

We formalise the first non-trivial slice, `m = 5`, here, proving that
each `5 · 2^k` (`k ≥ 3`) is pair-free with every odd number. The
internal `m = 5` conflict structure (`(5·2^k, 5·2^{k+2})` is the only
forbidden pair shape) and the cross-`m` analysis are left as the
natural follow-up direction. -/

/-- For odd `a > 0` and `k ≥ 3`, the pair `(a, 5·2^k)` is not a unit
fraction pair.

The proof uses the Bezout-style identity
`gcd(d, a · b) ∣ gcd(d, a) · gcd(d, b)` (`gcd_mul_dvd_mul_gcd` in any
GCD monoid). Setting `d = a + 5·2^k`, both `gcd(d, a)` and `gcd(d, 5·2^k)`
equal `gcd(5, a)` (since `a` is odd, hence coprime to `2^k`), and
`gcd(5, a) ∈ {1, 5}`. So `d ≤ 25`, contradicting `d ≥ 41` for `k ≥ 3`. -/
theorem fivePow_odd_pair_free {a k : ℕ} (ha : 0 < a) (hodd : a % 2 = 1)
    (hk : 3 ≤ k) : ¬ IsUnitFractionPair a (5 * 2 ^ k) := by
  unfold IsUnitFractionPair
  intro hdvd
  have hgcd_a2k : Nat.gcd a (2 ^ k) = 1 := by
    refine Nat.Coprime.pow_right k ?_
    rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd
  -- `gcd(5·2^k, a) = gcd(5, a)` since `gcd(2^k, a) = 1`.
  have hgcd_a_5pow : Nat.gcd (5 * 2 ^ k) a = Nat.gcd 5 a := by
    apply Nat.dvd_antisymm
    · -- gcd(5·2^k, a) ∣ gcd(5, a) · gcd(2^k, a) = gcd(5, a).
      have h : Nat.gcd a (5 * 2 ^ k) ∣ Nat.gcd a 5 * Nat.gcd a (2 ^ k) :=
        gcd_mul_dvd_mul_gcd a 5 (2 ^ k)
      rw [show Nat.gcd a (2 ^ k) = 1 from hgcd_a2k] at h
      rw [Nat.mul_one] at h
      rw [Nat.gcd_comm (5 * 2 ^ k) a, Nat.gcd_comm 5 a]
      exact h
    · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
      exact (Nat.gcd_dvd_left _ _).trans ⟨2 ^ k, rfl⟩
  -- `gcd(a + 5·2^k, a) = gcd(5·2^k, a) = gcd(5, a)`.
  have hg1 : Nat.gcd (a + 5 * 2 ^ k) a = Nat.gcd 5 a := by
    rw [Nat.add_comm, Nat.gcd_add_self_left]; exact hgcd_a_5pow
  -- `gcd(a + 5·2^k, 5·2^k) = gcd(a, 5·2^k) = gcd(a, 5)`.
  have hgcd_a_5pow' : Nat.gcd a (5 * 2 ^ k) = Nat.gcd a 5 := by
    rw [Nat.gcd_comm a (5 * 2 ^ k), hgcd_a_5pow, Nat.gcd_comm]
  have hg2 : Nat.gcd (a + 5 * 2 ^ k) (5 * 2 ^ k) = Nat.gcd a 5 := by
    rw [Nat.gcd_add_self_left]; exact hgcd_a_5pow'
  -- Bezout-style: `gcd(d, a · (5·2^k)) ∣ gcd(d, a) · gcd(d, 5·2^k)`.
  set d := a + 5 * 2 ^ k with hd_def
  have hbez : d.gcd (a * (5 * 2 ^ k)) ∣ d.gcd a * d.gcd (5 * 2 ^ k) :=
    gcd_mul_dvd_mul_gcd d a (5 * 2 ^ k)
  rw [hg1, hg2] at hbez
  -- `d ∣ a · (5·2^k)` so `gcd(d, …) = d`.
  have hgcd_eq : d.gcd (a * (5 * 2 ^ k)) = d := Nat.gcd_eq_left hdvd
  rw [hgcd_eq] at hbez
  -- `gcd 5 a = gcd a 5`.
  rw [show Nat.gcd 5 a = Nat.gcd a 5 from Nat.gcd_comm _ _] at hbez
  -- `gcd(a, 5) ∈ {1, 5}`, so the product is at most 25.
  set g := Nat.gcd a 5 with hg_def
  have hg_dvd5 : g ∣ 5 := Nat.gcd_dvd_right _ _
  have hg_le : g ≤ 5 := Nat.le_of_dvd (by norm_num) hg_dvd5
  have h2k_ge : (8 : ℕ) ≤ 2 ^ k := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hd_ge : 41 ≤ d := by omega
  have hg2_pos : 0 < g * g := by
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ ha
    positivity
  have hd_le : d ≤ g * g := Nat.le_of_dvd hg2_pos hbez
  nlinarith

/-- For `k ≥ 3` and `l ≥ 1`, the pair `(5·2^k, 2^l)` is not a unit
fraction pair. -/
theorem fivePow_powerOfTwo_pair_free {k l : ℕ} (_hk : 3 ≤ k) (hl : 1 ≤ l) :
    ¬ IsUnitFractionPair (5 * 2 ^ k) (2 ^ l) := by
  unfold IsUnitFractionPair
  intro hdvd
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · -- k < l. Sum factors as 2^k (5 + 2^(l-k)) with odd factor 5 + 2^(l-k) ≥ 7.
    have hpow : 2 ^ l = 2 ^ k * 2 ^ (l - k) := by
      rw [← pow_add]; congr 1; omega
    have hsum_eq : 5 * 2 ^ k + 2 ^ l = 2 ^ k * (5 + 2 ^ (l - k)) := by
      rw [hpow]; ring
    have hprod_eq : 5 * 2 ^ k * 2 ^ l = 2 ^ k * (5 * 2 ^ l) := by ring
    rw [hsum_eq, hprod_eq] at hdvd
    have h2k_pos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos _
    have hcancel : (5 + 2 ^ (l - k)) ∣ 5 * 2 ^ l :=
      (Nat.mul_dvd_mul_iff_left h2k_pos).mp hdvd
    have hlk_pos : 1 ≤ l - k := by omega
    have hodd_sum : (5 + 2 ^ (l - k)) % 2 = 1 := by
      have h2dvd : (2 : ℕ) ∣ 2 ^ (l - k) := dvd_pow_self 2 (by omega)
      omega
    have hcop : Nat.Coprime (5 + 2 ^ (l - k)) (2 ^ l) := by
      refine Nat.Coprime.pow_right l ?_
      rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd_sum
    have hcancel5 : (5 + 2 ^ (l - k)) ∣ 5 :=
      hcop.dvd_of_dvd_mul_right hcancel
    have h2le : 2 ≤ 2 ^ (l - k) := by
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ (l - k) := Nat.pow_le_pow_right (by norm_num) hlk_pos
    have hge : 7 ≤ 5 + 2 ^ (l - k) := by omega
    have hle : 5 + 2 ^ (l - k) ≤ 5 := Nat.le_of_dvd (by norm_num) hcancel5
    omega
  · -- k = l. Sum = 2^k · 6 = 6·2^k; product = 5·2^{2k}. (6·2^k) | 5·2^{2k} iff 3 | 5·2^k.
    subst hkl
    have hsum_eq : 5 * 2 ^ k + 2 ^ k = 6 * 2 ^ k := by ring
    have hprod_eq : 5 * 2 ^ k * 2 ^ k = 5 * 2 ^ (2 * k) := by
      rw [two_mul, pow_add]; ring
    rw [hsum_eq, hprod_eq] at hdvd
    -- 6 · 2^k ∣ 5 · 2^{2k}. Divide by 2^k: 6 ∣ 5 · 2^k. 3 ∣ 5·2^k. Contradiction.
    have h2k_pos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos _
    have hcancel : (6 : ℕ) ∣ 5 * 2 ^ k := by
      -- Rewrite `5 * 2^{2k}` as `2^k * (5 * 2^k)` to cancel.
      have hreq : 5 * 2 ^ (2 * k) = 2 ^ k * (5 * 2 ^ k) := by
        rw [show (2 * k) = k + k from by ring, pow_add]; ring
      rw [hreq] at hdvd
      have hcancel' : 2 ^ k * 6 ∣ 2 ^ k * (5 * 2 ^ k) := by
        rw [Nat.mul_comm (2 ^ k) 6]; exact hdvd
      exact (Nat.mul_dvd_mul_iff_left h2k_pos).mp hcancel'
    have h3dvd : (3 : ℕ) ∣ 5 * 2 ^ k := dvd_trans (by norm_num : (3 : ℕ) ∣ 6) hcancel
    have hcop3 : Nat.Coprime 3 (5 * 2 ^ k) := by
      have h35 : Nat.Coprime 3 5 := by decide
      have h32 : Nat.Coprime 3 (2 ^ k) := by
        refine Nat.Coprime.pow_right k ?_; decide
      exact h35.mul_right h32
    -- A coprime divisor must be 1.
    have h3eq1 : (3 : ℕ) = 1 := by
      have hgcd_eq : Nat.gcd 3 (5 * 2 ^ k) = 3 := Nat.gcd_eq_left h3dvd
      rw [hcop3] at hgcd_eq
      omega
    omega
  · -- k > l. Sum = 2^l(5·2^(k-l) + 1); odd factor 5·2^(k-l) + 1 ≥ 11 > 5.
    have hpow : 2 ^ k = 2 ^ l * 2 ^ (k - l) := by
      rw [← pow_add]; congr 1; omega
    have hsum_eq : 5 * 2 ^ k + 2 ^ l = 2 ^ l * (5 * 2 ^ (k - l) + 1) := by
      rw [hpow]; ring
    have hprod_eq : 5 * 2 ^ k * 2 ^ l = 2 ^ l * (5 * 2 ^ k) := by ring
    rw [hsum_eq, hprod_eq] at hdvd
    have h2l_pos : 0 < (2 : ℕ) ^ l := Nat.two_pow_pos _
    have hcancel : (5 * 2 ^ (k - l) + 1) ∣ 5 * 2 ^ k :=
      (Nat.mul_dvd_mul_iff_left h2l_pos).mp hdvd
    have hkl_pos : 1 ≤ k - l := by omega
    have hodd_sum : (5 * 2 ^ (k - l) + 1) % 2 = 1 := by
      have h2dvd : (2 : ℕ) ∣ 2 ^ (k - l) := dvd_pow_self 2 (by omega)
      omega
    have hcop : Nat.Coprime (5 * 2 ^ (k - l) + 1) (2 ^ k) := by
      refine Nat.Coprime.pow_right k ?_
      rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd_sum
    have hcancel5 : (5 * 2 ^ (k - l) + 1) ∣ 5 :=
      hcop.dvd_of_dvd_mul_right hcancel
    have h2le : 2 ≤ 2 ^ (k - l) := by
      calc (2 : ℕ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ (k - l) := Nat.pow_le_pow_right (by norm_num) hkl_pos
    have hge : 11 ≤ 5 * 2 ^ (k - l) + 1 := by omega
    have hle : 5 * 2 ^ (k - l) + 1 ≤ 5 := Nat.le_of_dvd (by norm_num) hcancel5
    omega

/-- Helper for `fivePow_pair_free_of_diff_ne_two`, assuming `k < l`. -/
private theorem fivePow_pair_free_aux {k l : ℕ}
    (h : k < l) (hlk_ne_two : l - k ≠ 2) :
    ¬ IsUnitFractionPair (5 * 2 ^ k) (5 * 2 ^ l) := by
  have hlk_pos : 1 ≤ l - k := by omega
  unfold IsUnitFractionPair
  intro hdvd
  have hpow : 2 ^ l = 2 ^ k * 2 ^ (l - k) := by
    rw [← pow_add]; congr 1; omega
  have hsum_eq : 5 * 2 ^ k + 5 * 2 ^ l = 5 * 2 ^ k * (1 + 2 ^ (l - k)) := by
    rw [hpow]; ring
  have hprod_eq : 5 * 2 ^ k * (5 * 2 ^ l) = 5 * 2 ^ k * (5 * 2 ^ l) := rfl
  rw [hsum_eq] at hdvd
  -- Cancel 5·2^k from both sides.
  have h_pos : 0 < 5 * 2 ^ k := by positivity
  have hcancel : (1 + 2 ^ (l - k)) ∣ 5 * 2 ^ l :=
    (Nat.mul_dvd_mul_iff_left h_pos).mp hdvd
  -- 1 + 2^(l-k) is odd.
  have hodd_sum : (1 + 2 ^ (l - k)) % 2 = 1 := by
    have h2dvd : (2 : ℕ) ∣ 2 ^ (l - k) := dvd_pow_self 2 (by omega)
    omega
  have hcop : Nat.Coprime (1 + 2 ^ (l - k)) (2 ^ l) := by
    refine Nat.Coprime.pow_right l ?_
    rw [Nat.coprime_two_right, Nat.odd_iff]; exact hodd_sum
  have hcancel5 : (1 + 2 ^ (l - k)) ∣ 5 :=
    hcop.dvd_of_dvd_mul_right hcancel
  -- 1 + 2^(l-k) ∣ 5 means 1 + 2^(l-k) ∈ {1, 5}, so 2^(l-k) ∈ {0, 4}.
  -- l - k ≥ 1 rules out 0; 2^(l-k) = 4 means l - k = 2.
  have h2pow_pos : 1 ≤ 2 ^ (l - k) := Nat.one_le_iff_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  have hle : 1 + 2 ^ (l - k) ≤ 5 := Nat.le_of_dvd (by norm_num) hcancel5
  -- 1 + 2^(l-k) divides 5. The odd divisors of 5 are 1 and 5.
  -- 1 + 2^(l-k) ≥ 3 (since 2^(l-k) ≥ 2 for l > k), so must equal 5.
  have h2le : 2 ≤ 2 ^ (l - k) := by
    calc (2 : ℕ) = 2 ^ 1 := by ring
      _ ≤ 2 ^ (l - k) := Nat.pow_le_pow_right (by norm_num) hlk_pos
  have heq5 : 1 + 2 ^ (l - k) = 5 := by
    -- divisors of 5 in [3, 5]: only 5.
    have : (1 + 2 ^ (l - k)) = 1 ∨ (1 + 2 ^ (l - k)) = 5 := by
      have h5 : Nat.Prime 5 := by decide
      rcases h5.eq_one_or_self_of_dvd _ hcancel5 with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases this with h | h
    · omega
    · exact h
  -- So 2^(l-k) = 4 = 2^2, hence l - k = 2.
  have : 2 ^ (l - k) = 4 := by omega
  have : l - k = 2 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4] at this
    exact Nat.pow_right_injective (by norm_num) this
  exact hlk_ne_two this

/-- For `k ≠ l` with `|k - l| ≠ 2`, the pair `(5·2^k, 5·2^l)` is not a
unit-fraction pair. The only internal `m = 5` conflict shape is exponents
differing by exactly 2. -/
theorem fivePow_pair_free_of_diff_ne_two {k l : ℕ} (hkl : k ≠ l)
    (hdiff_k : l + 2 ≠ k) (hdiff_l : k + 2 ≠ l) :
    ¬ IsUnitFractionPair (5 * 2 ^ k) (5 * 2 ^ l) := by
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · -- k < l: direct.
    apply fivePow_pair_free_aux hlt
    intro heq
    apply hdiff_l; omega
  · -- k > l: convert via commutativity.
    intro hpair
    have hpair' : IsUnitFractionPair (5 * 2 ^ l) (5 * 2 ^ k) := by
      unfold IsUnitFractionPair at hpair ⊢
      have heq_sum : 5 * 2 ^ l + 5 * 2 ^ k = 5 * 2 ^ k + 5 * 2 ^ l := by ring
      have heq_prod : 5 * 2 ^ l * (5 * 2 ^ k) = 5 * 2 ^ k * (5 * 2 ^ l) := by ring
      rw [heq_sum, heq_prod]; exact hpair
    apply fivePow_pair_free_aux hgt _ hpair'
    intro heq
    apply hdiff_k; omega

/-! ### Construction with `m = 5` alternating-exponent family. -/

/-- The `m = 5` family with exponents `k ≡ 3 (mod 4)`. Any two distinct
exponents in this set differ by a multiple of 4, hence never by exactly 2,
so the family is internally pair-free. -/
def m5FamilyIn (N : ℕ) : Finset ℕ :=
  ((Finset.Icc 0 (Nat.log 2 N)).filter (fun k => k % 4 = 3 ∧ 5 * 2 ^ k ≤ N)).image
    (fun k => 5 * 2 ^ k)

/-- The extended construction: odd numbers ∪ powers of 2 ∪ the m=5
alternating family. -/
def oddPlusPowersOfTwoPlusM5 (N : ℕ) : Finset ℕ :=
  oddPlusPowersOfTwo N ∪ m5FamilyIn N

/-- Every element of `m5FamilyIn N` has exponent `≥ 3` (the smallest `k`
with `k % 4 = 3` is `k = 3`). -/
private lemma m5FamilyIn_exp_ge_three {k : ℕ} (hk_mod : k % 4 = 3) : 3 ≤ k := by
  omega

/-- Members of `m5FamilyIn N` are exactly `5·2^k` for `k ≡ 3 (mod 4)`
with `k ≥ 3` and `5·2^k ≤ N`. -/
private lemma mem_m5FamilyIn_iff {N n : ℕ} :
    n ∈ m5FamilyIn N ↔
      ∃ k : ℕ, k % 4 = 3 ∧ 5 * 2 ^ k ≤ N ∧ n = 5 * 2 ^ k := by
  unfold m5FamilyIn
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨⟨_, _⟩, hk_mod, hk_bound⟩, hkn⟩
    exact ⟨k, hk_mod, hk_bound, hkn.symm⟩
  · rintro ⟨k, hk_mod, hk_bound, hkn⟩
    refine ⟨k, ⟨⟨Nat.zero_le _, ?_⟩, hk_mod, hk_bound⟩, hkn.symm⟩
    have hk_ge : 3 ≤ k := m5FamilyIn_exp_ge_three hk_mod
    have hN_pos : 0 < N := by
      have h2k_ge : 8 ≤ 2 ^ k := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk_ge
      omega
    have h2k_le : 2 ^ k ≤ N := by
      have h2pos : 0 < 2 ^ k := Nat.two_pow_pos _
      linarith
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hN_pos.ne').mpr h2k_le

/-- The m=5 family is internally pair-free: any two distinct exponents
in residue class 3 mod 4 differ by a multiple of 4, hence never by exactly 2. -/
theorem pairFree_m5FamilyIn (N : ℕ) : PairFree (m5FamilyIn N) := by
  intro a ha b hb hab hpair
  rw [mem_m5FamilyIn_iff] at ha hb
  obtain ⟨ka, ha_mod, _, ha_eq⟩ := ha
  obtain ⟨kb, hb_mod, _, hb_eq⟩ := hb
  have hka_ne_kb : ka ≠ kb := by
    intro heq
    apply hab
    rw [ha_eq, hb_eq, heq]
  -- ka, kb ≡ 3 mod 4, so ka - kb is a multiple of 4. Hence ≠ 2.
  have hdiff_k : kb + 2 ≠ ka := by intro h; omega
  have hdiff_l : ka + 2 ≠ kb := by intro h; omega
  rw [ha_eq, hb_eq] at hpair
  exact fivePow_pair_free_of_diff_ne_two hka_ne_kb hdiff_k hdiff_l hpair

/-- Pair-freeness of the extended construction. -/
theorem pairFree_oddPlusPowersOfTwoPlusM5 (N : ℕ) :
    PairFree (oddPlusPowersOfTwoPlusM5 N) := by
  intro a ha b hb hab hpair
  simp only [oddPlusPowersOfTwoPlusM5, Finset.mem_union] at ha hb
  rcases ha with ha_oddpow | ha_m5
  · rcases hb with hb_oddpow | hb_m5
    · -- Both in oddPlusPowersOfTwo.
      exact pairFree_oddPlusPowersOfTwo N a ha_oddpow b hb_oddpow hab hpair
    · -- a ∈ oddPlusPowersOfTwo, b ∈ m5Family.
      rw [mem_m5FamilyIn_iff] at hb_m5
      obtain ⟨kb, hb_mod, _, hb_eq⟩ := hb_m5
      have hkb_ge : 3 ≤ kb := m5FamilyIn_exp_ge_three hb_mod
      simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
        Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_image] at ha_oddpow
      rcases ha_oddpow with ⟨ha_range, ha_odd⟩ | ⟨ka, ⟨hka_pos, _⟩, hka_eq⟩
      · -- a odd, b = 5·2^kb. Use fivePow_odd_pair_free.
        have ha_pos : 0 < a := by have := ha_range.1; omega
        rw [hb_eq] at hpair
        exact fivePow_odd_pair_free ha_pos ha_odd hkb_ge hpair
      · -- a = 2^ka, b = 5·2^kb. Use fivePow_powerOfTwo_pair_free (swap).
        rw [← hka_eq, hb_eq] at hpair
        have hpair' : IsUnitFractionPair (5 * 2 ^ kb) (2 ^ ka) := by
          unfold IsUnitFractionPair at hpair ⊢
          have heq_sum : 5 * 2 ^ kb + 2 ^ ka = 2 ^ ka + 5 * 2 ^ kb := by ring
          have heq_prod : 5 * 2 ^ kb * 2 ^ ka = 2 ^ ka * (5 * 2 ^ kb) := by ring
          rw [heq_sum, heq_prod]; exact hpair
        exact fivePow_powerOfTwo_pair_free hkb_ge hka_pos hpair'
  · rcases hb with hb_oddpow | hb_m5
    · -- a ∈ m5Family, b ∈ oddPlusPowersOfTwo: symmetric.
      rw [mem_m5FamilyIn_iff] at ha_m5
      obtain ⟨ka, ha_mod, _, ha_eq⟩ := ha_m5
      have hka_ge : 3 ≤ ka := m5FamilyIn_exp_ge_three ha_mod
      simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
        Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_image] at hb_oddpow
      rcases hb_oddpow with ⟨hb_range, hb_odd⟩ | ⟨kb, ⟨hkb_pos, _⟩, hkb_eq⟩
      · have hb_pos : 0 < b := by have := hb_range.1; omega
        rw [ha_eq] at hpair
        have hpair' : IsUnitFractionPair b (5 * 2 ^ ka) := by
          unfold IsUnitFractionPair at hpair ⊢
          have heq_sum : b + 5 * 2 ^ ka = 5 * 2 ^ ka + b := by ring
          have heq_prod : b * (5 * 2 ^ ka) = 5 * 2 ^ ka * b := by ring
          rw [heq_sum, heq_prod]; exact hpair
        exact fivePow_odd_pair_free hb_pos hb_odd hka_ge hpair'
      · rw [ha_eq, ← hkb_eq] at hpair
        exact fivePow_powerOfTwo_pair_free hka_ge hkb_pos hpair
    · -- Both in m5Family.
      exact pairFree_m5FamilyIn N a ha_m5 b hb_m5 hab hpair

/-! ### Cardinality of the extended construction. -/

/-- The m=5 family is disjoint from the odd-plus-powers-of-2 set:
elements `5·2^k` with `k ≥ 3` are even (so not odd) and not pure powers
of 2 (since `5 ∤ 2^j` for any `j`). -/
theorem disjoint_oddPlusPowersOfTwo_m5 (N : ℕ) :
    Disjoint (oddPlusPowersOfTwo N) (m5FamilyIn N) := by
  rw [Finset.disjoint_left]
  intro n hn_op hn_m5
  rw [mem_m5FamilyIn_iff] at hn_m5
  obtain ⟨k, hk_mod, _, hk_eq⟩ := hn_m5
  have hk_ge : 3 ≤ k := m5FamilyIn_exp_ge_three hk_mod
  simp only [oddPlusPowersOfTwo, oddNumbersIn, powersOfTwoIn,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image] at hn_op
  rcases hn_op with ⟨_, hn_odd⟩ | ⟨j, ⟨hj_pos, _⟩, hj_eq⟩
  · -- n odd but n = 5·2^k is even.
    have h2dvd : (2 : ℕ) ∣ n := by
      rw [hk_eq]
      have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
      exact h2.mul_left 5
    omega
  · -- n = 2^j and n = 5·2^k, so 5·2^k = 2^j ⇒ 5 ∣ 2^j, impossible.
    have heq : 2 ^ j = 5 * 2 ^ k := by rw [hj_eq, hk_eq]
    have h5dvd : (5 : ℕ) ∣ 2 ^ j := by
      rw [heq]; exact Dvd.intro (2 ^ k) rfl
    have hcop : Nat.Coprime 5 (2 ^ j) := by
      refine Nat.Coprime.pow_right j ?_; decide
    have : (5 : ℕ) = 1 := by
      have := Nat.gcd_eq_left h5dvd
      rw [hcop] at this; omega
    omega

/-- Cardinality of the m=5 family. -/
theorem card_m5FamilyIn (N : ℕ) :
    (m5FamilyIn N).card =
      ((Finset.Icc 0 (Nat.log 2 N)).filter
        (fun k => k % 4 = 3 ∧ 5 * 2 ^ k ≤ N)).card := by
  unfold m5FamilyIn
  rw [Finset.card_image_of_injOn]
  intro a _ b _ hab
  exact Nat.pow_right_injective (le_refl 2) (by
    have h5_pos : 0 < (5 : ℕ) := by norm_num
    have heq : 5 * 2 ^ a = 5 * 2 ^ b := hab
    exact (Nat.mul_left_cancel h5_pos heq))

/-- Cardinality of the extended construction. -/
theorem card_oddPlusPowersOfTwoPlusM5 (N : ℕ) :
    (oddPlusPowersOfTwoPlusM5 N).card =
      (N + 1) / 2 + Nat.log 2 N +
        ((Finset.Icc 0 (Nat.log 2 N)).filter
          (fun k => k % 4 = 3 ∧ 5 * 2 ^ k ≤ N)).card := by
  unfold oddPlusPowersOfTwoPlusM5
  rw [Finset.card_union_of_disjoint (disjoint_oddPlusPowersOfTwo_m5 N),
    card_oddPlusPowersOfTwo, card_m5FamilyIn]

/-- The extended construction lies in `[1, N]`. -/
theorem oddPlusPowersOfTwoPlusM5_subset_Icc (N : ℕ) :
    oddPlusPowersOfTwoPlusM5 N ⊆ Finset.Icc 1 N := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn_op | hn_m5
  · exact oddPlusPowersOfTwo_subset_Icc N hn_op
  · rw [mem_m5FamilyIn_iff] at hn_m5
    obtain ⟨k, hk_mod, hk_le, hk_eq⟩ := hn_m5
    have hk_ge : 3 ≤ k := m5FamilyIn_exp_ge_three hk_mod
    rw [Finset.mem_Icc, hk_eq]
    refine ⟨?_, ?_⟩
    · have : 8 ≤ 2 ^ k := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk_ge
      omega
    · -- 5·2^k ≤ N follows from the family's defining filter.
      exact hk_le

/-- **Further-improved lower bound for #327.** The maximum size of a
pair-free subset of `[1, N]` is at least
`(N + 1) / 2 + ⌊log₂ N⌋ + |{k ≤ ⌊log₂ N⌋ : k ≡ 3 (mod 4), 5·2^k ≤ N}|`.

For `N ≥ 40` the extra m=5 term contributes at least one element; in
general it contributes `Θ(log N)` more elements on top of the
`(N + 1)/2 + ⌊log₂ N⌋` bound from `exists_pairFree_card_ge`. -/
theorem exists_pairFree_card_ge_v2 (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PairFree A ∧
      A.card = (N + 1) / 2 + Nat.log 2 N +
        ((Finset.Icc 0 (Nat.log 2 N)).filter
          (fun k => k % 4 = 3 ∧ 5 * 2 ^ k ≤ N)).card := by
  exact ⟨oddPlusPowersOfTwoPlusM5 N,
    oddPlusPowersOfTwoPlusM5_subset_Icc N,
    pairFree_oddPlusPowersOfTwoPlusM5 N,
    card_oddPlusPowersOfTwoPlusM5 N⟩

end UnitFractionPairs
