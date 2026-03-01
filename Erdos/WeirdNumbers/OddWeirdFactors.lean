/-
# Odd Weird Numbers Need ≥3 Distinct Prime Factors

Combining existing results:
- 0 prime factors: n = 1, not abundant
- 1 prime factor: n = p^a, not abundant (prime_pow_not_abundant)
- 2 prime factors: n = p^a · q^b for distinct odd primes, not abundant
  (two_odd_primes_not_abundant)

Therefore any odd weird number must have at least 3 distinct prime factors.
This is a step toward Erdős's $10 question on odd weird numbers.
-/
import Erdos.WeirdNumbers.OddWeird

namespace WeirdNumbers

/-! ### Odd numbers with ≤ 2 prime factors are not abundant -/

/-- **An odd number with at most 2 distinct prime factors is not abundant.**

    Case analysis on the number of prime factors:
    - 0 factors: n = 1, and σ(1) = 1 < 2
    - 1 factor: n = p^a for odd prime p, deficient by `prime_pow_not_abundant`
    - 2 factors: n = p^a · q^b for distinct odd primes, deficient by
      `two_odd_primes_not_abundant` -/
theorem odd_le_two_primes_not_abundant {n : ℕ} (hn : 0 < n) (hodd : ¬Even n)
    (hpf : n.primeFactors.card ≤ 2) : ¬Abundant n := by
  -- n = ∏ p in n.primeFactors, p ^ n.factorization p
  have hfact := Nat.factorization_prod_pow_eq_self (Nat.ne_of_gt (by omega : 0 < n))
  rcases h : n.primeFactors.card with _ | _ | _
  · -- 0 prime factors: n = 1
    rw [Finset.card_eq_zero] at h
    have hn1 : n = 1 := by
      rw [← hfact]
      simp only [Finsupp.prod, Nat.support_factorization, h, Finset.prod_empty]
    subst hn1
    intro ⟨_, hab⟩; simp at hab
  · -- 1 prime factor: n = p^a
    rw [Finset.card_eq_one] at h
    obtain ⟨p, hp⟩ := h
    have hpmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton.mpr rfl
    have hprime : Nat.Prime p := (Nat.mem_primeFactors.mp hpmem).1
    have : n = p ^ n.factorization p := by
      conv_lhs => rw [← hfact]
      simp only [Finsupp.prod, Nat.support_factorization, hp]
      rw [Finset.prod_singleton]
    rw [this]
    exact prime_pow_not_abundant hprime _
  · -- 2 prime factors: extract them
    have h2 : n.primeFactors.card = 2 := by omega
    obtain ⟨p, q, hpq, hpqs⟩ := Finset.card_eq_two.mp h2
    -- Both are prime
    have hpmem : p ∈ n.primeFactors := by
      rw [hpqs]; exact Finset.mem_insert_self _ _
    have hqmem : q ∈ n.primeFactors := by
      rw [hpqs]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    have hp : Nat.Prime p := (Nat.mem_primeFactors.mp hpmem).1
    have hq : Nat.Prime q := (Nat.mem_primeFactors.mp hqmem).1
    -- Both are odd (since n is odd)
    have hp_odd : p ≠ 2 := by
      intro h2; subst h2
      exact hodd (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hpmem))
    have hq_odd : q ≠ 2 := by
      intro h2; subst h2
      exact hodd (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hqmem))
    have hp3 : 3 ≤ p := by
      have := hp.two_le; omega
    have hq3 : 3 ≤ q := by
      have := hq.two_le; omega
    -- n = p^a * q^b
    have hfact2 : n = p ^ n.factorization p * q ^ n.factorization q := by
      conv_lhs => rw [← hfact]
      simp only [Finsupp.prod, Nat.support_factorization, hpqs]
      rw [Finset.prod_insert (by simp [hpq])]
      rw [Finset.prod_singleton]
    rw [hfact2]
    -- WLOG p ≤ q or q < p; both ≥ 3 and prime, distinct ⟹ one ≥ 5
    -- Both ≥ 3 and distinct ⟹ at least one ≥ 5.
    -- If both < 5: each is 3 (only odd prime in [3,5)), contradicting p ≠ q.
    have not_prime_four : ¬Nat.Prime 4 := by decide
    by_cases hle : p ≤ q
    · have hq5 : 5 ≤ q := by
        rcases Nat.lt_or_ge q 5 with hlt | hge
        · -- q ∈ {3, 4}, prime, so q = 3. Then p ≤ 3 and p ≥ 3, so p = 3 = q.
          have : q = 3 ∨ q = 4 := by omega
          rcases this with rfl | rfl
          · omega  -- p ≤ 3, p ≥ 3, p ≠ 3 is impossible
          · exact absurd hq not_prime_four
        · exact hge
      exact two_odd_primes_not_abundant hp hq hpq hp3 hq5 _ _
    · push_neg at hle
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with hlt | hge
        · have : p = 3 ∨ p = 4 := by omega
          rcases this with rfl | rfl
          · omega  -- q < 3 = p, q ≥ 3 is impossible
          · exact absurd hp not_prime_four
        · exact hge
      rw [mul_comm]
      exact two_odd_primes_not_abundant hq hp (Ne.symm hpq) hq3 hp5 _ _

/-- **Any odd weird number must have at least 3 distinct prime factors.**

    Contrapositive of `odd_le_two_primes_not_abundant`: if n has ≤ 2 prime
    factors and is odd, it's not abundant, hence not weird. -/
theorem odd_weird_three_prime_factors {n : ℕ} (hw : Weird n) (hodd : ¬Even n) :
    3 ≤ n.primeFactors.card := by
  by_contra h
  push_neg at h
  exact odd_le_two_primes_not_abundant hw.1.1 hodd (by omega) hw.1

end WeirdNumbers
