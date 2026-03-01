/-
# Erdős-Straus Conjecture: Combined Results

This file combines all proven cases of the Erdős-Straus conjecture.

## Complete coverage:

### By residue class:
- Even n: 4/(2m) = 1/m + 1/(m+1) + 1/(m(m+1))
- n ≡ 3 mod 4: via x = (n+1)/4 and partial fractions
- n ≡ 2 mod 3: via 1/((n+1)/3) + 1/n + 1/(n(n+1)/3)
- n ≡ 0 mod 3: via 1/(n/3) + 1/(n+1) + 1/(n(n+1)/3)
- n ≡ 13 mod 24: via c = 3, d = 2 factorization

### By prime factorization:
- n ≡ 1 mod 4 with a prime factor p ≡ 3 mod 4: via c = p, d = p

### Net result:
The conjecture holds for ALL n > 2 except possibly n ≡ 1 mod 4 whose
prime factorization consists entirely of primes ≡ 1 mod 4, AND where
n ≡ 1 mod 3 (so all primes are ≡ 1 mod 12), AND where additionally the
"greedy" c = 3 decomposition fails (all prime factors of n(n+3)/4 are ≡ 1 mod 3).

### Reduction theorems:
- `reduction_to_odd_primes`: the full conjecture follows from the conjecture
  for all odd primes
- `reduction_to_primes_1_mod_24`: the full conjecture follows from the
  conjecture for primes p ≡ 1 (mod 24)
-/
import Erdos.ErdosStraus.EvenCase
import Erdos.ErdosStraus.Mod4Eq3
import Erdos.ErdosStraus.Mod4Eq1
import Erdos.ErdosStraus.Factorization
import Erdos.ErdosStraus.PrimeFactor
import Erdos.ErdosStraus.Divisor

namespace ErdosStraus

/-- The Erdős-Straus conjecture holds for all n > 2 that are not ≡ 1 (mod 24). -/
theorem not_1_mod_24 (n : ℕ) (hn : 2 < n) (hmod : n % 24 ≠ 1) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  by_cases heven : n % 2 = 0
  · exact even_case n hn ⟨n / 2, by omega⟩
  · by_cases h3 : n % 4 = 3
    · exact mod4_eq3_case n hn h3
    · by_cases h30 : n % 3 = 0
      · exact mod3_eq0_case n hn h30
      · by_cases h32 : n % 3 = 2
        · exact mod3_eq2_case n hn h32
        · by_cases h13 : n % 24 = 13
          · exact mod24_eq13_case n hn h13
          · exfalso; apply hmod; omega

/-- The Erdős-Straus conjecture reduces to odd primes: if the conjecture holds
    for every prime p ≥ 3, then it holds for all n > 2.

    Proof: For even n, use `even_case`. For odd n > 2, extract its smallest
    prime factor p via `Nat.minFac`. Since n is odd, p is odd, so p ≥ 3.
    Write n = (n/p) · p and apply `of_multiple` to lift the decomposition
    from p to n. -/
theorem reduction_to_odd_primes
    (h : ∀ p : ℕ, Nat.Prime p → 2 < p →
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    Conjecture := by
  intro n hn
  by_cases heven : n % 2 = 0
  · exact even_case n hn ⟨n / 2, by omega⟩
  · -- n is odd, n > 2. Extract its smallest prime factor.
    set p := n.minFac with hp_def
    have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
    have hp_dvd : p ∣ n := Nat.minFac_dvd n
    -- p ≠ 2 since 2 ∤ n (n is odd)
    have hp_ne_2 : p ≠ 2 := by
      intro heq; have h2dvd : 2 ∣ n := heq ▸ hp_dvd; obtain ⟨k, hk⟩ := h2dvd; omega
    have hp_gt2 : 2 < p := by have := hp_prime.two_le; omega
    -- Write n = (n/p) · p and lift via of_multiple
    set k := n / p with hk_def
    have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_prime.pos
    have hn_eq : k * p = n := Nat.div_mul_cancel hp_dvd
    rw [← hn_eq]; push_cast [Nat.cast_mul]
    exact of_multiple p k hp_gt2 hk_pos (h p hp_prime hp_gt2)

/-- The Erdős-Straus conjecture reduces to primes ≡ 1 (mod 24): if the
    conjecture holds for every prime p with p ≡ 1 (mod 24), then it holds
    for all n > 2.

    This is the strongest elementary reduction we can achieve. Combined with
    our complete coverage of all other residue classes (even, ≡ 3 mod 4,
    ≡ 0 mod 3, ≡ 2 mod 3, ≡ 13 mod 24), the entire conjecture rests on
    a single sparse case: primes p ≡ 1 (mod 24). -/
theorem reduction_to_primes_1_mod_24
    (h : ∀ p : ℕ, Nat.Prime p → p % 24 = 1 →
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    Conjecture := by
  apply reduction_to_odd_primes
  intro p hp_prime hp_gt2
  by_cases hmod24 : p % 24 = 1
  · exact h p hp_prime hmod24
  · exact not_1_mod_24 p hp_gt2 hmod24

end ErdosStraus
