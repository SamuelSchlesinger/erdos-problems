/-
# Primitive Weird Numbers of the Form 2pq

For distinct primes p, q ≥ 5, if 2pq is weird then it is primitive weird.
The proper divisors of 2pq are {1, 2, p, q, 2p, 2q, pq}, and none is
abundant:
- 1, 2: too small to be abundant
- p, q: prime powers, deficient
- 2p, 2q: σ(2p) = 3(1+p) < 4p for p ≥ 5
- pq: σ(pq) = (1+p)(1+q) < 2pq for p,q ≥ 5

Since no proper divisor is abundant, none is weird, so 2pq is primitive.

This gives a structural proof that 70 = 2·5·7 is primitive weird,
replacing the `native_decide` proof.
-/
import Erdos.WeirdNumbers.OddWeird

namespace WeirdNumbers

/-! ### σ bounds for proper divisors of 2pq -/

/-- Helper: compute σ(p) = 1 + p for a prime p. -/
private theorem sigma_prime {p : ℕ} (hp : Nat.Prime p) :
    p.divisors.sum id = 1 + p := by
  rw [hp.divisors, Finset.sum_pair (Ne.symm hp.one_lt.ne')]
  simp

/-- **σ(2p) < 2·(2p) for prime p ≥ 5.**
    σ(2p) = σ(2)·σ(p) = 3·(1+p) by coprimality. Then 3+3p < 4p iff p > 3. -/
theorem sigma_two_prime_lt {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (2 * p).divisors.sum id < 2 * (2 * p) := by
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2
    have := hp.eq_one_or_self_of_dvd 2 h2
    omega
  have hmul : (2 * p).divisors.sum id = (2 : ℕ).divisors.sum id * p.divisors.sum id :=
    hcop.sum_divisors_mul
  have hσ2 : (2 : ℕ).divisors.sum id = 3 := by decide
  have hσp : p.divisors.sum id = 1 + p := sigma_prime hp
  rw [hmul, hσ2, hσp]
  nlinarith

/-- **σ(pq) < 2·(pq) for distinct primes p, q ≥ 5.**
    σ(pq) = (1+p)(1+q) by coprimality. Then 1+p+q+pq < 2pq iff 1+p+q < pq,
    which holds for p,q ≥ 5 since pq ≥ 25 > 11 ≥ 1+p+q. -/
theorem sigma_prime_prod_lt {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) :
    (p * q).divisors.sum id < 2 * (p * q) := by
  have hcop : Nat.Coprime p q := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd; exact hpq (hq.eq_one_or_self_of_dvd p hdvd |>.resolve_left hp.one_lt.ne')
  have hmul : (p * q).divisors.sum id = p.divisors.sum id * q.divisors.sum id :=
    hcop.sum_divisors_mul
  have hσp : p.divisors.sum id = 1 + p := sigma_prime hp
  have hσq : q.divisors.sum id = 1 + q := sigma_prime hq
  rw [hmul, hσp, hσq]
  nlinarith

/-- 2p is not abundant for prime p ≥ 5. -/
theorem two_prime_not_abundant {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    ¬Abundant (2 * p) := by
  intro ⟨_, hab⟩
  have hσ := sigma_two_prime_lt hp hp5
  have hsplit : (2 * p).divisors.sum id =
    (2 * p).properDivisors.sum id + 2 * p :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  linarith

/-- pq is not abundant for distinct primes p, q ≥ 5. -/
theorem prime_prod_not_abundant {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) :
    ¬Abundant (p * q) := by
  intro ⟨_, hab⟩
  have hσ := sigma_prime_prod_lt hp hq hpq hp5 hq5
  have hsplit : (p * q).divisors.sum id =
    (p * q).properDivisors.sum id + p * q :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  linarith

/-! ### No proper divisor of 2pq is weird -/

/-- Helper: if d divides a * b and d is coprime to b, then d divides a. -/
private theorem dvd_left_of_dvd_mul_coprime {d a b : ℕ}
    (hdvd : d ∣ a * b) (hcop : Nat.Coprime d b) : d ∣ a :=
  Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd

/-- **Divisor enumeration for 2pq.**
    If d divides 2*p*q where 2, p, q are distinct primes with p,q ≥ 5,
    then d ∈ {1, 2, p, q, 2p, 2q, pq, 2pq}. -/
private theorem dvd_two_pq_cases {p q d : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (_hpq : p ≠ q)
    (hdvd : d ∣ 2 * p * q) :
    d = 1 ∨ d = 2 ∨ d = p ∨ d = q ∨ d = 2 * p ∨ d = 2 * q ∨ d = p * q ∨ d = 2 * p * q := by
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  -- Case split on q | d
  by_cases hqd : q ∣ d
  · -- q | d, write d = q * e
    obtain ⟨e, he⟩ := hqd
    -- e | 2*p since d | 2*p*q and d = q*e
    have hq_ne : (q : ℕ) ≠ 0 := hq.ne_zero
    have he_dvd : e ∣ 2 * p := by
      have h1 : q * e ∣ 2 * p * q := he ▸ hdvd
      rwa [show 2 * p * q = q * (2 * p) from by ring,
           mul_dvd_mul_iff_left hq_ne] at h1
    -- Case split on p | e
    by_cases hpe : p ∣ e
    · -- p | e, write e = p * f
      obtain ⟨f, hf⟩ := hpe
      have hp_ne : (p : ℕ) ≠ 0 := hp.ne_zero
      have hf_dvd : f ∣ 2 := by
        have h1 : p * f ∣ 2 * p := hf ▸ he_dvd
        rwa [show 2 * p = p * 2 from by ring,
             mul_dvd_mul_iff_left hp_ne] at h1
      -- f | 2 means f ∈ {1, 2}
      have hf_le : f ≤ 2 := Nat.le_of_dvd (by omega) hf_dvd
      interval_cases f
      · -- f = 0: impossible since f | 2
        omega
      · -- f = 1: d = q * (p * 1) = pq
        right; right; right; right; right; right; left
        rw [he, hf]; ring
      · -- f = 2: d = q * (p * 2) = 2pq
        right; right; right; right; right; right; right
        rw [he, hf]; ring
    · -- p ∤ e, so e is coprime to p, hence e | 2
      have hcop : Nat.Coprime e p := by
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        exact hpe
      have he2 : e ∣ 2 := dvd_left_of_dvd_mul_coprime he_dvd hcop
      have he_le : e ≤ 2 := Nat.le_of_dvd (by omega) he2
      interval_cases e
      · -- e = 0: impossible
        omega
      · -- e = 1: d = q
        right; right; right; left
        rw [he]; ring
      · -- e = 2: d = 2q
        right; right; right; right; right; left
        rw [he]; ring
  · -- q ∤ d, so d is coprime to q
    have hcop : Nat.Coprime d q := by
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      exact hqd
    -- d | 2*p (since d | 2*p*q and gcd(d,q) = 1)
    have hd_dvd2p : d ∣ 2 * p :=
      dvd_left_of_dvd_mul_coprime hdvd hcop
    -- Case split on p | d
    by_cases hpd : p ∣ d
    · obtain ⟨f, hf⟩ := hpd
      have hp_ne : (p : ℕ) ≠ 0 := hp.ne_zero
      have hf_dvd : f ∣ 2 := by
        have h1 : p * f ∣ 2 * p := hf ▸ hd_dvd2p
        rwa [show 2 * p = p * 2 from by ring,
             mul_dvd_mul_iff_left hp_ne] at h1
      have hf_le : f ≤ 2 := Nat.le_of_dvd (by omega) hf_dvd
      interval_cases f
      · omega
      · -- f = 1: d = p
        right; right; left
        rw [hf]; ring
      · -- f = 2: d = 2p
        right; right; right; right; left
        rw [hf]; ring
    · -- p ∤ d, so d is coprime to p
      have hcop2 : Nat.Coprime d p := by
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        exact hpd
      have hd2 : d ∣ 2 := dvd_left_of_dvd_mul_coprime hd_dvd2p hcop2
      have hd_le : d ≤ 2 := Nat.le_of_dvd (by omega) hd2
      interval_cases d
      · omega
      · left; rfl
      · right; left; rfl

/-- No proper divisor of 2pq is weird, for distinct primes p, q ≥ 5.

    The proper divisors are {1, 2, p, q, 2p, 2q, pq}. None is abundant:
    - 1: σ(1) = 1 < 2
    - 2: σ(2) = 3 < 4
    - p, q: prime powers are deficient
    - 2p, 2q: σ(2p) = 3(1+p) < 4p for p ≥ 5
    - pq: σ(pq) = (1+p)(1+q) < 2pq for p,q ≥ 5 -/
theorem no_weird_proper_divisor_2pq {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) :
    ∀ d ∈ (2 * p * q).properDivisors, ¬Weird d := by
  intro d hd hw
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨hd_dvd, hd_lt⟩ := hd
  have hab := hw.1
  -- Enumerate: d ∈ {1, 2, p, q, 2p, 2q, pq, 2pq}
  rcases dvd_two_pq_cases hp hq hp5 hq5 hpq hd_dvd with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- d = 1: not abundant
  · exact (fun ⟨_, h⟩ => by simp at h) hab
  -- d = 2: prime power, not abundant
  · exact prime_pow_not_abundant Nat.prime_two 1 (by rwa [pow_one]) |>.elim
  -- d = p: prime power, not abundant
  · exact prime_pow_not_abundant hp 1 (by rwa [pow_one]) |>.elim
  -- d = q: prime power, not abundant
  · exact prime_pow_not_abundant hq 1 (by rwa [pow_one]) |>.elim
  -- d = 2p: not abundant
  · exact two_prime_not_abundant hp hp5 hab
  -- d = 2q: not abundant
  · exact two_prime_not_abundant hq hq5 hab
  -- d = pq: not abundant
  · exact prime_prod_not_abundant hp hq hpq hp5 hq5 hab
  -- d = 2pq: contradicts d < 2pq
  · omega

/-- **For distinct primes p, q ≥ 5, if 2pq is weird then it is primitive weird.**

    Since no proper divisor of 2pq is weird (none is even abundant),
    weirdness of 2pq immediately implies primitive weirdness. -/
theorem two_pq_primitive_when_weird {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hw : Weird (2 * p * q)) :
    PrimitiveWeird (2 * p * q) :=
  ⟨hw, no_weird_proper_divisor_2pq hp hq hpq hp5 hq5⟩

/-- **70 = 2·5·7 is primitive weird (structural proof).**

    This replaces the `native_decide` proof of `seventy_is_primitive_weird`
    with a structural argument. -/
theorem seventy_primitive_weird_structural : PrimitiveWeird 70 := by
  have h70 : 2 * 5 * 7 = 70 := by norm_num
  rw [← h70]
  exact two_pq_primitive_when_weird (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    (by rw [h70]; exact seventy_is_weird)

end WeirdNumbers
