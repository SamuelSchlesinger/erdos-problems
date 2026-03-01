/-
# Structural Results Toward Odd Weird Numbers

Key results constraining weird numbers:

1. **Prime powers are deficient**: σ(p^a) < 2·p^a for any prime p.
   No prime power is abundant, hence none is weird.

2. **Products of two distinct odd primes are deficient**:
   For distinct odd primes p ≥ 3, q ≥ 5: σ(p^a·q^b) < 2·p^a·q^b.

3. **Corollary**: Any odd weird number must have ≥ 3 distinct prime factors.

These are steps toward Erdős's $10 question: do odd weird numbers exist?
-/
import Erdos.WeirdNumbers.Statement

namespace WeirdNumbers

/-! ### Prime powers are deficient -/

/-- The geometric sum 1 + p + ... + p^a satisfies the identity
    (∑ p^i) · (p - 1) = p^{a+1} - 1 in ℕ, for p ≥ 2. -/
private theorem geom_sum_mul_pred {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) = p ^ (a + 1) - 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have h1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ p ^ (a + 2) := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2, show 1 ≤ p from by omega]
    ring

/-- **σ(p^a) < 2·p^a for any prime p.**
    Proof by induction: σ(p^{a+1}) = σ(p^a) + p^{a+1} < 2p^a + p^{a+1} ≤ 2p^{a+1}. -/
theorem sigma_prime_pow_lt {p : ℕ} (hp : Nat.Prime p) (a : ℕ) :
    (p ^ a).divisors.sum id < 2 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [id]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ]
    have hge2 := hp.two_le
    have hpa_pos : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
    -- 2·p^a ≤ p^(a+1) since p ≥ 2
    have hstep : 2 * p ^ a ≤ p ^ (a + 1) := by
      rw [pow_succ]
      nlinarith
    linarith

/-- No prime power is abundant. -/
theorem prime_pow_not_abundant {p : ℕ} (hp : Nat.Prime p) (a : ℕ) :
    ¬Abundant (p ^ a) := by
  intro ⟨_, hab⟩
  have hσ := sigma_prime_pow_lt hp a
  have hsplit : (p ^ a).divisors.sum id =
    (p ^ a).properDivisors.sum id + p ^ a :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  linarith

/-- No prime power is weird. -/
theorem prime_pow_not_weird {p : ℕ} (hp : Nat.Prime p) (a : ℕ) :
    ¬Weird (p ^ a) :=
  fun ⟨hab, _⟩ => prime_pow_not_abundant hp a hab

/-! ### Tighter bounds for the two-prime argument -/

/-- For p ≥ 3: 2·σ(p^a) < 3·p^a.
    From the identity σ·(p-1) = p^{a+1}-1, we get
    2·(p^{a+1}-1) < 3·p^a·(p-1) since (p-3)·p^a + 2 > 0. -/
private theorem sigma_bound_ge3 {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) (a : ℕ) :
    2 * (p ^ a).divisors.sum id < 3 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  set s := ∑ i ∈ Finset.range (a + 1), p ^ i
  have hmul := geom_sum_mul_pred hp.two_le a  -- s * (p-1) = p^(a+1) - 1
  have hpa : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hpa1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  suffices h : 2 * s * (p - 1) < 3 * p ^ a * (p - 1) by
    exact (Nat.mul_lt_mul_right (by omega : 0 < p - 1)).mp h
  -- Additive form of the identity, avoiding ℕ subtraction
  have hmul_add : s * (p - 1) + 1 = p ^ (a + 1) := by
    rw [hmul]; exact Nat.sub_add_cancel hpa1
  have hpow : p ^ (a + 1) = p ^ a * p := pow_succ p a
  -- Lift to ℤ for clean nlinarith
  zify [show 1 ≤ p from by omega] at hmul_add hpow hpa hp3 ⊢
  nlinarith

/-- For p ≥ 5: 4·σ(p^a) < 5·p^a. -/
private theorem sigma_bound_ge5 {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (a : ℕ) :
    4 * (p ^ a).divisors.sum id < 5 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  set s := ∑ i ∈ Finset.range (a + 1), p ^ i
  have hmul := geom_sum_mul_pred hp.two_le a
  have hpa : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hpa1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  suffices h : 4 * s * (p - 1) < 5 * p ^ a * (p - 1) by
    exact (Nat.mul_lt_mul_right (by omega : 0 < p - 1)).mp h
  have hmul_add : s * (p - 1) + 1 = p ^ (a + 1) := by
    rw [hmul]; exact Nat.sub_add_cancel hpa1
  have hpow : p ^ (a + 1) = p ^ a * p := pow_succ p a
  zify [show 1 ≤ p from by omega] at hmul_add hpow hpa hp5 ⊢
  nlinarith

/-! ### Products of two distinct odd primes are deficient -/

/-- **σ(p^a · q^b) < 2·p^a·q^b for distinct odd primes p ≥ 3, q ≥ 5.**

    We use the bounds 2·σ(p^a) < 3·p^a and 4·σ(q^b) < 5·q^b.
    Multiplying: 8·σ(p^a)·σ(q^b) < 15·p^a·q^b < 16·p^a·q^b.
    Dividing by 8: σ(p^a)·σ(q^b) < 2·p^a·q^b. -/
theorem sigma_two_odd_primes_lt {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (a b : ℕ) :
    (p ^ a * q ^ b).divisors.sum id < 2 * (p ^ a * q ^ b) := by
  -- Coprimality of p^a and q^b
  have hcop : Nat.Coprime (p ^ a) (q ^ b) := by
    apply Nat.Coprime.pow
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    rcases hq.eq_one_or_self_of_dvd p hdvd with h | h
    · exact absurd h hp.one_lt.ne'
    · exact hpq h
  -- Multiplicativity: σ(p^a · q^b) = σ(p^a) · σ(q^b)
  have hmul : (p ^ a * q ^ b).divisors.sum id =
    (p ^ a).divisors.sum id * (q ^ b).divisors.sum id :=
    hcop.sum_divisors_mul
  rw [hmul]
  set σp := (p ^ a).divisors.sum id
  set σq := (q ^ b).divisors.sum id
  -- Bounds: 2σp < 3·p^a and 4σq < 5·q^b
  have hbp := sigma_bound_ge3 hp hp3 a   -- 2*σp < 3*p^a
  have hbq := sigma_bound_ge5 hq hq5 b   -- 4*σq < 5*q^b
  -- Positivity
  have hσp_pos : 0 < σp := by
    apply Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    exact ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσq_pos : 0 < σq := by
    apply Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    exact ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hpa_pos : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hqb_pos : 0 < q ^ b := Nat.pos_of_ne_zero (pow_ne_zero b (by omega))
  -- Key products: (2σp)*(4σq) < (3p^a)*(5q^b) = 15p^aq^b
  have hmul1 : σp * (4 * σq) < σp * (5 * q ^ b) :=
    mul_lt_mul_of_pos_left hbq hσp_pos
  have hmul2 : (2 * σp) * (5 * q ^ b) < (3 * p ^ a) * (5 * q ^ b) :=
    mul_lt_mul_of_pos_right hbp (by positivity)
  -- 8σpσq < 15p^aq^b ≤ 16p^aq^b = 8·2p^aq^b, so σpσq < 2p^aq^b
  nlinarith

/-- Products of two distinct odd primes (with any exponents) are not abundant. -/
theorem two_odd_primes_not_abundant {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (a b : ℕ) :
    ¬Abundant (p ^ a * q ^ b) := by
  intro ⟨_, hab⟩
  have hσ := sigma_two_odd_primes_lt hp hq hpq hp3 hq5 a b
  have hsplit : (p ^ a * q ^ b).divisors.sum id =
    (p ^ a * q ^ b).properDivisors.sum id + p ^ a * q ^ b :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  linarith

end WeirdNumbers
