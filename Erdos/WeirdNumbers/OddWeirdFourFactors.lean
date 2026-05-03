/-
# Odd Weird Numbers Need ≥4 Distinct Prime Factors

For any odd number n with exactly 3 distinct prime factors p < q < r:
- If (p,q,r) ∉ {(3,5,7), (3,5,11), (3,5,13)}, then n is not abundant.
- For each surviving triple, every abundant n = p^a·q^b·r^c is pseudoperfect
  (proved via explicit covering: one of 8 primitive abundant numbers divides n).

Therefore any odd weird number must have at least 4 distinct prime factors.
This strengthens `odd_weird_three_prime_factors` toward Liddy-Riedl's ≥6.
-/
import Erdos.WeirdNumbers.OddWeirdFactors
import Erdos.WeirdNumbers.Structure

namespace WeirdNumbers

/-! ### Additional σ bounds for prime powers -/

/-- The geometric sum identity, re-exported from OddWeird.lean's proof pattern. -/
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

/-- The sum of divisors of a prime is `p + 1`. -/
private theorem sum_divisors_prime_pow_one {p : ℕ} (hp : Nat.Prime p) :
    (p ^ 1).divisors.sum id = p + 1 := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp [Finset.sum_range_succ]
  omega

/-- For p ≥ 7: 6·σ(p^a) < 7·p^a. -/
private theorem sigma_bound_ge7 {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (a : ℕ) :
    6 * (p ^ a).divisors.sum id < 7 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  set s := ∑ i ∈ Finset.range (a + 1), p ^ i
  have hmul := geom_sum_mul_pred hp.two_le a
  have hpa : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hpa1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  suffices h : 6 * s * (p - 1) < 7 * p ^ a * (p - 1) by
    exact (Nat.mul_lt_mul_right (by omega : 0 < p - 1)).mp h
  have hmul_add : s * (p - 1) + 1 = p ^ (a + 1) := by
    rw [hmul]; exact Nat.sub_add_cancel hpa1
  have hpow : p ^ (a + 1) = p ^ a * p := pow_succ p a
  zify [show 1 ≤ p from by omega] at hmul_add hpow hpa hp7 ⊢
  nlinarith

/-- For p ≥ 11: 10·σ(p^a) < 11·p^a. -/
private theorem sigma_bound_ge11 {p : ℕ} (hp : Nat.Prime p) (hp11 : 11 ≤ p) (a : ℕ) :
    10 * (p ^ a).divisors.sum id < 11 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  set s := ∑ i ∈ Finset.range (a + 1), p ^ i
  have hmul := geom_sum_mul_pred hp.two_le a
  have hpa : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hpa1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  suffices h : 10 * s * (p - 1) < 11 * p ^ a * (p - 1) by
    exact (Nat.mul_lt_mul_right (by omega : 0 < p - 1)).mp h
  have hmul_add : s * (p - 1) + 1 = p ^ (a + 1) := by
    rw [hmul]; exact Nat.sub_add_cancel hpa1
  have hpow : p ^ (a + 1) = p ^ a * p := pow_succ p a
  zify [show 1 ≤ p from by omega] at hmul_add hpow hpa hp11 ⊢
  nlinarith

/-- For p ≥ 13: 12·σ(p^a) < 13·p^a. -/
private theorem sigma_bound_ge13 {p : ℕ} (hp : Nat.Prime p) (hp13 : 13 ≤ p) (a : ℕ) :
    12 * (p ^ a).divisors.sum id < 13 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  set s := ∑ i ∈ Finset.range (a + 1), p ^ i
  have hmul := geom_sum_mul_pred hp.two_le a
  have hpa : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hpa1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  suffices h : 12 * s * (p - 1) < 13 * p ^ a * (p - 1) by
    exact (Nat.mul_lt_mul_right (by omega : 0 < p - 1)).mp h
  have hmul_add : s * (p - 1) + 1 = p ^ (a + 1) := by
    rw [hmul]; exact Nat.sub_add_cancel hpa1
  have hpow : p ^ (a + 1) = p ^ a * p := pow_succ p a
  zify [show 1 ≤ p from by omega] at hmul_add hpow hpa hp13 ⊢
  nlinarith

/-- For p ≥ 17: 16·σ(p^a) < 17·p^a. -/
private theorem sigma_bound_ge17 {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p) (a : ℕ) :
    16 * (p ^ a).divisors.sum id < 17 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  set s := ∑ i ∈ Finset.range (a + 1), p ^ i
  have hmul := geom_sum_mul_pred hp.two_le a
  have hpa : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hpa1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  suffices h : 16 * s * (p - 1) < 17 * p ^ a * (p - 1) by
    exact (Nat.mul_lt_mul_right (by omega : 0 < p - 1)).mp h
  have hmul_add : s * (p - 1) + 1 = p ^ (a + 1) := by
    rw [hmul]; exact Nat.sub_add_cancel hpa1
  have hpow : p ^ (a + 1) = p ^ a * p := pow_succ p a
  zify [show 1 ≤ p from by omega] at hmul_add hpow hpa hp17 ⊢
  nlinarith

/-- For p ≥ 19: 18·σ(p^a) < 19·p^a. -/
private theorem sigma_bound_ge19 {p : ℕ} (hp : Nat.Prime p) (hp19 : 19 ≤ p) (a : ℕ) :
    18 * (p ^ a).divisors.sum id < 19 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  set s := ∑ i ∈ Finset.range (a + 1), p ^ i
  have hmul := geom_sum_mul_pred hp.two_le a
  have hpa : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hpa1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  suffices h : 18 * s * (p - 1) < 19 * p ^ a * (p - 1) by
    exact (Nat.mul_lt_mul_right (by omega : 0 < p - 1)).mp h
  have hmul_add : s * (p - 1) + 1 = p ^ (a + 1) := by
    rw [hmul]; exact Nat.sub_add_cancel hpa1
  have hpow : p ^ (a + 1) = p ^ a * p := pow_succ p a
  zify [show 1 ≤ p from by omega] at hmul_add hpow hpa hp19 ⊢
  nlinarith

/-! ### σ multiplicativity for three coprime prime powers -/

/-- σ is multiplicative over three pairwise coprime prime powers. -/
theorem sigma_three_primes_mul {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (a b c : ℕ) :
    (p ^ a * q ^ b * r ^ c).divisors.sum id =
      (p ^ a).divisors.sum id * (q ^ b).divisors.sum id * (r ^ c).divisors.sum id := by
  -- Coprimality: p^a coprime to q^b * r^c, and q^b coprime to r^c
  have hcop_qr : Nat.Coprime (q ^ b) (r ^ c) := by
    apply Nat.Coprime.pow
    rw [hq.coprime_iff_not_dvd]
    intro hdvd
    rcases hr.eq_one_or_self_of_dvd q hdvd with h | h
    · exact absurd h hq.one_lt.ne'
    · exact hqr h
  have hcop_p_qr : Nat.Coprime (p ^ a) (q ^ b * r ^ c) := by
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      rcases hq.eq_one_or_self_of_dvd p hdvd with h | h
      · exact absurd h hp.one_lt.ne'
      · exact hpq h
    · apply Nat.Coprime.pow
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      rcases hr.eq_one_or_self_of_dvd p hdvd with h | h
      · exact absurd h hp.one_lt.ne'
      · exact hpr h
  -- Use multiplicativity: σ(mn) = σ(m)σ(n) for coprime m, n
  have h1 : (p ^ a * (q ^ b * r ^ c)).divisors.sum id =
      (p ^ a).divisors.sum id * (q ^ b * r ^ c).divisors.sum id :=
    hcop_p_qr.sum_divisors_mul
  have h2 : (q ^ b * r ^ c).divisors.sum id =
      (q ^ b).divisors.sum id * (r ^ c).divisors.sum id :=
    hcop_qr.sum_divisors_mul
  rw [mul_assoc, h1, h2, mul_assoc]

/-! ### Reusable σ-bound helpers (re-export from OddWeird.lean) -/

-- We need the ge3 and ge5 bounds from OddWeird.lean. Since they are `private`,
-- we re-prove them here with the same pattern.

/-- For p ≥ 3: 2·σ(p^a) < 3·p^a (re-proved for local use). -/
private theorem sigma_bound_ge3 {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) (a : ℕ) :
    2 * (p ^ a).divisors.sum id < 3 * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  set s := ∑ i ∈ Finset.range (a + 1), p ^ i
  have hmul := geom_sum_mul_pred hp.two_le a
  have hpa : 0 < p ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by omega))
  have hpa1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  suffices h : 2 * s * (p - 1) < 3 * p ^ a * (p - 1) by
    exact (Nat.mul_lt_mul_right (by omega : 0 < p - 1)).mp h
  have hmul_add : s * (p - 1) + 1 = p ^ (a + 1) := by
    rw [hmul]; exact Nat.sub_add_cancel hpa1
  have hpow : p ^ (a + 1) = p ^ a * p := pow_succ p a
  zify [show 1 ≤ p from by omega] at hmul_add hpow hpa hp3 ⊢
  nlinarith

/-- For p ≥ 5: 4·σ(p^a) < 5·p^a (re-proved for local use). -/
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

/-! ### Three-prime not-abundant helper -/

/-- Three primes all ≥ 5: σ(p^a·q^b·r^c) < 2·p^a·q^b·r^c.
    From 4σ_p < 5p^a, 4σ_q < 5q^b, 4σ_r < 5r^c:
    64·σ_p·σ_q·σ_r < 125·p^a·q^b·r^c < 128·p^a·q^b·r^c. -/
private theorem sigma_three_ge5_lt {p q r : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hr5 : 5 ≤ r) (a b c : ℕ) :
    (p ^ a * q ^ b * r ^ c).divisors.sum id < 2 * (p ^ a * q ^ b * r ^ c) := by
  rw [sigma_three_primes_mul hp hq hr hpq hpr hqr]
  set σp := (p ^ a).divisors.sum id
  set σq := (q ^ b).divisors.sum id
  set σr := (r ^ c).divisors.sum id
  have hbp := sigma_bound_ge5 hp hp5 a  -- 4σp < 5p^a
  have hbq := sigma_bound_ge5 hq hq5 b  -- 4σq < 5q^b
  have hbr := sigma_bound_ge5 hr hr5 c  -- 4σr < 5r^c
  have hσp_pos : 0 < σp := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσq_pos : 0 < σq := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσr_pos : 0 < σr := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hpa_pos : 0 < p ^ a := by positivity
  have hqb_pos : 0 < q ^ b := by positivity
  have hrc_pos : 0 < r ^ c := by positivity
  -- 64·σpσqσr < 125·p^aq^br^c ≤ 128·p^aq^br^c
  have step1 : σq * (4 * σr) < σq * (5 * r ^ c) :=
    mul_lt_mul_of_pos_left hbr hσq_pos
  have step2 : (4 * σq) * (5 * r ^ c) < (5 * q ^ b) * (5 * r ^ c) :=
    mul_lt_mul_of_pos_right hbq (by positivity)
  have step3 : (4 * σp) * (5 * q ^ b * (5 * r ^ c)) <
      (5 * p ^ a) * (5 * q ^ b * (5 * r ^ c)) :=
    mul_lt_mul_of_pos_right hbp (by positivity)
  have hn_pos : 0 < p ^ a * q ^ b * r ^ c := by positivity
  nlinarith

/-- p=3, q≥7, r≥11: σ(3^a·q^b·r^c) < 2·3^a·q^b·r^c.
    From 2σ₃ < 3·3^a, 6σ_q < 7q^b, 10σ_r < 11r^c:
    120·σ₃·σ_q·σ_r < 231·n < 240·n. -/
private theorem sigma_three_3_ge7_ge11_lt {q r : ℕ}
    (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hq7 : 7 ≤ q) (hr11 : 11 ≤ r) (hqr : q ≠ r) (a b c : ℕ) :
    (3 ^ a * q ^ b * r ^ c).divisors.sum id < 2 * (3 ^ a * q ^ b * r ^ c) := by
  have hp3 : Nat.Prime 3 := by decide
  have h3q : (3 : ℕ) ≠ q := by omega
  have h3r : (3 : ℕ) ≠ r := by omega
  rw [sigma_three_primes_mul hp3 hq hr h3q h3r hqr]
  set σ3 := (3 ^ a).divisors.sum id
  set σq := (q ^ b).divisors.sum id
  set σr := (r ^ c).divisors.sum id
  have hb3 := sigma_bound_ge3 hp3 (le_refl 3) a   -- 2σ3 < 3·3^a
  have hbq := sigma_bound_ge7 hq hq7 b              -- 6σq < 7q^b
  have hbr := sigma_bound_ge11 hr hr11 c             -- 10σr < 11r^c
  have hσ3_pos : 0 < σ3 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσq_pos : 0 < σq := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσr_pos : 0 < σr := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have h3a_pos : 0 < 3 ^ a := by positivity
  have hqb_pos : 0 < q ^ b := by positivity
  have hrc_pos : 0 < r ^ c := by positivity
  -- 120·σ₃σqσr < 231·n < 240·n = 120·2n
  have step1 : σq * (10 * σr) < σq * (11 * r ^ c) :=
    mul_lt_mul_of_pos_left hbr hσq_pos
  have step2 : (6 * σq) * (11 * r ^ c) < (7 * q ^ b) * (11 * r ^ c) :=
    mul_lt_mul_of_pos_right hbq (by positivity)
  have step3 : (2 * σ3) * (7 * q ^ b * (11 * r ^ c)) <
      (3 * 3 ^ a) * (7 * q ^ b * (11 * r ^ c)) :=
    mul_lt_mul_of_pos_right hb3 (by positivity)
  have hn_pos : 0 < 3 ^ a * q ^ b * r ^ c := by positivity
  nlinarith

/-- p=3, q=5, r≥17: σ(3^a·5^b·r^c) < 2·3^a·5^b·r^c.
    From 2σ₃ < 3·3^a, 4σ₅ < 5·5^b, 16σ_r < 17r^c:
    128·σ₃σ₅σ_r < 255·n < 256·n = 128·2n. -/
private theorem sigma_three_3_5_ge17_lt {r : ℕ}
    (hr : Nat.Prime r) (hr17 : 17 ≤ r) (a b c : ℕ) :
    (3 ^ a * 5 ^ b * r ^ c).divisors.sum id < 2 * (3 ^ a * 5 ^ b * r ^ c) := by
  have hp3 : Nat.Prime 3 := by decide
  have hp5 : Nat.Prime 5 := by decide
  have h35 : (3 : ℕ) ≠ 5 := by omega
  have h3r : (3 : ℕ) ≠ r := by omega
  have h5r : (5 : ℕ) ≠ r := by omega
  rw [sigma_three_primes_mul hp3 hp5 hr h35 h3r h5r]
  set σ3 := (3 ^ a).divisors.sum id
  set σ5 := (5 ^ b).divisors.sum id
  set σr := (r ^ c).divisors.sum id
  have hb3 := sigma_bound_ge3 hp3 (le_refl 3) a
  have hb5 := sigma_bound_ge5 hp5 (le_refl 5) b
  have hbr := sigma_bound_ge17 hr hr17 c
  have hσ3_pos : 0 < σ3 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσ5_pos : 0 < σ5 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσr_pos : 0 < σr := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have h3a_pos : 0 < 3 ^ a := by positivity
  have h5b_pos : 0 < 5 ^ b := by positivity
  have hrc_pos : 0 < r ^ c := by positivity
  -- 128·σ₃σ₅σr < 255·n < 256·n = 128·2n
  -- Step 1: 16σr < 17r^c → σ5 * (16σr) < σ5 * (17r^c)
  have step1 : σ5 * (16 * σr) < σ5 * (17 * r ^ c) :=
    mul_lt_mul_of_pos_left hbr hσ5_pos
  -- Step 2: 4σ5 < 5·5^b → (4σ5) * (17r^c) < (5·5^b) * (17r^c)
  have step2 : (4 * σ5) * (17 * r ^ c) < (5 * 5 ^ b) * (17 * r ^ c) :=
    mul_lt_mul_of_pos_right hb5 (by positivity)
  -- Step 3: 2σ3 < 3·3^a → (2σ3) * (5·5^b * 17r^c) < (3·3^a) * (5·5^b * 17r^c)
  have step3 : (2 * σ3) * (5 * 5 ^ b * (17 * r ^ c)) <
      (3 * 3 ^ a) * (5 * 5 ^ b * (17 * r ^ c)) :=
    mul_lt_mul_of_pos_right hb3 (by positivity)
  -- Combining: 128·σ3·σ5·σr < 255·3^a·5^b·r^c
  -- Then 255·n < 256·n since n ≥ 1
  have hn_pos : 0 < 3 ^ a * 5 ^ b * r ^ c := by positivity
  nlinarith

/-- Helper: σ(n) < 2n implies n is not abundant. -/
private theorem not_abundant_of_sigma_lt {n : ℕ}
    (h : n.divisors.sum id < 2 * n) : ¬Abundant n := by
  intro ⟨_, hab⟩
  have hsplit : n.divisors.sum id = n.properDivisors.sum id + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  linarith

/-- Repackage a concrete value of `n.divisors.sum id` as a value of
    `n.properDivisors.sum id`. -/
private theorem properDivisors_sum_eq_sub {n σ : ℕ} (hσ : n.divisors.sum id = σ) :
    n.properDivisors.sum id = σ - n := by
  have hsplit : n.divisors.sum id = n.properDivisors.sum id + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  omega

/-! ### Exceptional non-abundant families -/

/-- If `a ≤ 2`, then `3^a * 5^b * 11^c` is not abundant. -/
private theorem three_five_eleven_a_le_two_not_abundant (a b c : ℕ) (ha : a ≤ 2) :
    ¬Abundant (3 ^ a * 5 ^ b * 11 ^ c) := by
  have hlt : (3 ^ a * 5 ^ b * 11 ^ c).divisors.sum id < 2 * (3 ^ a * 5 ^ b * 11 ^ c) := by
    have hp3 : Nat.Prime 3 := by decide
    have hp5 : Nat.Prime 5 := by decide
    have hp11 : Nat.Prime 11 := by decide
    rw [sigma_three_primes_mul hp3 hp5 hp11 (by omega) (by omega) (by omega)]
    set σ3 := (3 ^ a).divisors.sum id
    set σ5 := (5 ^ b).divisors.sum id
    set σ11 := (11 ^ c).divisors.sum id
    have hσ3n : 9 * σ3 ≤ 13 * 3 ^ a := by
      dsimp [σ3]
      rw [Nat.sum_divisors_prime_pow hp3]
      interval_cases a <;> norm_num
    have hb5n : 4 * σ5 < 5 * 5 ^ b := by
      simpa [σ5] using sigma_bound_ge5 hp5 (le_refl 5) b
    have hc11n : 10 * σ11 < 11 * 11 ^ c := by
      simpa [σ11] using sigma_bound_ge11 hp11 (le_refl 11) c
    have hσ3 : (9 : ℚ) * σ3 ≤ 13 * 3 ^ a := by
      exact_mod_cast hσ3n
    have hb5 : (4 : ℚ) * σ5 < 5 * 5 ^ b := by
      exact_mod_cast hb5n
    have hc11 : (10 : ℚ) * σ11 < 11 * 11 ^ c := by
      exact_mod_cast hc11n
    have h3a : (0 : ℚ) < 3 ^ a := by positivity
    have h5b : (0 : ℚ) < 5 ^ b := by positivity
    have h11c : (0 : ℚ) < 11 ^ c := by positivity
    have hσ5_pos : (0 : ℚ) < σ5 := by exact_mod_cast
      (Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
        ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩ :
          0 < (5 ^ b).divisors.sum id)
    have hσ3_pos : (0 : ℚ) < σ3 := by exact_mod_cast
      (Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
        ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩ :
          0 < (3 ^ a).divisors.sum id)
    have step1 : (σ5 : ℚ) * (10 * σ11) < σ5 * (11 * 11 ^ c) :=
      mul_lt_mul_of_pos_left hc11 hσ5_pos
    have step2 : (4 * (σ5 : ℚ)) * (11 * 11 ^ c) <
        (5 * 5 ^ b) * (11 * 11 ^ c) :=
      mul_lt_mul_of_pos_right hb5 (by positivity)
    have step3 : (9 * (σ3 : ℚ)) * (5 * 5 ^ b * (11 * 11 ^ c)) ≤
        (13 * 3 ^ a) * (5 * 5 ^ b * (11 * 11 ^ c)) :=
      mul_le_mul_of_nonneg_right hσ3 (by positivity)
    have step1' : (9 * (σ3 : ℚ)) * (σ5 * (10 * σ11)) <
        (9 * σ3) * (σ5 * (11 * 11 ^ c)) :=
      mul_lt_mul_of_pos_left step1 (by positivity)
    have step2' : (9 * (σ3 : ℚ)) * ((4 * σ5) * (11 * 11 ^ c)) <
        (9 * σ3) * ((5 * 5 ^ b) * (11 * 11 ^ c)) :=
      mul_lt_mul_of_pos_left step2 (by positivity)
    exact_mod_cast (show (σ3 : ℚ) * σ5 * σ11 < 2 * (3 ^ a * 5 ^ b * 11 ^ c) by
      nlinarith [step1', step2', step3])
  exact not_abundant_of_sigma_lt hlt

/-- If `b = 1`, then `3^a * 5 * 11^c` is not abundant. -/
private theorem three_five_eleven_b_one_not_abundant (a c : ℕ) :
    ¬Abundant (3 ^ a * 5 ^ 1 * 11 ^ c) := by
  apply not_abundant_of_sigma_lt
  have hp3 : Nat.Prime 3 := by decide
  have hp11 : Nat.Prime 11 := by decide
  rw [sigma_three_primes_mul hp3 (by decide) hp11 (by omega) (by omega) (by omega)]
  have hσ5 : (5 ^ (1 : ℕ)).divisors.sum id = 6 := by
    rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 5)]
    norm_num
  rw [hσ5]
  set σ3 := (3 ^ a).divisors.sum id
  set σ11 := (11 ^ c).divisors.sum id
  have ha3n : 2 * σ3 < 3 * 3 ^ a := by
    simpa [σ3] using sigma_bound_ge3 hp3 (le_refl 3) a
  have hc11n : 10 * σ11 < 11 * 11 ^ c := by
    simpa [σ11] using sigma_bound_ge11 hp11 (le_refl 11) c
  have ha3 : (2 : ℚ) * σ3 < 3 * 3 ^ a := by
    exact_mod_cast ha3n
  have hc11 : (10 : ℚ) * σ11 < 11 * 11 ^ c := by
    exact_mod_cast hc11n
  have h3a : (0 : ℚ) < 3 ^ a := by positivity
  have h11c : (0 : ℚ) < 11 ^ c := by positivity
  exact_mod_cast (show (σ3 : ℚ) * 6 * σ11 < 2 * (3 ^ a * 5 ^ 1 * 11 ^ c) by
    nlinarith)

/-- If `a = 1`, then `3 * 5^b * 7^c` is not abundant. -/
private theorem three_five_seven_a_one_not_abundant (b c : ℕ) :
    ¬Abundant (3 ^ 1 * 5 ^ b * 7 ^ c) := by
  apply not_abundant_of_sigma_lt
  have hp5 : Nat.Prime 5 := by decide
  have hp7 : Nat.Prime 7 := by decide
  rw [sigma_three_primes_mul (by decide) hp5 hp7 (by omega) (by omega) (by omega)]
  have hσ3 : (3 ^ (1 : ℕ)).divisors.sum id = 4 := by
    rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 3)]
    norm_num
  rw [hσ3]
  set σ5 := (5 ^ b).divisors.sum id
  set σ7 := (7 ^ c).divisors.sum id
  have hb5 := sigma_bound_ge5 hp5 (le_refl 5) b
  have hc7 := sigma_bound_ge7 hp7 (le_refl 7) c
  have hσ5_pos : 0 < σ5 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have h5b_pos : 0 < 5 ^ b := by positivity
  have h7c_pos : 0 < 7 ^ c := by positivity
  have h1 : σ5 * (6 * σ7) < σ5 * (7 * 7 ^ c) :=
    mul_lt_mul_of_pos_left hc7 hσ5_pos
  have h2 : (4 * σ5) * (7 * 7 ^ c) < (5 * 5 ^ b) * (7 * 7 ^ c) :=
    mul_lt_mul_of_pos_right hb5 (by positivity)
  nlinarith

/-- `3^2 * 5 * 7 = 315` is not abundant. -/
private theorem three_five_seven_two_one_one_not_abundant :
    ¬Abundant (3 ^ 2 * 5 ^ 1 * 7 ^ 1) := by
  apply not_abundant_of_sigma_lt
  have hp3 : Nat.Prime 3 := by decide
  have hp5 : Nat.Prime 5 := by decide
  have hp7 : Nat.Prime 7 := by decide
  rw [sigma_three_primes_mul hp3 hp5 hp7 (by omega) (by omega) (by omega)]
  rw [Nat.sum_divisors_prime_pow hp3, Nat.sum_divisors_prime_pow hp5,
    Nat.sum_divisors_prime_pow hp7]
  norm_num

/-- If `a ≤ 2`, then `3^a * 5^b * 13^c` is not abundant. -/
private theorem three_five_thirteen_a_le_two_not_abundant (a b c : ℕ) (ha : a ≤ 2) :
    ¬Abundant (3 ^ a * 5 ^ b * 13 ^ c) := by
  have hlt : (3 ^ a * 5 ^ b * 13 ^ c).divisors.sum id < 2 * (3 ^ a * 5 ^ b * 13 ^ c) := by
    have hp3 : Nat.Prime 3 := by decide
    have hp5 : Nat.Prime 5 := by decide
    have hp13 : Nat.Prime 13 := by decide
    rw [sigma_three_primes_mul hp3 hp5 hp13 (by omega) (by omega) (by omega)]
    set σ3 := (3 ^ a).divisors.sum id
    set σ5 := (5 ^ b).divisors.sum id
    set σ13 := (13 ^ c).divisors.sum id
    have hσ3n : 9 * σ3 ≤ 13 * 3 ^ a := by
      dsimp [σ3]
      rw [Nat.sum_divisors_prime_pow hp3]
      interval_cases a <;> norm_num
    have hb5n : 4 * σ5 < 5 * 5 ^ b := by
      simpa [σ5] using sigma_bound_ge5 hp5 (le_refl 5) b
    have hc13n : 12 * σ13 < 13 * 13 ^ c := by
      simpa [σ13] using sigma_bound_ge13 hp13 (le_refl 13) c
    have hσ3 : (9 : ℚ) * σ3 ≤ 13 * 3 ^ a := by
      exact_mod_cast hσ3n
    have hb5 : (4 : ℚ) * σ5 < 5 * 5 ^ b := by
      exact_mod_cast hb5n
    have hc13 : (12 : ℚ) * σ13 < 13 * 13 ^ c := by
      exact_mod_cast hc13n
    have h3a : (0 : ℚ) < 3 ^ a := by positivity
    have h5b : (0 : ℚ) < 5 ^ b := by positivity
    have h13c : (0 : ℚ) < 13 ^ c := by positivity
    have hσ5_pos : (0 : ℚ) < σ5 := by exact_mod_cast
      (Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
        ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩ :
          0 < (5 ^ b).divisors.sum id)
    have hσ3_pos : (0 : ℚ) < σ3 := by exact_mod_cast
      (Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
        ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩ :
          0 < (3 ^ a).divisors.sum id)
    have step1 : (σ5 : ℚ) * (12 * σ13) < σ5 * (13 * 13 ^ c) :=
      mul_lt_mul_of_pos_left hc13 hσ5_pos
    have step2 : (4 * (σ5 : ℚ)) * (13 * 13 ^ c) <
        (5 * 5 ^ b) * (13 * 13 ^ c) :=
      mul_lt_mul_of_pos_right hb5 (by positivity)
    have step3 : (9 * (σ3 : ℚ)) * (5 * 5 ^ b * (13 * 13 ^ c)) ≤
        (13 * 3 ^ a) * (5 * 5 ^ b * (13 * 13 ^ c)) :=
      mul_le_mul_of_nonneg_right hσ3 (by positivity)
    have step1' : (9 * (σ3 : ℚ)) * (σ5 * (12 * σ13)) <
        (9 * σ3) * (σ5 * (13 * 13 ^ c)) :=
      mul_lt_mul_of_pos_left step1 (by positivity)
    have step2' : (9 * (σ3 : ℚ)) * ((4 * σ5) * (13 * 13 ^ c)) <
        (9 * σ3) * ((5 * 5 ^ b) * (13 * 13 ^ c)) :=
      mul_lt_mul_of_pos_left step2 (by positivity)
    exact_mod_cast (show (σ3 : ℚ) * σ5 * σ13 < 2 * (3 ^ a * 5 ^ b * 13 ^ c) by
      nlinarith [step1', step2', step3])
  exact not_abundant_of_sigma_lt hlt

/-- If `a = 3` and `b ≤ 2`, then `3^3 * 5^b * 13^c` is not abundant. -/
private theorem three_five_thirteen_three_b_le_two_not_abundant (b c : ℕ) (hb : b ≤ 2) :
    ¬Abundant (3 ^ 3 * 5 ^ b * 13 ^ c) := by
  apply not_abundant_of_sigma_lt
  have hp5 : Nat.Prime 5 := by decide
  have hp13 : Nat.Prime 13 := by decide
  rw [sigma_three_primes_mul (by decide) hp5 hp13 (by omega) (by omega) (by omega)]
  have hσ3 : (3 ^ (3 : ℕ)).divisors.sum id = 40 := by
    rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 3)]
    norm_num
  rw [hσ3]
  set σ5 := (5 ^ b).divisors.sum id
  set σ13 := (13 ^ c).divisors.sum id
  have hσ5n : 25 * σ5 ≤ 31 * 5 ^ b := by
    dsimp [σ5]
    rw [Nat.sum_divisors_prime_pow hp5]
    interval_cases b <;> norm_num
  have hc13n : 12 * σ13 < 13 * 13 ^ c := by
    simpa [σ13] using sigma_bound_ge13 hp13 (le_refl 13) c
  have hσ5 : (25 : ℚ) * σ5 ≤ 31 * 5 ^ b := by
    exact_mod_cast hσ5n
  have hc13 : (12 : ℚ) * σ13 < 13 * 13 ^ c := by
    exact_mod_cast hc13n
  have h5b : (0 : ℚ) < 5 ^ b := by positivity
  have h13c : (0 : ℚ) < 13 ^ c := by positivity
  exact_mod_cast (show (40 : ℚ) * σ5 * σ13 < 2 * (3 ^ 3 * 5 ^ b * 13 ^ c) by
    nlinarith)

/-- If `a = 3` and `c = 1`, then `3^3 * 5^b * 13` is not abundant. -/
private theorem three_five_thirteen_three_c_one_not_abundant (b : ℕ) :
    ¬Abundant (3 ^ 3 * 5 ^ b * 13 ^ 1) := by
  apply not_abundant_of_sigma_lt
  have hp5 : Nat.Prime 5 := by decide
  rw [sigma_three_primes_mul (by decide) hp5 (by decide) (by omega) (by omega) (by omega)]
  have hσ3 : (3 ^ (3 : ℕ)).divisors.sum id = 40 := by
    rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 3)]
    norm_num
  have hσ13 : (13 ^ (1 : ℕ)).divisors.sum id = 14 := by
    rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 13)]
    norm_num
  rw [hσ3, hσ13]
  set σ5 := (5 ^ b).divisors.sum id
  have hb5n : 4 * σ5 < 5 * 5 ^ b := by
    simpa [σ5] using sigma_bound_ge5 (by decide : Nat.Prime 5) (le_refl 5) b
  have hb5 : (4 : ℚ) * σ5 < 5 * 5 ^ b := by
    exact_mod_cast hb5n
  have h5b : (0 : ℚ) < 5 ^ b := by positivity
  exact_mod_cast (show (40 : ℚ) * σ5 * 14 < 2 * (3 ^ 3 * 5 ^ b * 13 ^ 1) by
    nlinarith)

/-- If `b = 1`, then `3^a * 5 * 13^c` is not abundant. -/
private theorem three_five_thirteen_b_one_not_abundant (a c : ℕ) :
    ¬Abundant (3 ^ a * 5 ^ 1 * 13 ^ c) := by
  apply not_abundant_of_sigma_lt
  have hp3 : Nat.Prime 3 := by decide
  have hp13 : Nat.Prime 13 := by decide
  rw [sigma_three_primes_mul hp3 (by decide) hp13 (by omega) (by omega) (by omega)]
  have hσ5 : (5 ^ (1 : ℕ)).divisors.sum id = 6 := by
    rw [Nat.sum_divisors_prime_pow (by decide : Nat.Prime 5)]
    norm_num
  rw [hσ5]
  set σ3 := (3 ^ a).divisors.sum id
  set σ13 := (13 ^ c).divisors.sum id
  have ha3n : 2 * σ3 < 3 * 3 ^ a := by
    simpa [σ3] using sigma_bound_ge3 hp3 (le_refl 3) a
  have hc13n : 12 * σ13 < 13 * 13 ^ c := by
    simpa [σ13] using sigma_bound_ge13 hp13 (le_refl 13) c
  have ha3 : (2 : ℚ) * σ3 < 3 * 3 ^ a := by
    exact_mod_cast ha3n
  have hc13 : (12 : ℚ) * σ13 < 13 * 13 ^ c := by
    exact_mod_cast hc13n
  have h3a : (0 : ℚ) < 3 ^ a := by positivity
  have h13c : (0 : ℚ) < 13 ^ c := by positivity
  exact_mod_cast (show (σ3 : ℚ) * 6 * σ13 < 2 * (3 ^ a * 5 ^ 1 * 13 ^ c) by
    nlinarith)

/-- `3^4 * 5^2 * 13` is not abundant. -/
private theorem three_five_thirteen_four_two_one_not_abundant :
    ¬Abundant (3 ^ 4 * 5 ^ 2 * 13 ^ 1) := by
  apply not_abundant_of_sigma_lt
  have hp3 : Nat.Prime 3 := by decide
  have hp5 : Nat.Prime 5 := by decide
  have hp13 : Nat.Prime 13 := by decide
  rw [sigma_three_primes_mul hp3 hp5 hp13 (by omega) (by omega) (by omega)]
  rw [Nat.sum_divisors_prime_pow hp3, Nat.sum_divisors_prime_pow hp5,
    Nat.sum_divisors_prime_pow hp13]
  norm_num

/-! ### Exceptional pseudoperfect base numbers -/

set_option linter.style.nativeDecide false in
private theorem pp_945 : Pseudoperfect 945 := by
  refine ⟨({7, 9, 15, 27, 35, 45, 63, 105, 135, 189, 315} : Finset ℕ),
    Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_1575 : Pseudoperfect 1575 := by
  refine ⟨({7, 15, 25, 45, 63, 75, 105, 175, 225, 315, 525} : Finset ℕ),
    Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_2205 : Pseudoperfect 2205 := by
  refine ⟨({3, 7, 15, 35, 45, 49, 63, 105, 147, 245, 315, 441, 735} :
    Finset ℕ), Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_7425 : Pseudoperfect 7425 := by
  refine ⟨({5, 9, 25, 27, 33, 45, 55, 75, 99, 135, 165, 225, 275, 297, 495,
    675, 825, 1485, 2475} : Finset ℕ), Finset.mem_powerset.mpr (by native_decide),
    by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_78975 : Pseudoperfect 78975 := by
  refine ⟨({5, 15, 25, 27, 39, 45, 65, 75, 81, 117, 135, 195, 225, 243, 325,
    351, 405, 585, 675, 975, 1053, 1215, 1755, 2025, 2925, 3159, 5265, 6075,
    8775, 15795, 26325} : Finset ℕ), Finset.mem_powerset.mpr (by native_decide),
    by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_131625 : Pseudoperfect 131625 := by
  refine ⟨({117, 195, 225, 325, 375, 405, 585, 675, 975, 1053, 1125, 1625,
    1755, 2025, 2925, 3375, 4875, 5265, 8775, 10125, 14625, 26325, 43875} :
    Finset ℕ), Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_342225 : Pseudoperfect 342225 := by
  refine ⟨({117, 225, 507, 585, 675, 845, 975, 1053, 1521, 1755, 2025, 2535,
    2925, 4225, 4563, 5265, 7605, 8775, 12675, 13689, 22815, 26325, 38025,
    68445, 114075} : Finset ℕ), Finset.mem_powerset.mpr (by native_decide),
    by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_570375 : Pseudoperfect 570375 := by
  refine ⟨({75, 169, 225, 325, 375, 507, 585, 675, 845, 975, 1125, 1521, 1625,
    1755, 2535, 2925, 3375, 4225, 4563, 4875, 7605, 8775, 12675, 14625, 21125,
    22815, 38025, 43875, 63375, 114075, 190125} : Finset ℕ),
    Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_15015 : Pseudoperfect 15015 := by
  refine ⟨({5, 7, 11, 13, 15, 21, 33, 35, 39, 55, 65, 91, 105, 143, 165,
    195, 231, 273, 385, 429, 455, 715, 1001, 1155, 1365, 3003, 5005} :
    Finset ℕ), Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_19635 : Pseudoperfect 19635 := by
  refine ⟨({1, 3, 5, 7, 15, 17, 33, 35, 51, 55, 77, 85, 105, 119, 165,
    187, 231, 255, 357, 561, 595, 935, 1155, 1309, 2805, 3927, 6545} :
    Finset ℕ), Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_21945 : Pseudoperfect 21945 := by
  refine ⟨({7, 11, 15, 19, 33, 35, 55, 57, 77, 95, 105, 133, 209, 231,
    285, 385, 399, 627, 665, 1045, 1155, 1463, 3135, 4389, 7315} :
    Finset ℕ), Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_23205 : Pseudoperfect 23205 := by
  refine ⟨({1, 3, 7, 13, 15, 17, 21, 35, 39, 51, 85, 91, 105, 195, 221,
    255, 273, 357, 455, 595, 663, 1105, 1365, 1547, 3315, 4641, 7735} :
    Finset ℕ), Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_25935 : Pseudoperfect 25935 := by
  refine ⟨({1, 3, 5, 13, 15, 19, 35, 39, 57, 65, 91, 95, 105, 195, 247,
    273, 285, 399, 455, 665, 741, 1235, 1365, 1995, 3705, 5187, 8645} :
    Finset ℕ), Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_26565 : Pseudoperfect 26565 := by
  refine ⟨({1, 5, 11, 15, 21, 23, 33, 35, 55, 69, 77, 105, 115, 161, 165,
    231, 253, 345, 483, 759, 805, 1155, 1265, 2415, 3795, 5313, 8855} :
    Finset ℕ), Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_692835 : Pseudoperfect 692835 := by
  refine ⟨({1, 11, 65, 1615, 4845, 12155, 12597, 13585, 17765, 20995, 36465,
    40755, 46189, 53295, 62985, 138567, 230945} : Finset ℕ),
    Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

/-! ### Pseudoperfect squarefree cores -/

/-- A prime at least `13` does not divide `3 * 5 * 7 * 11`. -/
private theorem prime_ge13_not_dvd_1155 {r : ℕ} (hr : Nat.Prime r) (hr13 : 13 ≤ r) :
    ¬ r ∣ 1155 := by
  intro hd
  have hd' : r ∣ 3 * (5 * (7 * 11)) := by
    simpa [show 1155 = 3 * (5 * (7 * 11)) by norm_num] using hd
  rw [hr.dvd_mul] at hd'
  rcases hd' with h3 | hd'
  · have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 3)).mp h3
    omega
  rw [hr.dvd_mul] at hd'
  rcases hd' with h5 | hd'
  · have : r = 5 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 5)).mp h5
    omega
  rw [hr.dvd_mul] at hd'
  rcases hd' with h7 | h11
  · have : r = 7 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 7)).mp h7
    omega
  · have : r = 11 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 11)).mp h11
    omega

set_option linter.style.nativeDecide false in
private theorem properDivisors_1155_sum : (1155 : ℕ).properDivisors.sum id = 1149 := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem divisors_1155_sum : (1155 : ℕ).divisors.sum id = 2304 := by
  native_decide

/- The product of the fixed core `3 * 5 * 7 * 11` with a prime
`13 ≤ r ≤ 383` is pseudoperfect.

Mathematically, the proper divisors of `1155` sum to `1149 = 1155 - 6`.
Thus the `r`-multiples of those divisors leave a gap of `6r`. The final
bounded check says that, for every prime `r` in this range, `6r` is a subset
sum of the divisors of `1155`. -/
set_option linter.style.nativeDecide false in
private theorem six_mul_subset_sum_1155_small {r : ℕ} (hr : Nat.Prime r) (hr13 : 13 ≤ r)
    (hr383 : r ≤ 383) :
    ∃ U : Finset ℕ, U ⊆ (1155 : ℕ).divisors ∧ U.sum id = 6 * r := by
  have hclosed : ∀ r ∈ Finset.Icc 13 383, Nat.Prime r →
      ∃ U : Finset ℕ, U ⊆ (1155 : ℕ).divisors ∧ U.sum id = 6 * r := by
    native_decide
  exact hclosed r (by simp [hr13, hr383]) hr

/-- If `13 ≤ r ≤ 383` is prime, then `1155 * r` is pseudoperfect.

This is the first parametric pseudoperfect-pruning lemma for the
`3,5,7,11` branch. -/
private theorem pp_1155_mul_of_small_prime {r : ℕ} (hr : Nat.Prime r) (hr13 : 13 ≤ r)
    (hr383 : r ≤ 383) : Pseudoperfect (1155 * r) := by
  obtain ⟨U, hUsub, hUsum⟩ := six_mul_subset_sum_1155_small hr hr13 hr383
  let R := (1155 : ℕ).properDivisors.image fun d => r * d
  refine ⟨U ∪ R, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hxU | hxR
    · have hxdiv1155 : x ∣ 1155 := Nat.dvd_of_mem_divisors (hUsub hxU)
      rw [Nat.mem_properDivisors]
      refine ⟨?_, ?_⟩
      · exact hxdiv1155.trans (dvd_mul_right 1155 r)
      · have hxle : x ≤ 1155 := Nat.le_of_dvd (by norm_num) hxdiv1155
        have hrgt : 1 < r := lt_of_lt_of_le (by norm_num : 1 < 13) hr13
        nlinarith
    · rw [Finset.mem_image] at hxR
      rcases hxR with ⟨d, hd, rfl⟩
      rw [Nat.mem_properDivisors] at hd ⊢
      refine ⟨?_, ?_⟩
      · rcases hd.1 with ⟨k, hk⟩
        use k
        rw [hk]
        ring
      · simpa [mul_comm] using Nat.mul_lt_mul_of_pos_left hd.2 hr.pos
  · have hdisj : Disjoint U R := by
      rw [Finset.disjoint_left]
      intro x hxU hxR
      rw [Finset.mem_image] at hxR
      rcases hxR with ⟨d, _hd, hxd⟩
      have hxdiv1155 : x ∣ 1155 := Nat.dvd_of_mem_divisors (hUsub hxU)
      have hrdvdx : r ∣ x := by
        rw [← hxd]
        exact dvd_mul_right r d
      exact prime_ge13_not_dvd_1155 hr hr13 (hrdvdx.trans hxdiv1155)
    rw [Finset.sum_union hdisj]
    have hsumR : R.sum id = r * 1149 := by
      dsimp [R]
      rw [Finset.sum_image]
      · change (∑ x ∈ (1155 : ℕ).properDivisors, r * id x) = r * 1149
        rw [← Finset.mul_sum, properDivisors_1155_sum]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hr.pos hab
    rw [hUsum, hsumR]
    ring

/-- No prime at least `13` can divide a divisor of `1155`. -/
private theorem no_prime_ge13_dvd_of_dvd_1155 {p x : ℕ} (hp : Nat.Prime p) (hp13 : 13 ≤ p)
    (hx : x ∣ 1155) : ¬ p ∣ x := by
  intro hpx
  exact prime_ge13_not_dvd_1155 hp hp13 (hpx.trans hx)

/-- A certificate lemma for the two-large-prime part of the `3,5,7,11` branch.

If `A + rB + sC = 6rs`, where `A`, `B`, and `C` are subset sums of divisors of
`1155`, then `1155*r*s` is pseudoperfect. The witness is the union of:

* the divisors in `A`;
* the `r`-multiples of the divisors in `B`;
* the `s`-multiples of the divisors in `C`;
* the `rs`-multiples of all proper divisors of `1155`.

The last layer contributes `rs*(1155-6)`, and the certificate fills the missing
`6rs`. -/
private theorem pp_1155_mul_mul_of_cert {r s : ℕ} (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hr13 : 13 ≤ r) (hs13 : 13 ≤ s) (hrs : r ≠ s)
    {A B C : Finset ℕ} (hA : A ⊆ (1155 : ℕ).divisors)
    (hB : B ⊆ (1155 : ℕ).divisors) (hC : C ⊆ (1155 : ℕ).divisors)
    (hsum : A.sum id + r * B.sum id + s * C.sum id = 6 * r * s) :
    Pseudoperfect (1155 * r * s) := by
  let RB := B.image fun d => r * d
  let SC := C.image fun d => s * d
  let RSD := (1155 : ℕ).properDivisors.image fun d => (r * s) * d
  let W := ((A ∪ RB) ∪ SC) ∪ RSD
  refine ⟨W, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro x hx
    dsimp [W] at hx
    rw [Finset.mem_union] at hx
    rcases hx with hxABC | hxD
    · rw [Finset.mem_union] at hxABC
      rcases hxABC with hxAB | hxSC
      · rw [Finset.mem_union] at hxAB
        rcases hxAB with hxA | hxRB
        · have hxdiv : x ∣ 1155 := Nat.dvd_of_mem_divisors (hA hxA)
          rw [Nat.mem_properDivisors]
          refine ⟨?_, ?_⟩
          · exact hxdiv.trans ((dvd_mul_right 1155 r).trans (dvd_mul_right (1155 * r) s))
          · have hxle : x ≤ 1155 := Nat.le_of_dvd (by norm_num) hxdiv
            have hrgt : 1 < r := lt_of_lt_of_le (by norm_num : 1 < 13) hr13
            have hsgt : 1 < s := lt_of_lt_of_le (by norm_num : 1 < 13) hs13
            nlinarith
        · rw [Finset.mem_image] at hxRB
          rcases hxRB with ⟨d, hd, rfl⟩
          have hddiv : d ∣ 1155 := Nat.dvd_of_mem_divisors (hB hd)
          rw [Nat.mem_properDivisors]
          refine ⟨?_, ?_⟩
          · rcases hddiv with ⟨k, hk⟩
            use k * s
            rw [hk]
            ring
          · have hdle : d ≤ 1155 := Nat.le_of_dvd (by norm_num) hddiv
            have hsgt : 1 < s := lt_of_lt_of_le (by norm_num : 1 < 13) hs13
            nlinarith [hr.pos]
      · rw [Finset.mem_image] at hxSC
        rcases hxSC with ⟨d, hd, rfl⟩
        have hddiv : d ∣ 1155 := Nat.dvd_of_mem_divisors (hC hd)
        rw [Nat.mem_properDivisors]
        refine ⟨?_, ?_⟩
        · rcases hddiv with ⟨k, hk⟩
          use k * r
          rw [hk]
          ring
        · have hdle : d ≤ 1155 := Nat.le_of_dvd (by norm_num) hddiv
          have hrgt : 1 < r := lt_of_lt_of_le (by norm_num : 1 < 13) hr13
          nlinarith [hs.pos]
    · rw [Finset.mem_image] at hxD
      rcases hxD with ⟨d, hd, rfl⟩
      rw [Nat.mem_properDivisors] at hd ⊢
      refine ⟨?_, ?_⟩
      · rcases hd.1 with ⟨k, hk⟩
        use k
        rw [hk]
        ring
      · nlinarith [Nat.mul_lt_mul_of_pos_left hd.2 (Nat.mul_pos hr.pos hs.pos)]
  · have hnot_r_dvd_s : ¬ r ∣ s := by
      intro hrsdvd
      exact hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp hrsdvd)
    have hcop_rs : Nat.Coprime r s := (hr.coprime_iff_not_dvd).mpr hnot_r_dvd_s
    have hA_RB : Disjoint A RB := by
      rw [Finset.disjoint_left]
      intro x hxA hxRB
      rw [Finset.mem_image] at hxRB
      rcases hxRB with ⟨b, _hb, hxb⟩
      have hxdiv : x ∣ 1155 := Nat.dvd_of_mem_divisors (hA hxA)
      have hrdvdx : r ∣ x := by
        rw [← hxb]
        exact dvd_mul_right r b
      exact no_prime_ge13_dvd_of_dvd_1155 hr hr13 hxdiv hrdvdx
    have hA_SC : Disjoint A SC := by
      rw [Finset.disjoint_left]
      intro x hxA hxSC
      rw [Finset.mem_image] at hxSC
      rcases hxSC with ⟨c, _hc, hxc⟩
      have hxdiv : x ∣ 1155 := Nat.dvd_of_mem_divisors (hA hxA)
      have hsdvdx : s ∣ x := by
        rw [← hxc]
        exact dvd_mul_right s c
      exact no_prime_ge13_dvd_of_dvd_1155 hs hs13 hxdiv hsdvdx
    have hRB_SC : Disjoint RB SC := by
      rw [Finset.disjoint_left]
      intro x hxRB hxSC
      rw [Finset.mem_image] at hxRB
      rw [Finset.mem_image] at hxSC
      rcases hxRB with ⟨b, _hb, hxb⟩
      rcases hxSC with ⟨c, hc, hxc⟩
      have hrdvd_sc : r ∣ s * c := by
        rw [hxc]
        rw [← hxb]
        exact dvd_mul_right r b
      have hrdvdc : r ∣ c := hcop_rs.dvd_of_dvd_mul_left hrdvd_sc
      have hcdiv : c ∣ 1155 := Nat.dvd_of_mem_divisors (hC hc)
      exact no_prime_ge13_dvd_of_dvd_1155 hr hr13 hcdiv hrdvdc
    have hA_RSD : Disjoint A RSD := by
      rw [Finset.disjoint_left]
      intro x hxA hxD
      rw [Finset.mem_image] at hxD
      rcases hxD with ⟨d, _hd, hxd⟩
      have hxdiv : x ∣ 1155 := Nat.dvd_of_mem_divisors (hA hxA)
      have hrdvdx : r ∣ x := by
        rw [← hxd]
        use s * d
        ring
      exact no_prime_ge13_dvd_of_dvd_1155 hr hr13 hxdiv hrdvdx
    have hRB_RSD : Disjoint RB RSD := by
      rw [Finset.disjoint_left]
      intro x hxRB hxD
      rw [Finset.mem_image] at hxRB
      rw [Finset.mem_image] at hxD
      rcases hxRB with ⟨b, hb, hxb⟩
      rcases hxD with ⟨d, _hd, hxd⟩
      have hb_eq : b = s * d := by
        apply Nat.eq_of_mul_eq_mul_left hr.pos
        calc
          r * b = x := hxb
          _ = r * (s * d) := by
            rw [← hxd]
            ring
      have hsdvdb : s ∣ b := by rw [hb_eq]; exact dvd_mul_right s d
      have hbdiv : b ∣ 1155 := Nat.dvd_of_mem_divisors (hB hb)
      exact no_prime_ge13_dvd_of_dvd_1155 hs hs13 hbdiv hsdvdb
    have hSC_RSD : Disjoint SC RSD := by
      rw [Finset.disjoint_left]
      intro x hxSC hxD
      rw [Finset.mem_image] at hxSC
      rw [Finset.mem_image] at hxD
      rcases hxSC with ⟨c, hc, hxc⟩
      rcases hxD with ⟨d, _hd, hxd⟩
      have hc_eq : c = r * d := by
        apply Nat.eq_of_mul_eq_mul_left hs.pos
        calc
          s * c = x := hxc
          _ = s * (r * d) := by
            rw [← hxd]
            ring
      have hrdvdc : r ∣ c := by rw [hc_eq]; exact dvd_mul_right r d
      have hcdiv : c ∣ 1155 := Nat.dvd_of_mem_divisors (hC hc)
      exact no_prime_ge13_dvd_of_dvd_1155 hr hr13 hcdiv hrdvdc
    have hAB_SC : Disjoint (A ∪ RB) SC := by
      rw [Finset.disjoint_left]
      intro x hx hxSC
      rw [Finset.mem_union] at hx
      rcases hx with hxA | hxRB
      · exact (Finset.disjoint_left.mp hA_SC) hxA hxSC
      · exact (Finset.disjoint_left.mp hRB_SC) hxRB hxSC
    have hABC_D : Disjoint ((A ∪ RB) ∪ SC) RSD := by
      rw [Finset.disjoint_left]
      intro x hx hxD
      rw [Finset.mem_union] at hx
      rcases hx with hxAB | hxSC
      · rw [Finset.mem_union] at hxAB
        rcases hxAB with hxA | hxRB
        · exact (Finset.disjoint_left.mp hA_RSD) hxA hxD
        · exact (Finset.disjoint_left.mp hRB_RSD) hxRB hxD
      · exact (Finset.disjoint_left.mp hSC_RSD) hxSC hxD
    dsimp [W]
    rw [Finset.sum_union hABC_D, Finset.sum_union hAB_SC, Finset.sum_union hA_RB]
    have hsumRB : RB.sum id = r * B.sum id := by
      dsimp [RB]
      rw [Finset.sum_image]
      · change (∑ x ∈ B, r * id x) = r * B.sum id
        rw [← Finset.mul_sum]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hr.pos hab
    have hsumSC : SC.sum id = s * C.sum id := by
      dsimp [SC]
      rw [Finset.sum_image]
      · change (∑ x ∈ C, s * id x) = s * C.sum id
        rw [← Finset.mul_sum]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hs.pos hab
    have hsumRSD : RSD.sum id = r * s * 1149 := by
      dsimp [RSD]
      rw [Finset.sum_image]
      · change (∑ x ∈ (1155 : ℕ).properDivisors, (r * s) * id x) = r * s * 1149
        rw [← Finset.mul_sum, properDivisors_1155_sum]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr.pos hs.pos) hab
    rw [hsumRB, hsumSC, hsumRSD]
    nlinarith

private theorem sigma_1155_mul_mul {r s : ℕ} (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hr13 : 13 ≤ r) (hs13 : 13 ≤ s) (hrs : r ≠ s) :
    (1155 * r * s).divisors.sum id = 2304 * (r + 1) * (s + 1) := by
  have hcop_1155_r : Nat.Coprime 1155 r := by
    rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
    exact prime_ge13_not_dvd_1155 hr hr13
  have hcop_1155_s : Nat.Coprime 1155 s := by
    rw [Nat.coprime_comm, hs.coprime_iff_not_dvd]
    exact prime_ge13_not_dvd_1155 hs hs13
  have hnot_r_dvd_s : ¬ r ∣ s := by
    intro hdiv
    exact hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp hdiv)
  have hcop_r_s : Nat.Coprime r s := (hr.coprime_iff_not_dvd).mpr hnot_r_dvd_s
  have hcop_1155r_s : Nat.Coprime (1155 * r) s :=
    Nat.Coprime.mul_left hcop_1155_s hcop_r_s
  have hσr : r.divisors.sum id = r + 1 := by
    simpa using sum_divisors_prime_pow_one hr
  have hσs : s.divisors.sum id = s + 1 := by
    simpa using sum_divisors_prime_pow_one hs
  have hσ1155r : (1155 * r).divisors.sum id = 2304 * (r + 1) := by
    calc
      (1155 * r).divisors.sum id =
          (1155 : ℕ).divisors.sum id * r.divisors.sum id :=
        hcop_1155_r.sum_divisors_mul
      _ = 2304 * (r + 1) := by rw [divisors_1155_sum, hσr]
  calc
    (1155 * r * s).divisors.sum id =
        (1155 * r).divisors.sum id * s.divisors.sum id :=
      hcop_1155r_s.sum_divisors_mul
    _ = (2304 * (r + 1)) * (s + 1) := by rw [hσ1155r, hσs]
    _ = 2304 * (r + 1) * (s + 1) := by ring

private theorem not_abundant_1155_mul_mul_of_ratio_lt {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr13 : 13 ≤ r) (hs13 : 13 ≤ s)
    (hrs : r ≠ s) (hratio : 384 * (r + s + 1) < r * s) :
    ¬Abundant (1155 * r * s) := by
  apply not_abundant_of_sigma_lt
  rw [sigma_1155_mul_mul hr hs hr13 hs13 hrs]
  nlinarith

private theorem not_abundant_1155_mul_mul_of_outside_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr13 : 13 ≤ r) (hs13 : 13 ≤ s)
    (hrs : r ≠ s) (hr384 : 384 < r)
    (hout : 384 * (r + 1) < s * (r - 384)) : ¬Abundant (1155 * r * s) := by
  apply not_abundant_1155_mul_mul_of_ratio_lt hr hs hr13 hs13 hrs
  zify [show 384 ≤ r from by omega] at hout ⊢
  nlinarith

private theorem corridor_of_abundant_1155_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr13 : 13 ≤ r) (hs13 : 13 ≤ s)
    (hrs : r ≠ s) (hr384 : 384 < r) (hab : Abundant (1155 * r * s)) :
    s * (r - 384) ≤ 384 * (r + 1) := by
  by_contra hout
  have hout' : 384 * (r + 1) < s * (r - 384) := by omega
  exact not_abundant_1155_mul_mul_of_outside_corridor hr hs hr13 hs13 hrs hr384 hout' hab

private theorem first_prime_le_768_of_abundant_1155_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr13 : 13 ≤ r) (hs13 : 13 ≤ s)
    (hrs : r ≠ s) (hrs_lt : r < s) (hr384 : 384 < r)
    (hab : Abundant (1155 * r * s)) : r ≤ 768 := by
  have hcorr :=
    corridor_of_abundant_1155_mul_mul hr hs hr13 hs13 hrs hr384 hab
  by_contra hle
  have hr769 : 769 ≤ r := by omega
  have hpos : 0 < r - 384 := by omega
  have hgt : r * (r - 384) < s * (r - 384) :=
    Nat.mul_lt_mul_of_pos_right hrs_lt hpos
  have hlt : r * (r - 384) < 384 * (r + 1) := lt_of_lt_of_le hgt hcorr
  zify [show 384 ≤ r from by omega] at hlt
  nlinarith

set_option linter.style.nativeDecide false in
private theorem prime_le_761_of_le_768 {r : ℕ} (hr : Nat.Prime r) (hrle : r ≤ 768) :
    r ≤ 761 := by
  by_contra hle761
  have hbad : ∀ r ∈ Finset.Icc 762 768, ¬ Nat.Prime r := by
    native_decide
  have hr762 : 762 ≤ r := by omega
  have hrmem : r ∈ Finset.Icc 762 768 := by
    simp [hr762, hrle]
  exact (hbad r hrmem) hr

/-- The product of the five-prime core `3,5,7,11,r` is `1155 * r`. -/
private theorem prod_3_5_7_11_r {r : ℕ} (hr13 : 13 ≤ r) :
    (∏ p ∈ ({3, 5, 7, 11, r} : Finset ℕ), p) = 1155 * r := by
  have h3r : 3 ≠ r := by omega
  have h5r : 5 ≠ r := by omega
  have h7r : 7 ≠ r := by omega
  have h11r : 11 ≠ r := by omega
  rw [Finset.prod_insert]
  · rw [Finset.prod_insert]
    · rw [Finset.prod_insert]
      · rw [Finset.prod_insert]
        · rw [Finset.prod_singleton]
          ring
        · simp [h11r]
      · simp [h7r]
    · simp [h5r]
  · simp [h3r]

/-- The product of the six-prime core `3,5,7,11,r,s` is `1155*r*s`,
provided the two extra primes are at least `13` and distinct. -/
private theorem prod_3_5_7_11_r_s {r s : ℕ} (hr13 : 13 ≤ r) (hs13 : 13 ≤ s)
    (hrs : r ≠ s) :
    (∏ p ∈ ({3, 5, 7, 11, r, s} : Finset ℕ), p) = 1155 * r * s := by
  have h3r : 3 ≠ r := by omega
  have h3s : 3 ≠ s := by omega
  have h5r : 5 ≠ r := by omega
  have h5s : 5 ≠ s := by omega
  have h7r : 7 ≠ r := by omega
  have h7s : 7 ≠ s := by omega
  have h11r : 11 ≠ r := by omega
  have h11s : 11 ≠ s := by omega
  rw [Finset.prod_insert]
  · rw [Finset.prod_insert]
    · rw [Finset.prod_insert]
      · rw [Finset.prod_insert]
        · rw [Finset.prod_insert]
          · rw [Finset.prod_singleton]
            ring
          · simp [hrs]
        · simp [h11r, h11s]
      · simp [h7r, h7s]
    · simp [h5r, h5s]
  · simp [h3r, h3s]

/-- If a pseudoperfect number divides a positive integer, then the integer is
pseudoperfect.

This is just `pseudoperfect_mul` with the quotient written on the left. -/
private theorem pseudoperfect_of_dvd {d n : ℕ} (hn : 0 < n) (hdvd : d ∣ n)
    (hpd : Pseudoperfect d) : Pseudoperfect n := by
  rcases hdvd with ⟨m, rfl⟩
  have hm : 0 < m := by
    by_contra hmpos
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hmpos
    simp [hm0] at hn
  simpa [mul_comm] using pseudoperfect_mul hm hpd

/-- In a squarefree number, the product of any selected prime factors divides
the number. -/
private theorem prod_dvd_of_subset_primeFactors_squarefree {n : ℕ} (hsq : Squarefree n)
    {T : Finset ℕ} (hsubset : T ⊆ n.primeFactors) :
    (∏ p ∈ T, p) ∣ n := by
  have hprod_dvd : (∏ p ∈ T, id p) ∣ ∏ p ∈ n.primeFactors, id p :=
    Finset.prod_dvd_prod_of_subset T n.primeFactors id hsubset
  simpa [Nat.prod_primeFactors_of_squarefree hsq] using hprod_dvd

/-- A squarefree number containing a pseudoperfect prime-factor core cannot be
weird. -/
private theorem not_weird_squarefree_of_pseudoperfect_primeFactors_subset {n : ℕ}
    (hsq : Squarefree n) {T : Finset ℕ} (hsubset : T ⊆ n.primeFactors)
    (hpp : Pseudoperfect (∏ p ∈ T, p)) : ¬Weird n := by
  intro hw
  exact hw.2 (pseudoperfect_of_dvd hw.1.1
    (prod_dvd_of_subset_primeFactors_squarefree hsq hsubset) hpp)

/-- A squarefree number whose prime factors include `3, 5, 7, 11, 13` is not
weird.

The core `3 * 5 * 7 * 11 * 13 = 15015` is already pseudoperfect, so every
positive multiple of it is pseudoperfect. This removes an infinite branch of
the squarefree six-prime search tree. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_13 {n : ℕ}
    (hsq : Squarefree n) (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h7 : 7 ∈ n.primeFactors) (h11 : 11 ∈ n.primeFactors)
    (h13 : 13 ∈ n.primeFactors) : ¬Weird n := by
  have hsubset : ({3, 5, 7, 11, 13} : Finset ℕ) ⊆ n.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h11
    · exact h13
  exact not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_15015)

/-- The pseudoperfect core `3 * 5 * 7 * 11 * 17` rules out every squarefree
weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_17 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 7, 11, 17} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_19635)

/-- The pseudoperfect core `3 * 5 * 7 * 11 * 19` rules out every squarefree
weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_19 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 7, 11, 19} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_21945)

/-- The pseudoperfect core `3 * 5 * 7 * 13 * 17` rules out every squarefree
weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_13_17 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 7, 13, 17} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_23205)

/-- The pseudoperfect core `3 * 5 * 7 * 13 * 19` rules out every squarefree
weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_13_19 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 7, 13, 19} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_25935)

/-- The pseudoperfect core `3 * 5 * 7 * 11 * 23` rules out every squarefree
weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_23 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 7, 11, 23} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_26565)

/-- In the `3,5,7,11` branch, any extra prime factor `r ≤ 383` makes the
candidate pseudoperfect, hence not weird. This removes the infinite part of the
branch: only the two-large-prime corridor remains. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_small_extra {n r : ℕ}
    (hsq : Squarefree n) (hr : Nat.Prime r) (hr13 : 13 ≤ r) (hr383 : r ≤ 383)
    (hsubset : ({3, 5, 7, 11, r} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    rw [prod_3_5_7_11_r hr13]
    exact pp_1155_mul_of_small_prime hr hr13 hr383)

/-- Certificate form for the remaining two-large-prime corridor in the
`3,5,7,11` branch.

To use this theorem, provide subset-sum certificates `A`, `B`, and `C` over the
divisors of `1155` satisfying `A.sum + r*B.sum + s*C.sum = 6rs`. Then any
squarefree number containing the six prime factors `3,5,7,11,r,s` is
pseudoperfect and therefore not weird. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_cert {n r s : ℕ}
    (hsq : Squarefree n) (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hr13 : 13 ≤ r) (hs13 : 13 ≤ s) (hrs : r ≠ s)
    {A B C : Finset ℕ} (hA : A ⊆ (1155 : ℕ).divisors)
    (hB : B ⊆ (1155 : ℕ).divisors) (hC : C ⊆ (1155 : ℕ).divisors)
    (hsum : A.sum id + r * B.sum id + s * C.sum id = 6 * r * s)
    (hsubset : ({3, 5, 7, 11, r, s} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    rw [prod_3_5_7_11_r_s hr13 hs13 hrs]
    exact pp_1155_mul_mul_of_cert hr hs hr13 hs13 hrs hA hB hC hsum)

/-- The ordered product `3*5*7*11*r*s` is not weird outside the finite
large-prime corridor

`s * (r - 384) ≤ 384 * (r + 1)`.

This is only an abundance obstruction: the exact divisor sum is
`2304*(r+1)*(s+1)`, so outside the corridor it is less than
`2*(1155*r*s)`. -/
theorem not_weird_1155_mul_mul_of_ordered_outside_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr384 : 384 < r)
    (hout : 384 * (r + 1) < s * (r - 384)) : ¬Weird (1155 * r * s) := by
  intro hw
  exact not_abundant_1155_mul_mul_of_outside_corridor hr hs (by omega) (by omega)
    (by omega) hr384 hout hw.1

/-- Any weird ordered product `3*5*7*11*r*s` with `384 < r < s` must lie in
the finite large-prime corridor

`s * (r - 384) ≤ 384 * (r + 1)`. -/
theorem corridor_of_weird_1155_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr384 : 384 < r)
    (hw : Weird (1155 * r * s)) :
    s * (r - 384) ≤ 384 * (r + 1) := by
  exact corridor_of_abundant_1155_mul_mul hr hs (by omega) (by omega) (by omega)
    hr384 hw.1

/-- In the same ordered large-prime branch, abundance already forces
`r ≤ 768`. Since `r` is prime and `384 < r`, this leaves a finite list for the
first extra prime. -/
theorem first_prime_le_768_of_weird_1155_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr384 : 384 < r)
    (hw : Weird (1155 * r * s)) : r ≤ 768 := by
  exact first_prime_le_768_of_abundant_1155_mul_mul hr hs (by omega) (by omega)
    (by omega) hrs_lt hr384 hw.1

/-- The preceding arithmetic bound plus a tiny finite prime check: in a weird
ordered product `3*5*7*11*r*s` with `384 < r < s`, the first extra prime is at
most `761`. -/
theorem first_prime_le_761_of_weird_1155_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr384 : 384 < r)
    (hw : Weird (1155 * r * s)) : r ≤ 761 :=
  prime_le_761_of_le_768 hr
    (first_prime_le_768_of_weird_1155_mul_mul hr hs hrs_lt hr384 hw)

set_option linter.style.nativeDecide false in
/-- One exceptional large-pair certificate in the `3,5,7,11` branch. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_491_883 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 7, 11, 491, 883} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n := by
  refine not_weird_of_squarefree_primeFactors_contains_3_5_7_11_cert (r := 491) (s := 883)
    hsq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (A := ({3, 5, 11, 21, 33, 35, 55, 105, 165, 231} : Finset ℕ))
    (B := ({1155} : Finset ℕ))
    (C := ({3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155} :
      Finset ℕ)) ?_ ?_ ?_ ?_ hsubset
  · native_decide
  · native_decide
  · native_decide
  · native_decide

set_option linter.style.nativeDecide false in
/-- One exceptional large-pair certificate in the `3,5,7,11` branch. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_557_619 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 7, 11, 557, 619} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n := by
  refine not_weird_of_squarefree_primeFactors_contains_3_5_7_11_cert (r := 557) (s := 619)
    hsq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (A := ({1, 3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 165, 231, 385} :
      Finset ℕ))
    (B := ({1155} : Finset ℕ))
    (C := ({1, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155} :
      Finset ℕ)) ?_ ?_ ?_ ?_ hsubset
  · native_decide
  · native_decide
  · native_decide
  · native_decide

set_option linter.style.nativeDecide false in
/-- One exceptional large-pair certificate in the `3,5,7,11` branch. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_11_571_587 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 7, 11, 571, 587} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n := by
  refine not_weird_of_squarefree_primeFactors_contains_3_5_7_11_cert (r := 571) (s := 587)
    hsq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (A := ({3, 11, 15, 21, 33, 55, 77, 105, 165, 385} : Finset ℕ))
    (B := ({1155} : Finset ℕ))
    (C := ({1, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155} :
      Finset ℕ)) ?_ ?_ ?_ ?_ hsubset
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- The six-prime pseudoperfect core `3 * 5 * 11 * 13 * 17 * 19` rules out
every squarefree weird multiple of it. This is the first branch not covered by a
five-prime pseudoperfect core in the small squarefree search. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_11_13_17_19 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 11, 13, 17, 19} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_692835)

/-! ### Exceptional abundant forms are pseudoperfect -/

/-- Any abundant number of the form `3^a * 5^b * 7^c` is pseudoperfect. -/
private theorem three_five_seven_pseudoperfect_of_abundant (a b c : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hab : Abundant (3 ^ a * 5 ^ b * 7 ^ c)) :
    Pseudoperfect (3 ^ a * 5 ^ b * 7 ^ c) := by
  by_cases ha3 : 3 ≤ a
  · have hdecomp :
        3 ^ a * 5 ^ b * 7 ^ c =
          (3 ^ (a - 3) * 5 ^ (b - 1) * 7 ^ (c - 1)) * 945 := by
      have ha' : a = (a - 3) + 3 := (Nat.sub_add_cancel ha3).symm
      have hb' : b = (b - 1) + 1 := (Nat.sub_add_cancel hb).symm
      have hc' : c = (c - 1) + 1 := (Nat.sub_add_cancel hc).symm
      rw [ha', hb', hc', pow_add, pow_add, pow_add]
      norm_num
      ring
    have hm : 0 < 3 ^ (a - 3) * 5 ^ (b - 1) * 7 ^ (c - 1) := by positivity
    simpa [hdecomp] using (pseudoperfect_mul hm pp_945)
  · have ha2 : a ≤ 2 := by omega
    have ha_eq2_or_eq1 : a = 1 ∨ a = 2 := by omega
    rcases ha_eq2_or_eq1 with rfl | rfl
    · exact (three_five_seven_a_one_not_abundant b c hab).elim
    · by_cases hb2 : 2 ≤ b
      · have hdecomp :
            3 ^ 2 * 5 ^ b * 7 ^ c =
              (5 ^ (b - 2) * 7 ^ (c - 1)) * 1575 := by
          have hb' : b = (b - 2) + 2 := (Nat.sub_add_cancel hb2).symm
          have hc' : c = (c - 1) + 1 := (Nat.sub_add_cancel hc).symm
          rw [hb', hc', pow_add, pow_add]
          norm_num
          ring
        have hm : 0 < 5 ^ (b - 2) * 7 ^ (c - 1) := by positivity
        rw [hdecomp]
        exact pseudoperfect_mul hm pp_1575
      · have hb_eq1 : b = 1 := by omega
        by_cases hc2 : 2 ≤ c
        · have hdecomp :
              3 ^ 2 * 5 ^ 1 * 7 ^ c =
                7 ^ (c - 2) * 2205 := by
            have hc' : c = (c - 2) + 2 := (Nat.sub_add_cancel hc2).symm
            rw [hc', pow_add]
            norm_num
            ring
          have hm : 0 < 7 ^ (c - 2) := by positivity
          rw [hb_eq1, hdecomp]
          exact pseudoperfect_mul hm pp_2205
        · have hc_eq1 : c = 1 := by omega
          exact (three_five_seven_two_one_one_not_abundant <|
            by simpa [hb_eq1, hc_eq1] using hab).elim

/-- Any abundant number of the form `3^a * 5^b * 11^c` is pseudoperfect. -/
private theorem three_five_eleven_pseudoperfect_of_abundant (a b c : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hab : Abundant (3 ^ a * 5 ^ b * 11 ^ c)) :
    Pseudoperfect (3 ^ a * 5 ^ b * 11 ^ c) := by
  by_cases ha3 : 3 ≤ a
  · by_cases hb2 : 2 ≤ b
    · have hdecomp :
          3 ^ a * 5 ^ b * 11 ^ c =
            (3 ^ (a - 3) * 5 ^ (b - 2) * 11 ^ (c - 1)) * 7425 := by
        have ha' : a = (a - 3) + 3 := (Nat.sub_add_cancel ha3).symm
        have hb' : b = (b - 2) + 2 := (Nat.sub_add_cancel hb2).symm
        have hc' : c = (c - 1) + 1 := (Nat.sub_add_cancel hc).symm
        rw [ha', hb', hc', pow_add, pow_add, pow_add]
        norm_num
        ring
      have hm : 0 < 3 ^ (a - 3) * 5 ^ (b - 2) * 11 ^ (c - 1) := by positivity
      simpa [hdecomp] using (pseudoperfect_mul hm pp_7425)
    · have hb_eq1 : b = 1 := by omega
      exact (three_five_eleven_b_one_not_abundant a c <|
        by simpa [hb_eq1] using hab).elim
  · have ha2 : a ≤ 2 := by omega
    exact (three_five_eleven_a_le_two_not_abundant a b c ha2 hab).elim

/-- Any abundant number of the form `3^a * 5^b * 13^c` is pseudoperfect. -/
private theorem three_five_thirteen_pseudoperfect_of_abundant (a b c : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hab : Abundant (3 ^ a * 5 ^ b * 13 ^ c)) :
    Pseudoperfect (3 ^ a * 5 ^ b * 13 ^ c) := by
  by_cases ha5 : 5 ≤ a
  · by_cases hb2 : 2 ≤ b
    · have hdecomp :
          3 ^ a * 5 ^ b * 13 ^ c =
            (3 ^ (a - 5) * 5 ^ (b - 2) * 13 ^ (c - 1)) * 78975 := by
        have ha' : a = (a - 5) + 5 := (Nat.sub_add_cancel ha5).symm
        have hb' : b = (b - 2) + 2 := (Nat.sub_add_cancel hb2).symm
        have hc' : c = (c - 1) + 1 := (Nat.sub_add_cancel hc).symm
        rw [ha', hb', hc', pow_add, pow_add, pow_add]
        norm_num
        ring
      have hm : 0 < 3 ^ (a - 5) * 5 ^ (b - 2) * 13 ^ (c - 1) := by positivity
      simpa [hdecomp] using (pseudoperfect_mul hm pp_78975)
    · have hb_eq1 : b = 1 := by omega
      exact (three_five_thirteen_b_one_not_abundant a c <|
        by simpa [hb_eq1] using hab).elim
  · by_cases ha4 : 4 ≤ a
    · have ha_eq4 : a = 4 := by omega
      by_cases hb3 : 3 ≤ b
      · have hdecomp :
            3 ^ 4 * 5 ^ b * 13 ^ c =
              (5 ^ (b - 3) * 13 ^ (c - 1)) * 131625 := by
          have hb' : b = (b - 3) + 3 := (Nat.sub_add_cancel hb3).symm
          have hc' : c = (c - 1) + 1 := (Nat.sub_add_cancel hc).symm
          rw [hb', hc', pow_add, pow_add]
          norm_num
          ring
        have hm : 0 < 5 ^ (b - 3) * 13 ^ (c - 1) := by positivity
        rw [ha_eq4, hdecomp]
        exact pseudoperfect_mul hm pp_131625
      · by_cases hb2 : 2 ≤ b
        · have hb_eq2 : b = 2 := by omega
          by_cases hc2 : 2 ≤ c
          · have hdecomp :
                3 ^ 4 * 5 ^ 2 * 13 ^ c =
                  13 ^ (c - 2) * 342225 := by
              have hc' : c = (c - 2) + 2 := (Nat.sub_add_cancel hc2).symm
              rw [hc', pow_add]
              norm_num
              ring
            have hm : 0 < 13 ^ (c - 2) := by positivity
            rw [ha_eq4, hb_eq2, hdecomp]
            exact pseudoperfect_mul hm pp_342225
          · have hc_eq1 : c = 1 := by omega
            exact (three_five_thirteen_four_two_one_not_abundant <|
              by simpa [ha_eq4, hb_eq2, hc_eq1] using hab).elim
        · have hb_eq1 : b = 1 := by omega
          exact (three_five_thirteen_b_one_not_abundant a c <|
            by simpa [hb_eq1] using hab).elim
    · by_cases ha3 : 3 ≤ a
      · have ha_eq3 : a = 3 := by omega
        by_cases hb3 : 3 ≤ b
        · by_cases hc2 : 2 ≤ c
          · have hdecomp :
                3 ^ 3 * 5 ^ b * 13 ^ c =
                  (5 ^ (b - 3) * 13 ^ (c - 2)) * 570375 := by
              have hb' : b = (b - 3) + 3 := (Nat.sub_add_cancel hb3).symm
              have hc' : c = (c - 2) + 2 := (Nat.sub_add_cancel hc2).symm
              rw [hb', hc', pow_add, pow_add]
              norm_num
              ring
            have hm : 0 < 5 ^ (b - 3) * 13 ^ (c - 2) := by positivity
            rw [ha_eq3, hdecomp]
            exact pseudoperfect_mul hm pp_570375
          · have hc_eq1 : c = 1 := by omega
            exact (three_five_thirteen_three_c_one_not_abundant b <|
              by simpa [ha_eq3, hc_eq1] using hab).elim
        · have hb2 : b ≤ 2 := by omega
          exact (three_five_thirteen_three_b_le_two_not_abundant b c hb2 <|
            by simpa [ha_eq3] using hab).elim
      · have ha2 : a ≤ 2 := by omega
        exact (three_five_thirteen_a_le_two_not_abundant a b c ha2 hab).elim

/-! ### Capstone: no odd weird number with exactly three prime factors -/

/-- Rebuild a number from three named prime factors. -/
private theorem eq_prime_power_product_of_primeFactors_eq_three {n p q r : ℕ}
    (hn : n ≠ 0) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpf : n.primeFactors = ({p, q, r} : Finset ℕ)) :
    n = p ^ n.factorization p * q ^ n.factorization q * r ^ n.factorization r := by
  have hfact := Nat.factorization_prod_pow_eq_self hn
  conv_lhs => rw [← hfact]
  simp only [Finsupp.prod, Nat.support_factorization, hpf]
  rw [Finset.prod_insert (by simp [hpq, hpr])]
  rw [Finset.prod_insert (by simp [hqr])]
  rw [Finset.prod_singleton]
  ring

/-- A named prime factor occurs with positive exponent. -/
private theorem one_le_factorization_of_mem_primeFactors {n p : ℕ} (hn : n ≠ 0)
    (hp : p ∈ n.primeFactors) : 1 ≤ n.factorization p :=
  Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
    (Nat.dvd_of_mem_primeFactors hp)

/-- In an odd number, every prime factor is at least `3`. -/
private theorem prime_factor_ge_three_of_odd {n p : ℕ} (hodd : ¬Even n)
    (hp_mem : p ∈ n.primeFactors) : 3 ≤ p := by
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hp_ne_two : p ≠ 2 := by
    intro h
    exact hodd (even_iff_two_dvd.mpr (h ▸ Nat.dvd_of_mem_primeFactors hp_mem))
  have hp_two_le := hp.two_le
  omega

/-- In an odd number, a prime factor other than `3` is at least `5`. -/
private theorem prime_factor_ge_five_of_ne_three {n p : ℕ} (hodd : ¬Even n)
    (hp_mem : p ∈ n.primeFactors) (hp_ne_three : p ≠ 3) : 5 ≤ p := by
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hp_ne_two : p ≠ 2 := by
    intro h
    exact hodd (even_iff_two_dvd.mpr (h ▸ Nat.dvd_of_mem_primeFactors hp_mem))
  by_contra h
  push_neg at h
  have hp_two_le := hp.two_le
  have hp_ne_four : p ≠ 4 := by intro hp4; subst hp4; norm_num at hp
  omega

/-- In an odd number, a prime factor other than `3` and `5` is at least `7`. -/
private theorem prime_factor_ge_seven_of_ne_three_five {n p : ℕ} (hodd : ¬Even n)
    (hp_mem : p ∈ n.primeFactors) (hp_ne_three : p ≠ 3) (hp_ne_five : p ≠ 5) :
    7 ≤ p := by
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hp_ne_two : p ≠ 2 := by
    intro h
    exact hodd (even_iff_two_dvd.mpr (h ▸ Nat.dvd_of_mem_primeFactors hp_mem))
  by_contra h
  push_neg at h
  have hp_two_le := hp.two_le
  have hp_ne_four : p ≠ 4 := by intro hp4; subst hp4; norm_num at hp
  have hp_ne_six : p ≠ 6 := by intro hp6; subst hp6; norm_num at hp
  omega

/-- A prime at least `7`, but not `7`, is at least `11`. -/
private theorem prime_ge_eleven_of_ge_seven_ne_seven {p : ℕ} (hp : Nat.Prime p)
    (hp7 : 7 ≤ p) (hp_ne_seven : p ≠ 7) : 11 ≤ p := by
  by_contra h
  push_neg at h
  have hp_ne_eight : p ≠ 8 := by intro hp8; subst hp8; norm_num at hp
  have hp_ne_nine : p ≠ 9 := by intro hp9; subst hp9; norm_num at hp
  have hp_ne_ten : p ≠ 10 := by intro hp10; subst hp10; norm_num at hp
  omega

/-- A prime at least `11`, but not `11`, is at least `13`. -/
private theorem prime_ge_thirteen_of_ge_eleven_ne_eleven {p : ℕ} (hp : Nat.Prime p)
    (hp11 : 11 ≤ p) (hp_ne_eleven : p ≠ 11) : 13 ≤ p := by
  by_contra h
  push_neg at h
  have hp_ne_twelve : p ≠ 12 := by intro hp12; subst hp12; norm_num at hp
  omega

/-- A prime at least `13`, but not `13`, is at least `17`. -/
private theorem prime_ge_seventeen_of_ge_thirteen_ne_thirteen {p : ℕ} (hp : Nat.Prime p)
    (hp13 : 13 ≤ p) (hp_ne_thirteen : p ≠ 13) : 17 ≤ p := by
  by_contra h
  push_neg at h
  have hp_ne_fourteen : p ≠ 14 := by intro hp14; subst hp14; norm_num at hp
  have hp_ne_fifteen : p ≠ 15 := by intro hp15; subst hp15; norm_num at hp
  have hp_ne_sixteen : p ≠ 16 := by intro hp16; subst hp16; norm_num at hp
  omega

/-- A prime at least `17`, but not `17`, is at least `19`. -/
private theorem prime_ge_nineteen_of_ge_seventeen_ne_seventeen {p : ℕ} (hp : Nat.Prime p)
    (hp17 : 17 ≤ p) (hp_ne_seventeen : p ≠ 17) : 19 ≤ p := by
  by_contra h
  push_neg at h
  have hp_ne_eighteen : p ≠ 18 := by intro hp18; subst hp18; norm_num at hp
  omega

/-- A prime at least `19`, but not `19`, is at least `23`. -/
private theorem prime_ge_twentythree_of_ge_nineteen_ne_nineteen {p : ℕ} (hp : Nat.Prime p)
    (hp19 : 19 ≤ p) (hp_ne_nineteen : p ≠ 19) : 23 ≤ p := by
  by_contra h
  push_neg at h
  have hp_ne_twenty : p ≠ 20 := by intro hp20; subst hp20; norm_num at hp
  have hp_ne_twentyone : p ≠ 21 := by intro hp21; subst hp21; norm_num at hp
  have hp_ne_twentytwo : p ≠ 22 := by intro hp22; subst hp22; norm_num at hp
  omega

/-- A prime at least `23`, but not `23`, is at least `29`. -/
private theorem prime_ge_twentynine_of_ge_twentythree_ne_twentythree {p : ℕ} (hp : Nat.Prime p)
    (hp23 : 23 ≤ p) (hp_ne_twentythree : p ≠ 23) : 29 ≤ p := by
  by_contra h
  push_neg at h
  have hp_ne_twentyfour : p ≠ 24 := by intro hp24; subst hp24; norm_num at hp
  have hp_ne_twentyfive : p ≠ 25 := by intro hp25; subst hp25; norm_num at hp
  have hp_ne_twentysix : p ≠ 26 := by intro hp26; subst hp26; norm_num at hp
  have hp_ne_twentyseven : p ≠ 27 := by intro hp27; subst hp27; norm_num at hp
  have hp_ne_twentyeight : p ≠ 28 := by intro hp28; subst hp28; norm_num at hp
  omega

/-- In an odd number, a prime factor outside `{3,5,7,11,13}` is at least `17`. -/
private theorem prime_factor_ge_seventeen_of_not_small {n p : ℕ} (hodd : ¬Even n)
    (hp_mem : p ∈ n.primeFactors) (hp_ne_three : p ≠ 3) (hp_ne_five : p ≠ 5)
    (hp_ne_seven : p ≠ 7) (hp_ne_eleven : p ≠ 11) (hp_ne_thirteen : p ≠ 13) :
    17 ≤ p := by
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hp_ne_two : p ≠ 2 := by
    intro h
    exact hodd (even_iff_two_dvd.mpr (h ▸ Nat.dvd_of_mem_primeFactors hp_mem))
  by_contra h
  push_neg at h
  have hp_two_le := hp.two_le
  have hp_ne_four : p ≠ 4 := by intro hp4; subst hp4; norm_num at hp
  have hp_ne_six : p ≠ 6 := by intro hp6; subst hp6; norm_num at hp
  have hp_ne_eight : p ≠ 8 := by intro hp8; subst hp8; norm_num at hp
  have hp_ne_nine : p ≠ 9 := by intro hp9; subst hp9; norm_num at hp
  have hp_ne_ten : p ≠ 10 := by intro hp10; subst hp10; norm_num at hp
  have hp_ne_twelve : p ≠ 12 := by intro hp12; subst hp12; norm_num at hp
  have hp_ne_fourteen : p ≠ 14 := by intro hp14; subst hp14; norm_num at hp
  have hp_ne_fifteen : p ≠ 15 := by intro hp15; subst hp15; norm_num at hp
  have hp_ne_sixteen : p ≠ 16 := by intro hp16; subst hp16; norm_num at hp
  omega

/-- Three odd prime factors, none equal to `3`, force non-abundance. -/
private theorem not_abundant_of_three_primeFactors_without_three {n p q r : ℕ}
    (hodd : ¬Even n) (hn : n ≠ 0)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpf : n.primeFactors = ({p, q, r} : Finset ℕ)) (hno3 : 3 ∉ n.primeFactors) :
    ¬Abundant n := by
  have hp_mem : p ∈ n.primeFactors := by rw [hpf]; simp
  have hq_mem : q ∈ n.primeFactors := by rw [hpf]; simp
  have hr_mem : r ∈ n.primeFactors := by rw [hpf]; simp
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hq : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
  have hr : Nat.Prime r := Nat.prime_of_mem_primeFactors hr_mem
  have hp5 : 5 ≤ p := prime_factor_ge_five_of_ne_three hodd hp_mem (by
    intro hp3; exact hno3 (hp3 ▸ hp_mem))
  have hq5 : 5 ≤ q := prime_factor_ge_five_of_ne_three hodd hq_mem (by
    intro hq3; exact hno3 (hq3 ▸ hq_mem))
  have hr5 : 5 ≤ r := prime_factor_ge_five_of_ne_three hodd hr_mem (by
    intro hr3; exact hno3 (hr3 ▸ hr_mem))
  have hn_eq := eq_prime_power_product_of_primeFactors_eq_three hn hpq hpr hqr hpf
  apply not_abundant_of_sigma_lt
  rw [hn_eq]
  exact sigma_three_ge5_lt hp hq hr hpq hpr hqr hp5 hq5 hr5
    (n.factorization p) (n.factorization q) (n.factorization r)

/-- Three odd prime factors containing `3` but not `5` force non-abundance. -/
private theorem not_abundant_of_three_primeFactors_with_three_without_five {n : ℕ}
    (hodd : ¬Even n) (hn : n ≠ 0) (hcard : n.primeFactors.card = 3)
    (h3 : 3 ∈ n.primeFactors) (hno5 : 5 ∉ n.primeFactors) : ¬Abundant n := by
  let R := n.primeFactors.erase 3
  have hRcard : R.card = 2 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem h3, hcard]
  obtain ⟨q, r, hqr, hR⟩ := Finset.card_eq_two.mp hRcard
  have hqR : q ∈ R := by rw [hR]; simp
  have hrR : r ∈ R := by rw [hR]; simp
  have hq_ne3 : q ≠ 3 := (Finset.mem_erase.mp hqR).1
  have hr_ne3 : r ≠ 3 := (Finset.mem_erase.mp hrR).1
  have hq_mem : q ∈ n.primeFactors := (Finset.mem_erase.mp hqR).2
  have hr_mem : r ∈ n.primeFactors := (Finset.mem_erase.mp hrR).2
  have hq_ne5 : q ≠ 5 := by intro hq5; exact hno5 (hq5 ▸ hq_mem)
  have hr_ne5 : r ≠ 5 := by intro hr5; exact hno5 (hr5 ▸ hr_mem)
  have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
  have hr_prime : Nat.Prime r := Nat.prime_of_mem_primeFactors hr_mem
  have hq7 : 7 ≤ q :=
    prime_factor_ge_seven_of_ne_three_five hodd hq_mem hq_ne3 hq_ne5
  have hr7 : 7 ≤ r :=
    prime_factor_ge_seven_of_ne_three_five hodd hr_mem hr_ne3 hr_ne5
  have hpf : n.primeFactors = ({3, q, r} : Finset ℕ) := by
    calc
      n.primeFactors = insert 3 R := (Finset.insert_erase h3).symm
      _ = ({3, q, r} : Finset ℕ) := by rw [hR]
  have hn_eq := eq_prime_power_product_of_primeFactors_eq_three hn
    hq_ne3.symm hr_ne3.symm hqr hpf
  apply not_abundant_of_sigma_lt
  by_cases hq_eq7 : q = 7
  · have hr11 : 11 ≤ r := prime_ge_eleven_of_ge_seven_ne_seven hr_prime hr7 (by
      intro hr_eq7
      exact hqr (by omega))
    rw [hn_eq]
    exact sigma_three_3_ge7_ge11_lt hq_prime hr_prime hq7 hr11 hqr
      (n.factorization 3) (n.factorization q) (n.factorization r)
  · have hq11 : 11 ≤ q := prime_ge_eleven_of_ge_seven_ne_seven hq_prime hq7 hq_eq7
    rw [hn_eq]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      sigma_three_3_ge7_ge11_lt hr_prime hq_prime hr7 hq11 hqr.symm
        (n.factorization 3) (n.factorization r) (n.factorization q)

/-- If the prime support is one of the three exceptional supports, abundance
forces pseudoperfectness; hence the number cannot be weird. -/
private theorem not_weird_of_exceptional_three_primeFactors {n r : ℕ} (hw : Weird n)
    (hn : n ≠ 0) (hr : r = 7 ∨ r = 11 ∨ r = 13)
    (hpf : n.primeFactors = ({3, 5, r} : Finset ℕ)) : False := by
  have h3 : 3 ∈ n.primeFactors := by rw [hpf]; simp
  have h5 : 5 ∈ n.primeFactors := by rw [hpf]; simp
  have hrmem : r ∈ n.primeFactors := by rw [hpf]; simp
  have ha : 1 ≤ n.factorization 3 := one_le_factorization_of_mem_primeFactors hn h3
  have hb : 1 ≤ n.factorization 5 := one_le_factorization_of_mem_primeFactors hn h5
  have hc : 1 ≤ n.factorization r := one_le_factorization_of_mem_primeFactors hn hrmem
  rcases hr with rfl | rfl | rfl
  · have hn_eq := eq_prime_power_product_of_primeFactors_eq_three hn
      (by norm_num : (3 : ℕ) ≠ 5) (by norm_num : (3 : ℕ) ≠ 7)
      (by norm_num : (5 : ℕ) ≠ 7) (by simpa using hpf)
    have hpseudo : Pseudoperfect n := by
      have hab : Abundant (3 ^ n.factorization 3 * 5 ^ n.factorization 5 *
          7 ^ n.factorization 7) := hn_eq ▸ hw.1
      exact hn_eq.symm ▸
        three_five_seven_pseudoperfect_of_abundant
          (n.factorization 3) (n.factorization 5) (n.factorization 7)
          ha hb hc hab
    exact hw.2 hpseudo
  · have hn_eq := eq_prime_power_product_of_primeFactors_eq_three hn
      (by norm_num : (3 : ℕ) ≠ 5) (by norm_num : (3 : ℕ) ≠ 11)
      (by norm_num : (5 : ℕ) ≠ 11) (by simpa using hpf)
    have hpseudo : Pseudoperfect n := by
      have hab : Abundant (3 ^ n.factorization 3 * 5 ^ n.factorization 5 *
          11 ^ n.factorization 11) := hn_eq ▸ hw.1
      exact hn_eq.symm ▸
        three_five_eleven_pseudoperfect_of_abundant
          (n.factorization 3) (n.factorization 5) (n.factorization 11)
          ha hb hc hab
    exact hw.2 hpseudo
  · have hn_eq := eq_prime_power_product_of_primeFactors_eq_three hn
      (by norm_num : (3 : ℕ) ≠ 5) (by norm_num : (3 : ℕ) ≠ 13)
      (by norm_num : (5 : ℕ) ≠ 13) (by simpa using hpf)
    have hpseudo : Pseudoperfect n := by
      have hab : Abundant (3 ^ n.factorization 3 * 5 ^ n.factorization 5 *
          13 ^ n.factorization 13) := hn_eq ▸ hw.1
      exact hn_eq.symm ▸
        three_five_thirteen_pseudoperfect_of_abundant
          (n.factorization 3) (n.factorization 5) (n.factorization 13)
          ha hb hc hab
    exact hw.2 hpseudo

/-- Three odd prime factors containing `3` and `5` still cannot be weird.

The only abundant-support candidates with three distinct odd prime factors are
`{3,5,7}`, `{3,5,11}`, and `{3,5,13}`; in each of these supports, the preceding
covering lemmas prove pseudoperfectness. All other third primes are at least
`17`, where the divisor-sum bound is already below the abundance threshold. -/
private theorem not_weird_of_three_primeFactors_with_three_five {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hn : n ≠ 0) (hcard : n.primeFactors.card = 3)
    (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors) : False := by
  let R := (n.primeFactors.erase 3).erase 5
  have h5R0 : 5 ∈ n.primeFactors.erase 3 := by
    exact Finset.mem_erase.mpr ⟨by norm_num, h5⟩
  have hErase3card : (n.primeFactors.erase 3).card = 2 := by
    rw [Finset.card_erase_of_mem h3, hcard]
  have hRcard : R.card = 1 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem h5R0, hErase3card]
  obtain ⟨r, hR⟩ := Finset.card_eq_one.mp hRcard
  have hrR : r ∈ R := by rw [hR]; simp
  have hr_ne5 : r ≠ 5 := (Finset.mem_erase.mp hrR).1
  have hrErase3 : r ∈ n.primeFactors.erase 3 := (Finset.mem_erase.mp hrR).2
  have hr_ne3 : r ≠ 3 := (Finset.mem_erase.mp hrErase3).1
  have hr_mem : r ∈ n.primeFactors := (Finset.mem_erase.mp hrErase3).2
  have hpf : n.primeFactors = ({3, 5, r} : Finset ℕ) := by
    calc
      n.primeFactors = insert 3 (n.primeFactors.erase 3) := (Finset.insert_erase h3).symm
      _ = insert 3 (insert 5 R) := by rw [Finset.insert_erase h5R0]
      _ = ({3, 5, r} : Finset ℕ) := by rw [hR]
  by_cases hr7 : r = 7
  · exact not_weird_of_exceptional_three_primeFactors hw hn (Or.inl hr7) hpf
  by_cases hr11 : r = 11
  · exact not_weird_of_exceptional_three_primeFactors hw hn (Or.inr (Or.inl hr11)) hpf
  by_cases hr13 : r = 13
  · exact not_weird_of_exceptional_three_primeFactors hw hn (Or.inr (Or.inr hr13)) hpf
  have hr17 : 17 ≤ r :=
    prime_factor_ge_seventeen_of_not_small hodd hr_mem hr_ne3 hr_ne5
      hr7 hr11 hr13
  have hrprime : Nat.Prime r := Nat.prime_of_mem_primeFactors hr_mem
  have hn_eq := eq_prime_power_product_of_primeFactors_eq_three hn
    (by norm_num : (3 : ℕ) ≠ 5) hr_ne3.symm hr_ne5.symm hpf
  have hnot : ¬Abundant n := by
    apply not_abundant_of_sigma_lt
    rw [hn_eq]
    exact sigma_three_3_5_ge17_lt hrprime hr17
      (n.factorization 3) (n.factorization 5) (n.factorization r)
  exact hnot hw.1

/-- **Any odd weird number has at least four distinct prime factors.**

This closes the three-prime case by combining the divisor-sum bounds with the
explicit pseudoperfect coverings for the only three exceptional supports. It is
a formal step toward Liddy--Riedl's stronger theorem that an odd weird number
would need at least six distinct prime factors. -/
theorem odd_weird_four_prime_factors {n : ℕ} (hw : Weird n) (hodd : ¬Even n) :
    4 ≤ n.primeFactors.card := by
  by_contra h
  push_neg at h
  have hthree : 3 ≤ n.primeFactors.card := odd_weird_three_prime_factors hw hodd
  have hcard : n.primeFactors.card = 3 := by omega
  have hn : n ≠ 0 := by exact Nat.ne_of_gt hw.1.1
  by_cases h3 : 3 ∈ n.primeFactors
  · by_cases h5 : 5 ∈ n.primeFactors
    · exact not_weird_of_three_primeFactors_with_three_five hw hodd hn hcard h3 h5
    · exact (not_abundant_of_three_primeFactors_with_three_without_five
        hodd hn hcard h3 h5) hw.1
  · obtain ⟨p, q, r, hpq, hpr, hqr, hpf⟩ := Finset.card_eq_three.mp hcard
    exact (not_abundant_of_three_primeFactors_without_three hodd hn hpq hpr hqr hpf h3) hw.1

/-! ### First constraint on the four-prime case -/

/-- σ is multiplicative over four pairwise coprime prime powers. -/
private theorem sigma_four_primes_mul {p q r s : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (a b c d : ℕ) :
    (p ^ a * q ^ b * r ^ c * s ^ d).divisors.sum id =
      (p ^ a).divisors.sum id * (q ^ b).divisors.sum id *
        (r ^ c).divisors.sum id * (s ^ d).divisors.sum id := by
  have hcop_p_s : Nat.Coprime (p ^ a) (s ^ d) := by
    apply Nat.Coprime.pow
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    rcases hs.eq_one_or_self_of_dvd p hdvd with h | h
    · exact absurd h hp.one_lt.ne'
    · exact hps h
  have hcop_q_s : Nat.Coprime (q ^ b) (s ^ d) := by
    apply Nat.Coprime.pow
    rw [hq.coprime_iff_not_dvd]
    intro hdvd
    rcases hs.eq_one_or_self_of_dvd q hdvd with h | h
    · exact absurd h hq.one_lt.ne'
    · exact hqs h
  have hcop_r_s : Nat.Coprime (r ^ c) (s ^ d) := by
    apply Nat.Coprime.pow
    rw [hr.coprime_iff_not_dvd]
    intro hdvd
    rcases hs.eq_one_or_self_of_dvd r hdvd with h | h
    · exact absurd h hr.one_lt.ne'
    · exact hrs h
  have hcop_pq_s : Nat.Coprime (p ^ a * q ^ b) (s ^ d) := by
    exact Nat.Coprime.mul_left hcop_p_s hcop_q_s
  have hcop_pqr_s : Nat.Coprime (p ^ a * q ^ b * r ^ c) (s ^ d) := by
    exact Nat.Coprime.mul_left hcop_pq_s hcop_r_s
  have hsplit :
      (p ^ a * q ^ b * r ^ c * s ^ d).divisors.sum id =
        (p ^ a * q ^ b * r ^ c).divisors.sum id * (s ^ d).divisors.sum id :=
    hcop_pqr_s.sum_divisors_mul
  rw [hsplit, sigma_three_primes_mul hp hq hr hpq hpr hqr]

/-- Four prime powers with all primes at least `7` are not abundant. -/
private theorem sigma_four_ge7_lt {p q r s : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hp7 : 7 ≤ p) (hq7 : 7 ≤ q) (hr7 : 7 ≤ r) (hs7 : 7 ≤ s)
    (a b c d : ℕ) :
    (p ^ a * q ^ b * r ^ c * s ^ d).divisors.sum id <
      2 * (p ^ a * q ^ b * r ^ c * s ^ d) := by
  rw [sigma_four_primes_mul hp hq hr hs hpq hpr hps hqr hqs hrs]
  set σp := (p ^ a).divisors.sum id
  set σq := (q ^ b).divisors.sum id
  set σr := (r ^ c).divisors.sum id
  set σs := (s ^ d).divisors.sum id
  have hbp := sigma_bound_ge7 hp hp7 a
  have hbq := sigma_bound_ge7 hq hq7 b
  have hbr := sigma_bound_ge7 hr hr7 c
  have hbs := sigma_bound_ge7 hs hs7 d
  have hbp' : 6 * σp < 7 * p ^ a := by simpa [σp] using hbp
  have hbq' : 6 * σq < 7 * q ^ b := by simpa [σq] using hbq
  have hbr' : 6 * σr < 7 * r ^ c := by simpa [σr] using hbr
  have hbs' : 6 * σs < 7 * s ^ d := by simpa [σs] using hbs
  have hσp_pos : 0 < σp := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσq_pos : 0 < σq := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσr_pos : 0 < σr := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have h1 : (6 * σp) * (6 * σq) * (6 * σr) * (6 * σs) <
      (6 * σp) * (6 * σq) * (6 * σr) * (7 * s ^ d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hbs' (by positivity :
        0 < (6 * σp) * (6 * σq) * (6 * σr))
  have h2 : (6 * σp) * (6 * σq) * (6 * σr) * (7 * s ^ d) <
      (6 * σp) * (6 * σq) * (7 * r ^ c) * (7 * s ^ d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hbr' (by positivity :
        0 < (6 * σp) * (6 * σq) * (7 * s ^ d))
  have h3 : (6 * σp) * (6 * σq) * (7 * r ^ c) * (7 * s ^ d) <
      (6 * σp) * (7 * q ^ b) * (7 * r ^ c) * (7 * s ^ d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hbq' (by positivity :
        0 < (6 * σp) * (7 * r ^ c) * (7 * s ^ d))
  have h4 : (6 * σp) * (7 * q ^ b) * (7 * r ^ c) * (7 * s ^ d) <
      (7 * p ^ a) * (7 * q ^ b) * (7 * r ^ c) * (7 * s ^ d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hbp' (by positivity :
        0 < (7 * q ^ b) * (7 * r ^ c) * (7 * s ^ d))
  have hn_pos : 0 < p ^ a * q ^ b * r ^ c * s ^ d := by positivity
  nlinarith [h1, h2, h3, h4]

/-- If one prime is at least `5` and the other three are at least `7`, the
four-prime divisor-sum ratio is still below the abundance threshold. -/
private theorem sigma_four_ge5_ge7_ge7_ge7_lt {p q r s : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hp5 : 5 ≤ p) (hq7 : 7 ≤ q) (hr7 : 7 ≤ r) (hs7 : 7 ≤ s)
    (a b c d : ℕ) :
    (p ^ a * q ^ b * r ^ c * s ^ d).divisors.sum id <
      2 * (p ^ a * q ^ b * r ^ c * s ^ d) := by
  rw [sigma_four_primes_mul hp hq hr hs hpq hpr hps hqr hqs hrs]
  set σp := (p ^ a).divisors.sum id
  set σq := (q ^ b).divisors.sum id
  set σr := (r ^ c).divisors.sum id
  set σs := (s ^ d).divisors.sum id
  have hbp := sigma_bound_ge5 hp hp5 a
  have hbq := sigma_bound_ge7 hq hq7 b
  have hbr := sigma_bound_ge7 hr hr7 c
  have hbs := sigma_bound_ge7 hs hs7 d
  have hbp' : 4 * σp < 5 * p ^ a := by simpa [σp] using hbp
  have hbq' : 6 * σq < 7 * q ^ b := by simpa [σq] using hbq
  have hbr' : 6 * σr < 7 * r ^ c := by simpa [σr] using hbr
  have hbs' : 6 * σs < 7 * s ^ d := by simpa [σs] using hbs
  have hσp_pos : 0 < σp := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσq_pos : 0 < σq := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσr_pos : 0 < σr := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have h1 : (4 * σp) * (6 * σq) * (6 * σr) * (6 * σs) <
      (4 * σp) * (6 * σq) * (6 * σr) * (7 * s ^ d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hbs' (by positivity :
        0 < (4 * σp) * (6 * σq) * (6 * σr))
  have h2 : (4 * σp) * (6 * σq) * (6 * σr) * (7 * s ^ d) <
      (4 * σp) * (6 * σq) * (7 * r ^ c) * (7 * s ^ d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hbr' (by positivity :
        0 < (4 * σp) * (6 * σq) * (7 * s ^ d))
  have h3 : (4 * σp) * (6 * σq) * (7 * r ^ c) * (7 * s ^ d) <
      (4 * σp) * (7 * q ^ b) * (7 * r ^ c) * (7 * s ^ d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hbq' (by positivity :
        0 < (4 * σp) * (7 * r ^ c) * (7 * s ^ d))
  have h4 : (4 * σp) * (7 * q ^ b) * (7 * r ^ c) * (7 * s ^ d) <
      (5 * p ^ a) * (7 * q ^ b) * (7 * r ^ c) * (7 * s ^ d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left hbp' (by positivity :
        0 < (7 * q ^ b) * (7 * r ^ c) * (7 * s ^ d))
  have hn_pos : 0 < p ^ a * q ^ b * r ^ c * s ^ d := by positivity
  nlinarith [h1, h2, h3, h4]

/-- Four odd prime factors with no factor `3` force non-abundance.

This is the first structural bite into the four-prime case: even allowing a
factor `5`, the other three factors must be at least `7`, and
`(5/4) * (7/6)^3 < 2`. -/
private theorem not_abundant_of_four_primeFactors_without_three {n p q r s : ℕ}
    (hodd : ¬Even n) (hn : n ≠ 0)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hpf : n.primeFactors = ({p, q, r, s} : Finset ℕ)) (hno3 : 3 ∉ n.primeFactors) :
    ¬Abundant n := by
  have hp_mem : p ∈ n.primeFactors := by rw [hpf]; simp
  have hq_mem : q ∈ n.primeFactors := by rw [hpf]; simp
  have hr_mem : r ∈ n.primeFactors := by rw [hpf]; simp
  have hs_mem : s ∈ n.primeFactors := by rw [hpf]; simp
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hq : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
  have hr : Nat.Prime r := Nat.prime_of_mem_primeFactors hr_mem
  have hs : Nat.Prime s := Nat.prime_of_mem_primeFactors hs_mem
  have hp_ne3 : p ≠ 3 := by intro h; exact hno3 (h ▸ hp_mem)
  have hq_ne3 : q ≠ 3 := by intro h; exact hno3 (h ▸ hq_mem)
  have hr_ne3 : r ≠ 3 := by intro h; exact hno3 (h ▸ hr_mem)
  have hs_ne3 : s ≠ 3 := by intro h; exact hno3 (h ▸ hs_mem)
  have hp5 : 5 ≤ p := prime_factor_ge_five_of_ne_three hodd hp_mem hp_ne3
  have hq5 : 5 ≤ q := prime_factor_ge_five_of_ne_three hodd hq_mem hq_ne3
  have hr5 : 5 ≤ r := prime_factor_ge_five_of_ne_three hodd hr_mem hr_ne3
  have hs5 : 5 ≤ s := prime_factor_ge_five_of_ne_three hodd hs_mem hs_ne3
  have hn_eq : n = p ^ n.factorization p * q ^ n.factorization q *
      r ^ n.factorization r * s ^ n.factorization s := by
    have hfact := Nat.factorization_prod_pow_eq_self hn
    conv_lhs => rw [← hfact]
    simp only [Finsupp.prod, Nat.support_factorization, hpf]
    rw [Finset.prod_insert (by simp [hpq, hpr, hps])]
    rw [Finset.prod_insert (by simp [hqr, hqs])]
    rw [Finset.prod_insert (by simp [hrs])]
    rw [Finset.prod_singleton]
    ring
  apply not_abundant_of_sigma_lt
  rw [hn_eq]
  by_cases hp_eq5 : p = 5
  · have hq7 : 7 ≤ q := prime_factor_ge_seven_of_ne_three_five hodd hq_mem hq_ne3
      (by intro h; exact hpq (by omega))
    have hr7 : 7 ≤ r := prime_factor_ge_seven_of_ne_three_five hodd hr_mem hr_ne3
      (by intro h; exact hpr (by omega))
    have hs7 : 7 ≤ s := prime_factor_ge_seven_of_ne_three_five hodd hs_mem hs_ne3
      (by intro h; exact hps (by omega))
    exact sigma_four_ge5_ge7_ge7_ge7_lt hp hq hr hs hpq hpr hps hqr hqs hrs
      hp5 hq7 hr7 hs7 _ _ _ _
  · by_cases hq_eq5 : q = 5
    · have hp7 : 7 ≤ p := prime_factor_ge_seven_of_ne_three_five hodd hp_mem hp_ne3 hp_eq5
      have hr7 : 7 ≤ r := prime_factor_ge_seven_of_ne_three_five hodd hr_mem hr_ne3
        (by intro h; exact hqr (by omega))
      have hs7 : 7 ≤ s := prime_factor_ge_seven_of_ne_three_five hodd hs_mem hs_ne3
        (by intro h; exact hqs (by omega))
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        sigma_four_ge5_ge7_ge7_ge7_lt hq hp hr hs hpq.symm hqr hqs hpr hps hrs
          hq5 hp7 hr7 hs7
          (n.factorization q) (n.factorization p) (n.factorization r) (n.factorization s)
    · by_cases hr_eq5 : r = 5
      · have hp7 : 7 ≤ p := prime_factor_ge_seven_of_ne_three_five hodd hp_mem hp_ne3 hp_eq5
        have hq7 : 7 ≤ q := prime_factor_ge_seven_of_ne_three_five hodd hq_mem hq_ne3 hq_eq5
        have hs7 : 7 ≤ s := prime_factor_ge_seven_of_ne_three_five hodd hs_mem hs_ne3
          (by intro h; exact hrs (by omega))
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          sigma_four_ge5_ge7_ge7_ge7_lt hr hp hq hs hpr.symm hqr.symm hrs hpq hps hqs
            hr5 hp7 hq7 hs7
            (n.factorization r) (n.factorization p) (n.factorization q) (n.factorization s)
      · by_cases hs_eq5 : s = 5
        · have hp7 : 7 ≤ p := prime_factor_ge_seven_of_ne_three_five hodd hp_mem hp_ne3 hp_eq5
          have hq7 : 7 ≤ q := prime_factor_ge_seven_of_ne_three_five hodd hq_mem hq_ne3 hq_eq5
          have hr7 : 7 ≤ r := prime_factor_ge_seven_of_ne_three_five hodd hr_mem hr_ne3 hr_eq5
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            sigma_four_ge5_ge7_ge7_ge7_lt hs hp hq hr hps.symm hqs.symm hrs.symm hpq hpr hqr
              hs5 hp7 hq7 hr7
              (n.factorization s) (n.factorization p) (n.factorization q) (n.factorization r)
        · have hp7 : 7 ≤ p := prime_factor_ge_seven_of_ne_three_five hodd hp_mem hp_ne3 hp_eq5
          have hq7 : 7 ≤ q := prime_factor_ge_seven_of_ne_three_five hodd hq_mem hq_ne3 hq_eq5
          have hr7 : 7 ≤ r := prime_factor_ge_seven_of_ne_three_five hodd hr_mem hr_ne3 hr_eq5
          have hs7 : 7 ≤ s := prime_factor_ge_seven_of_ne_three_five hodd hs_mem hs_ne3 hs_eq5
          exact sigma_four_ge7_lt hp hq hr hs hpq hpr hps hqr hqs hrs
            hp7 hq7 hr7 hs7 _ _ _ _

/-- **Any odd weird number with exactly four distinct prime factors is divisible
by `3`.**

This is a genuinely new formal constraint beyond the three-prime exclusion:
the four-prime case, if it exists at all, must start with the smallest odd
prime. -/
theorem odd_weird_four_prime_factors_contains_three {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 4) :
    3 ∈ n.primeFactors := by
  by_contra hno3
  have hn : n ≠ 0 := by exact Nat.ne_of_gt hw.1.1
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hpf⟩ :=
    Finset.card_eq_four.mp hcard
  exact (not_abundant_of_four_primeFactors_without_three hodd hn hpq hpr hps hqr hqs hrs hpf hno3)
    hw.1

/-! ### A six-prime frontier constraint -/

/-- Reindex a product over a finite linearly ordered set by its increasing
order embedding from `Fin k`. -/
private theorem prod_finset_eq_orderEmbOfFin {α M : Type*} [LinearOrder α] [CommMonoid M]
    (S : Finset α) {k : ℕ} (hS : S.card = k) (f : α → M) :
    (∏ x ∈ S, f x) = ∏ i : Fin k, f (S.orderEmbOfFin hS i) := by
  have himage : Finset.image (S.orderEmbOfFin hS) Finset.univ = S :=
    Finset.image_orderEmbOfFin_univ S hS
  calc
    (∏ x ∈ S, f x) = ∏ x ∈ Finset.image (S.orderEmbOfFin hS) Finset.univ, f x := by
      rw [himage]
    _ = ∏ i ∈ (Finset.univ : Finset (Fin k)), f (S.orderEmbOfFin hS i) := by
      rw [Finset.prod_image]
      intro a _ b _ h
      exact (S.orderEmbOfFin hS).injective h
    _ = ∏ i : Fin k, f (S.orderEmbOfFin hS i) := by simp

/-- Expand a product over `Fin 6` without invoking the simplifier at each use. -/
private theorem prod_fin_six {M : Type*} [CommMonoid M] (f : Fin 6 → M) :
    (∏ i : Fin 6, f i) =
      f ⟨0, by decide⟩ * f ⟨1, by decide⟩ * f ⟨2, by decide⟩ *
        f ⟨3, by decide⟩ * f ⟨4, by decide⟩ * f ⟨5, by decide⟩ := by
  norm_num [Fin.prod_univ_succ, Fin.succ, mul_assoc]

/-- The numerical heart of the six-prime divisor-sum bound. -/
private theorem six_scaled_ratio_lt (s0 s1 s2 s3 s4 s5 p0 p1 p2 p3 p4 p5 : ℕ)
    (h : (4 * s0) * (6 * s1) * (10 * s2) * (12 * s3) * (16 * s4) *
          (18 * s5) <
        (5 * p0) * (7 * p1) * (11 * p2) * (13 * p3) * (17 * p4) *
          (19 * p5)) :
    s0 * s1 * s2 * s3 * s4 * s5 < 2 * (p0 * p1 * p2 * p3 * p4 * p5) := by
  have hscaled :
      829440 * (s0 * s1 * s2 * s3 * s4 * s5) <
        1616615 * (p0 * p1 * p2 * p3 * p4 * p5) := by
    nlinarith [h]
  have hceil :
      1616615 * (p0 * p1 * p2 * p3 * p4 * p5) ≤
        829440 * (2 * (p0 * p1 * p2 * p3 * p4 * p5)) := by
    nlinarith [show 0 ≤ p0 * p1 * p2 * p3 * p4 * p5 from Nat.zero_le _]
  have hscaled' :
      829440 * (s0 * s1 * s2 * s3 * s4 * s5) <
        829440 * (2 * (p0 * p1 * p2 * p3 * p4 * p5)) :=
    lt_of_lt_of_le hscaled hceil
  exact (Nat.mul_lt_mul_left (by norm_num : 0 < 829440)).mp hscaled'

/-- The exact squarefree ratio bound for six ordered odd prime factors with
lower bounds `3,7,11,13,17,19`. -/
private theorem squarefree_six_ratio_lt (p0 p1 p2 p3 p4 p5 : ℕ)
    (hp0 : 3 ≤ p0) (hp1 : 7 ≤ p1) (hp2 : 11 ≤ p2)
    (hp3 : 13 ≤ p3) (hp4 : 17 ≤ p4) (hp5 : 19 ≤ p5) :
    (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) <
      2 * (p0 * p1 * p2 * p3 * p4 * p5) := by
  let A0 := p0 + 1
  let A1 := p1 + 1
  let A2 := p2 + 1
  let A3 := p3 + 1
  let A4 := p4 + 1
  let A5 := p5 + 1
  let B0 := p0
  let B1 := p1
  let B2 := p2
  let B3 := p3
  let B4 := p4
  let B5 := p5
  have h0 : 3 * A0 ≤ 4 * B0 := by dsimp [A0, B0]; nlinarith
  have h1 : 7 * A1 ≤ 8 * B1 := by dsimp [A1, B1]; nlinarith
  have h2 : 11 * A2 ≤ 12 * B2 := by dsimp [A2, B2]; nlinarith
  have h3 : 13 * A3 ≤ 14 * B3 := by dsimp [A3, B3]; nlinarith
  have h4 : 17 * A4 ≤ 18 * B4 := by dsimp [A4, B4]; nlinarith
  have h5 : 19 * A5 ≤ 20 * B5 := by dsimp [A5, B5]; nlinarith
  have hchain :
      (3 * A0) * (7 * A1) * (11 * A2) * (13 * A3) * (17 * A4) * (19 * A5) ≤
        (4 * B0) * (8 * B1) * (12 * B2) * (14 * B3) * (18 * B4) * (20 * B5) := by
    gcongr
  have hscaled : 969969 * (A0 * A1 * A2 * A3 * A4 * A5) ≤
      1935360 * (B0 * B1 * B2 * B3 * B4 * B5) := by
    calc
      969969 * (A0 * A1 * A2 * A3 * A4 * A5)
          = (3 * A0) * (7 * A1) * (11 * A2) * (13 * A3) * (17 * A4) * (19 * A5) := by
            ring
      _ ≤ (4 * B0) * (8 * B1) * (12 * B2) * (14 * B3) * (18 * B4) * (20 * B5) :=
        hchain
      _ = 1935360 * (B0 * B1 * B2 * B3 * B4 * B5) := by ring
  have hBpos : 0 < B0 * B1 * B2 * B3 * B4 * B5 := by
    dsimp [B0, B1, B2, B3, B4, B5]
    positivity
  have hceil : 1935360 * (B0 * B1 * B2 * B3 * B4 * B5) <
      969969 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) := by
    have hconst : 1935360 < 969969 * 2 := by norm_num
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_right hconst hBpos
  have hscaled' : 969969 * (A0 * A1 * A2 * A3 * A4 * A5) <
      969969 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) :=
    lt_of_le_of_lt hscaled hceil
  have hlt : A0 * A1 * A2 * A3 * A4 * A5 <
      2 * (B0 * B1 * B2 * B3 * B4 * B5) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 969969)).mp hscaled'
  simpa [A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5] using hlt

/-- The exact squarefree ratio bound for lower bounds `3,5,17,19,23,29`. -/
private theorem squarefree_six_ratio_3_5_17_19_23_29_lt (p0 p1 p2 p3 p4 p5 : ℕ)
    (hp0 : 3 ≤ p0) (hp1 : 5 ≤ p1) (hp2 : 17 ≤ p2)
    (hp3 : 19 ≤ p3) (hp4 : 23 ≤ p4) (hp5 : 29 ≤ p5) :
    (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) <
      2 * (p0 * p1 * p2 * p3 * p4 * p5) := by
  let A0 := p0 + 1
  let A1 := p1 + 1
  let A2 := p2 + 1
  let A3 := p3 + 1
  let A4 := p4 + 1
  let A5 := p5 + 1
  let B0 := p0
  let B1 := p1
  let B2 := p2
  let B3 := p3
  let B4 := p4
  let B5 := p5
  have h0 : 3 * A0 ≤ 4 * B0 := by dsimp [A0, B0]; nlinarith
  have h1 : 5 * A1 ≤ 6 * B1 := by dsimp [A1, B1]; nlinarith
  have h2 : 17 * A2 ≤ 18 * B2 := by dsimp [A2, B2]; nlinarith
  have h3 : 19 * A3 ≤ 20 * B3 := by dsimp [A3, B3]; nlinarith
  have h4 : 23 * A4 ≤ 24 * B4 := by dsimp [A4, B4]; nlinarith
  have h5 : 29 * A5 ≤ 30 * B5 := by dsimp [A5, B5]; nlinarith
  have hchain :
      (3 * A0) * (5 * A1) * (17 * A2) * (19 * A3) * (23 * A4) * (29 * A5) ≤
        (4 * B0) * (6 * B1) * (18 * B2) * (20 * B3) * (24 * B4) * (30 * B5) := by
    gcongr
  have hscaled : 3231615 * (A0 * A1 * A2 * A3 * A4 * A5) ≤
      6220800 * (B0 * B1 * B2 * B3 * B4 * B5) := by
    calc
      3231615 * (A0 * A1 * A2 * A3 * A4 * A5)
          = (3 * A0) * (5 * A1) * (17 * A2) * (19 * A3) * (23 * A4) * (29 * A5) := by
            ring
      _ ≤ (4 * B0) * (6 * B1) * (18 * B2) * (20 * B3) * (24 * B4) * (30 * B5) :=
        hchain
      _ = 6220800 * (B0 * B1 * B2 * B3 * B4 * B5) := by ring
  have hBpos : 0 < B0 * B1 * B2 * B3 * B4 * B5 := by
    dsimp [B0, B1, B2, B3, B4, B5]
    positivity
  have hceil : 6220800 * (B0 * B1 * B2 * B3 * B4 * B5) <
      3231615 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) := by
    have hconst : 6220800 < 3231615 * 2 := by norm_num
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_right hconst hBpos
  have hscaled' : 3231615 * (A0 * A1 * A2 * A3 * A4 * A5) <
      3231615 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) :=
    lt_of_le_of_lt hscaled hceil
  have hlt : A0 * A1 * A2 * A3 * A4 * A5 <
      2 * (B0 * B1 * B2 * B3 * B4 * B5) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 3231615)).mp hscaled'
  simpa [A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5] using hlt

/-- Six distinct odd prime factors with no factor `3` force non-abundance.

The ordered prime factors are at least `5, 7, 11, 13, 17, 19`; hence
`σ(n)/n` is bounded by
`(5/4)(7/6)(11/10)(13/12)(17/16)(19/18) < 2`. -/
private theorem not_abundant_of_six_primeFactors_without_three {n : ℕ}
    (hodd : ¬Even n) (hn : n ≠ 0) (hcard : n.primeFactors.card = 6)
    (hno3 : 3 ∉ n.primeFactors) : ¬Abundant n := by
  let S := n.primeFactors
  let e := S.orderEmbOfFin hcard
  let p0 := e ⟨0, by decide⟩
  let p1 := e ⟨1, by decide⟩
  let p2 := e ⟨2, by decide⟩
  let p3 := e ⟨3, by decide⟩
  let p4 := e ⟨4, by decide⟩
  let p5 := e ⟨5, by decide⟩
  let P0 := p0 ^ n.factorization p0
  let P1 := p1 ^ n.factorization p1
  let P2 := p2 ^ n.factorization p2
  let P3 := p3 ^ n.factorization p3
  let P4 := p4 ^ n.factorization p4
  let P5 := p5 ^ n.factorization p5
  let σ0 := P0.divisors.sum id
  let σ1 := P1.divisors.sum id
  let σ2 := P2.divisors.sum id
  let σ3 := P3.divisors.sum id
  let σ4 := P4.divisors.sum id
  let σ5 := P5.divisors.sum id
  have hp0_mem : p0 ∈ n.primeFactors := by
    dsimp [p0, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨0, by decide⟩
  have hp1_mem : p1 ∈ n.primeFactors := by
    dsimp [p1, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨1, by decide⟩
  have hp2_mem : p2 ∈ n.primeFactors := by
    dsimp [p2, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨2, by decide⟩
  have hp3_mem : p3 ∈ n.primeFactors := by
    dsimp [p3, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨3, by decide⟩
  have hp4_mem : p4 ∈ n.primeFactors := by
    dsimp [p4, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨4, by decide⟩
  have hp5_mem : p5 ∈ n.primeFactors := by
    dsimp [p5, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨5, by decide⟩
  have hp0 : Nat.Prime p0 := Nat.prime_of_mem_primeFactors hp0_mem
  have hp1 : Nat.Prime p1 := Nat.prime_of_mem_primeFactors hp1_mem
  have hp2 : Nat.Prime p2 := Nat.prime_of_mem_primeFactors hp2_mem
  have hp3 : Nat.Prime p3 := Nat.prime_of_mem_primeFactors hp3_mem
  have hp4 : Nat.Prime p4 := Nat.prime_of_mem_primeFactors hp4_mem
  have hp5 : Nat.Prime p5 := Nat.prime_of_mem_primeFactors hp5_mem
  have hp01 : p0 < p1 := by
    dsimp [p0, p1, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp12 : p1 < p2 := by
    dsimp [p1, p2, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp23 : p2 < p3 := by
    dsimp [p2, p3, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp34 : p3 < p4 := by
    dsimp [p3, p4, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp45 : p4 < p5 := by
    dsimp [p4, p5, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp0_ne3 : p0 ≠ 3 := by intro h; exact hno3 (h ▸ hp0_mem)
  have hp1_ne3 : p1 ≠ 3 := by intro h; exact hno3 (h ▸ hp1_mem)
  have hp2_ne3 : p2 ≠ 3 := by intro h; exact hno3 (h ▸ hp2_mem)
  have hp3_ne3 : p3 ≠ 3 := by intro h; exact hno3 (h ▸ hp3_mem)
  have hp4_ne3 : p4 ≠ 3 := by intro h; exact hno3 (h ▸ hp4_mem)
  have hp5_ne3 : p5 ≠ 3 := by intro h; exact hno3 (h ▸ hp5_mem)
  have hp0_ge5 : 5 ≤ p0 := prime_factor_ge_five_of_ne_three hodd hp0_mem hp0_ne3
  have hp1_ne5 : p1 ≠ 5 := by intro h; omega
  have hp1_ge7 : 7 ≤ p1 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp1_mem hp1_ne3 hp1_ne5
  have hp2_ne5 : p2 ≠ 5 := by intro h; omega
  have hp2_ge7 : 7 ≤ p2 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp2_mem hp2_ne3 hp2_ne5
  have hp2_ne7 : p2 ≠ 7 := by intro h; omega
  have hp2_ge11 : 11 ≤ p2 := prime_ge_eleven_of_ge_seven_ne_seven hp2 hp2_ge7 hp2_ne7
  have hp3_ne5 : p3 ≠ 5 := by intro h; omega
  have hp3_ge7 : 7 ≤ p3 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp3_mem hp3_ne3 hp3_ne5
  have hp3_ne7 : p3 ≠ 7 := by intro h; omega
  have hp3_ge11 : 11 ≤ p3 := prime_ge_eleven_of_ge_seven_ne_seven hp3 hp3_ge7 hp3_ne7
  have hp3_ne11 : p3 ≠ 11 := by intro h; omega
  have hp3_ge13 : 13 ≤ p3 :=
    prime_ge_thirteen_of_ge_eleven_ne_eleven hp3 hp3_ge11 hp3_ne11
  have hp4_ne5 : p4 ≠ 5 := by intro h; omega
  have hp4_ge7 : 7 ≤ p4 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp4_mem hp4_ne3 hp4_ne5
  have hp4_ne7 : p4 ≠ 7 := by intro h; omega
  have hp4_ge11 : 11 ≤ p4 := prime_ge_eleven_of_ge_seven_ne_seven hp4 hp4_ge7 hp4_ne7
  have hp4_ne11 : p4 ≠ 11 := by intro h; omega
  have hp4_ge13 : 13 ≤ p4 :=
    prime_ge_thirteen_of_ge_eleven_ne_eleven hp4 hp4_ge11 hp4_ne11
  have hp4_ne13 : p4 ≠ 13 := by intro h; omega
  have hp4_ge17 : 17 ≤ p4 :=
    prime_ge_seventeen_of_ge_thirteen_ne_thirteen hp4 hp4_ge13 hp4_ne13
  have hp5_ne5 : p5 ≠ 5 := by intro h; omega
  have hp5_ge7 : 7 ≤ p5 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp5_mem hp5_ne3 hp5_ne5
  have hp5_ne7 : p5 ≠ 7 := by intro h; omega
  have hp5_ge11 : 11 ≤ p5 := prime_ge_eleven_of_ge_seven_ne_seven hp5 hp5_ge7 hp5_ne7
  have hp5_ne11 : p5 ≠ 11 := by intro h; omega
  have hp5_ge13 : 13 ≤ p5 :=
    prime_ge_thirteen_of_ge_eleven_ne_eleven hp5 hp5_ge11 hp5_ne11
  have hp5_ne13 : p5 ≠ 13 := by intro h; omega
  have hp5_ge17 : 17 ≤ p5 :=
    prime_ge_seventeen_of_ge_thirteen_ne_thirteen hp5 hp5_ge13 hp5_ne13
  have hp5_ne17 : p5 ≠ 17 := by intro h; omega
  have hp5_ge19 : 19 ≤ p5 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp5 hp5_ge17 hp5_ne17
  have hsum_prod : n.divisors.sum id =
      ∏ i : Fin 6, ((e i) ^ n.factorization (e i)).divisors.sum id := by
    have hprod : n.divisors.sum id =
        ∏ p ∈ S, (p ^ n.factorization p).divisors.sum id := by
      dsimp [S]
      change (∑ d ∈ n.divisors, d) =
        ∏ p ∈ n.primeFactors, (p ^ n.factorization p).divisors.sum id
      rw [Nat.sum_divisors hn]
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]
      simp
    calc
      n.divisors.sum id = ∏ p ∈ S, (p ^ n.factorization p).divisors.sum id := hprod
      _ = ∏ i : Fin 6, ((e i) ^ n.factorization (e i)).divisors.sum id := by
        simpa [e] using
          prod_finset_eq_orderEmbOfFin S hcard
            (fun p => (p ^ n.factorization p).divisors.sum id)
  have hn_prod : n = ∏ i : Fin 6, (e i) ^ n.factorization (e i) := by
    have hprod : n = ∏ p ∈ S, p ^ n.factorization p := by
      dsimp [S]
      have hfact := Nat.factorization_prod_pow_eq_self hn
      conv_lhs => rw [← hfact]
      simp only [Finsupp.prod, Nat.support_factorization]
    calc
      n = ∏ p ∈ S, p ^ n.factorization p := hprod
      _ = ∏ i : Fin 6, (e i) ^ n.factorization (e i) := by
        simpa [e] using
          prod_finset_eq_orderEmbOfFin S hcard (fun p => p ^ n.factorization p)
  have hb0 : 4 * σ0 < 5 * P0 := by
    simpa [σ0, P0] using sigma_bound_ge5 hp0 hp0_ge5 (n.factorization p0)
  have hb1 : 6 * σ1 < 7 * P1 := by
    simpa [σ1, P1] using sigma_bound_ge7 hp1 hp1_ge7 (n.factorization p1)
  have hb2 : 10 * σ2 < 11 * P2 := by
    simpa [σ2, P2] using sigma_bound_ge11 hp2 hp2_ge11 (n.factorization p2)
  have hb3 : 12 * σ3 < 13 * P3 := by
    simpa [σ3, P3] using sigma_bound_ge13 hp3 hp3_ge13 (n.factorization p3)
  have hb4 : 16 * σ4 < 17 * P4 := by
    simpa [σ4, P4] using sigma_bound_ge17 hp4 hp4_ge17 (n.factorization p4)
  have hb5 : 18 * σ5 < 19 * P5 := by
    simpa [σ5, P5] using sigma_bound_ge19 hp5 hp5_ge19 (n.factorization p5)
  let A0 := 4 * σ0
  let A1 := 6 * σ1
  let A2 := 10 * σ2
  let A3 := 12 * σ3
  let A4 := 16 * σ4
  let A5 := 18 * σ5
  let B0 := 5 * P0
  let B1 := 7 * P1
  let B2 := 11 * P2
  let B3 := 13 * P3
  let B4 := 17 * P4
  let B5 := 19 * P5
  have hb0' : A0 < B0 := by simpa [A0, B0] using hb0
  have hb1' : A1 < B1 := by simpa [A1, B1] using hb1
  have hb2' : A2 < B2 := by simpa [A2, B2] using hb2
  have hb3' : A3 < B3 := by simpa [A3, B3] using hb3
  have hb4' : A4 < B4 := by simpa [A4, B4] using hb4
  have hb5' : A5 < B5 := by simpa [A5, B5] using hb5
  have hP0_pos : 0 < P0 := by dsimp [P0]; exact pow_pos hp0.pos _
  have hP1_pos : 0 < P1 := by dsimp [P1]; exact pow_pos hp1.pos _
  have hP2_pos : 0 < P2 := by dsimp [P2]; exact pow_pos hp2.pos _
  have hP3_pos : 0 < P3 := by dsimp [P3]; exact pow_pos hp3.pos _
  have hP4_pos : 0 < P4 := by dsimp [P4]; exact pow_pos hp4.pos _
  have hP5_pos : 0 < P5 := by dsimp [P5]; exact pow_pos hp5.pos _
  have hσ0_pos : 0 < σ0 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσ1_pos : 0 < σ1 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσ2_pos : 0 < σ2 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσ3_pos : 0 < σ3 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hσ4_pos : 0 < σ4 := Finset.sum_pos (fun x hx => Nat.pos_of_mem_divisors hx)
    ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  have hA0_pos : 0 < A0 := by dsimp [A0]; exact Nat.mul_pos (by norm_num) hσ0_pos
  have hA1_pos : 0 < A1 := by dsimp [A1]; exact Nat.mul_pos (by norm_num) hσ1_pos
  have hA2_pos : 0 < A2 := by dsimp [A2]; exact Nat.mul_pos (by norm_num) hσ2_pos
  have hA3_pos : 0 < A3 := by dsimp [A3]; exact Nat.mul_pos (by norm_num) hσ3_pos
  have hA4_pos : 0 < A4 := by dsimp [A4]; exact Nat.mul_pos (by norm_num) hσ4_pos
  have hB1_pos : 0 < B1 := by dsimp [B1]; exact Nat.mul_pos (by norm_num) hP1_pos
  have hB2_pos : 0 < B2 := by dsimp [B2]; exact Nat.mul_pos (by norm_num) hP2_pos
  have hB3_pos : 0 < B3 := by dsimp [B3]; exact Nat.mul_pos (by norm_num) hP3_pos
  have hB4_pos : 0 < B4 := by dsimp [B4]; exact Nat.mul_pos (by norm_num) hP4_pos
  have hB5_pos : 0 < B5 := by dsimp [B5]; exact Nat.mul_pos (by norm_num) hP5_pos
  have hA01234_pos : 0 < A0 * A1 * A2 * A3 * A4 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA0_pos hA1_pos) hA2_pos)
      hA3_pos) hA4_pos
  have hA0123_pos : 0 < A0 * A1 * A2 * A3 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA0_pos hA1_pos) hA2_pos) hA3_pos
  have hA012_pos : 0 < A0 * A1 * A2 :=
    Nat.mul_pos (Nat.mul_pos hA0_pos hA1_pos) hA2_pos
  have hA01_pos : 0 < A0 * A1 := Nat.mul_pos hA0_pos hA1_pos
  have hB45_pos : 0 < B4 * B5 := Nat.mul_pos hB4_pos hB5_pos
  have hB345_pos : 0 < B3 * B4 * B5 := Nat.mul_pos (Nat.mul_pos hB3_pos hB4_pos) hB5_pos
  have hB2345_pos : 0 < B2 * B3 * B4 * B5 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hB2_pos hB3_pos) hB4_pos) hB5_pos
  have hB12345_pos : 0 < B1 * B2 * B3 * B4 * B5 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hB1_pos hB2_pos) hB3_pos)
      hB4_pos) hB5_pos
  have h1 : (A0 * A1 * A2 * A3 * A4) * A5 <
      (A0 * A1 * A2 * A3 * A4) * B5 :=
    mul_lt_mul_of_pos_left hb5' hA01234_pos
  have h2 : (A0 * A1 * A2 * A3) * (A4 * B5) <
      (A0 * A1 * A2 * A3) * (B4 * B5) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hb4' hB5_pos) hA0123_pos
  have h3 : (A0 * A1 * A2) * (A3 * B4 * B5) <
      (A0 * A1 * A2) * (B3 * B4 * B5) := by
    have hbase : A3 * (B4 * B5) < B3 * (B4 * B5) :=
      mul_lt_mul_of_pos_right hb3' hB45_pos
    simpa [mul_assoc] using mul_lt_mul_of_pos_left hbase hA012_pos
  have h4 : (A0 * A1) * (A2 * B3 * B4 * B5) <
      (A0 * A1) * (B2 * B3 * B4 * B5) := by
    have hbase : A2 * (B3 * B4 * B5) < B2 * (B3 * B4 * B5) :=
      mul_lt_mul_of_pos_right hb2' hB345_pos
    simpa [mul_assoc] using mul_lt_mul_of_pos_left hbase hA01_pos
  have h5 : A0 * (A1 * B2 * B3 * B4 * B5) <
      A0 * (B1 * B2 * B3 * B4 * B5) := by
    have hbase : A1 * (B2 * B3 * B4 * B5) < B1 * (B2 * B3 * B4 * B5) :=
      mul_lt_mul_of_pos_right hb1' hB2345_pos
    simpa [mul_assoc] using mul_lt_mul_of_pos_left hbase hA0_pos
  have h6 : A0 * (B1 * B2 * B3 * B4 * B5) <
      B0 * (B1 * B2 * B3 * B4 * B5) :=
    mul_lt_mul_of_pos_right hb0' hB12345_pos
  have hscaled : A0 * A1 * A2 * A3 * A4 * A5 < B0 * B1 * B2 * B3 * B4 * B5 := by
    calc
      A0 * A1 * A2 * A3 * A4 * A5 = (A0 * A1 * A2 * A3 * A4) * A5 := by ring
      _ < (A0 * A1 * A2 * A3 * A4) * B5 := h1
      _ = (A0 * A1 * A2 * A3) * (A4 * B5) := by ring
      _ < (A0 * A1 * A2 * A3) * (B4 * B5) := h2
      _ = (A0 * A1 * A2) * (A3 * B4 * B5) := by ring
      _ < (A0 * A1 * A2) * (B3 * B4 * B5) := h3
      _ = (A0 * A1) * (A2 * B3 * B4 * B5) := by ring
      _ < (A0 * A1) * (B2 * B3 * B4 * B5) := h4
      _ = A0 * (A1 * B2 * B3 * B4 * B5) := by ring
      _ < A0 * (B1 * B2 * B3 * B4 * B5) := h5
      _ < B0 * (B1 * B2 * B3 * B4 * B5) := h6
      _ = B0 * B1 * B2 * B3 * B4 * B5 := by ring
  have hlt : σ0 * σ1 * σ2 * σ3 * σ4 * σ5 <
      2 * (P0 * P1 * P2 * P3 * P4 * P5) := by
    dsimp [A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5] at hscaled
    exact six_scaled_ratio_lt σ0 σ1 σ2 σ3 σ4 σ5 P0 P1 P2 P3 P4 P5 hscaled
  apply not_abundant_of_sigma_lt
  rw [hsum_prod]
  conv_rhs => rw [hn_prod]
  simpa [Fin.prod_univ_succ, Fin.succ, p0, p1, p2, p3, p4, p5,
    P0, P1, P2, P3, P4, P5, σ0, σ1, σ2, σ3, σ4, σ5, mul_assoc] using hlt

/-- **Any odd weird number with exactly six distinct prime factors is divisible
by `3`.**

This is a structural constraint on the first case not ruled out by the known
Liddy--Riedl lower bound. It follows from a sharp enough divisor-sum ceiling:
if `3` is absent, the six distinct odd prime factors are at least
`5,7,11,13,17,19`, whose prime-power abundancy ceilings multiply to less than
`2`. -/
theorem odd_weird_six_prime_factors_contains_three {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6) :
    3 ∈ n.primeFactors := by
  by_contra hno3
  have hn : n ≠ 0 := by exact Nat.ne_of_gt hw.1.1
  exact (not_abundant_of_six_primeFactors_without_three hodd hn hcard hno3) hw.1

/-- Squarefree six-prime odd numbers without a factor `5` are not abundant.

The sorted prime factors are at least `3,7,11,13,17,19`; in the squarefree
case the abundancy index is exactly the product of `(p+1)/p`, and this product
is still below `2`. -/
private theorem not_abundant_of_squarefree_six_primeFactors_without_five {n : ℕ}
    (hodd : ¬Even n) (hn : n ≠ 0) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) (hno5 : 5 ∉ n.primeFactors) : ¬Abundant n := by
  let S := n.primeFactors
  let e := S.orderEmbOfFin hcard
  let p0 := e ⟨0, by decide⟩
  let p1 := e ⟨1, by decide⟩
  let p2 := e ⟨2, by decide⟩
  let p3 := e ⟨3, by decide⟩
  let p4 := e ⟨4, by decide⟩
  let p5 := e ⟨5, by decide⟩
  have hp0_mem : p0 ∈ n.primeFactors := by
    dsimp [p0, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨0, by decide⟩
  have hp1_mem : p1 ∈ n.primeFactors := by
    dsimp [p1, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨1, by decide⟩
  have hp2_mem : p2 ∈ n.primeFactors := by
    dsimp [p2, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨2, by decide⟩
  have hp3_mem : p3 ∈ n.primeFactors := by
    dsimp [p3, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨3, by decide⟩
  have hp4_mem : p4 ∈ n.primeFactors := by
    dsimp [p4, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨4, by decide⟩
  have hp5_mem : p5 ∈ n.primeFactors := by
    dsimp [p5, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨5, by decide⟩
  have hp0 : Nat.Prime p0 := Nat.prime_of_mem_primeFactors hp0_mem
  have hp1 : Nat.Prime p1 := Nat.prime_of_mem_primeFactors hp1_mem
  have hp2 : Nat.Prime p2 := Nat.prime_of_mem_primeFactors hp2_mem
  have hp3 : Nat.Prime p3 := Nat.prime_of_mem_primeFactors hp3_mem
  have hp4 : Nat.Prime p4 := Nat.prime_of_mem_primeFactors hp4_mem
  have hp5 : Nat.Prime p5 := Nat.prime_of_mem_primeFactors hp5_mem
  have hp01 : p0 < p1 := by
    dsimp [p0, p1, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp12 : p1 < p2 := by
    dsimp [p1, p2, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp23 : p2 < p3 := by
    dsimp [p2, p3, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp34 : p3 < p4 := by
    dsimp [p3, p4, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp45 : p4 < p5 := by
    dsimp [p4, p5, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp0_ge3 : 3 ≤ p0 := prime_factor_ge_three_of_odd hodd hp0_mem
  have hp1_ne3 : p1 ≠ 3 := by intro h; omega
  have hp1_ne5 : p1 ≠ 5 := by intro h; exact hno5 (h ▸ hp1_mem)
  have hp1_ge7 : 7 ≤ p1 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp1_mem hp1_ne3 hp1_ne5
  have hp2_ne3 : p2 ≠ 3 := by intro h; omega
  have hp2_ne5 : p2 ≠ 5 := by intro h; exact hno5 (h ▸ hp2_mem)
  have hp2_ge7 : 7 ≤ p2 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp2_mem hp2_ne3 hp2_ne5
  have hp2_ne7 : p2 ≠ 7 := by intro h; omega
  have hp2_ge11 : 11 ≤ p2 := prime_ge_eleven_of_ge_seven_ne_seven hp2 hp2_ge7 hp2_ne7
  have hp3_ne3 : p3 ≠ 3 := by intro h; omega
  have hp3_ne5 : p3 ≠ 5 := by intro h; exact hno5 (h ▸ hp3_mem)
  have hp3_ge7 : 7 ≤ p3 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp3_mem hp3_ne3 hp3_ne5
  have hp3_ne7 : p3 ≠ 7 := by intro h; omega
  have hp3_ge11 : 11 ≤ p3 := prime_ge_eleven_of_ge_seven_ne_seven hp3 hp3_ge7 hp3_ne7
  have hp3_ne11 : p3 ≠ 11 := by intro h; omega
  have hp3_ge13 : 13 ≤ p3 :=
    prime_ge_thirteen_of_ge_eleven_ne_eleven hp3 hp3_ge11 hp3_ne11
  have hp4_ne3 : p4 ≠ 3 := by intro h; omega
  have hp4_ne5 : p4 ≠ 5 := by intro h; exact hno5 (h ▸ hp4_mem)
  have hp4_ge7 : 7 ≤ p4 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp4_mem hp4_ne3 hp4_ne5
  have hp4_ne7 : p4 ≠ 7 := by intro h; omega
  have hp4_ge11 : 11 ≤ p4 := prime_ge_eleven_of_ge_seven_ne_seven hp4 hp4_ge7 hp4_ne7
  have hp4_ne11 : p4 ≠ 11 := by intro h; omega
  have hp4_ge13 : 13 ≤ p4 :=
    prime_ge_thirteen_of_ge_eleven_ne_eleven hp4 hp4_ge11 hp4_ne11
  have hp4_ne13 : p4 ≠ 13 := by intro h; omega
  have hp4_ge17 : 17 ≤ p4 :=
    prime_ge_seventeen_of_ge_thirteen_ne_thirteen hp4 hp4_ge13 hp4_ne13
  have hp5_ne3 : p5 ≠ 3 := by intro h; omega
  have hp5_ne5 : p5 ≠ 5 := by intro h; exact hno5 (h ▸ hp5_mem)
  have hp5_ge7 : 7 ≤ p5 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp5_mem hp5_ne3 hp5_ne5
  have hp5_ne7 : p5 ≠ 7 := by intro h; omega
  have hp5_ge11 : 11 ≤ p5 := prime_ge_eleven_of_ge_seven_ne_seven hp5 hp5_ge7 hp5_ne7
  have hp5_ne11 : p5 ≠ 11 := by intro h; omega
  have hp5_ge13 : 13 ≤ p5 :=
    prime_ge_thirteen_of_ge_eleven_ne_eleven hp5 hp5_ge11 hp5_ne11
  have hp5_ne13 : p5 ≠ 13 := by intro h; omega
  have hp5_ge17 : 17 ≤ p5 :=
    prime_ge_seventeen_of_ge_thirteen_ne_thirteen hp5 hp5_ge13 hp5_ne13
  have hp5_ne17 : p5 ≠ 17 := by intro h; omega
  have hp5_ge19 : 19 ≤ p5 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp5 hp5_ge17 hp5_ne17
  have hf0 : n.factorization p0 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp0 (Nat.dvd_of_mem_primeFactors hp0_mem)
  have hf1 : n.factorization p1 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp1 (Nat.dvd_of_mem_primeFactors hp1_mem)
  have hf2 : n.factorization p2 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp2 (Nat.dvd_of_mem_primeFactors hp2_mem)
  have hf3 : n.factorization p3 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp3 (Nat.dvd_of_mem_primeFactors hp3_mem)
  have hf4 : n.factorization p4 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp4 (Nat.dvd_of_mem_primeFactors hp4_mem)
  have hf5 : n.factorization p5 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp5 (Nat.dvd_of_mem_primeFactors hp5_mem)
  have hsum_ordered : n.divisors.sum id =
      ∏ i : Fin 6, ((e i) ^ n.factorization (e i)).divisors.sum id := by
    have hprod : n.divisors.sum id =
        ∏ p ∈ S, (p ^ n.factorization p).divisors.sum id := by
      dsimp [S]
      change (∑ d ∈ n.divisors, d) =
        ∏ p ∈ n.primeFactors, (p ^ n.factorization p).divisors.sum id
      rw [Nat.sum_divisors hn]
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]
      simp
    calc
      n.divisors.sum id = ∏ p ∈ S, (p ^ n.factorization p).divisors.sum id := hprod
      _ = ∏ i : Fin 6, ((e i) ^ n.factorization (e i)).divisors.sum id := by
        simpa [e] using
          prod_finset_eq_orderEmbOfFin S hcard
            (fun p => (p ^ n.factorization p).divisors.sum id)
  have hn_ordered : n = ∏ i : Fin 6, (e i) ^ n.factorization (e i) := by
    have hprod : n = ∏ p ∈ S, p ^ n.factorization p := by
      dsimp [S]
      have hfact := Nat.factorization_prod_pow_eq_self hn
      conv_lhs => rw [← hfact]
      simp only [Finsupp.prod, Nat.support_factorization]
    calc
      n = ∏ p ∈ S, p ^ n.factorization p := hprod
      _ = ∏ i : Fin 6, (e i) ^ n.factorization (e i) := by
        simpa [e] using
          prod_finset_eq_orderEmbOfFin S hcard (fun p => p ^ n.factorization p)
  have hsum_squarefree : n.divisors.sum id =
      (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) := by
    have hσ0 : (p0 ^ n.factorization p0).divisors.sum id = p0 + 1 := by
      rw [hf0]
      exact sum_divisors_prime_pow_one hp0
    have hσ1 : (p1 ^ n.factorization p1).divisors.sum id = p1 + 1 := by
      rw [hf1]
      exact sum_divisors_prime_pow_one hp1
    have hσ2 : (p2 ^ n.factorization p2).divisors.sum id = p2 + 1 := by
      rw [hf2]
      exact sum_divisors_prime_pow_one hp2
    have hσ3 : (p3 ^ n.factorization p3).divisors.sum id = p3 + 1 := by
      rw [hf3]
      exact sum_divisors_prime_pow_one hp3
    have hσ4 : (p4 ^ n.factorization p4).divisors.sum id = p4 + 1 := by
      rw [hf4]
      exact sum_divisors_prime_pow_one hp4
    have hσ5 : (p5 ^ n.factorization p5).divisors.sum id = p5 + 1 := by
      rw [hf5]
      exact sum_divisors_prime_pow_one hp5
    rw [hsum_ordered, prod_fin_six]
    change (p0 ^ n.factorization p0).divisors.sum id *
        (p1 ^ n.factorization p1).divisors.sum id *
        (p2 ^ n.factorization p2).divisors.sum id *
        (p3 ^ n.factorization p3).divisors.sum id *
        (p4 ^ n.factorization p4).divisors.sum id *
        (p5 ^ n.factorization p5).divisors.sum id =
      (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1)
    rw [hσ0, hσ1, hσ2, hσ3, hσ4, hσ5]
  have hn_squarefree : n = p0 * p1 * p2 * p3 * p4 * p5 := by
    rw [hn_ordered, prod_fin_six]
    change p0 ^ n.factorization p0 * p1 ^ n.factorization p1 *
        p2 ^ n.factorization p2 * p3 ^ n.factorization p3 *
        p4 ^ n.factorization p4 * p5 ^ n.factorization p5 =
      p0 * p1 * p2 * p3 * p4 * p5
    rw [hf0, hf1, hf2, hf3, hf4, hf5]
    simp [pow_one]
  have hlt :
      (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) <
        2 * (p0 * p1 * p2 * p3 * p4 * p5) :=
    squarefree_six_ratio_lt p0 p1 p2 p3 p4 p5
      hp0_ge3 hp1_ge7 hp2_ge11 hp3_ge13 hp4_ge17 hp5_ge19
  apply not_abundant_of_sigma_lt
  rw [hsum_squarefree, hn_squarefree]
  exact hlt

/-- **A squarefree odd weird number with exactly six distinct prime factors
must be divisible by `5`.**

Combined with `odd_weird_six_prime_factors_contains_three`, this says that the
squarefree six-prime frontier, if it exists, must already contain both `3` and
`5`. -/
theorem odd_weird_squarefree_six_prime_factors_contains_five {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) : 5 ∈ n.primeFactors := by
  by_contra hno5
  have hn : n ≠ 0 := by exact Nat.ne_of_gt hw.1.1
  exact (not_abundant_of_squarefree_six_primeFactors_without_five
    hodd hn hcard hsq hno5) hw.1

/-- Squarefree six-prime odd numbers missing all of `7`, `11`, and `13` are
not abundant.

The ordered prime factors are then at least `3,5,17,19,23,29`, whose
squarefree abundancy product is below `2`. -/
private theorem not_abundant_of_squarefree_six_primeFactors_without_7_11_13 {n : ℕ}
    (hodd : ¬Even n) (hn : n ≠ 0) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) (hno7 : 7 ∉ n.primeFactors) (hno11 : 11 ∉ n.primeFactors)
    (hno13 : 13 ∉ n.primeFactors) : ¬Abundant n := by
  let S := n.primeFactors
  let e := S.orderEmbOfFin hcard
  let p0 := e ⟨0, by decide⟩
  let p1 := e ⟨1, by decide⟩
  let p2 := e ⟨2, by decide⟩
  let p3 := e ⟨3, by decide⟩
  let p4 := e ⟨4, by decide⟩
  let p5 := e ⟨5, by decide⟩
  have hp0_mem : p0 ∈ n.primeFactors := by
    dsimp [p0, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨0, by decide⟩
  have hp1_mem : p1 ∈ n.primeFactors := by
    dsimp [p1, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨1, by decide⟩
  have hp2_mem : p2 ∈ n.primeFactors := by
    dsimp [p2, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨2, by decide⟩
  have hp3_mem : p3 ∈ n.primeFactors := by
    dsimp [p3, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨3, by decide⟩
  have hp4_mem : p4 ∈ n.primeFactors := by
    dsimp [p4, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨4, by decide⟩
  have hp5_mem : p5 ∈ n.primeFactors := by
    dsimp [p5, e, S]
    exact Finset.orderEmbOfFin_mem n.primeFactors hcard ⟨5, by decide⟩
  have hp0 : Nat.Prime p0 := Nat.prime_of_mem_primeFactors hp0_mem
  have hp1 : Nat.Prime p1 := Nat.prime_of_mem_primeFactors hp1_mem
  have hp2 : Nat.Prime p2 := Nat.prime_of_mem_primeFactors hp2_mem
  have hp3 : Nat.Prime p3 := Nat.prime_of_mem_primeFactors hp3_mem
  have hp4 : Nat.Prime p4 := Nat.prime_of_mem_primeFactors hp4_mem
  have hp5 : Nat.Prime p5 := Nat.prime_of_mem_primeFactors hp5_mem
  have hp01 : p0 < p1 := by
    dsimp [p0, p1, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp12 : p1 < p2 := by
    dsimp [p1, p2, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp23 : p2 < p3 := by
    dsimp [p2, p3, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp34 : p3 < p4 := by
    dsimp [p3, p4, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp45 : p4 < p5 := by
    dsimp [p4, p5, e]
    exact (S.orderEmbOfFin hcard).strictMono (by decide)
  have hp0_ge3 : 3 ≤ p0 := prime_factor_ge_three_of_odd hodd hp0_mem
  have hp1_ne3 : p1 ≠ 3 := by intro h; omega
  have hp1_ge5 : 5 ≤ p1 := prime_factor_ge_five_of_ne_three hodd hp1_mem hp1_ne3
  have hp2_ne3 : p2 ≠ 3 := by intro h; omega
  have hp2_ne5 : p2 ≠ 5 := by intro h; omega
  have hp2_ne7 : p2 ≠ 7 := by intro h; exact hno7 (h ▸ hp2_mem)
  have hp2_ne11 : p2 ≠ 11 := by intro h; exact hno11 (h ▸ hp2_mem)
  have hp2_ne13 : p2 ≠ 13 := by intro h; exact hno13 (h ▸ hp2_mem)
  have hp2_ge17 : 17 ≤ p2 :=
    prime_factor_ge_seventeen_of_not_small hodd hp2_mem hp2_ne3 hp2_ne5
      hp2_ne7 hp2_ne11 hp2_ne13
  have hp3_ne3 : p3 ≠ 3 := by intro h; omega
  have hp3_ne5 : p3 ≠ 5 := by intro h; omega
  have hp3_ne7 : p3 ≠ 7 := by intro h; exact hno7 (h ▸ hp3_mem)
  have hp3_ne11 : p3 ≠ 11 := by intro h; exact hno11 (h ▸ hp3_mem)
  have hp3_ne13 : p3 ≠ 13 := by intro h; exact hno13 (h ▸ hp3_mem)
  have hp3_ge17 : 17 ≤ p3 :=
    prime_factor_ge_seventeen_of_not_small hodd hp3_mem hp3_ne3 hp3_ne5
      hp3_ne7 hp3_ne11 hp3_ne13
  have hp3_ne17 : p3 ≠ 17 := by intro h; omega
  have hp3_ge19 : 19 ≤ p3 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp3 hp3_ge17 hp3_ne17
  have hp4_ne3 : p4 ≠ 3 := by intro h; omega
  have hp4_ne5 : p4 ≠ 5 := by intro h; omega
  have hp4_ne7 : p4 ≠ 7 := by intro h; exact hno7 (h ▸ hp4_mem)
  have hp4_ne11 : p4 ≠ 11 := by intro h; exact hno11 (h ▸ hp4_mem)
  have hp4_ne13 : p4 ≠ 13 := by intro h; exact hno13 (h ▸ hp4_mem)
  have hp4_ge17 : 17 ≤ p4 :=
    prime_factor_ge_seventeen_of_not_small hodd hp4_mem hp4_ne3 hp4_ne5
      hp4_ne7 hp4_ne11 hp4_ne13
  have hp4_ne17 : p4 ≠ 17 := by intro h; omega
  have hp4_ge19 : 19 ≤ p4 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp4 hp4_ge17 hp4_ne17
  have hp4_ne19 : p4 ≠ 19 := by intro h; omega
  have hp4_ge23 : 23 ≤ p4 :=
    prime_ge_twentythree_of_ge_nineteen_ne_nineteen hp4 hp4_ge19 hp4_ne19
  have hp5_ne3 : p5 ≠ 3 := by intro h; omega
  have hp5_ne5 : p5 ≠ 5 := by intro h; omega
  have hp5_ne7 : p5 ≠ 7 := by intro h; exact hno7 (h ▸ hp5_mem)
  have hp5_ne11 : p5 ≠ 11 := by intro h; exact hno11 (h ▸ hp5_mem)
  have hp5_ne13 : p5 ≠ 13 := by intro h; exact hno13 (h ▸ hp5_mem)
  have hp5_ge17 : 17 ≤ p5 :=
    prime_factor_ge_seventeen_of_not_small hodd hp5_mem hp5_ne3 hp5_ne5
      hp5_ne7 hp5_ne11 hp5_ne13
  have hp5_ne17 : p5 ≠ 17 := by intro h; omega
  have hp5_ge19 : 19 ≤ p5 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp5 hp5_ge17 hp5_ne17
  have hp5_ne19 : p5 ≠ 19 := by intro h; omega
  have hp5_ge23 : 23 ≤ p5 :=
    prime_ge_twentythree_of_ge_nineteen_ne_nineteen hp5 hp5_ge19 hp5_ne19
  have hp5_ne23 : p5 ≠ 23 := by intro h; omega
  have hp5_ge29 : 29 ≤ p5 :=
    prime_ge_twentynine_of_ge_twentythree_ne_twentythree hp5 hp5_ge23 hp5_ne23
  have hf0 : n.factorization p0 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp0 (Nat.dvd_of_mem_primeFactors hp0_mem)
  have hf1 : n.factorization p1 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp1 (Nat.dvd_of_mem_primeFactors hp1_mem)
  have hf2 : n.factorization p2 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp2 (Nat.dvd_of_mem_primeFactors hp2_mem)
  have hf3 : n.factorization p3 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp3 (Nat.dvd_of_mem_primeFactors hp3_mem)
  have hf4 : n.factorization p4 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp4 (Nat.dvd_of_mem_primeFactors hp4_mem)
  have hf5 : n.factorization p5 = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hp5 (Nat.dvd_of_mem_primeFactors hp5_mem)
  have hsum_ordered : n.divisors.sum id =
      ∏ i : Fin 6, ((e i) ^ n.factorization (e i)).divisors.sum id := by
    have hprod : n.divisors.sum id =
        ∏ p ∈ S, (p ^ n.factorization p).divisors.sum id := by
      dsimp [S]
      change (∑ d ∈ n.divisors, d) =
        ∏ p ∈ n.primeFactors, (p ^ n.factorization p).divisors.sum id
      rw [Nat.sum_divisors hn]
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]
      simp
    calc
      n.divisors.sum id = ∏ p ∈ S, (p ^ n.factorization p).divisors.sum id := hprod
      _ = ∏ i : Fin 6, ((e i) ^ n.factorization (e i)).divisors.sum id := by
        simpa [e] using
          prod_finset_eq_orderEmbOfFin S hcard
            (fun p => (p ^ n.factorization p).divisors.sum id)
  have hn_ordered : n = ∏ i : Fin 6, (e i) ^ n.factorization (e i) := by
    have hprod : n = ∏ p ∈ S, p ^ n.factorization p := by
      dsimp [S]
      have hfact := Nat.factorization_prod_pow_eq_self hn
      conv_lhs => rw [← hfact]
      simp only [Finsupp.prod, Nat.support_factorization]
    calc
      n = ∏ p ∈ S, p ^ n.factorization p := hprod
      _ = ∏ i : Fin 6, (e i) ^ n.factorization (e i) := by
        simpa [e] using
          prod_finset_eq_orderEmbOfFin S hcard (fun p => p ^ n.factorization p)
  have hsum_squarefree : n.divisors.sum id =
      (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) := by
    have hσ0 : (p0 ^ n.factorization p0).divisors.sum id = p0 + 1 := by
      rw [hf0]
      exact sum_divisors_prime_pow_one hp0
    have hσ1 : (p1 ^ n.factorization p1).divisors.sum id = p1 + 1 := by
      rw [hf1]
      exact sum_divisors_prime_pow_one hp1
    have hσ2 : (p2 ^ n.factorization p2).divisors.sum id = p2 + 1 := by
      rw [hf2]
      exact sum_divisors_prime_pow_one hp2
    have hσ3 : (p3 ^ n.factorization p3).divisors.sum id = p3 + 1 := by
      rw [hf3]
      exact sum_divisors_prime_pow_one hp3
    have hσ4 : (p4 ^ n.factorization p4).divisors.sum id = p4 + 1 := by
      rw [hf4]
      exact sum_divisors_prime_pow_one hp4
    have hσ5 : (p5 ^ n.factorization p5).divisors.sum id = p5 + 1 := by
      rw [hf5]
      exact sum_divisors_prime_pow_one hp5
    rw [hsum_ordered, prod_fin_six]
    change (p0 ^ n.factorization p0).divisors.sum id *
        (p1 ^ n.factorization p1).divisors.sum id *
        (p2 ^ n.factorization p2).divisors.sum id *
        (p3 ^ n.factorization p3).divisors.sum id *
        (p4 ^ n.factorization p4).divisors.sum id *
        (p5 ^ n.factorization p5).divisors.sum id =
      (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1)
    rw [hσ0, hσ1, hσ2, hσ3, hσ4, hσ5]
  have hn_squarefree : n = p0 * p1 * p2 * p3 * p4 * p5 := by
    rw [hn_ordered, prod_fin_six]
    change p0 ^ n.factorization p0 * p1 ^ n.factorization p1 *
        p2 ^ n.factorization p2 * p3 ^ n.factorization p3 *
        p4 ^ n.factorization p4 * p5 ^ n.factorization p5 =
      p0 * p1 * p2 * p3 * p4 * p5
    rw [hf0, hf1, hf2, hf3, hf4, hf5]
    simp [pow_one]
  have hlt :
      (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) <
        2 * (p0 * p1 * p2 * p3 * p4 * p5) :=
    squarefree_six_ratio_3_5_17_19_23_29_lt p0 p1 p2 p3 p4 p5
      hp0_ge3 hp1_ge5 hp2_ge17 hp3_ge19 hp4_ge23 hp5_ge29
  apply not_abundant_of_sigma_lt
  rw [hsum_squarefree, hn_squarefree]
  exact hlt

/-- **A squarefree odd weird number with exactly six distinct prime factors
must be divisible by at least one of `7`, `11`, and `13`.**

Together with the preceding two theorems, the squarefree six-prime frontier
must contain `3`, `5`, and at least one of the next three odd primes. -/
theorem odd_weird_squarefree_six_prime_factors_contains_7_or_11_or_13 {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) : 7 ∈ n.primeFactors ∨ 11 ∈ n.primeFactors ∨
      13 ∈ n.primeFactors := by
  by_contra hnone
  push_neg at hnone
  have hn : n ≠ 0 := by exact Nat.ne_of_gt hw.1.1
  exact (not_abundant_of_squarefree_six_primeFactors_without_7_11_13
    hodd hn hcard hsq hnone.1 hnone.2.1 hnone.2.2) hw.1

/-- Squarefree six-prime candidates in the `3,5,7,11` branch reduce to a
finite corridor.

If an odd squarefree weird number has exactly six prime factors and contains
`3,5,7,11`, then its two remaining prime factors can be written as
`384 < r < s`, with

`s * (r - 384) ≤ 384 * (r + 1)`

and in fact `r ≤ 761`. -/
theorem squarefree_six_3_5_7_11_frontier_corridor {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h7 : 7 ∈ n.primeFactors) (h11 : 11 ∈ n.primeFactors) :
    ∃ r s : ℕ,
      Nat.Prime r ∧ Nat.Prime s ∧ 384 < r ∧ r < s ∧
        s * (r - 384) ≤ 384 * (r + 1) ∧ r ≤ 761 ∧ n = 1155 * r * s := by
  let B : Finset ℕ := {3, 5, 7, 11}
  have hBsub : B ⊆ n.primeFactors := by
    intro p hp
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h11
  let R := n.primeFactors \ B
  have hRcard : R.card = 2 := by
    change (n.primeFactors \ B).card = 2
    have hsdiff : (n.primeFactors \ B).card + B.card = n.primeFactors.card :=
      Finset.card_sdiff_add_card_eq_card hBsub
    have hBcard : B.card = 4 := by decide
    rw [hBcard, hcard] at hsdiff
    omega
  obtain ⟨a, b, hab, hR⟩ := Finset.card_eq_two.mp hRcard
  have haR : a ∈ R := by rw [hR]; simp
  have hbR : b ∈ R := by rw [hR]; simp
  have ha_mem : a ∈ n.primeFactors := (Finset.mem_sdiff.mp haR).1
  have hb_mem : b ∈ n.primeFactors := (Finset.mem_sdiff.mp hbR).1
  have ha_notB : a ∉ B := (Finset.mem_sdiff.mp haR).2
  have hb_notB : b ∉ B := (Finset.mem_sdiff.mp hbR).2
  have ha_prime : Nat.Prime a := Nat.prime_of_mem_primeFactors ha_mem
  have hb_prime : Nat.Prime b := Nat.prime_of_mem_primeFactors hb_mem
  have ha_ne3 : a ≠ 3 := by intro h; exact ha_notB (by simp [B, h])
  have ha_ne5 : a ≠ 5 := by intro h; exact ha_notB (by simp [B, h])
  have ha_ne7 : a ≠ 7 := by intro h; exact ha_notB (by simp [B, h])
  have ha_ne11 : a ≠ 11 := by intro h; exact ha_notB (by simp [B, h])
  have hb_ne3 : b ≠ 3 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne5 : b ≠ 5 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne7 : b ≠ 7 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne11 : b ≠ 11 := by intro h; exact hb_notB (by simp [B, h])
  have ha_ge7 : 7 ≤ a := prime_factor_ge_seven_of_ne_three_five hodd ha_mem ha_ne3 ha_ne5
  have hb_ge7 : 7 ≤ b := prime_factor_ge_seven_of_ne_three_five hodd hb_mem hb_ne3 hb_ne5
  have ha_ge11 : 11 ≤ a := prime_ge_eleven_of_ge_seven_ne_seven ha_prime ha_ge7 ha_ne7
  have hb_ge11 : 11 ≤ b := prime_ge_eleven_of_ge_seven_ne_seven hb_prime hb_ge7 hb_ne7
  have ha_ge13 : 13 ≤ a := prime_ge_thirteen_of_ge_eleven_ne_eleven ha_prime ha_ge11 ha_ne11
  have hb_ge13 : 13 ≤ b := prime_ge_thirteen_of_ge_eleven_ne_eleven hb_prime hb_ge11 hb_ne11
  have hasubset : ({3, 5, 7, 11, a} : Finset ℕ) ⊆ n.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h11
    · exact ha_mem
  have hbsubset : ({3, 5, 7, 11, b} : Finset ℕ) ⊆ n.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h11
    · exact hb_mem
  have ha384 : 384 < a := by
    by_contra hle384
    have ha_ne384 : a ≠ 384 := by intro h; subst a; norm_num at ha_prime
    have ha383 : a ≤ 383 := by omega
    exact (not_weird_of_squarefree_primeFactors_contains_3_5_7_11_small_extra
      hsq ha_prime ha_ge13 ha383 hasubset) hw
  have hb384 : 384 < b := by
    by_contra hle384
    have hb_ne384 : b ≠ 384 := by intro h; subst b; norm_num at hb_prime
    have hb383 : b ≤ 383 := by omega
    exact (not_weird_of_squarefree_primeFactors_contains_3_5_7_11_small_extra
      hsq hb_prime hb_ge13 hb383 hbsubset) hw
  have hpf : n.primeFactors = ({3, 5, 7, 11, a, b} : Finset ℕ) := by
    ext p
    constructor
    · intro hp
      by_cases hpB : p ∈ B
      · have hpbase : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
          simpa only [B, Finset.mem_insert, Finset.mem_singleton] using hpB
        rcases hpbase with rfl | rfl | rfl | rfl <;> simp
      · have hpR : p ∈ R := Finset.mem_sdiff.mpr ⟨hp, hpB⟩
        rw [hR] at hpR
        rcases (by simpa using hpR : p = a ∨ p = b) with rfl | rfl <;> simp
    · intro hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h11
      · exact ha_mem
      · exact hb_mem
  have hnprod : n = 1155 * a * b := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf,
      prod_3_5_7_11_r_s ha_ge13 hb_ge13 hab]
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · have hwprod : Weird (1155 * a * b) := by simpa [hnprod] using hw
    refine ⟨a, b, ha_prime, hb_prime, ha384, hab_lt,
      corridor_of_weird_1155_mul_mul ha_prime hb_prime hab_lt ha384 hwprod,
      first_prime_le_761_of_weird_1155_mul_mul ha_prime hb_prime hab_lt ha384 hwprod,
      hnprod⟩
  · have hnprod' : n = 1155 * b * a := by
      rw [hnprod]
      ring
    have hwprod : Weird (1155 * b * a) := by simpa [hnprod'] using hw
    refine ⟨b, a, hb_prime, ha_prime, hb384, hba_lt,
      corridor_of_weird_1155_mul_mul hb_prime ha_prime hba_lt hb384 hwprod,
      first_prime_le_761_of_weird_1155_mul_mul hb_prime ha_prime hba_lt hb384 hwprod,
      hnprod'⟩

end WeirdNumbers
