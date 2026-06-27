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

set_option linter.style.nativeDecide false in
private theorem pp_1225785 : Pseudoperfect 1225785 := by
  refine ⟨({3, 11, 15, 17, 19, 23, 33, 51, 55, 57, 69, 85, 115, 165, 187,
    209, 253, 255, 285, 323, 345, 391, 437, 561, 627, 759, 935, 969, 1045,
    1173, 1265, 1311, 1615, 2185, 2805, 3135, 3553, 3795, 4301, 4807, 4845,
    5865, 6555, 7429, 12903, 14421, 17765, 21505, 22287, 37145, 53295, 64515,
    72105, 81719, 111435, 245157, 408595} : Finset ℕ),
    Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_1545555 : Pseudoperfect 1545555 := by
  refine ⟨({1, 3, 11, 15, 17, 19, 29, 33, 51, 55, 85, 87, 95, 145, 165, 187,
    209, 255, 285, 319, 323, 435, 493, 551, 561, 627, 935, 957, 969, 1479,
    1595, 1615, 1653, 2465, 2755, 2805, 3135, 3553, 4785, 4845, 5423, 6061,
    7395, 8265, 9367, 10659, 16269, 17765, 27115, 28101, 30305, 46835, 53295,
    81345, 90915, 103037, 140505, 309111, 515185} : Finset ℕ),
    Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_1652145 : Pseudoperfect 1652145 := by
  refine ⟨({3, 11, 15, 17, 19, 31, 33, 51, 55, 57, 85, 93, 95, 155, 165, 187,
    209, 255, 285, 323, 341, 465, 527, 561, 589, 627, 935, 969, 1023, 1045,
    1581, 1615, 1705, 1767, 2635, 2945, 3135, 3553, 4845, 5115, 5797, 6479,
    7905, 8835, 10013, 17391, 17765, 19437, 28985, 30039, 32395, 50065, 53295,
    86955, 97185, 110143, 150195, 330429, 550715} : Finset ℕ),
    Finset.mem_powerset.mpr (by native_decide), by native_decide⟩

set_option linter.style.nativeDecide false in
private theorem pp_1448655 : Pseudoperfect 1448655 := by
  refine ⟨({13, 15, 19, 39, 51, 57, 65, 69, 85, 95, 115, 195, 221, 247, 255,
    285, 299, 323, 345, 391, 437, 663, 741, 897, 969, 1105, 1173, 1235, 1311,
    1495, 1615, 1955, 2185, 3315, 3705, 4199, 4485, 4845, 5083, 5865, 6555,
    7429, 12597, 15249, 17043, 20995, 22287, 25415, 28405, 37145, 62985,
    76245, 85215, 96577, 111435, 289731, 482885} : Finset ℕ),
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

/-- A prime at least `17` does not divide `3 * 5 * 7 * 13`. -/
private theorem prime_ge17_not_dvd_1365 {r : ℕ} (hr : Nat.Prime r) (hr17 : 17 ≤ r) :
    ¬ r ∣ 1365 := by
  intro hd
  have hd' : r ∣ 3 * (5 * (7 * 13)) := by
    simpa [show 1365 = 3 * (5 * (7 * 13)) by norm_num] using hd
  rw [hr.dvd_mul] at hd'
  rcases hd' with h3 | hd'
  · have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 3)).mp h3
    omega
  rw [hr.dvd_mul] at hd'
  rcases hd' with h5 | hd'
  · have : r = 5 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 5)).mp h5
    omega
  rw [hr.dvd_mul] at hd'
  rcases hd' with h7 | h13
  · have : r = 7 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 7)).mp h7
    omega
  · have : r = 13 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 13)).mp h13
    omega

/-- A prime at least `17` does not divide `3 * 5 * 11 * 13`. -/
private theorem prime_ge17_not_dvd_2145 {r : ℕ} (hr : Nat.Prime r) (hr17 : 17 ≤ r) :
    ¬ r ∣ 2145 := by
  intro hd
  have hd' : r ∣ 3 * (5 * (11 * 13)) := by
    simpa [show 2145 = 3 * (5 * (11 * 13)) by norm_num] using hd
  rw [hr.dvd_mul] at hd'
  rcases hd' with h3 | hd'
  · have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 3)).mp h3
    omega
  rw [hr.dvd_mul] at hd'
  rcases hd' with h5 | hd'
  · have : r = 5 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 5)).mp h5
    omega
  rw [hr.dvd_mul] at hd'
  rcases hd' with h11 | h13
  · have : r = 11 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 11)).mp h11
    omega
  · have : r = 13 := (Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 13)).mp h13
    omega

set_option linter.style.nativeDecide false in
private theorem properDivisors_1155_sum : (1155 : ℕ).properDivisors.sum id = 1149 := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem divisors_1155_sum : (1155 : ℕ).divisors.sum id = 2304 := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem properDivisors_1365_sum : (1365 : ℕ).properDivisors.sum id = 1323 := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem divisors_1365_sum : (1365 : ℕ).divisors.sum id = 2688 := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem properDivisors_2145_sum : (2145 : ℕ).properDivisors.sum id = 1887 := by
  native_decide

set_option linter.style.nativeDecide false in
private theorem divisors_2145_sum : (2145 : ℕ).divisors.sum id = 4032 := by
  native_decide

/- The proper-divisor subset sums of `1155` fill `0..1149` except `2` and
`1147`. The following bitmask table is a compact certificate: bit `i` chooses
the `i`th proper divisor in `divisor1155At`. The table value is arbitrary at
the two holes. -/
set_option linter.style.longLine false in
private def properSubsetSum1155Masks : List ℕ := [
  0, 1, 0, 2, 3, 4, 5, 8, 6, 7, 10, 11, 12, 13, 18, 14,
  15, 21, 24, 22, 23, 26, 27, 28, 29, 42, 30, 31, 45, 50, 46, 47,
  53, 56, 54, 55, 58, 59, 60, 61, 86, 62, 63, 91, 92, 93, 106, 94,
  95, 109, 114, 110, 111, 117, 120, 118, 119, 122, 123, 124, 125, 173, 126, 127,
  175, 181, 184, 182, 183, 186, 187, 188, 189, 214, 190, 191, 219, 220, 221, 234,
  222, 223, 237, 242, 238, 239, 245, 248, 246, 247, 250, 251, 252, 253, 380, 254,
  255, 382, 383, 431, 437, 440, 438, 439, 442, 443, 444, 445, 470, 446, 447, 475,
  476, 477, 490, 478, 479, 493, 498, 494, 495, 501, 504, 502, 503, 506, 507, 508,
  509, 702, 510, 511, 732, 733, 746, 734, 735, 749, 754, 750, 751, 757, 760, 758,
  759, 762, 763, 764, 765, 892, 766, 767, 894, 895, 943, 949, 952, 950, 951, 954,
  955, 956, 957, 982, 958, 959, 987, 988, 989, 1002, 990, 991, 1005, 1010, 1006, 1007,
  1013, 1016, 1014, 1015, 1018, 1019, 1020, 1021, 1469, 1022, 1023, 1471, 1499, 1500, 1501, 1514,
  1502, 1503, 1517, 1522, 1518, 1519, 1525, 1528, 1526, 1527, 1530, 1531, 1532, 1533, 1726, 1534,
  1535, 1756, 1757, 1770, 1758, 1759, 1773, 1778, 1774, 1775, 1781, 1784, 1782, 1783, 1786, 1787,
  1788, 1789, 1916, 1790, 1791, 1918, 1919, 1967, 1973, 1976, 1974, 1975, 1978, 1979, 1980, 1981,
  2006, 1982, 1983, 2011, 2012, 2013, 2026, 2014, 2015, 2029, 2034, 2030, 2031, 2037, 2040, 2038,
  2039, 2042, 2043, 2044, 2045, 3000, 2046, 2047, 3002, 3003, 3004, 3005, 3030, 3006, 3007, 3035,
  3036, 3037, 3050, 3038, 3039, 3053, 3058, 3054, 3055, 3061, 3064, 3062, 3063, 3066, 3067, 3068,
  3069, 3517, 3070, 3071, 3519, 3547, 3548, 3549, 3562, 3550, 3551, 3565, 3570, 3566, 3567, 3573,
  3576, 3574, 3575, 3578, 3579, 3580, 3581, 3774, 3582, 3583, 3804, 3805, 3818, 3806, 3807, 3821,
  3826, 3822, 3823, 3829, 3832, 3830, 3831, 3834, 3835, 3836, 3837, 3964, 3838, 3839, 3966, 3967,
  4015, 4021, 4024, 4022, 4023, 4026, 4027, 4028, 4029, 4054, 4030, 4031, 4059, 4060, 4061, 4074,
  4062, 4063, 4077, 4082, 4078, 4079, 4085, 4088, 4086, 4087, 4090, 4091, 4092, 4093, 5623, 4094,
  4095, 5628, 5629, 5822, 5630, 5631, 5852, 5853, 5866, 5854, 5855, 5869, 5874, 5870, 5871, 5877,
  5880, 5878, 5879, 5882, 5883, 5884, 5885, 6012, 5886, 5887, 6014, 6015, 6063, 6069, 6072, 6070,
  6071, 6074, 6075, 6076, 6077, 6102, 6078, 6079, 6107, 6108, 6109, 6122, 6110, 6111, 6125, 6130,
  6126, 6127, 6133, 6136, 6134, 6135, 6138, 6139, 6140, 6141, 7096, 6142, 6143, 7098, 7099, 7100,
  7101, 7126, 7102, 7103, 7131, 7132, 7133, 7146, 7134, 7135, 7149, 7154, 7150, 7151, 7157, 7160,
  7158, 7159, 7162, 7163, 7164, 7165, 7613, 7166, 7167, 7615, 7643, 7644, 7645, 7658, 7646, 7647,
  7661, 7666, 7662, 7663, 7669, 7672, 7670, 7671, 7674, 7675, 7676, 7677, 7870, 7678, 7679, 7900,
  7901, 7914, 7902, 7903, 7917, 7922, 7918, 7919, 7925, 7928, 7926, 7927, 7930, 7931, 7932, 7933,
  8060, 7934, 7935, 8062, 8063, 8111, 8117, 8120, 8118, 8119, 8122, 8123, 8124, 8125, 8150, 8126,
  8127, 8155, 8156, 8157, 8170, 8158, 8159, 8173, 8178, 8174, 8175, 8181, 8184, 8182, 8183, 8186,
  8187, 8188, 8189, 11762, 8190, 8191, 11765, 11768, 11766, 11767, 11770, 11771, 11772, 11773, 11966, 11774,
  11775, 11996, 11997, 12010, 11998, 11999, 12013, 12018, 12014, 12015, 12021, 12024, 12022, 12023, 12026, 12027,
  12028, 12029, 12156, 12030, 12031, 12158, 12159, 12207, 12213, 12216, 12214, 12215, 12218, 12219, 12220, 12221,
  12246, 12222, 12223, 12251, 12252, 12253, 12266, 12254, 12255, 12269, 12274, 12270, 12271, 12277, 12280, 12278,
  12279, 12282, 12283, 12284, 12285, 13815, 12286, 12287, 13820, 13821, 14014, 13822, 13823, 14044, 14045, 14058,
  14046, 14047, 14061, 14066, 14062, 14063, 14069, 14072, 14070, 14071, 14074, 14075, 14076, 14077, 14204, 14078,
  14079, 14206, 14207, 14255, 14261, 14264, 14262, 14263, 14266, 14267, 14268, 14269, 14294, 14270, 14271, 14299,
  14300, 14301, 14314, 14302, 14303, 14317, 14322, 14318, 14319, 14325, 14328, 14326, 14327, 14330, 14331, 14332,
  14333, 15288, 14334, 14335, 15290, 15291, 15292, 15293, 15318, 15294, 15295, 15323, 15324, 15325, 15338, 15326,
  15327, 15341, 15346, 15342, 15343, 15349, 15352, 15350, 15351, 15354, 15355, 15356, 15357, 15805, 15358, 15359,
  15807, 15835, 15836, 15837, 15850, 15838, 15839, 15853, 15858, 15854, 15855, 15861, 15864, 15862, 15863, 15866,
  15867, 15868, 15869, 16062, 15870, 15871, 16092, 16093, 16106, 16094, 16095, 16109, 16114, 16110, 16111, 16117,
  16120, 16118, 16119, 16122, 16123, 16124, 16125, 16252, 16126, 16127, 16254, 16255, 16303, 16309, 16312, 16310,
  16311, 16314, 16315, 16316, 16317, 16342, 16318, 16319, 16347, 16348, 16349, 16362, 16350, 16351, 16365, 16370,
  16366, 16367, 16373, 16376, 16374, 16375, 16378, 16379, 16380, 16381, 22238, 16382, 16383, 22258, 22254, 22255,
  22261, 22264, 22262, 22263, 22266, 22267, 22268, 22269, 22396, 22270, 22271, 22398, 22399, 22447, 22453, 22456,
  22454, 22455, 22458, 22459, 22460, 22461, 22486, 22462, 22463, 22491, 22492, 22493, 22506, 22494, 22495, 22509,
  22514, 22510, 22511, 22517, 22520, 22518, 22519, 22522, 22523, 22524, 22525, 23480, 22526, 22527, 23482, 23483,
  23484, 23485, 23510, 23486, 23487, 23515, 23516, 23517, 23530, 23518, 23519, 23533, 23538, 23534, 23535, 23541,
  23544, 23542, 23543, 23546, 23547, 23548, 23549, 23997, 23550, 23551, 23999, 24027, 24028, 24029, 24042, 24030,
  24031, 24045, 24050, 24046, 24047, 24053, 24056, 24054, 24055, 24058, 24059, 24060, 24061, 24254, 24062, 24063,
  24284, 24285, 24298, 24286, 24287, 24301, 24306, 24302, 24303, 24309, 24312, 24310, 24311, 24314, 24315, 24316,
  24317, 24444, 24318, 24319, 24446, 24447, 24495, 24501, 24504, 24502, 24503, 24506, 24507, 24508, 24509, 24534,
  24510, 24511, 24539, 24540, 24541, 24554, 24542, 24543, 24557, 24562, 24558, 24559, 24565, 24568, 24566, 24567,
  24570, 24571, 24572, 24573, 28146, 24574, 24575, 28149, 28152, 28150, 28151, 28154, 28155, 28156, 28157, 28350,
  28158, 28159, 28380, 28381, 28394, 28382, 28383, 28397, 28402, 28398, 28399, 28405, 28408, 28406, 28407, 28410,
  28411, 28412, 28413, 28540, 28414, 28415, 28542, 28543, 28591, 28597, 28600, 28598, 28599, 28602, 28603, 28604,
  28605, 28630, 28606, 28607, 28635, 28636, 28637, 28650, 28638, 28639, 28653, 28658, 28654, 28655, 28661, 28664,
  28662, 28663, 28666, 28667, 28668, 28669, 30199, 28670, 28671, 30204, 30205, 30398, 30206, 30207, 30428, 30429,
  30442, 30430, 30431, 30445, 30450, 30446, 30447, 30453, 30456, 30454, 30455, 30458, 30459, 30460, 30461, 30588,
  30462, 30463, 30590, 30591, 30639, 30645, 30648, 30646, 30647, 30650, 30651, 30652, 30653, 30678, 30654, 30655,
  30683, 30684, 30685, 30698, 30686, 30687, 30701, 30706, 30702, 30703, 30709, 30712, 30710, 30711, 30714, 30715,
  30716, 30717, 31672, 30718, 30719, 31674, 31675, 31676, 31677, 31702, 31678, 31679, 31707, 31708, 31709, 31722,
  31710, 31711, 31725, 31730, 31726, 31727, 31733, 31736, 31734, 31735, 31738, 31739, 31740, 31741, 32189, 31742,
  31743, 32191, 32219, 32220, 32221, 32234, 32222, 32223, 32237, 32242, 32238, 32239, 32245, 32248, 32246, 32247,
  32250, 32251, 32252, 32253, 32446, 32254, 32255, 32476, 32477, 32490, 32478, 32479, 32493, 32498, 32494, 32495,
  32501, 32504, 32502, 32503, 32506, 32507, 32508, 32509, 32636, 32510, 32511, 32638, 32639, 32687, 32693, 32696,
  32694, 32695, 32698, 32699, 32700, 32701, 32726, 32702, 32703, 32731, 32732, 32733, 32746, 32734, 32735, 32749,
  32754, 32750, 32751, 32757, 32760, 32758, 32759, 32762, 32763, 32764, 32765, 0, 32766, 32767
]

private def subsetSum1155Allowed (t : ℕ) : Bool :=
  t ≤ 2304 && t != 2 && t != 1147 && t != 1150 && t != 1151 && t != 1152 &&
    t != 1153 && t != 1154 && t != 1157 && t != 2302

private def subsetSum1155Mask (t : ℕ) : ℕ :=
  if t ≤ 1149 then
    properSubsetSum1155Masks.getD t 0
  else if 1155 ≤ t then
    32768 + properSubsetSum1155Masks.getD (t - 1155) 0
  else
    0

private def divisor1155At : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 15
  | 6 => 21
  | 7 => 33
  | 8 => 35
  | 9 => 55
  | 10 => 77
  | 11 => 105
  | 12 => 165
  | 13 => 231
  | 14 => 385
  | _ => 1155

private def subsetSum1155Witness (t : ℕ) : Finset ℕ :=
  ((Finset.range 16).filter fun i => (subsetSum1155Mask t).testBit i).image divisor1155At

set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 0 in
private theorem subsetSum1155Witness_spec {t : ℕ} (ht : subsetSum1155Allowed t = true) :
    subsetSum1155Witness t ⊆ (1155 : ℕ).divisors ∧ (subsetSum1155Witness t).sum id = t := by
  have hclosed : ∀ t ∈ Finset.Icc 0 2304, subsetSum1155Allowed t = true →
      subsetSum1155Witness t ⊆ (1155 : ℕ).divisors ∧
        (subsetSum1155Witness t).sum id = t := by
    native_decide
  have htle : t ≤ 2304 := by
    by_contra htle
    unfold subsetSum1155Allowed at ht
    simp [htle] at ht
  exact hclosed t (by simp [htle]) ht

private def certShift1155 (r s : ℕ) : ℕ :=
  let T := 6 * s * (r - 384)
  let q := T / r
  let rem := T % r
  if subsetSum1155Allowed q && subsetSum1155Allowed rem then 0
  else if subsetSum1155Allowed (q - 2) && subsetSum1155Allowed (rem + 2 * r) then 2
  else if subsetSum1155Allowed (q - 3) && subsetSum1155Allowed (rem + 3 * r) then 3
  else if subsetSum1155Allowed (q - 4) && subsetSum1155Allowed (rem + 4 * r) then 4
  else if subsetSum1155Allowed (q - 5) && subsetSum1155Allowed (rem + 5 * r) then 5
  else 1

private def certShift1155Spec (r s : ℕ) : Bool :=
  let T := 6 * s * (r - 384)
  let k := certShift1155 r s
  k ≤ 5 && k ≤ T / r && subsetSum1155Allowed (T / r - k) &&
    subsetSum1155Allowed (T % r + k * r)

/- In the finite corridor, the quotient/remainder construction works after a
shift by at most five, except for the three explicit pairs handled separately
below. This is a bounded finite verification over the `3,5,7,11` corridor. -/
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 0 in
private theorem certShift1155Spec_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr384 : 384 < r) (hrs : r < s)
    (hr761 : r ≤ 761) (hcorr : s * (r - 384) ≤ 384 * (r + 1))
    (hne491 : ¬ (r = 491 ∧ s = 883))
    (hne557 : ¬ (r = 557 ∧ s = 619))
    (hne571 : ¬ (r = 571 ∧ s = 587)) : certShift1155Spec r s = true := by
  have hclosed : ∀ r ∈ Finset.Icc 389 761, ∀ s ∈ Finset.Icc (r + 1) 29952,
      Nat.Prime r → Nat.Prime s → s * (r - 384) ≤ 384 * (r + 1) →
      ¬ (r = 491 ∧ s = 883) → ¬ (r = 557 ∧ s = 619) →
      ¬ (r = 571 ∧ s = 587) → certShift1155Spec r s = true := by
    native_decide
  have hr389 : 389 ≤ r := by
    by_contra h
    push Not at h
    have hr_cases : r = 385 ∨ r = 386 ∨ r = 387 ∨ r = 388 := by omega
    rcases hr_cases with rfl | rfl | rfl | rfl <;> norm_num at hr
  have hrmem : r ∈ Finset.Icc 389 761 := by
    simp [hr389, hr761]
  have hsle : s ≤ 29952 := by
    have hden_pos : 0 < r - 384 := by omega
    have hnum : 384 * (r + 1) ≤ 29952 * (r - 384) := by
      zify [show 384 ≤ r from by omega]
      nlinarith
    have hprod : s * (r - 384) ≤ 29952 * (r - 384) := le_trans hcorr hnum
    exact Nat.le_of_mul_le_mul_right hprod hden_pos
  have hsge : r + 1 ≤ s := by omega
  have hsmem : s ∈ Finset.Icc (r + 1) 29952 := by
    simp [hsge, hsle]
  exact hclosed r hrmem s hsmem hr hs hcorr hne491 hne557 hne571

private theorem cert_1155_of_corridor_nonexception {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr384 : 384 < r) (hrs : r < s)
    (hr761 : r ≤ 761) (hcorr : s * (r - 384) ≤ 384 * (r + 1))
    (hne491 : ¬ (r = 491 ∧ s = 883))
    (hne557 : ¬ (r = 557 ∧ s = 619))
    (hne571 : ¬ (r = 571 ∧ s = 587)) :
    ∃ A B C : Finset ℕ, A ⊆ (1155 : ℕ).divisors ∧ B ⊆ (1155 : ℕ).divisors ∧
      C ⊆ (1155 : ℕ).divisors ∧ A.sum id + r * B.sum id + s * C.sum id =
        6 * r * s := by
  let T := 6 * s * (r - 384)
  let k := certShift1155 r s
  have hspec : k ≤ 5 ∧ k ≤ T / r ∧ subsetSum1155Allowed (T / r - k) = true ∧
      subsetSum1155Allowed (T % r + k * r) = true := by
    have hraw := certShift1155Spec_of_corridor hr hs hr384 hrs hr761 hcorr
      hne491 hne557 hne571
    dsimp [certShift1155Spec, T, k] at hraw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hraw
    rcases hraw with ⟨⟨⟨hk5, hkdiv⟩, hB⟩, hA⟩
    exact ⟨hk5, hkdiv, hB, hA⟩
  rcases hspec with ⟨_hk5, hkdiv, hBallowed, hAallowed⟩
  let A := subsetSum1155Witness (T % r + k * r)
  let B := subsetSum1155Witness (T / r - k)
  let C := (1155 : ℕ).divisors
  obtain ⟨hAsub, hAsum⟩ := subsetSum1155Witness_spec hAallowed
  obtain ⟨hBsub, hBsum⟩ := subsetSum1155Witness_spec hBallowed
  refine ⟨A, B, C, hAsub, hBsub, ?_, ?_⟩
  · intro x hx
    exact hx
  · have hCsum : C.sum id = 2304 := by
      dsimp [C]
      exact divisors_1155_sum
    rw [hAsum, hBsum, hCsum]
    have hfill : T % r + k * r + r * (T / r - k) = T := by
      have hdecomp : T % r + r * (T / r) = T := Nat.mod_add_div T r
      have hq : T / r = T / r - k + k := (Nat.sub_add_cancel hkdiv).symm
      rw [hq, Nat.mul_add] at hdecomp
      calc
        T % r + k * r + r * (T / r - k) =
            T % r + (r * (T / r - k) + r * k) := by
          rw [mul_comm k r]
          rw [Nat.add_assoc, Nat.add_comm (r * k) (r * (T / r - k))]
        _ = T := hdecomp
    calc
      T % r + k * r + r * (T / r - k) + s * 2304 = T + s * 2304 := by
        rw [hfill]
      _ = 6 * r * s := by
        dsimp [T]
        zify [show 384 ≤ r from by omega]
        ring

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

/-- No prime at least `17` can divide a divisor of `1365`. -/
private theorem no_prime_ge17_dvd_of_dvd_1365 {p x : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (hx : x ∣ 1365) : ¬ p ∣ x := by
  intro hpx
  exact prime_ge17_not_dvd_1365 hp hp17 (hpx.trans hx)

/- The product of the fixed core `3 * 5 * 7 * 13` with a prime
`17 ≤ r ≤ 61` is pseudoperfect.

Here the proper divisors of `1365` sum to `1323 = 1365 - 42`, so the
`r`-multiples of those divisors leave a gap of `42r`. A bounded subset-sum
check over the divisors of `1365` fills that gap for each prime in this range. -/
set_option linter.style.nativeDecide false in
private theorem forty_two_mul_subset_sum_1365_small {r : ℕ} (hr : Nat.Prime r)
    (hr17 : 17 ≤ r) (hr61 : r ≤ 61) :
    ∃ U : Finset ℕ, U ⊆ (1365 : ℕ).divisors ∧ U.sum id = 42 * r := by
  have hclosed : ∀ r ∈ Finset.Icc 17 61, Nat.Prime r →
      ∃ U : Finset ℕ, U ⊆ (1365 : ℕ).divisors ∧ U.sum id = 42 * r := by
    native_decide
  exact hclosed r (by simp [hr17, hr61]) hr

/-- If `17 ≤ r ≤ 61` is prime, then `1365 * r` is pseudoperfect.

This is the first parametric pruning lemma for the `3,5,7,13` branch. -/
private theorem pp_1365_mul_of_small_prime {r : ℕ} (hr : Nat.Prime r) (hr17 : 17 ≤ r)
    (hr61 : r ≤ 61) : Pseudoperfect (1365 * r) := by
  obtain ⟨U, hUsub, hUsum⟩ := forty_two_mul_subset_sum_1365_small hr hr17 hr61
  let R := (1365 : ℕ).properDivisors.image fun d => r * d
  refine ⟨U ∪ R, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hxU | hxR
    · have hxdiv1365 : x ∣ 1365 := Nat.dvd_of_mem_divisors (hUsub hxU)
      rw [Nat.mem_properDivisors]
      refine ⟨?_, ?_⟩
      · exact hxdiv1365.trans (dvd_mul_right 1365 r)
      · have hxle : x ≤ 1365 := Nat.le_of_dvd (by norm_num) hxdiv1365
        have hrgt : 1 < r := lt_of_lt_of_le (by norm_num : 1 < 17) hr17
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
      have hxdiv1365 : x ∣ 1365 := Nat.dvd_of_mem_divisors (hUsub hxU)
      have hrdvdx : r ∣ x := by
        rw [← hxd]
        exact dvd_mul_right r d
      exact prime_ge17_not_dvd_1365 hr hr17 (hrdvdx.trans hxdiv1365)
    rw [Finset.sum_union hdisj]
    have hsumR : R.sum id = r * 1323 := by
      dsimp [R]
      rw [Finset.sum_image]
      · change (∑ x ∈ (1365 : ℕ).properDivisors, r * id x) = r * 1323
        rw [← Finset.mul_sum, properDivisors_1365_sum]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left hr.pos hab
    rw [hUsum, hsumR]
    ring

/- The proper-divisor subset sums of `1365` fill `0..1323` except `2` and
`1321`. This table mirrors `properSubsetSum1155Masks`: bit `i` chooses the
`i`th proper divisor in `divisor1365At`. -/
set_option linter.style.longLine false in
private def properSubsetSum1365Masks : List ℕ := [
  0, 1, 0, 2, 3, 4, 5, 8, 6, 7, 10, 11, 12, 13, 17, 14,
  15, 19, 20, 21, 24, 22, 23, 26, 27, 28, 29, 44, 30, 31, 46, 47,
  51, 52, 53, 56, 54, 55, 58, 59, 60, 61, 86, 62, 63, 91, 92, 93,
  108, 94, 95, 110, 111, 115, 116, 117, 120, 118, 119, 122, 123, 124, 125, 158,
  126, 127, 175, 179, 180, 181, 184, 182, 183, 186, 187, 188, 189, 214, 190, 191,
  219, 220, 221, 236, 222, 223, 238, 239, 243, 244, 245, 248, 246, 247, 250, 251,
  252, 253, 378, 254, 255, 381, 414, 382, 383, 431, 435, 436, 437, 440, 438, 439,
  442, 443, 444, 445, 470, 446, 447, 475, 476, 477, 492, 478, 479, 494, 495, 499,
  500, 501, 504, 502, 503, 506, 507, 508, 509, 695, 510, 511, 700, 701, 726, 702,
  703, 731, 732, 733, 748, 734, 735, 750, 751, 755, 756, 757, 760, 758, 759, 762,
  763, 764, 765, 890, 766, 767, 893, 926, 894, 895, 943, 947, 948, 949, 952, 950,
  951, 954, 955, 956, 957, 982, 958, 959, 987, 988, 989, 1004, 990, 991, 1006, 1007,
  1011, 1012, 1013, 1016, 1014, 1015, 1018, 1019, 1020, 1021, 1463, 1022, 1023, 1468, 1469, 1494,
  1470, 1471, 1499, 1500, 1501, 1516, 1502, 1503, 1518, 1519, 1523, 1524, 1525, 1528, 1526, 1527,
  1530, 1531, 1532, 1533, 1719, 1534, 1535, 1724, 1725, 1750, 1726, 1727, 1755, 1756, 1757, 1772,
  1758, 1759, 1774, 1775, 1779, 1780, 1781, 1784, 1782, 1783, 1786, 1787, 1788, 1789, 1914, 1790,
  1791, 1917, 1950, 1918, 1919, 1967, 1971, 1972, 1973, 1976, 1974, 1975, 1978, 1979, 1980, 1981,
  2006, 1982, 1983, 2011, 2012, 2013, 2028, 2014, 2015, 2030, 2031, 2035, 2036, 2037, 2040, 2038,
  2039, 2042, 2043, 2044, 2045, 3038, 2046, 2047, 3055, 3059, 3060, 3061, 3064, 3062, 3063, 3066,
  3067, 3068, 3069, 3511, 3070, 3071, 3516, 3517, 3542, 3518, 3519, 3547, 3548, 3549, 3564, 3550,
  3551, 3566, 3567, 3571, 3572, 3573, 3576, 3574, 3575, 3578, 3579, 3580, 3581, 3767, 3582, 3583,
  3772, 3773, 3798, 3774, 3775, 3803, 3804, 3805, 3820, 3806, 3807, 3822, 3823, 3827, 3828, 3829,
  3832, 3830, 3831, 3834, 3835, 3836, 3837, 3962, 3838, 3839, 3965, 3998, 3966, 3967, 4015, 4019,
  4020, 4021, 4024, 4022, 4023, 4026, 4027, 4028, 4029, 4054, 4030, 4031, 4059, 4060, 4061, 4076,
  4062, 4063, 4078, 4079, 4083, 4084, 4085, 4088, 4086, 4087, 4090, 4091, 4092, 4093, 5118, 4094,
  4095, 5565, 5590, 5566, 5567, 5595, 5596, 5597, 5612, 5598, 5599, 5614, 5615, 5619, 5620, 5621,
  5624, 5622, 5623, 5626, 5627, 5628, 5629, 5815, 5630, 5631, 5820, 5821, 5846, 5822, 5823, 5851,
  5852, 5853, 5868, 5854, 5855, 5870, 5871, 5875, 5876, 5877, 5880, 5878, 5879, 5882, 5883, 5884,
  5885, 6010, 5886, 5887, 6013, 6046, 6014, 6015, 6063, 6067, 6068, 6069, 6072, 6070, 6071, 6074,
  6075, 6076, 6077, 6102, 6078, 6079, 6107, 6108, 6109, 6124, 6110, 6111, 6126, 6127, 6131, 6132,
  6133, 6136, 6134, 6135, 6138, 6139, 6140, 6141, 7134, 6142, 6143, 7151, 7155, 7156, 7157, 7160,
  7158, 7159, 7162, 7163, 7164, 7165, 7607, 7166, 7167, 7612, 7613, 7638, 7614, 7615, 7643, 7644,
  7645, 7660, 7646, 7647, 7662, 7663, 7667, 7668, 7669, 7672, 7670, 7671, 7674, 7675, 7676, 7677,
  7863, 7678, 7679, 7868, 7869, 7894, 7870, 7871, 7899, 7900, 7901, 7916, 7902, 7903, 7918, 7919,
  7923, 7924, 7925, 7928, 7926, 7927, 7930, 7931, 7932, 7933, 8058, 7934, 7935, 8061, 8094, 8062,
  8063, 8111, 8115, 8116, 8117, 8120, 8118, 8119, 8122, 8123, 8124, 8125, 8150, 8126, 8127, 8155,
  8156, 8157, 8172, 8158, 8159, 8174, 8175, 8179, 8180, 8181, 8184, 8182, 8183, 8186, 8187, 8188,
  8189, 11743, 8190, 8191, 11763, 11764, 11765, 11768, 11766, 11767, 11770, 11771, 11772, 11773, 11959, 11774,
  11775, 11964, 11965, 11990, 11966, 11967, 11995, 11996, 11997, 12012, 11998, 11999, 12014, 12015, 12019, 12020,
  12021, 12024, 12022, 12023, 12026, 12027, 12028, 12029, 12154, 12030, 12031, 12157, 12190, 12158, 12159, 12207,
  12211, 12212, 12213, 12216, 12214, 12215, 12218, 12219, 12220, 12221, 12246, 12222, 12223, 12251, 12252, 12253,
  12268, 12254, 12255, 12270, 12271, 12275, 12276, 12277, 12280, 12278, 12279, 12282, 12283, 12284, 12285, 13310,
  12286, 12287, 13757, 13782, 13758, 13759, 13787, 13788, 13789, 13804, 13790, 13791, 13806, 13807, 13811, 13812,
  13813, 13816, 13814, 13815, 13818, 13819, 13820, 13821, 14007, 13822, 13823, 14012, 14013, 14038, 14014, 14015,
  14043, 14044, 14045, 14060, 14046, 14047, 14062, 14063, 14067, 14068, 14069, 14072, 14070, 14071, 14074, 14075,
  14076, 14077, 14202, 14078, 14079, 14205, 14238, 14206, 14207, 14255, 14259, 14260, 14261, 14264, 14262, 14263,
  14266, 14267, 14268, 14269, 14294, 14270, 14271, 14299, 14300, 14301, 14316, 14302, 14303, 14318, 14319, 14323,
  14324, 14325, 14328, 14326, 14327, 14330, 14331, 14332, 14333, 15326, 14334, 14335, 15343, 15347, 15348, 15349,
  15352, 15350, 15351, 15354, 15355, 15356, 15357, 15799, 15358, 15359, 15804, 15805, 15830, 15806, 15807, 15835,
  15836, 15837, 15852, 15838, 15839, 15854, 15855, 15859, 15860, 15861, 15864, 15862, 15863, 15866, 15867, 15868,
  15869, 16055, 15870, 15871, 16060, 16061, 16086, 16062, 16063, 16091, 16092, 16093, 16108, 16094, 16095, 16110,
  16111, 16115, 16116, 16117, 16120, 16118, 16119, 16122, 16123, 16124, 16125, 16250, 16126, 16127, 16253, 16286,
  16254, 16255, 16303, 16307, 16308, 16309, 16312, 16310, 16311, 16314, 16315, 16316, 16317, 16342, 16318, 16319,
  16347, 16348, 16349, 16364, 16350, 16351, 16366, 16367, 16371, 16372, 16373, 16376, 16374, 16375, 16378, 16379,
  16380, 16381, 21998, 16382, 16383, 22004, 22005, 22008, 22006, 22007, 22010, 22011, 22012, 22013, 22199, 22014,
  22015, 22204, 22205, 22230, 22206, 22207, 22235, 22236, 22237, 22252, 22238, 22239, 22254, 22255, 22259, 22260,
  22261, 22264, 22262, 22263, 22266, 22267, 22268, 22269, 22394, 22270, 22271, 22397, 22430, 22398, 22399, 22447,
  22451, 22452, 22453, 22456, 22454, 22455, 22458, 22459, 22460, 22461, 22486, 22462, 22463, 22491, 22492, 22493,
  22508, 22494, 22495, 22510, 22511, 22515, 22516, 22517, 22520, 22518, 22519, 22522, 22523, 22524, 22525, 23518,
  22526, 22527, 23535, 23539, 23540, 23541, 23544, 23542, 23543, 23546, 23547, 23548, 23549, 23991, 23550, 23551,
  23996, 23997, 24022, 23998, 23999, 24027, 24028, 24029, 24044, 24030, 24031, 24046, 24047, 24051, 24052, 24053,
  24056, 24054, 24055, 24058, 24059, 24060, 24061, 24247, 24062, 24063, 24252, 24253, 24278, 24254, 24255, 24283,
  24284, 24285, 24300, 24286, 24287, 24302, 24303, 24307, 24308, 24309, 24312, 24310, 24311, 24314, 24315, 24316,
  24317, 24442, 24318, 24319, 24445, 24478, 24446, 24447, 24495, 24499, 24500, 24501, 24504, 24502, 24503, 24506,
  24507, 24508, 24509, 24534, 24510, 24511, 24539, 24540, 24541, 24556, 24542, 24543, 24558, 24559, 24563, 24564,
  24565, 24568, 24566, 24567, 24570, 24571, 24572, 24573, 28127, 24574, 24575, 28147, 28148, 28149, 28152, 28150,
  28151, 28154, 28155, 28156, 28157, 28343, 28158, 28159, 28348, 28349, 28374, 28350, 28351, 28379, 28380, 28381,
  28396, 28382, 28383, 28398, 28399, 28403, 28404, 28405, 28408, 28406, 28407, 28410, 28411, 28412, 28413, 28538,
  28414, 28415, 28541, 28574, 28542, 28543, 28591, 28595, 28596, 28597, 28600, 28598, 28599, 28602, 28603, 28604,
  28605, 28630, 28606, 28607, 28635, 28636, 28637, 28652, 28638, 28639, 28654, 28655, 28659, 28660, 28661, 28664,
  28662, 28663, 28666, 28667, 28668, 28669, 29694, 28670, 28671, 30141, 30166, 30142, 30143, 30171, 30172, 30173,
  30188, 30174, 30175, 30190, 30191, 30195, 30196, 30197, 30200, 30198, 30199, 30202, 30203, 30204, 30205, 30391,
  30206, 30207, 30396, 30397, 30422, 30398, 30399, 30427, 30428, 30429, 30444, 30430, 30431, 30446, 30447, 30451,
  30452, 30453, 30456, 30454, 30455, 30458, 30459, 30460, 30461, 30586, 30462, 30463, 30589, 30622, 30590, 30591,
  30639, 30643, 30644, 30645, 30648, 30646, 30647, 30650, 30651, 30652, 30653, 30678, 30654, 30655, 30683, 30684,
  30685, 30700, 30686, 30687, 30702, 30703, 30707, 30708, 30709, 30712, 30710, 30711, 30714, 30715, 30716, 30717,
  31710, 30718, 30719, 31727, 31731, 31732, 31733, 31736, 31734, 31735, 31738, 31739, 31740, 31741, 32183, 31742,
  31743, 32188, 32189, 32214, 32190, 32191, 32219, 32220, 32221, 32236, 32222, 32223, 32238, 32239, 32243, 32244,
  32245, 32248, 32246, 32247, 32250, 32251, 32252, 32253, 32439, 32254, 32255, 32444, 32445, 32470, 32446, 32447,
  32475, 32476, 32477, 32492, 32478, 32479, 32494, 32495, 32499, 32500, 32501, 32504, 32502, 32503, 32506, 32507,
  32508, 32509, 32634, 32510, 32511, 32637, 32670, 32638, 32639, 32687, 32691, 32692, 32693, 32696, 32694, 32695,
  32698, 32699, 32700, 32701, 32726, 32702, 32703, 32731, 32732, 32733, 32748, 32734, 32735, 32750, 32751, 32755,
  32756, 32757, 32760, 32758, 32759, 32762, 32763, 32764, 32765, 0, 32766, 32767
]

private def subsetSum1365Allowed (t : ℕ) : Bool :=
  t ≤ 2688 && t != 2 && t != 1321 && !(1324 ≤ t && t ≤ 1364) &&
    t != 1367 && t != 2686

private def subsetSum1365Mask (t : ℕ) : ℕ :=
  if t ≤ 1323 then
    properSubsetSum1365Masks.getD t 0
  else if 1365 ≤ t then
    32768 + properSubsetSum1365Masks.getD (t - 1365) 0
  else
    0

private def divisor1365At : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 13
  | 5 => 15
  | 6 => 21
  | 7 => 35
  | 8 => 39
  | 9 => 65
  | 10 => 91
  | 11 => 105
  | 12 => 195
  | 13 => 273
  | 14 => 455
  | _ => 1365

private def subsetSum1365Witness (t : ℕ) : Finset ℕ :=
  ((Finset.range 16).filter fun i => (subsetSum1365Mask t).testBit i).image divisor1365At

set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 0 in
private theorem subsetSum1365Witness_spec {t : ℕ} (ht : subsetSum1365Allowed t = true) :
    subsetSum1365Witness t ⊆ (1365 : ℕ).divisors ∧ (subsetSum1365Witness t).sum id = t := by
  have hclosed : ∀ t ∈ Finset.Icc 0 2688, subsetSum1365Allowed t = true →
      subsetSum1365Witness t ⊆ (1365 : ℕ).divisors ∧
        (subsetSum1365Witness t).sum id = t := by
    native_decide
  have htle : t ≤ 2688 := by
    by_contra htle
    unfold subsetSum1365Allowed at ht
    simp [htle] at ht
  exact hclosed t (by simp [htle]) ht

private def certShift1365 (r s : ℕ) : ℕ :=
  let T := 42 * s * (r - 64)
  ((List.range 34).find? fun k =>
    k ≤ T / r && subsetSum1365Allowed (T / r - k) &&
      subsetSum1365Allowed (T % r + k * r)).getD 0

private def certShift1365Spec (r s : ℕ) : Bool :=
  let T := 42 * s * (r - 64)
  let k := certShift1365 r s
  k ≤ 33 && k ≤ T / r && subsetSum1365Allowed (T / r - k) &&
    subsetSum1365Allowed (T % r + k * r)

/- In the finite `3,5,7,13` corridor, the quotient/remainder construction works
after a shift by at most `33`, except for the explicit pair handled below. -/
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 0 in
private theorem certShift1365Spec_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr64 : 64 < r) (hrs : r < s)
    (hr127 : r ≤ 127) (hcorr : s * (r - 64) ≤ 64 * (r + 1))
    (hne73 : ¬ (r = 73 ∧ s = 263)) : certShift1365Spec r s = true := by
  have hclosed : ∀ r ∈ Finset.Icc 67 127, ∀ s ∈ Finset.Icc (r + 1) 1451,
      Nat.Prime r → Nat.Prime s → s * (r - 64) ≤ 64 * (r + 1) →
      ¬ (r = 73 ∧ s = 263) → certShift1365Spec r s = true := by
    native_decide
  have hr67 : 67 ≤ r := by
    by_contra h
    push Not at h
    have hr_cases : r = 65 ∨ r = 66 := by omega
    rcases hr_cases with rfl | rfl <;> norm_num at hr
  have hrmem : r ∈ Finset.Icc 67 127 := by
    simp [hr67, hr127]
  have hsle : s ≤ 1451 := by
    have hden_pos : 0 < r - 64 := by omega
    have hnum : 64 * (r + 1) ≤ 1451 * (r - 64) := by
      zify [show 64 ≤ r from by omega]
      nlinarith
    have hprod : s * (r - 64) ≤ 1451 * (r - 64) := le_trans hcorr hnum
    exact Nat.le_of_mul_le_mul_right hprod hden_pos
  have hsge : r + 1 ≤ s := by omega
  have hsmem : s ∈ Finset.Icc (r + 1) 1451 := by
    simp [hsge, hsle]
  exact hclosed r hrmem s hsmem hr hs hcorr hne73

private theorem cert_1365_of_corridor_nonexception {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr64 : 64 < r) (hrs : r < s)
    (hr127 : r ≤ 127) (hcorr : s * (r - 64) ≤ 64 * (r + 1))
    (hne73 : ¬ (r = 73 ∧ s = 263)) :
    ∃ A B C : Finset ℕ, A ⊆ (1365 : ℕ).divisors ∧ B ⊆ (1365 : ℕ).divisors ∧
      C ⊆ (1365 : ℕ).divisors ∧ A.sum id + r * B.sum id + s * C.sum id =
        42 * r * s := by
  let T := 42 * s * (r - 64)
  let k := certShift1365 r s
  have hspec : k ≤ 33 ∧ k ≤ T / r ∧ subsetSum1365Allowed (T / r - k) = true ∧
      subsetSum1365Allowed (T % r + k * r) = true := by
    have hraw := certShift1365Spec_of_corridor hr hs hr64 hrs hr127 hcorr hne73
    dsimp [certShift1365Spec, T, k] at hraw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hraw
    rcases hraw with ⟨⟨⟨hk33, hkdiv⟩, hB⟩, hA⟩
    exact ⟨hk33, hkdiv, hB, hA⟩
  rcases hspec with ⟨_hk33, hkdiv, hBallowed, hAallowed⟩
  let A := subsetSum1365Witness (T % r + k * r)
  let B := subsetSum1365Witness (T / r - k)
  let C := (1365 : ℕ).divisors
  obtain ⟨hAsub, hAsum⟩ := subsetSum1365Witness_spec hAallowed
  obtain ⟨hBsub, hBsum⟩ := subsetSum1365Witness_spec hBallowed
  refine ⟨A, B, C, hAsub, hBsub, ?_, ?_⟩
  · intro x hx
    exact hx
  · have hCsum : C.sum id = 2688 := by
      dsimp [C]
      exact divisors_1365_sum
    rw [hAsum, hBsum, hCsum]
    have hfill : T % r + k * r + r * (T / r - k) = T := by
      have hdecomp : T % r + r * (T / r) = T := Nat.mod_add_div T r
      have hq : T / r = T / r - k + k := (Nat.sub_add_cancel hkdiv).symm
      rw [hq, Nat.mul_add] at hdecomp
      calc
        T % r + k * r + r * (T / r - k) =
            T % r + (r * (T / r - k) + r * k) := by
          rw [mul_comm k r]
          rw [Nat.add_assoc, Nat.add_comm (r * k) (r * (T / r - k))]
        _ = T := hdecomp
    calc
      T % r + k * r + r * (T / r - k) + s * 2688 = T + s * 2688 := by
        rw [hfill]
      _ = 42 * r * s := by
        dsimp [T]
        zify [show 64 ≤ r from by omega]
        ring

/-- A certificate lemma for the two-large-prime part of the `3,5,7,13` branch.

If `A + rB + sC = 42rs`, where `A`, `B`, and `C` are subset sums of divisors of
`1365`, then `1365*r*s` is pseudoperfect. -/
private theorem pp_1365_mul_mul_of_cert {r s : ℕ} (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hr17 : 17 ≤ r) (hs17 : 17 ≤ s) (hrs : r ≠ s)
    {A B C : Finset ℕ} (hA : A ⊆ (1365 : ℕ).divisors)
    (hB : B ⊆ (1365 : ℕ).divisors) (hC : C ⊆ (1365 : ℕ).divisors)
    (hsum : A.sum id + r * B.sum id + s * C.sum id = 42 * r * s) :
    Pseudoperfect (1365 * r * s) := by
  let RB := B.image fun d => r * d
  let SC := C.image fun d => s * d
  let RSD := (1365 : ℕ).properDivisors.image fun d => (r * s) * d
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
        · have hxdiv : x ∣ 1365 := Nat.dvd_of_mem_divisors (hA hxA)
          rw [Nat.mem_properDivisors]
          refine ⟨?_, ?_⟩
          · exact hxdiv.trans ((dvd_mul_right 1365 r).trans (dvd_mul_right (1365 * r) s))
          · have hxle : x ≤ 1365 := Nat.le_of_dvd (by norm_num) hxdiv
            have hrgt : 1 < r := lt_of_lt_of_le (by norm_num : 1 < 17) hr17
            have hsgt : 1 < s := lt_of_lt_of_le (by norm_num : 1 < 17) hs17
            nlinarith
        · rw [Finset.mem_image] at hxRB
          rcases hxRB with ⟨d, hd, rfl⟩
          have hddiv : d ∣ 1365 := Nat.dvd_of_mem_divisors (hB hd)
          rw [Nat.mem_properDivisors]
          refine ⟨?_, ?_⟩
          · rcases hddiv with ⟨k, hk⟩
            use k * s
            rw [hk]
            ring
          · have hdle : d ≤ 1365 := Nat.le_of_dvd (by norm_num) hddiv
            have hsgt : 1 < s := lt_of_lt_of_le (by norm_num : 1 < 17) hs17
            nlinarith [hr.pos]
      · rw [Finset.mem_image] at hxSC
        rcases hxSC with ⟨d, hd, rfl⟩
        have hddiv : d ∣ 1365 := Nat.dvd_of_mem_divisors (hC hd)
        rw [Nat.mem_properDivisors]
        refine ⟨?_, ?_⟩
        · rcases hddiv with ⟨k, hk⟩
          use k * r
          rw [hk]
          ring
        · have hdle : d ≤ 1365 := Nat.le_of_dvd (by norm_num) hddiv
          have hrgt : 1 < r := lt_of_lt_of_le (by norm_num : 1 < 17) hr17
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
      have hxdiv : x ∣ 1365 := Nat.dvd_of_mem_divisors (hA hxA)
      have hrdvdx : r ∣ x := by
        rw [← hxb]
        exact dvd_mul_right r b
      exact no_prime_ge17_dvd_of_dvd_1365 hr hr17 hxdiv hrdvdx
    have hA_SC : Disjoint A SC := by
      rw [Finset.disjoint_left]
      intro x hxA hxSC
      rw [Finset.mem_image] at hxSC
      rcases hxSC with ⟨c, _hc, hxc⟩
      have hxdiv : x ∣ 1365 := Nat.dvd_of_mem_divisors (hA hxA)
      have hsdvdx : s ∣ x := by
        rw [← hxc]
        exact dvd_mul_right s c
      exact no_prime_ge17_dvd_of_dvd_1365 hs hs17 hxdiv hsdvdx
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
      have hcdiv : c ∣ 1365 := Nat.dvd_of_mem_divisors (hC hc)
      exact no_prime_ge17_dvd_of_dvd_1365 hr hr17 hcdiv hrdvdc
    have hA_RSD : Disjoint A RSD := by
      rw [Finset.disjoint_left]
      intro x hxA hxD
      rw [Finset.mem_image] at hxD
      rcases hxD with ⟨d, _hd, hxd⟩
      have hxdiv : x ∣ 1365 := Nat.dvd_of_mem_divisors (hA hxA)
      have hrdvdx : r ∣ x := by
        rw [← hxd]
        use s * d
        ring
      exact no_prime_ge17_dvd_of_dvd_1365 hr hr17 hxdiv hrdvdx
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
      have hbdiv : b ∣ 1365 := Nat.dvd_of_mem_divisors (hB hb)
      exact no_prime_ge17_dvd_of_dvd_1365 hs hs17 hbdiv hsdvdb
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
      have hcdiv : c ∣ 1365 := Nat.dvd_of_mem_divisors (hC hc)
      exact no_prime_ge17_dvd_of_dvd_1365 hr hr17 hcdiv hrdvdc
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
    have hsumRSD : RSD.sum id = r * s * 1323 := by
      dsimp [RSD]
      rw [Finset.sum_image]
      · change (∑ x ∈ (1365 : ℕ).properDivisors, (r * s) * id x) = r * s * 1323
        rw [← Finset.mul_sum, properDivisors_1365_sum]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr.pos hs.pos) hab
    rw [hsumRB, hsumSC, hsumRSD]
    nlinarith

set_option linter.style.nativeDecide false in
private theorem pp_1365_mul_mul_73_263 : Pseudoperfect (1365 * 73 * 263) := by
  refine pp_1365_mul_mul_of_cert (r := 73) (s := 263)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (A := ({5, 13, 15, 21, 35, 39, 65, 91, 105, 195, 273, 455, 1365} :
      Finset ℕ))
    (B := ({3, 5, 7, 13, 15, 21, 35, 39, 65, 91, 105, 195, 273, 455, 1365} :
      Finset ℕ))
    (C := ({1, 3, 5, 7, 13, 15, 21, 35, 39, 65, 91, 195, 455, 1365} :
      Finset ℕ)) ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

private theorem pp_1365_mul_mul_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr64 : 64 < r)
    (hr127 : r ≤ 127) (hcorr : s * (r - 64) ≤ 64 * (r + 1)) :
    Pseudoperfect (1365 * r * s) := by
  by_cases h73 : r = 73 ∧ s = 263
  · rcases h73 with ⟨rfl, rfl⟩
    exact pp_1365_mul_mul_73_263
  obtain ⟨A, B, C, hA, hB, hC, hsum⟩ :=
    cert_1365_of_corridor_nonexception hr hs hr64 hrs_lt hr127 hcorr h73
  exact pp_1365_mul_mul_of_cert hr hs (by omega) (by omega) (by omega) hA hB hC hsum

private theorem sigma_1365_mul_mul {r s : ℕ} (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hr17 : 17 ≤ r) (hs17 : 17 ≤ s) (hrs : r ≠ s) :
    (1365 * r * s).divisors.sum id = 2688 * (r + 1) * (s + 1) := by
  have hcop_1365_r : Nat.Coprime 1365 r := by
    rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
    exact prime_ge17_not_dvd_1365 hr hr17
  have hcop_1365_s : Nat.Coprime 1365 s := by
    rw [Nat.coprime_comm, hs.coprime_iff_not_dvd]
    exact prime_ge17_not_dvd_1365 hs hs17
  have hnot_r_dvd_s : ¬ r ∣ s := by
    intro hdiv
    exact hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp hdiv)
  have hcop_r_s : Nat.Coprime r s := (hr.coprime_iff_not_dvd).mpr hnot_r_dvd_s
  have hcop_1365r_s : Nat.Coprime (1365 * r) s :=
    Nat.Coprime.mul_left hcop_1365_s hcop_r_s
  have hσr : r.divisors.sum id = r + 1 := by
    simpa using sum_divisors_prime_pow_one hr
  have hσs : s.divisors.sum id = s + 1 := by
    simpa using sum_divisors_prime_pow_one hs
  have hσ1365r : (1365 * r).divisors.sum id = 2688 * (r + 1) := by
    calc
      (1365 * r).divisors.sum id =
          (1365 : ℕ).divisors.sum id * r.divisors.sum id :=
        hcop_1365_r.sum_divisors_mul
      _ = 2688 * (r + 1) := by rw [divisors_1365_sum, hσr]
  calc
    (1365 * r * s).divisors.sum id =
        (1365 * r).divisors.sum id * s.divisors.sum id :=
      hcop_1365r_s.sum_divisors_mul
    _ = (2688 * (r + 1)) * (s + 1) := by rw [hσ1365r, hσs]
    _ = 2688 * (r + 1) * (s + 1) := by ring

private theorem not_abundant_1365_mul_mul_of_ratio_lt {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) (hratio : 64 * (r + s + 1) < r * s) :
    ¬Abundant (1365 * r * s) := by
  apply not_abundant_of_sigma_lt
  rw [sigma_1365_mul_mul hr hs hr17 hs17 hrs]
  nlinarith

private theorem not_abundant_1365_mul_mul_of_outside_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) (hr64 : 64 < r)
    (hout : 64 * (r + 1) < s * (r - 64)) : ¬Abundant (1365 * r * s) := by
  apply not_abundant_1365_mul_mul_of_ratio_lt hr hs hr17 hs17 hrs
  zify [show 64 ≤ r from by omega] at hout ⊢
  nlinarith

private theorem corridor_of_abundant_1365_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) (hr64 : 64 < r) (hab : Abundant (1365 * r * s)) :
    s * (r - 64) ≤ 64 * (r + 1) := by
  by_contra hout
  have hout' : 64 * (r + 1) < s * (r - 64) := by omega
  exact not_abundant_1365_mul_mul_of_outside_corridor hr hs hr17 hs17 hrs hr64 hout' hab

private theorem first_prime_le_128_of_abundant_1365_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) (hrs_lt : r < s) (hr64 : 64 < r)
    (hab : Abundant (1365 * r * s)) : r ≤ 128 := by
  have hcorr :=
    corridor_of_abundant_1365_mul_mul hr hs hr17 hs17 hrs hr64 hab
  by_contra hle
  have hr129 : 129 ≤ r := by omega
  have hpos : 0 < r - 64 := by omega
  have hgt : r * (r - 64) < s * (r - 64) :=
    Nat.mul_lt_mul_of_pos_right hrs_lt hpos
  have hlt : r * (r - 64) < 64 * (r + 1) := lt_of_lt_of_le hgt hcorr
  zify [show 64 ≤ r from by omega] at hlt
  nlinarith

private theorem prime_le_127_of_le_128 {r : ℕ} (hr : Nat.Prime r) (hrle : r ≤ 128) :
    r ≤ 127 := by
  by_contra hle127
  have hr128 : r = 128 := by omega
  subst r
  norm_num at hr

/-- The ordered product `3*5*7*13*r*s` is not weird outside the finite
large-prime corridor

`s * (r - 64) ≤ 64 * (r + 1)`. -/
theorem not_weird_1365_mul_mul_of_ordered_outside_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr64 : 64 < r)
    (hout : 64 * (r + 1) < s * (r - 64)) : ¬Weird (1365 * r * s) := by
  intro hw
  exact not_abundant_1365_mul_mul_of_outside_corridor hr hs (by omega) (by omega)
    (by omega) hr64 hout hw.1

/-- Any weird ordered product `3*5*7*13*r*s` with `64 < r < s` must lie in the
finite large-prime corridor. -/
theorem corridor_of_weird_1365_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr64 : 64 < r)
    (hw : Weird (1365 * r * s)) :
    s * (r - 64) ≤ 64 * (r + 1) := by
  exact corridor_of_abundant_1365_mul_mul hr hs (by omega) (by omega) (by omega)
    hr64 hw.1

/-- In a weird ordered product `3*5*7*13*r*s` with `64 < r < s`, the first
extra prime is at most `127`. -/
theorem first_prime_le_127_of_weird_1365_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr64 : 64 < r)
    (hw : Weird (1365 * r * s)) : r ≤ 127 :=
  prime_le_127_of_le_128 hr
    (first_prime_le_128_of_abundant_1365_mul_mul hr hs (by omega) (by omega)
      (by omega) hrs_lt hr64 hw.1)

/-- The finite corridor for the ordered product `3*5*7*13*r*s` is completely
pseudoperfect. -/
theorem not_weird_1365_mul_mul_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr64 : 64 < r)
    (hr127 : r ≤ 127) (hcorr : s * (r - 64) ≤ 64 * (r + 1)) :
    ¬Weird (1365 * r * s) := by
  intro hw
  exact hw.2 (pp_1365_mul_mul_of_corridor hr hs hrs_lt hr64 hr127 hcorr)

/-- No prime at least `17` can divide a divisor of `2145`. -/
private theorem no_prime_ge17_dvd_of_dvd_2145 {p x : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (hx : x ∣ 2145) : ¬ p ∣ x := by
  intro hpx
  exact prime_ge17_not_dvd_2145 hp hp17 (hpx.trans hx)

private def divisor2145At : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 11
  | 4 => 13
  | 5 => 15
  | 6 => 33
  | 7 => 39
  | 8 => 55
  | 9 => 65
  | 10 => 143
  | 11 => 165
  | 12 => 195
  | 13 => 429
  | 14 => 715
  | _ => 2145

private def mask2145Set (m : ℕ) : Finset ℕ :=
  ((Finset.range 16).filter fun i => m.testBit i).image divisor2145At

private def certMasks2145 : ℕ → ℕ → ℕ × ℕ × ℕ
  | 17, 19 => (65503, 65535, 6135)
  | 17, 23 => (65527, 65535, 20428)
  | 17, 29 => (65501, 65535, 32765)
  | 17, 31 => (12151, 65535, 32768)
  | 17, 37 => (65500, 65535, 34235)
  | 17, 41 => (65530, 65535, 36342)
  | 17, 43 => (65488, 65535, 38872)
  | 17, 47 => (65279, 65535, 40826)
  | 17, 53 => (65500, 65535, 44414)
  | 17, 59 => (65530, 65535, 48093)
  | 17, 61 => (65401, 65535, 48383)
  | 17, 67 => (65503, 65535, 49134)
  | 17, 71 => (65518, 65535, 53115)
  | 17, 73 => (65518, 65535, 53214)
  | 17, 79 => (65375, 65535, 56543)
  | 17, 83 => (65470, 65535, 56791)
  | 17, 89 => (65465, 65535, 57292)
  | 17, 97 => (65499, 65535, 59326)
  | 17, 101 => (65277, 65535, 59388)
  | 17, 103 => (65272, 65535, 60406)
  | 17, 107 => (65492, 65535, 60664)
  | 17, 109 => (64983, 65535, 60790)
  | 17, 113 => (65492, 65535, 60879)
  | 17, 127 => (63450, 65535, 61402)
  | 17, 131 => (64751, 65535, 61436)
  | 17, 137 => (61306, 65535, 63480)
  | 17, 139 => (65501, 65535, 63485)
  | 17, 149 => (65519, 65535, 64751)
  | 17, 151 => (64973, 65535, 64762)
  | 17, 157 => (65405, 65535, 64892)
  | 17, 163 => (65465, 65535, 64983)
  | 17, 167 => (64959, 65535, 64991)
  | 17, 173 => (64984, 65535, 65023)
  | 17, 179 => (64990, 65535, 65398)
  | 17, 181 => (60380, 65535, 65402)
  | 17, 191 => (59357, 65535, 65496)
  | 17, 193 => (61434, 65535, 65498)
  | 17, 197 => (64991, 65535, 65518)
  | 17, 199 => (60414, 65535, 65528)
  | 19, 23 => (65510, 65535, 24314)
  | 19, 29 => (52985, 65535, 32768)
  | 19, 31 => (65528, 65535, 33244)
  | 19, 37 => (65516, 65535, 38911)
  | 19, 41 => (65470, 65535, 42970)
  | 19, 43 => (65277, 65535, 44494)
  | 19, 47 => (65004, 65535, 48376)
  | 19, 53 => (65494, 65535, 53206)
  | 19, 59 => (64894, 65535, 56830)
  | 19, 61 => (64767, 65535, 57306)
  | 19, 67 => (65407, 65535, 60637)
  | 19, 71 => (65279, 65535, 60923)
  | 19, 73 => (65400, 65535, 61311)
  | 19, 79 => (64732, 65535, 64506)
  | 19, 83 => (65401, 65535, 64957)
  | 19, 89 => (65530, 65535, 65469)
  | 23, 29 => (65390, 65535, 36302)
  | 23, 31 => (65400, 65535, 40440)
  | 23, 37 => (65519, 65535, 52696)
  | 23, 41 => (65529, 65535, 57294)
  | 23, 43 => (65274, 65535, 60408)
  | 23, 47 => (65405, 65535, 64495)
  | 29, 31 => (65275, 65535, 57306)
  | _, _ => (0, 0, 0)

private def cert2145A (r s : ℕ) : Finset ℕ :=
  mask2145Set (certMasks2145 r s).1

private def cert2145B (r s : ℕ) : Finset ℕ :=
  mask2145Set (certMasks2145 r s).2.1

private def cert2145C (r s : ℕ) : Finset ℕ :=
  mask2145Set (certMasks2145 r s).2.2

/- The `3,5,11,13` abundance corridor contains only 62 ordered prime pairs.
For each pair, `certMasks2145` supplies three divisor masks with
`A.sum + r*B.sum + s*C.sum = 258rs`. -/
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 0 in
private theorem cert_2145_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hrs : r < s)
    (hr31 : r ≤ 31) (hcorr : s * (43 * r - 672) ≤ 672 * (r + 1)) :
    ∃ A B C : Finset ℕ, A ⊆ (2145 : ℕ).divisors ∧ B ⊆ (2145 : ℕ).divisors ∧
      C ⊆ (2145 : ℕ).divisors ∧ A.sum id + r * B.sum id + s * C.sum id =
        258 * r * s := by
  have hclosed : ∀ r ∈ Finset.Icc 17 31, ∀ s ∈ Finset.Icc (r + 1) 206,
      Nat.Prime r → Nat.Prime s → s * (43 * r - 672) ≤ 672 * (r + 1) →
      cert2145A r s ⊆ (2145 : ℕ).divisors ∧ cert2145B r s ⊆ (2145 : ℕ).divisors ∧
        cert2145C r s ⊆ (2145 : ℕ).divisors ∧
          (cert2145A r s).sum id + r * (cert2145B r s).sum id +
            s * (cert2145C r s).sum id = 258 * r * s := by
    native_decide
  have hrmem : r ∈ Finset.Icc 17 31 := by
    simp [hr17, hr31]
  have hsle : s ≤ 206 := by
    have hden_pos : 0 < 43 * r - 672 := by omega
    have hnum : 672 * (r + 1) ≤ 206 * (43 * r - 672) := by
      zify [show 672 ≤ 43 * r from by nlinarith]
      nlinarith
    have hprod : s * (43 * r - 672) ≤ 206 * (43 * r - 672) := le_trans hcorr hnum
    exact Nat.le_of_mul_le_mul_right hprod hden_pos
  have hsge : r + 1 ≤ s := by omega
  have hsmem : s ∈ Finset.Icc (r + 1) 206 := by
    simp [hsge, hsle]
  exact ⟨cert2145A r s, cert2145B r s, cert2145C r s,
    hclosed r hrmem s hsmem hr hs hcorr⟩

/-- A certificate lemma for the finite `3,5,11,13` branch.

If `A + rB + sC = 258rs`, where `A`, `B`, and `C` are subset sums of divisors
of `2145`, then `2145*r*s` is pseudoperfect. -/
private theorem pp_2145_mul_mul_of_cert {r s : ℕ} (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hr17 : 17 ≤ r) (hs17 : 17 ≤ s) (hrs : r ≠ s)
    {A B C : Finset ℕ} (hA : A ⊆ (2145 : ℕ).divisors)
    (hB : B ⊆ (2145 : ℕ).divisors) (hC : C ⊆ (2145 : ℕ).divisors)
    (hsum : A.sum id + r * B.sum id + s * C.sum id = 258 * r * s) :
    Pseudoperfect (2145 * r * s) := by
  let RB := B.image fun d => r * d
  let SC := C.image fun d => s * d
  let RSD := (2145 : ℕ).properDivisors.image fun d => (r * s) * d
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
        · have hxdiv : x ∣ 2145 := Nat.dvd_of_mem_divisors (hA hxA)
          rw [Nat.mem_properDivisors]
          refine ⟨?_, ?_⟩
          · exact hxdiv.trans ((dvd_mul_right 2145 r).trans (dvd_mul_right (2145 * r) s))
          · have hxle : x ≤ 2145 := Nat.le_of_dvd (by norm_num) hxdiv
            have hrgt : 1 < r := lt_of_lt_of_le (by norm_num : 1 < 17) hr17
            have hsgt : 1 < s := lt_of_lt_of_le (by norm_num : 1 < 17) hs17
            nlinarith
        · rw [Finset.mem_image] at hxRB
          rcases hxRB with ⟨d, hd, rfl⟩
          have hddiv : d ∣ 2145 := Nat.dvd_of_mem_divisors (hB hd)
          rw [Nat.mem_properDivisors]
          refine ⟨?_, ?_⟩
          · rcases hddiv with ⟨k, hk⟩
            use k * s
            rw [hk]
            ring
          · have hdle : d ≤ 2145 := Nat.le_of_dvd (by norm_num) hddiv
            have hsgt : 1 < s := lt_of_lt_of_le (by norm_num : 1 < 17) hs17
            nlinarith [hr.pos]
      · rw [Finset.mem_image] at hxSC
        rcases hxSC with ⟨d, hd, rfl⟩
        have hddiv : d ∣ 2145 := Nat.dvd_of_mem_divisors (hC hd)
        rw [Nat.mem_properDivisors]
        refine ⟨?_, ?_⟩
        · rcases hddiv with ⟨k, hk⟩
          use k * r
          rw [hk]
          ring
        · have hdle : d ≤ 2145 := Nat.le_of_dvd (by norm_num) hddiv
          have hrgt : 1 < r := lt_of_lt_of_le (by norm_num : 1 < 17) hr17
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
      have hxdiv : x ∣ 2145 := Nat.dvd_of_mem_divisors (hA hxA)
      have hrdvdx : r ∣ x := by
        rw [← hxb]
        exact dvd_mul_right r b
      exact no_prime_ge17_dvd_of_dvd_2145 hr hr17 hxdiv hrdvdx
    have hA_SC : Disjoint A SC := by
      rw [Finset.disjoint_left]
      intro x hxA hxSC
      rw [Finset.mem_image] at hxSC
      rcases hxSC with ⟨c, _hc, hxc⟩
      have hxdiv : x ∣ 2145 := Nat.dvd_of_mem_divisors (hA hxA)
      have hsdvdx : s ∣ x := by
        rw [← hxc]
        exact dvd_mul_right s c
      exact no_prime_ge17_dvd_of_dvd_2145 hs hs17 hxdiv hsdvdx
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
      have hcdiv : c ∣ 2145 := Nat.dvd_of_mem_divisors (hC hc)
      exact no_prime_ge17_dvd_of_dvd_2145 hr hr17 hcdiv hrdvdc
    have hA_RSD : Disjoint A RSD := by
      rw [Finset.disjoint_left]
      intro x hxA hxD
      rw [Finset.mem_image] at hxD
      rcases hxD with ⟨d, _hd, hxd⟩
      have hxdiv : x ∣ 2145 := Nat.dvd_of_mem_divisors (hA hxA)
      have hrdvdx : r ∣ x := by
        rw [← hxd]
        use s * d
        ring
      exact no_prime_ge17_dvd_of_dvd_2145 hr hr17 hxdiv hrdvdx
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
      have hbdiv : b ∣ 2145 := Nat.dvd_of_mem_divisors (hB hb)
      exact no_prime_ge17_dvd_of_dvd_2145 hs hs17 hbdiv hsdvdb
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
      have hcdiv : c ∣ 2145 := Nat.dvd_of_mem_divisors (hC hc)
      exact no_prime_ge17_dvd_of_dvd_2145 hr hr17 hcdiv hrdvdc
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
    have hsumRSD : RSD.sum id = r * s * 1887 := by
      dsimp [RSD]
      rw [Finset.sum_image]
      · change (∑ x ∈ (2145 : ℕ).properDivisors, (r * s) * id x) = r * s * 1887
        rw [← Finset.mul_sum, properDivisors_2145_sum]
      · intro a _ha b _hb hab
        exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr.pos hs.pos) hab
    rw [hsumRB, hsumSC, hsumRSD]
    nlinarith

private theorem pp_2145_mul_mul_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr17 : 17 ≤ r)
    (hr31 : r ≤ 31) (hcorr : s * (43 * r - 672) ≤ 672 * (r + 1)) :
    Pseudoperfect (2145 * r * s) := by
  obtain ⟨A, B, C, hA, hB, hC, hsum⟩ :=
    cert_2145_of_corridor hr hs hr17 hrs_lt hr31 hcorr
  exact pp_2145_mul_mul_of_cert hr hs hr17 (by omega) (by omega) hA hB hC hsum

private theorem sigma_2145_mul_mul {r s : ℕ} (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hr17 : 17 ≤ r) (hs17 : 17 ≤ s) (hrs : r ≠ s) :
    (2145 * r * s).divisors.sum id = 4032 * (r + 1) * (s + 1) := by
  have hcop_2145_r : Nat.Coprime 2145 r := by
    rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
    exact prime_ge17_not_dvd_2145 hr hr17
  have hcop_2145_s : Nat.Coprime 2145 s := by
    rw [Nat.coprime_comm, hs.coprime_iff_not_dvd]
    exact prime_ge17_not_dvd_2145 hs hs17
  have hnot_r_dvd_s : ¬ r ∣ s := by
    intro hdiv
    exact hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp hdiv)
  have hcop_r_s : Nat.Coprime r s := (hr.coprime_iff_not_dvd).mpr hnot_r_dvd_s
  have hcop_2145r_s : Nat.Coprime (2145 * r) s :=
    Nat.Coprime.mul_left hcop_2145_s hcop_r_s
  have hσr : r.divisors.sum id = r + 1 := by
    simpa using sum_divisors_prime_pow_one hr
  have hσs : s.divisors.sum id = s + 1 := by
    simpa using sum_divisors_prime_pow_one hs
  have hσ2145r : (2145 * r).divisors.sum id = 4032 * (r + 1) := by
    calc
      (2145 * r).divisors.sum id =
          (2145 : ℕ).divisors.sum id * r.divisors.sum id :=
        hcop_2145_r.sum_divisors_mul
      _ = 4032 * (r + 1) := by rw [divisors_2145_sum, hσr]
  calc
    (2145 * r * s).divisors.sum id =
        (2145 * r).divisors.sum id * s.divisors.sum id :=
      hcop_2145r_s.sum_divisors_mul
    _ = (4032 * (r + 1)) * (s + 1) := by rw [hσ2145r, hσs]
    _ = 4032 * (r + 1) * (s + 1) := by ring

private theorem not_abundant_2145_mul_mul_of_ratio_lt {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) (hratio : 672 * (r + s + 1) < 43 * r * s) :
    ¬Abundant (2145 * r * s) := by
  apply not_abundant_of_sigma_lt
  rw [sigma_2145_mul_mul hr hs hr17 hs17 hrs]
  nlinarith

private theorem not_abundant_2145_mul_mul_of_outside_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) (hout : 672 * (r + 1) < s * (43 * r - 672)) :
    ¬Abundant (2145 * r * s) := by
  apply not_abundant_2145_mul_mul_of_ratio_lt hr hs hr17 hs17 hrs
  zify [show 672 ≤ 43 * r from by nlinarith] at hout ⊢
  nlinarith

private theorem corridor_of_abundant_2145_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) (hab : Abundant (2145 * r * s)) :
    s * (43 * r - 672) ≤ 672 * (r + 1) := by
  by_contra hout
  have hout' : 672 * (r + 1) < s * (43 * r - 672) := by omega
  exact not_abundant_2145_mul_mul_of_outside_corridor hr hs hr17 hs17 hrs hout' hab

private theorem first_prime_le_31_of_abundant_2145_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) (hrs_lt : r < s) (hab : Abundant (2145 * r * s)) : r ≤ 31 := by
  have hcorr := corridor_of_abundant_2145_mul_mul hr hs hr17 hs17 hrs hab
  by_contra hle
  have hr32 : 32 ≤ r := by omega
  have hpos : 0 < 43 * r - 672 := by omega
  have hgt : r * (43 * r - 672) < s * (43 * r - 672) :=
    Nat.mul_lt_mul_of_pos_right hrs_lt hpos
  have hlt : r * (43 * r - 672) < 672 * (r + 1) := lt_of_lt_of_le hgt hcorr
  zify [show 672 ≤ 43 * r from by nlinarith] at hlt
  nlinarith

/-- Any weird ordered product `3*5*11*13*r*s` with `17 ≤ r < s` must lie in
the finite large-prime corridor. -/
theorem corridor_of_weird_2145_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hrs_lt : r < s)
    (hw : Weird (2145 * r * s)) :
    s * (43 * r - 672) ≤ 672 * (r + 1) :=
  corridor_of_abundant_2145_mul_mul hr hs hr17 (by omega) (by omega) hw.1

/-- In a weird ordered product `3*5*11*13*r*s` with `17 ≤ r < s`, the first
extra prime is at most `31`. -/
theorem first_prime_le_31_of_weird_2145_mul_mul {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hrs_lt : r < s)
    (hw : Weird (2145 * r * s)) : r ≤ 31 :=
  first_prime_le_31_of_abundant_2145_mul_mul hr hs hr17 (by omega) (by omega)
    hrs_lt hw.1

/-- The finite corridor for the ordered product `3*5*11*13*r*s` is completely
pseudoperfect. -/
theorem not_weird_2145_mul_mul_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hr17 : 17 ≤ r) (hrs_lt : r < s)
    (hr31 : r ≤ 31) (hcorr : s * (43 * r - 672) ≤ 672 * (r + 1)) :
    ¬Weird (2145 * r * s) := by
  intro hw
  exact hw.2 (pp_2145_mul_mul_of_corridor hr hs hrs_lt hr17 hr31 hcorr)

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

set_option linter.style.nativeDecide false in
private theorem pp_1155_mul_mul_491_883 : Pseudoperfect (1155 * 491 * 883) := by
  refine pp_1155_mul_mul_of_cert (r := 491) (s := 883)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (A := ({3, 5, 11, 21, 33, 35, 55, 105, 165, 231} : Finset ℕ))
    (B := ({1155} : Finset ℕ))
    (C := ({3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155} :
      Finset ℕ)) ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

set_option linter.style.nativeDecide false in
private theorem pp_1155_mul_mul_557_619 : Pseudoperfect (1155 * 557 * 619) := by
  refine pp_1155_mul_mul_of_cert (r := 557) (s := 619)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (A := ({1, 3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 165, 231, 385} :
      Finset ℕ))
    (B := ({1155} : Finset ℕ))
    (C := ({1, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155} :
      Finset ℕ)) ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

set_option linter.style.nativeDecide false in
private theorem pp_1155_mul_mul_571_587 : Pseudoperfect (1155 * 571 * 587) := by
  refine pp_1155_mul_mul_of_cert (r := 571) (s := 587)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (A := ({3, 11, 15, 21, 33, 55, 77, 105, 165, 385} : Finset ℕ))
    (B := ({1155} : Finset ℕ))
    (C := ({1, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155} :
      Finset ℕ)) ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

private theorem pp_1155_mul_mul_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr384 : 384 < r)
    (hr761 : r ≤ 761) (hcorr : s * (r - 384) ≤ 384 * (r + 1)) :
    Pseudoperfect (1155 * r * s) := by
  by_cases h491 : r = 491 ∧ s = 883
  · rcases h491 with ⟨rfl, rfl⟩
    exact pp_1155_mul_mul_491_883
  by_cases h557 : r = 557 ∧ s = 619
  · rcases h557 with ⟨rfl, rfl⟩
    exact pp_1155_mul_mul_557_619
  by_cases h571 : r = 571 ∧ s = 587
  · rcases h571 with ⟨rfl, rfl⟩
    exact pp_1155_mul_mul_571_587
  obtain ⟨A, B, C, hA, hB, hC, hsum⟩ :=
    cert_1155_of_corridor_nonexception hr hs hr384 hrs_lt hr761 hcorr h491 h557 h571
  exact pp_1155_mul_mul_of_cert hr hs (by omega) (by omega) (by omega) hA hB hC hsum

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

/-- The product of the five-prime core `3,5,7,13,r` is `1365 * r`. -/
private theorem prod_3_5_7_13_r {r : ℕ} (hr17 : 17 ≤ r) :
    (∏ p ∈ ({3, 5, 7, 13, r} : Finset ℕ), p) = 1365 * r := by
  have h3r : 3 ≠ r := by omega
  have h5r : 5 ≠ r := by omega
  have h7r : 7 ≠ r := by omega
  have h13r : 13 ≠ r := by omega
  rw [Finset.prod_insert]
  · rw [Finset.prod_insert]
    · rw [Finset.prod_insert]
      · rw [Finset.prod_insert]
        · rw [Finset.prod_singleton]
          ring
        · simp [h13r]
      · simp [h7r]
    · simp [h5r]
  · simp [h3r]

/-- The product of the six-prime core `3,5,7,13,r,s` is `1365*r*s`,
provided the two extra primes are at least `17` and distinct. -/
private theorem prod_3_5_7_13_r_s {r s : ℕ} (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) :
    (∏ p ∈ ({3, 5, 7, 13, r, s} : Finset ℕ), p) = 1365 * r * s := by
  have h3r : 3 ≠ r := by omega
  have h3s : 3 ≠ s := by omega
  have h5r : 5 ≠ r := by omega
  have h5s : 5 ≠ s := by omega
  have h7r : 7 ≠ r := by omega
  have h7s : 7 ≠ s := by omega
  have h13r : 13 ≠ r := by omega
  have h13s : 13 ≠ s := by omega
  rw [Finset.prod_insert]
  · rw [Finset.prod_insert]
    · rw [Finset.prod_insert]
      · rw [Finset.prod_insert]
        · rw [Finset.prod_insert]
          · rw [Finset.prod_singleton]
            ring
          · simp [hrs]
        · simp [h13r, h13s]
      · simp [h7r, h7s]
    · simp [h5r, h5s]
  · simp [h3r, h3s]

/-- The product of the six-prime core `3,5,11,13,r,s` is `2145*r*s`,
provided the two extra primes are at least `17` and distinct. -/
private theorem prod_3_5_11_13_r_s {r s : ℕ} (hr17 : 17 ≤ r) (hs17 : 17 ≤ s)
    (hrs : r ≠ s) :
    (∏ p ∈ ({3, 5, 11, 13, r, s} : Finset ℕ), p) = 2145 * r * s := by
  have h3r : 3 ≠ r := by omega
  have h3s : 3 ≠ s := by omega
  have h5r : 5 ≠ r := by omega
  have h5s : 5 ≠ s := by omega
  have h11r : 11 ≠ r := by omega
  have h11s : 11 ≠ s := by omega
  have h13r : 13 ≠ r := by omega
  have h13s : 13 ≠ s := by omega
  rw [Finset.prod_insert]
  · rw [Finset.prod_insert]
    · rw [Finset.prod_insert]
      · rw [Finset.prod_insert]
        · rw [Finset.prod_insert]
          · rw [Finset.prod_singleton]
            ring
          · simp [hrs]
        · simp [h13r, h13s]
      · simp [h11r, h11s]
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

/-- In the `3,5,7,13` branch with no extra `11`, any extra prime
`17 ≤ r ≤ 61` makes the candidate pseudoperfect, hence not weird. This is the
small-prime side of the next squarefree six-prime branch. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_7_13_small_extra {n r : ℕ}
    (hsq : Squarefree n) (hr : Nat.Prime r) (hr17 : 17 ≤ r) (hr61 : r ≤ 61)
    (hsubset : ({3, 5, 7, 13, r} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    rw [prod_3_5_7_13_r hr17]
    exact pp_1365_mul_of_small_prime hr hr17 hr61)

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

/-- The finite corridor for the ordered product `3*5*7*11*r*s` is completely
pseudoperfect. This closes the product-level `3,5,7,11` branch: outside the
corridor the product is not abundant, and inside it the product is
pseudoperfect. -/
theorem not_weird_1155_mul_mul_of_corridor {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs_lt : r < s) (hr384 : 384 < r)
    (hr761 : r ≤ 761) (hcorr : s * (r - 384) ≤ 384 * (r + 1)) :
    ¬Weird (1155 * r * s) := by
  intro hw
  exact hw.2 (pp_1155_mul_mul_of_corridor hr hs hrs_lt hr384 hr761 hcorr)

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

/-- The pseudoperfect core `3 * 5 * 11 * 17 * 19 * 23` rules out every
squarefree weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_11_17_19_23 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 11, 17, 19, 23} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_1225785)

/-- The pseudoperfect core `3 * 5 * 11 * 17 * 19 * 29` rules out every
squarefree weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_11_17_19_29 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 11, 17, 19, 29} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_1545555)

/-- The pseudoperfect core `3 * 5 * 11 * 17 * 19 * 31` rules out every
squarefree weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_11_17_19_31 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 11, 17, 19, 31} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_1652145)

/-- The pseudoperfect core `3 * 5 * 13 * 17 * 19 * 23` rules out every
squarefree weird multiple of it. -/
theorem not_weird_of_squarefree_primeFactors_contains_3_5_13_17_19_23 {n : ℕ}
    (hsq : Squarefree n)
    (hsubset : ({3, 5, 13, 17, 19, 23} : Finset ℕ) ⊆ n.primeFactors) : ¬Weird n :=
  not_weird_squarefree_of_pseudoperfect_primeFactors_subset hsq hsubset (by
    simpa using pp_1448655)

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
  have hfact := Nat.prod_factorization_pow_eq_self hn
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
  push Not at h
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
  push Not at h
  have hp_two_le := hp.two_le
  have hp_ne_four : p ≠ 4 := by intro hp4; subst hp4; norm_num at hp
  have hp_ne_six : p ≠ 6 := by intro hp6; subst hp6; norm_num at hp
  omega

/-- A prime at least `7`, but not `7`, is at least `11`. -/
private theorem prime_ge_eleven_of_ge_seven_ne_seven {p : ℕ} (hp : Nat.Prime p)
    (hp7 : 7 ≤ p) (hp_ne_seven : p ≠ 7) : 11 ≤ p := by
  by_contra h
  push Not at h
  have hp_ne_eight : p ≠ 8 := by intro hp8; subst hp8; norm_num at hp
  have hp_ne_nine : p ≠ 9 := by intro hp9; subst hp9; norm_num at hp
  have hp_ne_ten : p ≠ 10 := by intro hp10; subst hp10; norm_num at hp
  omega

/-- A prime at least `11`, but not `11`, is at least `13`. -/
private theorem prime_ge_thirteen_of_ge_eleven_ne_eleven {p : ℕ} (hp : Nat.Prime p)
    (hp11 : 11 ≤ p) (hp_ne_eleven : p ≠ 11) : 13 ≤ p := by
  by_contra h
  push Not at h
  have hp_ne_twelve : p ≠ 12 := by intro hp12; subst hp12; norm_num at hp
  omega

/-- A prime at least `13`, but not `13`, is at least `17`. -/
private theorem prime_ge_seventeen_of_ge_thirteen_ne_thirteen {p : ℕ} (hp : Nat.Prime p)
    (hp13 : 13 ≤ p) (hp_ne_thirteen : p ≠ 13) : 17 ≤ p := by
  by_contra h
  push Not at h
  have hp_ne_fourteen : p ≠ 14 := by intro hp14; subst hp14; norm_num at hp
  have hp_ne_fifteen : p ≠ 15 := by intro hp15; subst hp15; norm_num at hp
  have hp_ne_sixteen : p ≠ 16 := by intro hp16; subst hp16; norm_num at hp
  omega

/-- A prime at least `17`, but not `17`, is at least `19`. -/
private theorem prime_ge_nineteen_of_ge_seventeen_ne_seventeen {p : ℕ} (hp : Nat.Prime p)
    (hp17 : 17 ≤ p) (hp_ne_seventeen : p ≠ 17) : 19 ≤ p := by
  by_contra h
  push Not at h
  have hp_ne_eighteen : p ≠ 18 := by intro hp18; subst hp18; norm_num at hp
  omega

/-- A prime at least `19`, but not `19`, is at least `23`. -/
private theorem prime_ge_twentythree_of_ge_nineteen_ne_nineteen {p : ℕ} (hp : Nat.Prime p)
    (hp19 : 19 ≤ p) (hp_ne_nineteen : p ≠ 19) : 23 ≤ p := by
  by_contra h
  push Not at h
  have hp_ne_twenty : p ≠ 20 := by intro hp20; subst hp20; norm_num at hp
  have hp_ne_twentyone : p ≠ 21 := by intro hp21; subst hp21; norm_num at hp
  have hp_ne_twentytwo : p ≠ 22 := by intro hp22; subst hp22; norm_num at hp
  omega

/-- A prime at least `23`, but not `23`, is at least `29`. -/
private theorem prime_ge_twentynine_of_ge_twentythree_ne_twentythree {p : ℕ} (hp : Nat.Prime p)
    (hp23 : 23 ≤ p) (hp_ne_twentythree : p ≠ 23) : 29 ≤ p := by
  by_contra h
  push Not at h
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
  push Not at h
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
  have h5R0 : 5 ∈ n.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by norm_num, h5⟩
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
  push Not at h
  have hthree : 3 ≤ n.primeFactors.card := odd_weird_three_prime_factors hw hodd
  have hcard : n.primeFactors.card = 3 := by omega
  have hn : n ≠ 0 := Nat.ne_of_gt hw.1.1
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
  have hcop_pq_s : Nat.Coprime (p ^ a * q ^ b) (s ^ d) := Nat.Coprime.mul_left hcop_p_s hcop_q_s
  have hcop_pqr_s : Nat.Coprime (p ^ a * q ^ b * r ^ c) (s ^ d) :=
    Nat.Coprime.mul_left hcop_pq_s hcop_r_s
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
    have hfact := Nat.prod_factorization_pow_eq_self hn
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
  have hn : n ≠ 0 := Nat.ne_of_gt hw.1.1
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

/-- The exact squarefree ratio bound for lower bounds `3,5,13,17,19,29`. -/
private theorem squarefree_six_ratio_3_5_13_17_19_29_lt (p0 p1 p2 p3 p4 p5 : ℕ)
    (hp0 : 3 ≤ p0) (hp1 : 5 ≤ p1) (hp2 : 13 ≤ p2)
    (hp3 : 17 ≤ p3) (hp4 : 19 ≤ p4) (hp5 : 29 ≤ p5) :
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
  have h2 : 13 * A2 ≤ 14 * B2 := by dsimp [A2, B2]; nlinarith
  have h3 : 17 * A3 ≤ 18 * B3 := by dsimp [A3, B3]; nlinarith
  have h4 : 19 * A4 ≤ 20 * B4 := by dsimp [A4, B4]; nlinarith
  have h5 : 29 * A5 ≤ 30 * B5 := by dsimp [A5, B5]; nlinarith
  have hchain :
      (3 * A0) * (5 * A1) * (13 * A2) * (17 * A3) * (19 * A4) * (29 * A5) ≤
        (4 * B0) * (6 * B1) * (14 * B2) * (18 * B3) * (20 * B4) * (30 * B5) := by
    gcongr
  have hscaled : 1826565 * (A0 * A1 * A2 * A3 * A4 * A5) ≤
      3628800 * (B0 * B1 * B2 * B3 * B4 * B5) := by
    calc
      1826565 * (A0 * A1 * A2 * A3 * A4 * A5)
          = (3 * A0) * (5 * A1) * (13 * A2) * (17 * A3) * (19 * A4) *
              (29 * A5) := by
            ring
      _ ≤ (4 * B0) * (6 * B1) * (14 * B2) * (18 * B3) * (20 * B4) *
          (30 * B5) :=
        hchain
      _ = 3628800 * (B0 * B1 * B2 * B3 * B4 * B5) := by ring
  have hBpos : 0 < B0 * B1 * B2 * B3 * B4 * B5 := by
    dsimp [B0, B1, B2, B3, B4, B5]
    positivity
  have hceil : 3628800 * (B0 * B1 * B2 * B3 * B4 * B5) <
      1826565 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) := by
    have hconst : 3628800 < 1826565 * 2 := by norm_num
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_right hconst hBpos
  have hscaled' : 1826565 * (A0 * A1 * A2 * A3 * A4 * A5) <
      1826565 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) :=
    lt_of_le_of_lt hscaled hceil
  have hlt : A0 * A1 * A2 * A3 * A4 * A5 <
      2 * (B0 * B1 * B2 * B3 * B4 * B5) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 1826565)).mp hscaled'
  simpa [A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5] using hlt

/-- The exact squarefree ratio bound for lower bounds `3,5,11,17,19,37`. -/
private theorem squarefree_six_ratio_3_5_11_17_19_37_lt (p0 p1 p2 p3 p4 p5 : ℕ)
    (hp0 : 3 ≤ p0) (hp1 : 5 ≤ p1) (hp2 : 11 ≤ p2)
    (hp3 : 17 ≤ p3) (hp4 : 19 ≤ p4) (hp5 : 37 ≤ p5) :
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
  have h2 : 11 * A2 ≤ 12 * B2 := by dsimp [A2, B2]; nlinarith
  have h3 : 17 * A3 ≤ 18 * B3 := by dsimp [A3, B3]; nlinarith
  have h4 : 19 * A4 ≤ 20 * B4 := by dsimp [A4, B4]; nlinarith
  have h5 : 37 * A5 ≤ 38 * B5 := by dsimp [A5, B5]; nlinarith
  have hchain :
      (3 * A0) * (5 * A1) * (11 * A2) * (17 * A3) * (19 * A4) * (37 * A5) ≤
        (4 * B0) * (6 * B1) * (12 * B2) * (18 * B3) * (20 * B4) * (38 * B5) := by
    gcongr
  have hscaled : 1971915 * (A0 * A1 * A2 * A3 * A4 * A5) ≤
      3939840 * (B0 * B1 * B2 * B3 * B4 * B5) := by
    calc
      1971915 * (A0 * A1 * A2 * A3 * A4 * A5)
          = (3 * A0) * (5 * A1) * (11 * A2) * (17 * A3) * (19 * A4) *
              (37 * A5) := by
            ring
      _ ≤ (4 * B0) * (6 * B1) * (12 * B2) * (18 * B3) * (20 * B4) *
          (38 * B5) :=
        hchain
      _ = 3939840 * (B0 * B1 * B2 * B3 * B4 * B5) := by ring
  have hBpos : 0 < B0 * B1 * B2 * B3 * B4 * B5 := by
    dsimp [B0, B1, B2, B3, B4, B5]
    positivity
  have hceil : 3939840 * (B0 * B1 * B2 * B3 * B4 * B5) <
      1971915 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) := by
    have hconst : 3939840 < 1971915 * 2 := by norm_num
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_right hconst hBpos
  have hscaled' : 1971915 * (A0 * A1 * A2 * A3 * A4 * A5) <
      1971915 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) :=
    lt_of_le_of_lt hscaled hceil
  have hlt : A0 * A1 * A2 * A3 * A4 * A5 <
      2 * (B0 * B1 * B2 * B3 * B4 * B5) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 1971915)).mp hscaled'
  simpa [A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5] using hlt

/-- The exact squarefree ratio bound for lower bounds `3,5,11,17,23,29`. -/
private theorem squarefree_six_ratio_3_5_11_17_23_29_lt (p0 p1 p2 p3 p4 p5 : ℕ)
    (hp0 : 3 ≤ p0) (hp1 : 5 ≤ p1) (hp2 : 11 ≤ p2)
    (hp3 : 17 ≤ p3) (hp4 : 23 ≤ p4) (hp5 : 29 ≤ p5) :
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
  have h2 : 11 * A2 ≤ 12 * B2 := by dsimp [A2, B2]; nlinarith
  have h3 : 17 * A3 ≤ 18 * B3 := by dsimp [A3, B3]; nlinarith
  have h4 : 23 * A4 ≤ 24 * B4 := by dsimp [A4, B4]; nlinarith
  have h5 : 29 * A5 ≤ 30 * B5 := by dsimp [A5, B5]; nlinarith
  have hchain :
      (3 * A0) * (5 * A1) * (11 * A2) * (17 * A3) * (23 * A4) * (29 * A5) ≤
        (4 * B0) * (6 * B1) * (12 * B2) * (18 * B3) * (24 * B4) * (30 * B5) := by
    gcongr
  have hscaled : 1870935 * (A0 * A1 * A2 * A3 * A4 * A5) ≤
      3732480 * (B0 * B1 * B2 * B3 * B4 * B5) := by
    calc
      1870935 * (A0 * A1 * A2 * A3 * A4 * A5)
          = (3 * A0) * (5 * A1) * (11 * A2) * (17 * A3) * (23 * A4) *
              (29 * A5) := by
            ring
      _ ≤ (4 * B0) * (6 * B1) * (12 * B2) * (18 * B3) * (24 * B4) *
          (30 * B5) :=
        hchain
      _ = 3732480 * (B0 * B1 * B2 * B3 * B4 * B5) := by ring
  have hBpos : 0 < B0 * B1 * B2 * B3 * B4 * B5 := by
    dsimp [B0, B1, B2, B3, B4, B5]
    positivity
  have hceil : 3732480 * (B0 * B1 * B2 * B3 * B4 * B5) <
      1870935 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) := by
    have hconst : 3732480 < 1870935 * 2 := by norm_num
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_right hconst hBpos
  have hscaled' : 1870935 * (A0 * A1 * A2 * A3 * A4 * A5) <
      1870935 * (2 * (B0 * B1 * B2 * B3 * B4 * B5)) :=
    lt_of_le_of_lt hscaled hceil
  have hlt : A0 * A1 * A2 * A3 * A4 * A5 <
      2 * (B0 * B1 * B2 * B3 * B4 * B5) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 1870935)).mp hscaled'
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
      have hfact := Nat.prod_factorization_pow_eq_self hn
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
  have hn : n ≠ 0 := Nat.ne_of_gt hw.1.1
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
      have hfact := Nat.prod_factorization_pow_eq_self hn
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
  have hn : n ≠ 0 := Nat.ne_of_gt hw.1.1
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
      have hfact := Nat.prod_factorization_pow_eq_self hn
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
  push Not at hnone
  have hn : n ≠ 0 := Nat.ne_of_gt hw.1.1
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

/-- **The `3,5,7,11` branch of the squarefree six-prime frontier is empty.**

Any squarefree odd weird number with exactly six prime factors and containing
`3,5,7,11` would reduce to the finite corridor above, but every product in
that corridor is pseudoperfect. -/
theorem not_weird_of_squarefree_six_primeFactors_contains_3_5_7_11 {n : ℕ}
    (hodd : ¬Even n) (hcard : n.primeFactors.card = 6) (hsq : Squarefree n)
    (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h7 : 7 ∈ n.primeFactors) (h11 : 11 ∈ n.primeFactors) : ¬Weird n := by
  intro hw
  obtain ⟨r, s, hr, hs, hr384, hrs, hcorr, hr761, hn⟩ :=
    squarefree_six_3_5_7_11_frontier_corridor hw hodd hcard hsq h3 h5 h7 h11
  have hwprod : Weird (1155 * r * s) := by
    simpa [hn] using hw
  exact not_weird_1155_mul_mul_of_corridor hr hs hrs hr384 hr761 hcorr hwprod

/-- Squarefree six-prime candidates in the `3,5,7,13` branch with no `11`
reduce to a finite corridor.

If an odd squarefree weird number has exactly six prime factors, contains
`3,5,7,13`, and avoids `11`, then its two remaining prime factors can be
written as `64 < r < s`, with

`s * (r - 64) ≤ 64 * (r + 1)`

and in fact `r ≤ 127`. -/
theorem squarefree_six_3_5_7_13_frontier_corridor {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h7 : 7 ∈ n.primeFactors) (h13 : 13 ∈ n.primeFactors)
    (hno11 : 11 ∉ n.primeFactors) :
    ∃ r s : ℕ,
      Nat.Prime r ∧ Nat.Prime s ∧ 64 < r ∧ r < s ∧
        s * (r - 64) ≤ 64 * (r + 1) ∧ r ≤ 127 ∧ n = 1365 * r * s := by
  let B : Finset ℕ := {3, 5, 7, 13}
  have hBsub : B ⊆ n.primeFactors := by
    intro p hp
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h13
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
  have ha_ne13 : a ≠ 13 := by intro h; exact ha_notB (by simp [B, h])
  have hb_ne3 : b ≠ 3 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne5 : b ≠ 5 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne7 : b ≠ 7 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne13 : b ≠ 13 := by intro h; exact hb_notB (by simp [B, h])
  have ha_ne11 : a ≠ 11 := by intro h; exact hno11 (h ▸ ha_mem)
  have hb_ne11 : b ≠ 11 := by intro h; exact hno11 (h ▸ hb_mem)
  have ha_ge17 : 17 ≤ a :=
    prime_factor_ge_seventeen_of_not_small hodd ha_mem ha_ne3 ha_ne5 ha_ne7 ha_ne11 ha_ne13
  have hb_ge17 : 17 ≤ b :=
    prime_factor_ge_seventeen_of_not_small hodd hb_mem hb_ne3 hb_ne5 hb_ne7 hb_ne11 hb_ne13
  have hasubset : ({3, 5, 7, 13, a} : Finset ℕ) ⊆ n.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h13
    · exact ha_mem
  have hbsubset : ({3, 5, 7, 13, b} : Finset ℕ) ⊆ n.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h13
    · exact hb_mem
  have ha64 : 64 < a := by
    by_contra hle64
    have ha61 : a ≤ 61 := by
      by_contra hle61
      push Not at hle61
      have hacases : a = 62 ∨ a = 63 ∨ a = 64 := by omega
      rcases hacases with rfl | rfl | rfl <;> norm_num at ha_prime
    exact (not_weird_of_squarefree_primeFactors_contains_3_5_7_13_small_extra
      hsq ha_prime ha_ge17 ha61 hasubset) hw
  have hb64 : 64 < b := by
    by_contra hle64
    have hb61 : b ≤ 61 := by
      by_contra hle61
      push Not at hle61
      have hbcases : b = 62 ∨ b = 63 ∨ b = 64 := by omega
      rcases hbcases with rfl | rfl | rfl <;> norm_num at hb_prime
    exact (not_weird_of_squarefree_primeFactors_contains_3_5_7_13_small_extra
      hsq hb_prime hb_ge17 hb61 hbsubset) hw
  have hpf : n.primeFactors = ({3, 5, 7, 13, a, b} : Finset ℕ) := by
    ext p
    constructor
    · intro hp
      by_cases hpB : p ∈ B
      · have hpbase : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 := by
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
      · exact h13
      · exact ha_mem
      · exact hb_mem
  have hnprod : n = 1365 * a * b := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf,
      prod_3_5_7_13_r_s ha_ge17 hb_ge17 hab]
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · have hwprod : Weird (1365 * a * b) := by simpa [hnprod] using hw
    refine ⟨a, b, ha_prime, hb_prime, ha64, hab_lt,
      corridor_of_weird_1365_mul_mul ha_prime hb_prime hab_lt ha64 hwprod,
      first_prime_le_127_of_weird_1365_mul_mul ha_prime hb_prime hab_lt ha64 hwprod,
      hnprod⟩
  · have hnprod' : n = 1365 * b * a := by
      rw [hnprod]
      ring
    have hwprod : Weird (1365 * b * a) := by simpa [hnprod'] using hw
    refine ⟨b, a, hb_prime, ha_prime, hb64, hba_lt,
      corridor_of_weird_1365_mul_mul hb_prime ha_prime hba_lt hb64 hwprod,
      first_prime_le_127_of_weird_1365_mul_mul hb_prime ha_prime hba_lt hb64 hwprod,
      hnprod'⟩

/-- **The `3,5,7,13` branch of the squarefree six-prime frontier is empty.**

The case with an additional factor `11` was already closed by the `3,5,7,11`
branch. In the remaining case the two extra primes are at least `17`; small
extra primes make the five-prime core pseudoperfect, while the large-prime
candidates reduce to the finite `1365` corridor, which is also pseudoperfect. -/
theorem not_weird_of_squarefree_six_primeFactors_contains_3_5_7_13 {n : ℕ}
    (hodd : ¬Even n) (hcard : n.primeFactors.card = 6) (hsq : Squarefree n)
    (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h7 : 7 ∈ n.primeFactors) (h13 : 13 ∈ n.primeFactors) : ¬Weird n := by
  intro hw
  by_cases h11 : 11 ∈ n.primeFactors
  · exact not_weird_of_squarefree_six_primeFactors_contains_3_5_7_11
      hodd hcard hsq h3 h5 h7 h11 hw
  obtain ⟨r, s, hr, hs, hr64, hrs, hcorr, hr127, hn⟩ :=
    squarefree_six_3_5_7_13_frontier_corridor hw hodd hcard hsq h3 h5 h7 h13 h11
  have hwprod : Weird (1365 * r * s) := by
    simpa [hn] using hw
  exact not_weird_1365_mul_mul_of_corridor hr hs hrs hr64 hr127 hcorr hwprod

/-- Squarefree six-prime candidates in the `3,5,11,13` branch with no `7`
reduce to a finite corridor.

If an odd squarefree weird number has exactly six prime factors, contains
`3,5,11,13`, and avoids `7`, then its two remaining prime factors can be
written as `17 ≤ r < s`, with

`s * (43 * r - 672) ≤ 672 * (r + 1)`

and in fact `r ≤ 31`. -/
theorem squarefree_six_3_5_11_13_frontier_corridor {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h11 : 11 ∈ n.primeFactors) (h13 : 13 ∈ n.primeFactors)
    (hno7 : 7 ∉ n.primeFactors) :
    ∃ r s : ℕ,
      Nat.Prime r ∧ Nat.Prime s ∧ 17 ≤ r ∧ r < s ∧
        s * (43 * r - 672) ≤ 672 * (r + 1) ∧ r ≤ 31 ∧ n = 2145 * r * s := by
  let B : Finset ℕ := {3, 5, 11, 13}
  have hBsub : B ⊆ n.primeFactors := by
    intro p hp
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h11
    · exact h13
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
  have ha_ne11 : a ≠ 11 := by intro h; exact ha_notB (by simp [B, h])
  have ha_ne13 : a ≠ 13 := by intro h; exact ha_notB (by simp [B, h])
  have hb_ne3 : b ≠ 3 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne5 : b ≠ 5 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne11 : b ≠ 11 := by intro h; exact hb_notB (by simp [B, h])
  have hb_ne13 : b ≠ 13 := by intro h; exact hb_notB (by simp [B, h])
  have ha_ne7 : a ≠ 7 := by intro h; exact hno7 (h ▸ ha_mem)
  have hb_ne7 : b ≠ 7 := by intro h; exact hno7 (h ▸ hb_mem)
  have ha_ge17 : 17 ≤ a :=
    prime_factor_ge_seventeen_of_not_small hodd ha_mem ha_ne3 ha_ne5 ha_ne7 ha_ne11 ha_ne13
  have hb_ge17 : 17 ≤ b :=
    prime_factor_ge_seventeen_of_not_small hodd hb_mem hb_ne3 hb_ne5 hb_ne7 hb_ne11 hb_ne13
  have hpf : n.primeFactors = ({3, 5, 11, 13, a, b} : Finset ℕ) := by
    ext p
    constructor
    · intro hp
      by_cases hpB : p ∈ B
      · have hpbase : p = 3 ∨ p = 5 ∨ p = 11 ∨ p = 13 := by
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
      · exact h11
      · exact h13
      · exact ha_mem
      · exact hb_mem
  have hnprod : n = 2145 * a * b := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf,
      prod_3_5_11_13_r_s ha_ge17 hb_ge17 hab]
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · have hwprod : Weird (2145 * a * b) := by simpa [hnprod] using hw
    refine ⟨a, b, ha_prime, hb_prime, ha_ge17, hab_lt,
      corridor_of_weird_2145_mul_mul ha_prime hb_prime ha_ge17 hab_lt hwprod,
      first_prime_le_31_of_weird_2145_mul_mul ha_prime hb_prime ha_ge17 hab_lt hwprod,
      hnprod⟩
  · have hnprod' : n = 2145 * b * a := by
      rw [hnprod]
      ring
    have hwprod : Weird (2145 * b * a) := by simpa [hnprod'] using hw
    refine ⟨b, a, hb_prime, ha_prime, hb_ge17, hba_lt,
      corridor_of_weird_2145_mul_mul hb_prime ha_prime hb_ge17 hba_lt hwprod,
      first_prime_le_31_of_weird_2145_mul_mul hb_prime ha_prime hb_ge17 hba_lt hwprod,
      hnprod'⟩

/-- **The `3,5,11,13` branch of the squarefree six-prime frontier is empty.**

The case with an additional factor `7` was already closed by the `3,5,7,11`
branch. In the remaining case the two extra primes are at least `17`, abundance
forces one of just 62 ordered prime pairs, and each pair has a pseudoperfect
certificate over the divisors of `2145`. -/
theorem not_weird_of_squarefree_six_primeFactors_contains_3_5_11_13 {n : ℕ}
    (hodd : ¬Even n) (hcard : n.primeFactors.card = 6) (hsq : Squarefree n)
    (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h11 : 11 ∈ n.primeFactors) (h13 : 13 ∈ n.primeFactors) : ¬Weird n := by
  intro hw
  by_cases h7 : 7 ∈ n.primeFactors
  · exact not_weird_of_squarefree_six_primeFactors_contains_3_5_7_11
      hodd hcard hsq h3 h5 h7 h11 hw
  obtain ⟨r, s, hr, hs, hr17, hrs, hcorr, hr31, hn⟩ :=
    squarefree_six_3_5_11_13_frontier_corridor hw hodd hcard hsq h3 h5 h11 h13 h7
  have hwprod : Weird (2145 * r * s) := by
    simpa [hn] using hw
  exact not_weird_2145_mul_mul_of_corridor hr hs hr17 hrs hr31 hcorr hwprod

/-- **The `3,5,13` singleton branch of the squarefree six-prime frontier is
empty.**

The pair branches with `7` or `11` are already closed. If neither appears,
the ordered prime factors are at least `3,5,13,17,19,23`. Once the largest is
at least `29`, the divisor-sum ratio is below `2`; otherwise primality and
ordering force the last three primes to be exactly `17,19,23`, whose six-prime
core is pseudoperfect. -/
theorem not_weird_of_squarefree_six_primeFactors_contains_3_5_13 {n : ℕ}
    (hodd : ¬Even n) (hcard : n.primeFactors.card = 6) (hsq : Squarefree n)
    (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h13 : 13 ∈ n.primeFactors) : ¬Weird n := by
  intro hw
  by_cases h7 : 7 ∈ n.primeFactors
  · exact not_weird_of_squarefree_six_primeFactors_contains_3_5_7_13
      hodd hcard hsq h3 h5 h7 h13 hw
  by_cases h11 : 11 ∈ n.primeFactors
  · exact not_weird_of_squarefree_six_primeFactors_contains_3_5_11_13
      hodd hcard hsq h3 h5 h11 h13 hw
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
  have hp2_ge7 : 7 ≤ p2 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp2_mem hp2_ne3 hp2_ne5
  have hp2_ne7 : p2 ≠ 7 := by intro h; exact h7 (h ▸ hp2_mem)
  have hp2_ge11 : 11 ≤ p2 := prime_ge_eleven_of_ge_seven_ne_seven hp2 hp2_ge7 hp2_ne7
  have hp2_ne11 : p2 ≠ 11 := by intro h; exact h11 (h ▸ hp2_mem)
  have hp2_ge13 : 13 ≤ p2 :=
    prime_ge_thirteen_of_ge_eleven_ne_eleven hp2 hp2_ge11 hp2_ne11
  have hp3_ne3 : p3 ≠ 3 := by intro h; omega
  have hp3_ne5 : p3 ≠ 5 := by intro h; omega
  have hp3_ne7 : p3 ≠ 7 := by intro h; exact h7 (h ▸ hp3_mem)
  have hp3_ne11 : p3 ≠ 11 := by intro h; exact h11 (h ▸ hp3_mem)
  have hp3_ne13 : p3 ≠ 13 := by intro h; omega
  have hp3_ge17 : 17 ≤ p3 :=
    prime_factor_ge_seventeen_of_not_small hodd hp3_mem hp3_ne3 hp3_ne5
      hp3_ne7 hp3_ne11 hp3_ne13
  have hp4_ne3 : p4 ≠ 3 := by intro h; omega
  have hp4_ne5 : p4 ≠ 5 := by intro h; omega
  have hp4_ne7 : p4 ≠ 7 := by intro h; exact h7 (h ▸ hp4_mem)
  have hp4_ne11 : p4 ≠ 11 := by intro h; exact h11 (h ▸ hp4_mem)
  have hp4_ne13 : p4 ≠ 13 := by intro h; omega
  have hp4_ge17 : 17 ≤ p4 :=
    prime_factor_ge_seventeen_of_not_small hodd hp4_mem hp4_ne3 hp4_ne5
      hp4_ne7 hp4_ne11 hp4_ne13
  have hp4_ne17 : p4 ≠ 17 := by intro h; omega
  have hp4_ge19 : 19 ≤ p4 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp4 hp4_ge17 hp4_ne17
  have hp5_ne3 : p5 ≠ 3 := by intro h; omega
  have hp5_ne5 : p5 ≠ 5 := by intro h; omega
  have hp5_ne7 : p5 ≠ 7 := by intro h; exact h7 (h ▸ hp5_mem)
  have hp5_ne11 : p5 ≠ 11 := by intro h; exact h11 (h ▸ hp5_mem)
  have hp5_ne13 : p5 ≠ 13 := by intro h; omega
  have hp5_ge17 : 17 ≤ p5 :=
    prime_factor_ge_seventeen_of_not_small hodd hp5_mem hp5_ne3 hp5_ne5
      hp5_ne7 hp5_ne11 hp5_ne13
  have hp5_ne17 : p5 ≠ 17 := by intro h; omega
  have hp5_ge19 : 19 ≤ p5 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp5 hp5_ge17 hp5_ne17
  have hp5_ne19 : p5 ≠ 19 := by intro h; omega
  have hp5_ge23 : 23 ≤ p5 :=
    prime_ge_twentythree_of_ge_nineteen_ne_nineteen hp5 hp5_ge19 hp5_ne19
  have hn : n ≠ 0 := Nat.ne_of_gt hw.1.1
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
      have hfact := Nat.prod_factorization_pow_eq_self hn
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
  by_cases hp5_large : 29 ≤ p5
  · have hlt :
        (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) <
          2 * (p0 * p1 * p2 * p3 * p4 * p5) :=
      squarefree_six_ratio_3_5_13_17_19_29_lt p0 p1 p2 p3 p4 p5
        hp0_ge3 hp1_ge5 hp2_ge13 hp3_ge17 hp4_ge19 hp5_large
    have hnot : ¬Abundant n := by
      apply not_abundant_of_sigma_lt
      rw [hsum_squarefree, hn_squarefree]
      exact hlt
    exact hnot hw.1
  · have hp5_le28 : p5 ≤ 28 := by omega
    have hp5_eq23 : p5 = 23 := by
      have hcases : p5 = 23 ∨ p5 = 24 ∨ p5 = 25 ∨ p5 = 26 ∨ p5 = 27 ∨ p5 = 28 := by
        omega
      rcases hcases with h23 | h24 | h25 | h26 | h27 | h28
      · exact h23
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 24) (by simpa [h24] using hp5)
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 25) (by simpa [h25] using hp5)
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 26) (by simpa [h26] using hp5)
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 27) (by simpa [h27] using hp5)
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 28) (by simpa [h28] using hp5)
    have hp4_eq19 : p4 = 19 := by
      have hp4_le22 : p4 ≤ 22 := by omega
      have hcases : p4 = 19 ∨ p4 = 20 ∨ p4 = 21 ∨ p4 = 22 := by omega
      rcases hcases with h19 | h20 | h21 | h22
      · exact h19
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 20) (by simpa [h20] using hp4)
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 21) (by simpa [h21] using hp4)
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 22) (by simpa [h22] using hp4)
    have hp3_eq17 : p3 = 17 := by
      have hp3_le18 : p3 ≤ 18 := by omega
      have hcases : p3 = 17 ∨ p3 = 18 := by omega
      rcases hcases with h17 | h18
      · exact h17
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 18) (by simpa [h18] using hp3)
    have hsubset : ({3, 5, 13, 17, 19, 23} : Finset ℕ) ⊆ n.primeFactors := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h13
      · simpa [hp3_eq17] using hp3_mem
      · simpa [hp4_eq19] using hp4_mem
      · simpa [hp5_eq23] using hp5_mem
    exact not_weird_of_squarefree_primeFactors_contains_3_5_13_17_19_23
      hsq hsubset hw

/-- **The `3,5,11` singleton branch of the squarefree six-prime frontier is
empty.**

The pair branches with `7` or `13` are already closed. If neither appears, the
ordered prime factors are at least `3,5,11,17,19,23`. Large tails are
non-abundant by ratio bounds; the remaining finite tails are exactly
`17,19,23`, `17,19,29`, and `17,19,31`, all of which are pseudoperfect cores. -/
theorem not_weird_of_squarefree_six_primeFactors_contains_3_5_11 {n : ℕ}
    (hodd : ¬Even n) (hcard : n.primeFactors.card = 6) (hsq : Squarefree n)
    (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (h11 : 11 ∈ n.primeFactors) : ¬Weird n := by
  intro hw
  by_cases h7 : 7 ∈ n.primeFactors
  · exact not_weird_of_squarefree_six_primeFactors_contains_3_5_7_11
      hodd hcard hsq h3 h5 h7 h11 hw
  by_cases h13 : 13 ∈ n.primeFactors
  · exact not_weird_of_squarefree_six_primeFactors_contains_3_5_11_13
      hodd hcard hsq h3 h5 h11 h13 hw
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
  have hp2_ge7 : 7 ≤ p2 :=
    prime_factor_ge_seven_of_ne_three_five hodd hp2_mem hp2_ne3 hp2_ne5
  have hp2_ne7 : p2 ≠ 7 := by intro h; exact h7 (h ▸ hp2_mem)
  have hp2_ge11 : 11 ≤ p2 := prime_ge_eleven_of_ge_seven_ne_seven hp2 hp2_ge7 hp2_ne7
  have hp3_ne3 : p3 ≠ 3 := by intro h; omega
  have hp3_ne5 : p3 ≠ 5 := by intro h; omega
  have hp3_ne7 : p3 ≠ 7 := by intro h; exact h7 (h ▸ hp3_mem)
  have hp3_ne11 : p3 ≠ 11 := by intro h; omega
  have hp3_ne13 : p3 ≠ 13 := by intro h; exact h13 (h ▸ hp3_mem)
  have hp3_ge17 : 17 ≤ p3 :=
    prime_factor_ge_seventeen_of_not_small hodd hp3_mem hp3_ne3 hp3_ne5
      hp3_ne7 hp3_ne11 hp3_ne13
  have hp4_ne3 : p4 ≠ 3 := by intro h; omega
  have hp4_ne5 : p4 ≠ 5 := by intro h; omega
  have hp4_ne7 : p4 ≠ 7 := by intro h; exact h7 (h ▸ hp4_mem)
  have hp4_ne11 : p4 ≠ 11 := by intro h; omega
  have hp4_ne13 : p4 ≠ 13 := by intro h; exact h13 (h ▸ hp4_mem)
  have hp4_ge17 : 17 ≤ p4 :=
    prime_factor_ge_seventeen_of_not_small hodd hp4_mem hp4_ne3 hp4_ne5
      hp4_ne7 hp4_ne11 hp4_ne13
  have hp4_ne17 : p4 ≠ 17 := by intro h; omega
  have hp4_ge19 : 19 ≤ p4 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp4 hp4_ge17 hp4_ne17
  have hp5_ne3 : p5 ≠ 3 := by intro h; omega
  have hp5_ne5 : p5 ≠ 5 := by intro h; omega
  have hp5_ne7 : p5 ≠ 7 := by intro h; exact h7 (h ▸ hp5_mem)
  have hp5_ne11 : p5 ≠ 11 := by intro h; omega
  have hp5_ne13 : p5 ≠ 13 := by intro h; exact h13 (h ▸ hp5_mem)
  have hp5_ge17 : 17 ≤ p5 :=
    prime_factor_ge_seventeen_of_not_small hodd hp5_mem hp5_ne3 hp5_ne5
      hp5_ne7 hp5_ne11 hp5_ne13
  have hp5_ne17 : p5 ≠ 17 := by intro h; omega
  have hp5_ge19 : 19 ≤ p5 :=
    prime_ge_nineteen_of_ge_seventeen_ne_seventeen hp5 hp5_ge17 hp5_ne17
  have hp5_ne19 : p5 ≠ 19 := by intro h; omega
  have hp5_ge23 : 23 ≤ p5 :=
    prime_ge_twentythree_of_ge_nineteen_ne_nineteen hp5 hp5_ge19 hp5_ne19
  have hn : n ≠ 0 := Nat.ne_of_gt hw.1.1
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
      have hfact := Nat.prod_factorization_pow_eq_self hn
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
  by_cases hp5_large : 37 ≤ p5
  · have hlt :
        (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) <
          2 * (p0 * p1 * p2 * p3 * p4 * p5) :=
      squarefree_six_ratio_3_5_11_17_19_37_lt p0 p1 p2 p3 p4 p5
        hp0_ge3 hp1_ge5 hp2_ge11 hp3_ge17 hp4_ge19 hp5_large
    have hnot : ¬Abundant n := by
      apply not_abundant_of_sigma_lt
      rw [hsum_squarefree, hn_squarefree]
      exact hlt
    exact hnot hw.1
  by_cases hp4_large : 23 ≤ p4
  · have hp5_ne23 : p5 ≠ 23 := by intro h; omega
    have hp5_ge29 : 29 ≤ p5 :=
      prime_ge_twentynine_of_ge_twentythree_ne_twentythree hp5 hp5_ge23 hp5_ne23
    have hlt :
        (p0 + 1) * (p1 + 1) * (p2 + 1) * (p3 + 1) * (p4 + 1) * (p5 + 1) <
          2 * (p0 * p1 * p2 * p3 * p4 * p5) :=
      squarefree_six_ratio_3_5_11_17_23_29_lt p0 p1 p2 p3 p4 p5
        hp0_ge3 hp1_ge5 hp2_ge11 hp3_ge17 hp4_large hp5_ge29
    have hnot : ¬Abundant n := by
      apply not_abundant_of_sigma_lt
      rw [hsum_squarefree, hn_squarefree]
      exact hlt
    exact hnot hw.1
  · have hp4_le22 : p4 ≤ 22 := by omega
    have hp4_eq19 : p4 = 19 := by
      have hcases : p4 = 19 ∨ p4 = 20 ∨ p4 = 21 ∨ p4 = 22 := by omega
      rcases hcases with h19 | h20 | h21 | h22
      · exact h19
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 20) (by simpa [h20] using hp4)
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 21) (by simpa [h21] using hp4)
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 22) (by simpa [h22] using hp4)
    have hp3_eq17 : p3 = 17 := by
      have hp3_le18 : p3 ≤ 18 := by omega
      have hcases : p3 = 17 ∨ p3 = 18 := by omega
      rcases hcases with h17 | h18
      · exact h17
      · exfalso
        exact (by norm_num : ¬ Nat.Prime 18) (by simpa [h18] using hp3)
    have hp5_le36 : p5 ≤ 36 := by omega
    have hp5_cases : p5 = 23 ∨ p5 = 29 ∨ p5 = 31 := by
      have hcases : p5 = 23 ∨ p5 = 24 ∨ p5 = 25 ∨ p5 = 26 ∨ p5 = 27 ∨
          p5 = 28 ∨ p5 = 29 ∨ p5 = 30 ∨ p5 = 31 ∨ p5 = 32 ∨ p5 = 33 ∨
          p5 = 34 ∨ p5 = 35 ∨ p5 = 36 := by
        omega
      rcases hcases with h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 |
        h32 | h33 | h34 | h35 | h36
      · exact Or.inl h23
      · exfalso; exact (by norm_num : ¬ Nat.Prime 24) (by simpa [h24] using hp5)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 25) (by simpa [h25] using hp5)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 26) (by simpa [h26] using hp5)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 27) (by simpa [h27] using hp5)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 28) (by simpa [h28] using hp5)
      · exact Or.inr (Or.inl h29)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 30) (by simpa [h30] using hp5)
      · exact Or.inr (Or.inr h31)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 32) (by simpa [h32] using hp5)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 33) (by simpa [h33] using hp5)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 34) (by simpa [h34] using hp5)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 35) (by simpa [h35] using hp5)
      · exfalso; exact (by norm_num : ¬ Nat.Prime 36) (by simpa [h36] using hp5)
    rcases hp5_cases with hp5_eq23 | hp5_eq29 | hp5_eq31
    · have hsubset : ({3, 5, 11, 17, 19, 23} : Finset ℕ) ⊆ n.primeFactors := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h3
        · exact h5
        · exact h11
        · simpa [hp3_eq17] using hp3_mem
        · simpa [hp4_eq19] using hp4_mem
        · simpa [hp5_eq23] using hp5_mem
      exact not_weird_of_squarefree_primeFactors_contains_3_5_11_17_19_23
        hsq hsubset hw
    · have hsubset : ({3, 5, 11, 17, 19, 29} : Finset ℕ) ⊆ n.primeFactors := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h3
        · exact h5
        · exact h11
        · simpa [hp3_eq17] using hp3_mem
        · simpa [hp4_eq19] using hp4_mem
        · simpa [hp5_eq29] using hp5_mem
      exact not_weird_of_squarefree_primeFactors_contains_3_5_11_17_19_29
        hsq hsubset hw
    · have hsubset : ({3, 5, 11, 17, 19, 31} : Finset ℕ) ⊆ n.primeFactors := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h3
        · exact h5
        · exact h11
        · simpa [hp3_eq17] using hp3_mem
        · simpa [hp4_eq19] using hp4_mem
        · simpa [hp5_eq31] using hp5_mem
      exact not_weird_of_squarefree_primeFactors_contains_3_5_11_17_19_31
        hsq hsubset hw

/-- A squarefree odd weird number with exactly six prime factors cannot contain
both `7` and `11`. The earlier frontier theorems force `3` and `5`; the new
`3,5,7,11` branch closure then gives the contradiction. -/
theorem odd_weird_squarefree_six_prime_factors_not_contains_7_and_11 {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) : ¬ (7 ∈ n.primeFactors ∧ 11 ∈ n.primeFactors) := by
  rintro ⟨h7, h11⟩
  have h3 : 3 ∈ n.primeFactors := odd_weird_six_prime_factors_contains_three hw hodd hcard
  have h5 : 5 ∈ n.primeFactors :=
    odd_weird_squarefree_six_prime_factors_contains_five hw hodd hcard hsq
  exact not_weird_of_squarefree_six_primeFactors_contains_3_5_7_11
    hodd hcard hsq h3 h5 h7 h11 hw

/-- A squarefree odd weird number with exactly six prime factors cannot contain
both `7` and `13`. -/
theorem odd_weird_squarefree_six_prime_factors_not_contains_7_and_13 {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) : ¬ (7 ∈ n.primeFactors ∧ 13 ∈ n.primeFactors) := by
  rintro ⟨h7, h13⟩
  have h3 : 3 ∈ n.primeFactors := odd_weird_six_prime_factors_contains_three hw hodd hcard
  have h5 : 5 ∈ n.primeFactors :=
    odd_weird_squarefree_six_prime_factors_contains_five hw hodd hcard hsq
  exact not_weird_of_squarefree_six_primeFactors_contains_3_5_7_13
    hodd hcard hsq h3 h5 h7 h13 hw

/-- A squarefree odd weird number with exactly six prime factors cannot contain
both `11` and `13`. -/
theorem odd_weird_squarefree_six_prime_factors_not_contains_11_and_13 {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) : ¬ (11 ∈ n.primeFactors ∧ 13 ∈ n.primeFactors) := by
  rintro ⟨h11, h13⟩
  have h3 : 3 ∈ n.primeFactors := odd_weird_six_prime_factors_contains_three hw hodd hcard
  have h5 : 5 ∈ n.primeFactors :=
    odd_weird_squarefree_six_prime_factors_contains_five hw hodd hcard hsq
  exact not_weird_of_squarefree_six_primeFactors_contains_3_5_11_13
    hodd hcard hsq h3 h5 h11 h13 hw

/-- A squarefree odd weird number with exactly six prime factors cannot contain
`13`. The earlier frontier theorems force `3` and `5`, and the singleton
`3,5,13` branch is empty. -/
theorem odd_weird_squarefree_six_prime_factors_not_contains_13 {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) : 13 ∉ n.primeFactors := by
  intro h13
  have h3 : 3 ∈ n.primeFactors := odd_weird_six_prime_factors_contains_three hw hodd hcard
  have h5 : 5 ∈ n.primeFactors :=
    odd_weird_squarefree_six_prime_factors_contains_five hw hodd hcard hsq
  exact not_weird_of_squarefree_six_primeFactors_contains_3_5_13
    hodd hcard hsq h3 h5 h13 hw

/-- A squarefree odd weird number with exactly six prime factors cannot contain
`11`. The earlier frontier theorems force `3` and `5`, and the singleton
`3,5,11` branch is empty. -/
theorem odd_weird_squarefree_six_prime_factors_not_contains_11 {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) : 11 ∉ n.primeFactors := by
  intro h11
  have h3 : 3 ∈ n.primeFactors := odd_weird_six_prime_factors_contains_three hw hodd hcard
  have h5 : 5 ∈ n.primeFactors :=
    odd_weird_squarefree_six_prime_factors_contains_five hw hodd hcard hsq
  exact not_weird_of_squarefree_six_primeFactors_contains_3_5_11
    hodd hcard hsq h3 h5 h11 hw

/-- At the current frontier, a squarefree odd weird number with exactly six
prime factors would have to contain `7`. The companion corollaries rule out
`11` and `13`. -/
theorem odd_weird_squarefree_six_prime_factors_contains_seven_only_frontier {n : ℕ}
    (hw : Weird n) (hodd : ¬Even n) (hcard : n.primeFactors.card = 6)
    (hsq : Squarefree n) : 7 ∈ n.primeFactors := by
  rcases odd_weird_squarefree_six_prime_factors_contains_7_or_11_or_13
      hw hodd hcard hsq with h7 | h11 | h13
  · exact h7
  · exact (odd_weird_squarefree_six_prime_factors_not_contains_11
      hw hodd hcard hsq h11).elim
  · exact (odd_weird_squarefree_six_prime_factors_not_contains_13
      hw hodd hcard hsq h13).elim

end WeirdNumbers
