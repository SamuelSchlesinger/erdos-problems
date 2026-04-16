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
    exact_mod_cast (show (σ3 : ℚ) * σ5 * σ11 < 2 * (3 ^ a * 5 ^ b * 11 ^ c) by
      nlinarith)
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
    exact_mod_cast (show (σ3 : ℚ) * σ5 * σ13 < 2 * (3 ^ a * 5 ^ b * 13 ^ c) by
      nlinarith)
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
private theorem pp_945 : Pseudoperfect 945 := by native_decide

set_option linter.style.nativeDecide false in
private theorem pp_1575 : Pseudoperfect 1575 := by native_decide

set_option linter.style.nativeDecide false in
private theorem pp_2205 : Pseudoperfect 2205 := by native_decide

set_option linter.style.nativeDecide false in
private theorem pp_7425 : Pseudoperfect 7425 := by native_decide

set_option linter.style.nativeDecide false in
private theorem pp_78975 : Pseudoperfect 78975 := by native_decide

set_option linter.style.nativeDecide false in
private theorem pp_131625 : Pseudoperfect 131625 := by native_decide

set_option linter.style.nativeDecide false in
private theorem pp_342225 : Pseudoperfect 342225 := by native_decide

set_option linter.style.nativeDecide false in
private theorem pp_570375 : Pseudoperfect 570375 := by native_decide

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
        simpa [hdecomp] using (pseudoperfect_mul hm pp_1575)
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
          simpa [hb_eq1, hdecomp] using (pseudoperfect_mul hm pp_2205)
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
        simpa [ha_eq4, hdecomp] using (pseudoperfect_mul hm pp_131625)
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
            simpa [ha_eq4, hb_eq2, hdecomp] using (pseudoperfect_mul hm pp_342225)
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
            simpa [ha_eq3, hdecomp] using (pseudoperfect_mul hm pp_570375)
          · have hc_eq1 : c = 1 := by omega
            exact (three_five_thirteen_three_c_one_not_abundant b <|
              by simpa [ha_eq3, hc_eq1] using hab).elim
        · have hb2 : b ≤ 2 := by omega
          exact (three_five_thirteen_three_b_le_two_not_abundant b c hb2 <|
            by simpa [ha_eq3] using hab).elim
      · have ha2 : a ≤ 2 := by omega
        exact (three_five_thirteen_a_le_two_not_abundant a b c ha2 hab).elim

end WeirdNumbers
