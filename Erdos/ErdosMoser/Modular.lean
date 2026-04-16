import Erdos.ErdosMoser.Statement
import Erdos.ErdosMoser.EvenEight

/-!
# Erdos-Moser Equation: Modular Obstructions

This file starts the modular-arithmetic phase for the Erdos-Moser equation.

Main result in this pass:
- Any positive-exponent solution satisfies `m % 4 = 0 ∨ m % 4 = 3`.
- Any odd-exponent solution satisfies `m % 3 = 0`.
- Any odd solution with `k ≥ 3` satisfies `m % 8 = 0`, hence `m % 24 = 0`.
-/

namespace ErdosMoser

private lemma zmod2_pow_eq_self (n k : ℕ) (hk : 0 < k) :
    ((n : ZMod 2) ^ k) = (n : ZMod 2) := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · have h0 : (n : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).2 hEven
    simp [h0, hk.ne']
  · have h1 : (n : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).2 hOdd
    simp [h1]

private lemma powerSum_cast_zmod2 (m k : ℕ) (hk : 0 < k) :
    ((powerSum m k : ℕ) : ZMod 2) = ∑ i ∈ Finset.range m, (i : ZMod 2) := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 2) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 2) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 2) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (i : ZMod 2) := by
      simp_rw [zmod2_pow_eq_self _ _ hk]

private lemma sum_range_cast_zmod2 (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ZMod 2)) = (m * (m - 1) / 2 : ℕ) := by
  have h : (∑ i ∈ Finset.range m, i) = m * (m - 1) / 2 := Finset.sum_range_id m
  have hcast : ((∑ i ∈ Finset.range m, i : ℕ) : ZMod 2) =
      (m * (m - 1) / 2 : ℕ) :=
    congrArg (fun t : ℕ => (t : ZMod 2)) h
  simpa using hcast

private lemma half_two_mul (q : ℕ) : (2 * q) / 2 = q := by
  simp [Nat.mul_comm]

private lemma tri_mod2_even (q : ℕ) :
    (((2 * q) * (2 * q - 1) / 2) % 2) = q % 2 := by
  cases q with
  | zero =>
      simp
  | succ q =>
      have h2dvd : 2 ∣ 2 * (q + 1) := dvd_mul_right 2 (q + 1)
      have hq : (2 * (q + 1)) / 2 = q + 1 := half_two_mul (q + 1)
      have hdiv :
          (2 * (q + 1) - 1) * (2 * (q + 1)) / 2 =
            (2 * (q + 1) - 1) * ((2 * (q + 1)) / 2) :=
        Nat.mul_div_assoc (2 * (q + 1) - 1) h2dvd
      calc
        ((2 * (q + 1)) * (2 * (q + 1) - 1) / 2) % 2 =
            ((2 * (q + 1) - 1) * (2 * (q + 1)) / 2) % 2 := by
          simp [Nat.mul_comm]
        _ = ((2 * (q + 1) - 1) * ((2 * (q + 1)) / 2)) % 2 := by
          rw [hdiv]
        _ = ((2 * (q + 1) - 1) * (q + 1)) % 2 := by
          rw [hq]
        _ = ((2 * (q + 1) - 1) % 2 * ((q + 1) % 2)) % 2 := by
          rw [Nat.mul_mod]
        _ = (1 * ((q + 1) % 2)) % 2 := by
          have hsub : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
          rw [hsub]
          have hodd : Odd (2 * q + 1) := ⟨q, by ring⟩
          rw [(Nat.odd_iff.mp hodd)]
        _ = (q + 1) % 2 := by
          simp

private lemma tri_mod2_odd (q : ℕ) :
    (((2 * q + 1) * (2 * q + 1 - 1) / 2) % 2) = q % 2 := by
  have h2dvd : 2 ∣ 2 * q := dvd_mul_right 2 q
  have hq : (2 * q) / 2 = q := half_two_mul q
  have hdiv : (2 * q + 1) * (2 * q) / 2 = (2 * q + 1) * ((2 * q) / 2) :=
    Nat.mul_div_assoc (2 * q + 1) h2dvd
  calc
    ((2 * q + 1) * (2 * q + 1 - 1) / 2) % 2 = ((2 * q + 1) * (2 * q) / 2) % 2 := by
      simp
    _ = ((2 * q + 1) * ((2 * q) / 2)) % 2 := by
      rw [hdiv]
    _ = ((2 * q + 1) * q) % 2 := by
      rw [hq]
    _ = ((2 * q + 1) % 2 * (q % 2)) % 2 := by
      rw [Nat.mul_mod]
    _ = (1 * (q % 2)) % 2 := by
      have hodd : Odd (2 * q + 1) := ⟨q, by ring⟩
      rw [(Nat.odd_iff.mp hodd)]
    _ = q % 2 := by
      simp

private lemma tri_mod2 (m : ℕ) : (m * (m - 1) / 2) % 2 = (m / 2) % 2 := by
  rcases Nat.even_or_odd m with hEven | hOdd
  · rcases hEven with ⟨q, hq⟩
    rw [hq]
    have hq' : q + q = 2 * q := by omega
    rw [hq', half_two_mul q]
    simpa using tri_mod2_even q
  · rcases hOdd with ⟨q, hq⟩
    rw [hq]
    have hhalf : (2 * q + 1) / 2 = q := by omega
    rw [hhalf]
    simpa using tri_mod2_odd q

private lemma half_mod_two_of_mod_four_eq_one (m : ℕ) (h : m % 4 = 1) :
    (m / 2) % 2 = 0 := by
  have hm : m = 1 + 4 * (m / 4) := by
    simpa [h] using (Nat.mod_add_div m 4).symm
  rw [hm]
  omega

private lemma half_mod_two_of_mod_four_eq_two (m : ℕ) (h : m % 4 = 2) :
    (m / 2) % 2 = 1 := by
  have hm : m = 2 + 4 * (m / 4) := by
    simpa [h] using (Nat.mod_add_div m 4).symm
  rw [hm]
  omega

private lemma mod4_of_parity (m : ℕ) (hpar : m % 2 = (m / 2) % 2) :
    m % 4 = 0 ∨ m % 4 = 3 := by
  have hm4lt : m % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hm4 : m % 4
  · left
    omega
  · exfalso
    have hm2 : m % 2 = 1 := by omega
    have hhalf : (m / 2) % 2 = 0 := half_mod_two_of_mod_four_eq_one m hm4
    omega
  · exfalso
    have hm2 : m % 2 = 0 := by omega
    have hhalf : (m / 2) % 2 = 1 := half_mod_two_of_mod_four_eq_two m hm4
    omega
  · right
    omega

/-- **First modular obstruction (mod 4).**

If `(m, k)` is a positive-exponent solution to the Erdos-Moser equation, then
`m` cannot lie in residue classes `1` or `2` modulo `4`.
Equivalently, `m ≡ 0` or `3 (mod 4)`. -/
theorem mod_four_obstruction {m k : ℕ} (hsol : IsSolution m k) :
    m % 4 = 0 ∨ m % 4 = 3 := by
  rcases hsol with ⟨_hmpos, hk, hEq⟩
  have hpow : ((m ^ k : ℕ) : ZMod 2) = (m : ZMod 2) := by
    simpa [Nat.cast_pow] using (zmod2_pow_eq_self m k hk)
  have hsum : ((powerSum m k : ℕ) : ZMod 2) = (m * (m - 1) / 2 : ℕ) := by
    calc
      ((powerSum m k : ℕ) : ZMod 2) = ∑ i ∈ Finset.range m, (i : ZMod 2) :=
        powerSum_cast_zmod2 m k hk
      _ = (m * (m - 1) / 2 : ℕ) := sum_range_cast_zmod2 m
  have hcastEq : (m : ZMod 2) = (m * (m - 1) / 2 : ℕ) := by
    calc
      (m : ZMod 2) = ((m ^ k : ℕ) : ZMod 2) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 2) := by
        exact congrArg (fun t : ℕ => (t : ZMod 2)) hEq.symm
      _ = (m * (m - 1) / 2 : ℕ) := hsum
  have hmod : (2 : ℕ).ModEq m (m * (m - 1) / 2) :=
    (ZMod.natCast_eq_natCast_iff m (m * (m - 1) / 2) 2).1 hcastEq
  have hparity : m % 2 = ((m * (m - 1) / 2) % 2) := by
    simpa [Nat.ModEq] using hmod
  have htri : ((m * (m - 1) / 2) % 2) = ((m / 2) % 2) := tri_mod2 m
  have hparity' : m % 2 = (m / 2) % 2 := by omega
  exact mod4_of_parity m hparity'

private lemma zmod3_pow_eq_self_of_odd (a : ZMod 3) {k : ℕ} (hkodd : Odd k) :
    a ^ k = a := by
  rcases hkodd with ⟨t, rfl⟩
  fin_cases a
  · simp
  · simp
  · have hsq : ((2 : ZMod 3) ^ 2) = 1 := by decide
    calc
      (2 : ZMod 3) ^ (2 * t + 1) = ((2 : ZMod 3) ^ (2 * t)) * (2 : ZMod 3) := by
        rw [pow_add, pow_one]
      _ = (((2 : ZMod 3) ^ 2) ^ t) * (2 : ZMod 3) := by
        rw [pow_mul]
      _ = 2 := by simp [hsq]

private lemma powerSum_cast_zmod3_of_odd (m k : ℕ) (hkodd : Odd k) :
    ((powerSum m k : ℕ) : ZMod 3) = ∑ i ∈ Finset.range m, (i : ZMod 3) := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 3) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 3) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 3) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (i : ZMod 3) := by
      simp_rw [zmod3_pow_eq_self_of_odd _ hkodd]

private lemma sum_range_cast_zmod3 (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ZMod 3)) = (m * (m - 1) / 2 : ℕ) := by
  have h : (∑ i ∈ Finset.range m, i) = m * (m - 1) / 2 := Finset.sum_range_id m
  have hcast : ((∑ i ∈ Finset.range m, i : ℕ) : ZMod 3) =
      (m * (m - 1) / 2 : ℕ) :=
    congrArg (fun t : ℕ => (t : ZMod 3)) h
  simpa using hcast

private lemma zmod3_zero_of_triangular_eq (m : ℕ) (hmpos : 0 < m)
    (hEq : (m : ZMod 3) = (m * (m - 1) / 2 : ℕ)) : (m : ZMod 3) = 0 := by
  have hm1 : 1 ≤ m := by omega
  have heven : Even (m * (m - 1)) := by
    have h : Even ((m - 1) * ((m - 1) + 1)) := Nat.even_mul_succ_self (m - 1)
    have hpred : (m - 1) + 1 = m := by omega
    simpa [hpred, Nat.mul_comm] using h
  have hdoubleNat : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
    Nat.two_mul_div_two_of_even heven
  have hEq2 : ((2 : ℕ) : ZMod 3) * (m : ZMod 3) = (m : ZMod 3) * ((m : ZMod 3) - 1) := by
    calc
      ((2 : ℕ) : ZMod 3) * (m : ZMod 3) = ((2 * m : ℕ) : ZMod 3) := by simp
      _ = ((2 * (m * (m - 1) / 2) : ℕ) : ZMod 3) := by
            simpa using congrArg (fun t : ZMod 3 => ((2 : ℕ) : ZMod 3) * t) hEq
      _ = (m * (m - 1) : ℕ) := by simp [hdoubleNat]
      _ = (m : ZMod 3) * ((m : ZMod 3) - 1) := by simp [Nat.cast_sub hm1]
  have hsq : (m : ZMod 3) ^ 2 = 0 := by
    calc
      (m : ZMod 3) ^ 2 = (m : ZMod 3) * ((m : ZMod 3) - 1) + (m : ZMod 3) := by ring
      _ = ((2 : ℕ) : ZMod 3) * (m : ZMod 3) + (m : ZMod 3) := by rw [← hEq2]
      _ = ((3 : ℕ) : ZMod 3) * (m : ZMod 3) := by ring
      _ = 0 := by
        have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
        rw [h3]
        simp
  exact (sq_eq_zero_iff).1 hsq

/-- **Second modular obstruction (odd exponents force divisibility by 3).**

If `(m, k)` is a solution and `k` is odd, then `m ≡ 0 (mod 3)`. -/
theorem mod_three_obstruction_of_odd {m k : ℕ} (hsol : IsSolution m k) (hkodd : Odd k) :
    m % 3 = 0 := by
  rcases hsol with ⟨hmpos, _hk, hEq⟩
  have hpow : ((m ^ k : ℕ) : ZMod 3) = (m : ZMod 3) := by
    simpa [Nat.cast_pow] using (zmod3_pow_eq_self_of_odd (m : ZMod 3) hkodd)
  have hsum : ((powerSum m k : ℕ) : ZMod 3) = (m * (m - 1) / 2 : ℕ) := by
    calc
      ((powerSum m k : ℕ) : ZMod 3) = ∑ i ∈ Finset.range m, (i : ZMod 3) :=
        powerSum_cast_zmod3_of_odd m k hkodd
      _ = (m * (m - 1) / 2 : ℕ) := sum_range_cast_zmod3 m
  have hcastEq : (m : ZMod 3) = (m * (m - 1) / 2 : ℕ) := by
    calc
      (m : ZMod 3) = ((m ^ k : ℕ) : ZMod 3) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 3) := by
        exact congrArg (fun t : ℕ => (t : ZMod 3)) hEq.symm
      _ = (m * (m - 1) / 2 : ℕ) := hsum
  have hmzero : (m : ZMod 3) = 0 := zmod3_zero_of_triangular_eq m hmpos hcastEq
  have hmod : (3 : ℕ).ModEq m 0 :=
    (ZMod.natCast_eq_natCast_iff m 0 3).1 (by simpa using hmzero)
  simpa [Nat.ModEq] using hmod

private lemma zmod5_pow_eq_self_of_mod_four_eq_one (a : ZMod 5) {k : ℕ}
    (hk : k % 4 = 1) : a ^ k = a := by
  have hk' : ∃ t : ℕ, k = 4 * t + 1 := by
    refine ⟨k / 4, ?_⟩
    omega
  rcases hk' with ⟨t, rfl⟩
  fin_cases a
  · simp
  · simp
  · have h4 : ((2 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (2 : ZMod 5) ^ (4 * t + 1) = ((2 : ZMod 5) ^ (4 * t)) * (2 : ZMod 5) := by
        rw [pow_add, pow_one]
      _ = (((2 : ZMod 5) ^ 4) ^ t) * (2 : ZMod 5) := by
        rw [pow_mul]
      _ = 2 := by simp [h4]
  · have h4 : ((3 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (3 : ZMod 5) ^ (4 * t + 1) = ((3 : ZMod 5) ^ (4 * t)) * (3 : ZMod 5) := by
        rw [pow_add, pow_one]
      _ = (((3 : ZMod 5) ^ 4) ^ t) * (3 : ZMod 5) := by
        rw [pow_mul]
      _ = 3 := by simp [h4]
  · have h4 : ((4 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (4 : ZMod 5) ^ (4 * t + 1) = ((4 : ZMod 5) ^ (4 * t)) * (4 : ZMod 5) := by
        rw [pow_add, pow_one]
      _ = (((4 : ZMod 5) ^ 4) ^ t) * (4 : ZMod 5) := by
        rw [pow_mul]
      _ = 4 := by simp [h4]

private lemma powerSum_cast_zmod5_of_mod_four_eq_one (m k : ℕ) (hk : k % 4 = 1) :
    ((powerSum m k : ℕ) : ZMod 5) = ∑ i ∈ Finset.range m, (i : ZMod 5) := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 5) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 5) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (i : ZMod 5) := by
      simp_rw [zmod5_pow_eq_self_of_mod_four_eq_one _ hk]

private lemma sum_range_cast_zmod5 (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ZMod 5)) = (m * (m - 1) / 2 : ℕ) := by
  have h : (∑ i ∈ Finset.range m, i) = m * (m - 1) / 2 := Finset.sum_range_id m
  have hcast : ((∑ i ∈ Finset.range m, i : ℕ) : ZMod 5) =
      (m * (m - 1) / 2 : ℕ) :=
    congrArg (fun t : ℕ => (t : ZMod 5)) h
  simpa using hcast

private lemma mod5_of_triangular_eq (m : ℕ) (hmpos : 0 < m)
    (hEq : (m : ZMod 5) = (m * (m - 1) / 2 : ℕ)) :
    m % 5 = 0 ∨ m % 5 = 3 := by
  have hm1 : 1 ≤ m := by omega
  have heven : Even (m * (m - 1)) := by
    have h : Even ((m - 1) * ((m - 1) + 1)) := Nat.even_mul_succ_self (m - 1)
    have hpred : (m - 1) + 1 = m := by omega
    simpa [hpred, Nat.mul_comm] using h
  have hdoubleNat : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
    Nat.two_mul_div_two_of_even heven
  have hEq2 : ((2 : ℕ) : ZMod 5) * (m : ZMod 5) = (m : ZMod 5) * ((m : ZMod 5) - 1) := by
    calc
      ((2 : ℕ) : ZMod 5) * (m : ZMod 5) = ((2 * m : ℕ) : ZMod 5) := by simp
      _ = ((2 * (m * (m - 1) / 2) : ℕ) : ZMod 5) := by
            simpa using congrArg (fun t : ZMod 5 => ((2 : ℕ) : ZMod 5) * t) hEq
      _ = (m * (m - 1) : ℕ) := by simp [hdoubleNat]
      _ = (m : ZMod 5) * ((m : ZMod 5) - 1) := by simp [Nat.cast_sub hm1]
  have hm5lt : m % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases hm5 : m % 5
  · left
    rfl
  · exfalso
    have hm : m = 1 + 5 * (m / 5) := by
      simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 1 := by
      rw [hm]
      calc
        (((1 + 5 * (m / 5) : ℕ) : ZMod 5)) = (1 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 1 := by simp [h5cast]
    have hcontr : ((2 : ℕ) : ZMod 5) * 1 = (1 : ZMod 5) * (1 - 1) := by
      simpa [hmcast] using hEq2
    have h20 : ((2 : ℕ) : ZMod 5) ≠ 0 := by decide
    exact h20 hcontr
  · exfalso
    have hm : m = 2 + 5 * (m / 5) := by
      simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 2 := by
      rw [hm]
      calc
        (((2 + 5 * (m / 5) : ℕ) : ZMod 5)) = (2 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 2 := by simp [h5cast]
    have hcontr : ((2 : ℕ) : ZMod 5) * 2 = (2 : ZMod 5) * (2 - 1) := by
      simpa [hmcast] using hEq2
    have h42 : ((4 : ℕ) : ZMod 5) ≠ 2 := by decide
    simpa [Nat.cast_mul] using h42 hcontr
  · right
    rfl
  · exfalso
    have hm : m = 4 + 5 * (m / 5) := by
      simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 4 := by
      rw [hm]
      calc
        (((4 + 5 * (m / 5) : ℕ) : ZMod 5)) = (4 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 4 := by simp [h5cast]
    have hcontr : ((2 : ℕ) : ZMod 5) * 4 = (4 : ZMod 5) * (4 - 1) := by
      simpa [hmcast] using hEq2
    have h31 : ((3 : ℕ) : ZMod 5) ≠ 2 := by decide
    have hcontr' : ((3 : ℕ) : ZMod 5) = 2 := by
      simpa [Nat.cast_mul] using hcontr
    exact h31 hcontr'

/-- **Mod-5 obstruction for exponents `k ≡ 1 (mod 4)`.**

In this exponent class, any solution must satisfy `m ≡ 0` or `3 (mod 5)`. -/
theorem mod_five_obstruction_of_mod_four_eq_one {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 4 = 1) :
    m % 5 = 0 ∨ m % 5 = 3 := by
  rcases hsol with ⟨hmpos, _hkpos, hEq⟩
  have hpow : ((m ^ k : ℕ) : ZMod 5) = (m : ZMod 5) := by
    simpa [Nat.cast_pow] using (zmod5_pow_eq_self_of_mod_four_eq_one (m : ZMod 5) hk)
  have hsum : ((powerSum m k : ℕ) : ZMod 5) = (m * (m - 1) / 2 : ℕ) := by
    calc
      ((powerSum m k : ℕ) : ZMod 5) = ∑ i ∈ Finset.range m, (i : ZMod 5) :=
        powerSum_cast_zmod5_of_mod_four_eq_one m k hk
      _ = (m * (m - 1) / 2 : ℕ) := sum_range_cast_zmod5 m
  have hcastEq : (m : ZMod 5) = (m * (m - 1) / 2 : ℕ) := by
    calc
      (m : ZMod 5) = ((m ^ k : ℕ) : ZMod 5) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 5) := by
        exact congrArg (fun t : ℕ => (t : ZMod 5)) hEq.symm
      _ = (m * (m - 1) / 2 : ℕ) := hsum
  exact mod5_of_triangular_eq m hmpos hcastEq

private lemma sum_range_cube_nat (m : ℕ) :
    (∑ i ∈ Finset.range m, i ^ 3) = (m * (m - 1) / 2) ^ 2 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      let A : ℕ := m * (m - 1) / 2
      have htri : ((m + 1) * ((m + 1) - 1) / 2) = A + m := by
        simpa [A, Nat.add_sub_cancel] using (Nat.triangle_succ m)
      rw [htri]
      have heven : Even (m * (m - 1)) := by
        rcases Nat.even_or_odd m with hmEven | hmOdd
        · exact hmEven.mul_right (m - 1)
        · rcases hmOdd with ⟨t, ht⟩
          have hsub : m - 1 = 2 * t := by
            rw [ht]
            omega
          rw [hsub]
          have hEven2t : Even (2 * t) := ⟨t, by ring⟩
          exact hEven2t.mul_left m
      have hA : 2 * A = m * (m - 1) := by
        simpa [A] using (Nat.two_mul_div_two_of_even heven)
      have hAplus : 2 * A + m = m * m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · subst hm0
          simp [A]
        · have hsum1 : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hmpos)
          calc
            2 * A + m = m * (m - 1) + m := by rw [hA]
            _ = m * (m - 1) + m * 1 := by simp
            _ = m * ((m - 1) + 1) := by rw [Nat.mul_add]
            _ = m * m := by rw [hsum1]
      have haux : 2 * A * m + m ^ 2 = m ^ 3 := by
        calc
          2 * A * m + m ^ 2 = m * (2 * A + m) := by ring
          _ = m * (m * m) := by rw [hAplus]
          _ = m ^ 3 := by ring
      calc
        A ^ 2 + m ^ 3 = A ^ 2 + (2 * A * m + m ^ 2) := by rw [haux]
        _ = (A + m) ^ 2 := by ring

private lemma zmod5_pow_eq_cube_of_mod_four_eq_three (a : ZMod 5) {k : ℕ}
    (hk : k % 4 = 3) : a ^ k = a ^ 3 := by
  have hk' : ∃ t : ℕ, k = 4 * t + 3 := by
    refine ⟨k / 4, ?_⟩
    omega
  rcases hk' with ⟨t, rfl⟩
  fin_cases a
  · simp
  · simp
  · have h4 : ((2 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (2 : ZMod 5) ^ (4 * t + 3) = ((2 : ZMod 5) ^ (4 * t)) * ((2 : ZMod 5) ^ 3) := by
        rw [pow_add]
      _ = (((2 : ZMod 5) ^ 4) ^ t) * ((2 : ZMod 5) ^ 3) := by
        rw [pow_mul]
      _ = (2 : ZMod 5) ^ 3 := by simp [h4]
  · have h4 : ((3 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (3 : ZMod 5) ^ (4 * t + 3) = ((3 : ZMod 5) ^ (4 * t)) * ((3 : ZMod 5) ^ 3) := by
        rw [pow_add]
      _ = (((3 : ZMod 5) ^ 4) ^ t) * ((3 : ZMod 5) ^ 3) := by
        rw [pow_mul]
      _ = (3 : ZMod 5) ^ 3 := by simp [h4]
  · have h4 : ((4 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (4 : ZMod 5) ^ (4 * t + 3) = ((4 : ZMod 5) ^ (4 * t)) * ((4 : ZMod 5) ^ 3) := by
        rw [pow_add]
      _ = (((4 : ZMod 5) ^ 4) ^ t) * ((4 : ZMod 5) ^ 3) := by
        rw [pow_mul]
      _ = (4 : ZMod 5) ^ 3 := by simp [h4]

private lemma powerSum_cast_zmod5_of_mod_four_eq_three (m k : ℕ) (hk : k % 4 = 3) :
    ((powerSum m k : ℕ) : ZMod 5) = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ 3 := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 5) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 5) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ 3 := by
      simp_rw [zmod5_pow_eq_cube_of_mod_four_eq_three _ hk]

private lemma sum_range_cube_cast_zmod5 (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ZMod 5) ^ 3) = ((m * (m - 1) / 2) ^ 2 : ℕ) := by
  have h : (∑ i ∈ Finset.range m, i ^ 3) = (m * (m - 1) / 2) ^ 2 := sum_range_cube_nat m
  have hcast : ((∑ i ∈ Finset.range m, i ^ 3 : ℕ) : ZMod 5) = ((m * (m - 1) / 2) ^ 2 : ℕ) :=
    congrArg (fun t : ℕ => (t : ZMod 5)) h
  simpa [Nat.cast_pow] using hcast

private lemma mod5_zero_of_poly (m : ℕ)
    (hpoly : ((m : ZMod 5) ^ 2) * (((m : ZMod 5) ^ 2) - (m : ZMod 5) + 1) = 0) :
    m % 5 = 0 := by
  have hm5lt : m % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases hm5 : m % 5
  · rfl
  · exfalso
    have hm : m = 1 + 5 * (m / 5) := by simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 1 := by
      rw [hm]
      calc
        (((1 + 5 * (m / 5) : ℕ) : ZMod 5)) = (1 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 1 := by simp [h5cast]
    rw [hmcast] at hpoly
    have h10 : ((1 : ZMod 5) ^ 2) * (((1 : ZMod 5) ^ 2) - (1 : ZMod 5) + 1) ≠ 0 := by decide
    exact h10 hpoly
  · exfalso
    have hm : m = 2 + 5 * (m / 5) := by simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 2 := by
      rw [hm]
      calc
        (((2 + 5 * (m / 5) : ℕ) : ZMod 5)) = (2 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 2 := by simp [h5cast]
    rw [hmcast] at hpoly
    have h20 : ((2 : ZMod 5) ^ 2) * (((2 : ZMod 5) ^ 2) - (2 : ZMod 5) + 1) ≠ 0 := by decide
    exact h20 hpoly
  · exfalso
    have hm : m = 3 + 5 * (m / 5) := by simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 3 := by
      rw [hm]
      calc
        (((3 + 5 * (m / 5) : ℕ) : ZMod 5)) = (3 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 3 := by simp [h5cast]
    rw [hmcast] at hpoly
    have h30 : ((3 : ZMod 5) ^ 2) * (((3 : ZMod 5) ^ 2) - (3 : ZMod 5) + 1) ≠ 0 := by decide
    exact h30 hpoly
  · exfalso
    have hm : m = 4 + 5 * (m / 5) := by simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 4 := by
      rw [hm]
      calc
        (((4 + 5 * (m / 5) : ℕ) : ZMod 5)) = (4 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 4 := by simp [h5cast]
    rw [hmcast] at hpoly
    have h40 : ((4 : ZMod 5) ^ 2) * (((4 : ZMod 5) ^ 2) - (4 : ZMod 5) + 1) ≠ 0 := by decide
    exact h40 hpoly

/-- **Mod-5 obstruction for exponents `k ≡ 3 (mod 4)`.**

In this exponent class, any solution must satisfy `m ≡ 0 (mod 5)`. -/
theorem mod_five_obstruction_of_mod_four_eq_three {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 4 = 3) :
    m % 5 = 0 := by
  rcases hsol with ⟨hmpos, _hkpos, hEq⟩
  have hm1 : 1 ≤ m := by omega
  have hpow : ((m ^ k : ℕ) : ZMod 5) = (m : ZMod 5) ^ 3 := by
    calc
      ((m ^ k : ℕ) : ZMod 5) = (m : ZMod 5) ^ k := by simp [Nat.cast_pow]
      _ = (m : ZMod 5) ^ 3 := zmod5_pow_eq_cube_of_mod_four_eq_three (m : ZMod 5) hk
  have hsum : ((powerSum m k : ℕ) : ZMod 5) = ((m * (m - 1) / 2) ^ 2 : ℕ) := by
    calc
      ((powerSum m k : ℕ) : ZMod 5) = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ 3 :=
        powerSum_cast_zmod5_of_mod_four_eq_three m k hk
      _ = ((m * (m - 1) / 2) ^ 2 : ℕ) := sum_range_cube_cast_zmod5 m
  have hEqCast : (m : ZMod 5) ^ 3 = ((m * (m - 1) / 2) ^ 2 : ℕ) := by
    calc
      (m : ZMod 5) ^ 3 = ((m ^ k : ℕ) : ZMod 5) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 5) := by
        exact congrArg (fun t : ℕ => (t : ZMod 5)) hEq.symm
      _ = ((m * (m - 1) / 2) ^ 2 : ℕ) := hsum
  let B : ℕ := m * (m - 1) / 2
  have heven : Even (m * (m - 1)) := by
    rcases Nat.even_or_odd m with hmEven | hmOdd
    · exact hmEven.mul_right (m - 1)
    · rcases hmOdd with ⟨t, ht⟩
      have hsub : m - 1 = 2 * t := by
        rw [ht]
        omega
      rw [hsub]
      have hEven2t : Even (2 * t) := ⟨t, by ring⟩
      exact hEven2t.mul_left m
  have hdoubleNat : 2 * B = m * (m - 1) := by
    simpa [B] using (Nat.two_mul_div_two_of_even heven)
  have hdoubleCast : ((2 : ℕ) : ZMod 5) * (B : ZMod 5) = (m : ZMod 5) * ((m : ZMod 5) - 1) := by
    calc
      ((2 : ℕ) : ZMod 5) * (B : ZMod 5) = ((2 * B : ℕ) : ZMod 5) := by simp
      _ = (m * (m - 1) : ℕ) := by simp [hdoubleNat]
      _ = (m : ZMod 5) * ((m : ZMod 5) - 1) := by simp [Nat.cast_sub hm1]
  have hEqBsq : ((B ^ 2 : ℕ) : ZMod 5) = (m : ZMod 5) ^ 3 := by
    simpa [B] using hEqCast.symm
  have hEqBsq' : ((B : ZMod 5) ^ 2) = (m : ZMod 5) ^ 3 := by
    simpa [Nat.cast_pow] using hEqBsq
  have hpoly : ((m : ZMod 5) ^ 2) * (((m : ZMod 5) ^ 2) - (m : ZMod 5) + 1) = 0 := by
    have h2sq : (((2 : ℕ) : ZMod 5) * (B : ZMod 5)) ^ 2 =
        ((m : ZMod 5) * ((m : ZMod 5) - 1)) ^ 2 := by
      simpa using congrArg (fun t : ZMod 5 => t ^ 2) hdoubleCast
    have hleft : (((2 : ℕ) : ZMod 5) * (B : ZMod 5)) ^ 2 =
        (4 : ZMod 5) * ((m : ZMod 5) ^ 3) := by
      calc
        (((2 : ℕ) : ZMod 5) * (B : ZMod 5)) ^ 2 =
            (((2 : ℕ) : ZMod 5) ^ 2) * ((B : ZMod 5) ^ 2) := by
          ring
        _ = (4 : ZMod 5) * ((m : ZMod 5) ^ 3) := by
          have h22 : (((2 : ℕ) : ZMod 5) ^ 2) = 4 := by decide
          rw [h22, hEqBsq']
    have hright : (((m : ZMod 5) * ((m : ZMod 5) - 1)) ^ 2) =
        ((m : ZMod 5) ^ 2) * (((m : ZMod 5) - 1) ^ 2) := by
      ring
    have hmain : (4 : ZMod 5) * ((m : ZMod 5) ^ 3) =
        ((m : ZMod 5) ^ 2) * (((m : ZMod 5) - 1) ^ 2) := by
      calc
        (4 : ZMod 5) * ((m : ZMod 5) ^ 3) = (((2 : ℕ) : ZMod 5) * (B : ZMod 5)) ^ 2 := hleft.symm
        _ = (((m : ZMod 5) * ((m : ZMod 5) - 1)) ^ 2) := h2sq
        _ = ((m : ZMod 5) ^ 2) * (((m : ZMod 5) - 1) ^ 2) := hright
    have hmain' : ((m : ZMod 5) ^ 2) * (((m : ZMod 5) - 1) ^ 2) -
        (4 : ZMod 5) * ((m : ZMod 5) ^ 3) = 0 := by
      apply sub_eq_zero.mpr
      simpa [eq_comm] using hmain
    have hpoly0 : ((m : ZMod 5) ^ 2) * ((((m : ZMod 5) - 1) ^ 2) -
        (4 : ZMod 5) * (m : ZMod 5)) = 0 := by
      calc
        ((m : ZMod 5) ^ 2) * ((((m : ZMod 5) - 1) ^ 2) - (4 : ZMod 5) * (m : ZMod 5)) =
            ((m : ZMod 5) ^ 2) * (((m : ZMod 5) - 1) ^ 2) - (4 : ZMod 5) * ((m : ZMod 5) ^ 3) := by
          ring
        _ = 0 := hmain'
    have h6 : (6 : ZMod 5) = 1 := by decide
    have hrewrite : ((m : ZMod 5) ^ 2) * (((m : ZMod 5) ^ 2) - (m : ZMod 5) + 1) =
        ((m : ZMod 5) ^ 2) * ((((m : ZMod 5) - 1) ^ 2) - (4 : ZMod 5) * (m : ZMod 5)) := by
      ring_nf
      simp [h6]
    rw [hrewrite]
    exact hpoly0
  exact mod5_zero_of_poly m hpoly

private lemma six_mul_sum_range_sq_nat (m : ℕ) :
    6 * (∑ i ∈ Finset.range m, i ^ 2) = m * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      by_cases hm0 : m = 0
      · subst hm0
        norm_num
      · have hm1 : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hm0)
        have hm2 : 1 ≤ 2 * m := by nlinarith
        have hpoly :
            m * (m - 1) * (2 * m - 1) + 6 * m ^ 2 = (m + 1) * m * (2 * m + 1) := by
          have hZ :
              ((m * (m - 1) * (2 * m - 1) + 6 * m ^ 2 : ℕ) : ℤ) =
              (((m + 1) * m * (2 * m + 1) : ℕ) : ℤ) := by
            simp [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hm1, Nat.cast_sub hm2]
            ring
          exact_mod_cast hZ
        have htarget :
            (m + 1) * (m + 1 - 1) * (2 * (m + 1) - 1) = (m + 1) * m * (2 * m + 1) := by
          rw [Nat.add_sub_cancel]
          have hinner : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
          rw [hinner]
        rw [hpoly, htarget]

private lemma zmod5_pow_eq_sq_of_mod_four_eq_two (a : ZMod 5) {k : ℕ}
    (hk : k % 4 = 2) : a ^ k = a ^ 2 := by
  have hk' : ∃ t : ℕ, k = 4 * t + 2 := by
    refine ⟨k / 4, ?_⟩
    omega
  rcases hk' with ⟨t, rfl⟩
  fin_cases a
  · simp
  · simp
  · have h4 : ((2 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (2 : ZMod 5) ^ (4 * t + 2) = ((2 : ZMod 5) ^ (4 * t)) * ((2 : ZMod 5) ^ 2) := by
        rw [pow_add]
      _ = (((2 : ZMod 5) ^ 4) ^ t) * ((2 : ZMod 5) ^ 2) := by
        rw [pow_mul]
      _ = (2 : ZMod 5) ^ 2 := by simp [h4]
  · have h4 : ((3 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (3 : ZMod 5) ^ (4 * t + 2) = ((3 : ZMod 5) ^ (4 * t)) * ((3 : ZMod 5) ^ 2) := by
        rw [pow_add]
      _ = (((3 : ZMod 5) ^ 4) ^ t) * ((3 : ZMod 5) ^ 2) := by
        rw [pow_mul]
      _ = (3 : ZMod 5) ^ 2 := by simp [h4]
  · have h4 : ((4 : ZMod 5) ^ 4) = 1 := by decide
    calc
      (4 : ZMod 5) ^ (4 * t + 2) = ((4 : ZMod 5) ^ (4 * t)) * ((4 : ZMod 5) ^ 2) := by
        rw [pow_add]
      _ = (((4 : ZMod 5) ^ 4) ^ t) * ((4 : ZMod 5) ^ 2) := by
        rw [pow_mul]
      _ = (4 : ZMod 5) ^ 2 := by simp [h4]

private lemma powerSum_cast_zmod5_of_mod_four_eq_two (m k : ℕ) (hk : k % 4 = 2) :
    ((powerSum m k : ℕ) : ZMod 5) = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ 2 := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 5) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 5) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ 2 := by
      simp_rw [zmod5_pow_eq_sq_of_mod_four_eq_two _ hk]

private lemma mod5_zero_of_even_poly (m : ℕ)
    (hpoly : (m : ZMod 5) * (2 * (m : ZMod 5) ^ 2 - 4 * (m : ZMod 5) + 1) = 0) :
    m % 5 = 0 := by
  have hm5lt : m % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases hm5 : m % 5
  · rfl
  · exfalso
    have hm : m = 1 + 5 * (m / 5) := by
      simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 1 := by
      rw [hm]
      calc
        (((1 + 5 * (m / 5) : ℕ) : ZMod 5)) = (1 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 1 := by simp [h5cast]
    rw [hmcast] at hpoly
    have h10 : (1 : ZMod 5) * (2 * (1 : ZMod 5) ^ 2 - 4 * (1 : ZMod 5) + 1) ≠ 0 := by decide
    exact h10 hpoly
  · exfalso
    have hm : m = 2 + 5 * (m / 5) := by
      simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 2 := by
      rw [hm]
      calc
        (((2 + 5 * (m / 5) : ℕ) : ZMod 5)) = (2 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 2 := by simp [h5cast]
    rw [hmcast] at hpoly
    have h20 : (2 : ZMod 5) * (2 * (2 : ZMod 5) ^ 2 - 4 * (2 : ZMod 5) + 1) ≠ 0 := by decide
    exact h20 hpoly
  · exfalso
    have hm : m = 3 + 5 * (m / 5) := by
      simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 3 := by
      rw [hm]
      calc
        (((3 + 5 * (m / 5) : ℕ) : ZMod 5)) = (3 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 3 := by simp [h5cast]
    rw [hmcast] at hpoly
    have h30 : (3 : ZMod 5) * (2 * (3 : ZMod 5) ^ 2 - 4 * (3 : ZMod 5) + 1) ≠ 0 := by decide
    exact h30 hpoly
  · exfalso
    have hm : m = 4 + 5 * (m / 5) := by
      simpa [hm5] using (Nat.mod_add_div m 5).symm
    have h5cast : ((5 * (m / 5) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff (5 * (m / 5)) 5).2 (dvd_mul_right 5 _)
    have hmcast : (m : ZMod 5) = 4 := by
      rw [hm]
      calc
        (((4 + 5 * (m / 5) : ℕ) : ZMod 5)) = (4 : ZMod 5) + ((5 * (m / 5) : ℕ) : ZMod 5) := by
          simp
        _ = 4 := by simp [h5cast]
    rw [hmcast] at hpoly
    have h40 : (4 : ZMod 5) * (2 * (4 : ZMod 5) ^ 2 - 4 * (4 : ZMod 5) + 1) ≠ 0 := by decide
    exact h40 hpoly

/-- **Even mod-5 obstruction for `k ≡ 2 (mod 4)`.**

In this even exponent class, any solution must satisfy `m ≡ 0 (mod 5)`. -/
theorem mod_five_obstruction_of_mod_four_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 4 = 2) :
    m % 5 = 0 := by
  rcases hsol with ⟨hmpos, _hkpos, hEq⟩
  have hm1 : 1 ≤ m := by omega
  have hpow : ((m ^ k : ℕ) : ZMod 5) = (m : ZMod 5) ^ 2 := by
    calc
      ((m ^ k : ℕ) : ZMod 5) = (m : ZMod 5) ^ k := by simp [Nat.cast_pow]
      _ = (m : ZMod 5) ^ 2 := zmod5_pow_eq_sq_of_mod_four_eq_two (m : ZMod 5) hk
  have hsum : ((powerSum m k : ℕ) : ZMod 5) = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ 2 := by
    exact powerSum_cast_zmod5_of_mod_four_eq_two m k hk
  have hEqCast : (m : ZMod 5) ^ 2 = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ 2 := by
    calc
      (m : ZMod 5) ^ 2 = ((m ^ k : ℕ) : ZMod 5) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 5) := by
        exact congrArg (fun t : ℕ => (t : ZMod 5)) hEq.symm
      _ = ∑ i ∈ Finset.range m, (i : ZMod 5) ^ 2 := hsum
  have hsqNatCast :
      (∑ i ∈ Finset.range m, (i : ZMod 5) ^ 2) = ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 5) := by
    simp [Nat.cast_pow]
  have hsixNat : 6 * (∑ i ∈ Finset.range m, i ^ 2) = m * (m - 1) * (2 * m - 1) :=
    six_mul_sum_range_sq_nat m
  have hsixCast :
      (((6 : ℕ) : ZMod 5) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 5)) =
        (m * (m - 1) * (2 * m - 1) : ℕ) := by
    calc
      (((6 : ℕ) : ZMod 5) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 5)) =
          ((6 * (∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ℕ) : ZMod 5) := by simp
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := by
        exact congrArg (fun t : ℕ => (t : ZMod 5)) hsixNat
  have hEq6 :
      (((6 : ℕ) : ZMod 5) * ((m : ZMod 5) ^ 2)) =
        (m * (m - 1) * (2 * m - 1) : ℕ) := by
    calc
      (((6 : ℕ) : ZMod 5) * ((m : ZMod 5) ^ 2)) =
          (((6 : ℕ) : ZMod 5) * (∑ i ∈ Finset.range m, (i : ZMod 5) ^ 2)) := by
        rw [hEqCast]
      _ = (((6 : ℕ) : ZMod 5) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 5)) := by
        rw [hsqNatCast]
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := hsixCast
  have hEq2 : (m : ZMod 5) ^ 2 = (m * (m - 1) * (2 * m - 1) : ℕ) := by
    have h6 : ((6 : ℕ) : ZMod 5) = 1 := by decide
    have h6mul : (((6 : ℕ) : ZMod 5) * ((m : ZMod 5) ^ 2)) = (m : ZMod 5) ^ 2 := by
      calc
        (((6 : ℕ) : ZMod 5) * ((m : ZMod 5) ^ 2)) =
            ((1 : ZMod 5) * ((m : ZMod 5) ^ 2)) := by
          exact congrArg (fun t : ZMod 5 => t * ((m : ZMod 5) ^ 2)) h6
        _ = (m : ZMod 5) ^ 2 := by simp
    calc
      (m : ZMod 5) ^ 2 = (((6 : ℕ) : ZMod 5) * ((m : ZMod 5) ^ 2)) := h6mul.symm
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := hEq6
  have hpoly : (m : ZMod 5) * (2 * (m : ZMod 5) ^ 2 - 4 * (m : ZMod 5) + 1) = 0 := by
    have hm2 : 1 ≤ 2 * m := by nlinarith [hmpos]
    have hEq2' : (m : ZMod 5) ^ 2 =
        (m : ZMod 5) * ((m : ZMod 5) - 1) * (2 * (m : ZMod 5) - 1) := by
      calc
        (m : ZMod 5) ^ 2 = (m * (m - 1) * (2 * m - 1) : ℕ) := hEq2
        _ = (m : ZMod 5) * ((m : ZMod 5) - 1) * (2 * (m : ZMod 5) - 1) := by
          simp [Nat.cast_sub hm1, Nat.cast_sub hm2]
    have hmain :
        (m : ZMod 5) ^ 2 -
          ((m : ZMod 5) * ((m : ZMod 5) - 1) * (2 * (m : ZMod 5) - 1)) = 0 := by
      exact sub_eq_zero.mpr hEq2'
    have hrew :
        (m : ZMod 5) ^ 2 -
            ((m : ZMod 5) * ((m : ZMod 5) - 1) * (2 * (m : ZMod 5) - 1)) =
          -((m : ZMod 5) * (2 * (m : ZMod 5) ^ 2 - 4 * (m : ZMod 5) + 1)) := by
      ring
    have hneg : -((m : ZMod 5) * (2 * (m : ZMod 5) ^ 2 - 4 * (m : ZMod 5) + 1)) = 0 := by
      simpa [hrew] using hmain
    exact neg_eq_zero.mp hneg
  exact mod5_zero_of_even_poly m hpoly

/-- Combining mod-4 with the `k ≡ 2 (mod 4)` even mod-5 obstruction:
solutions in this branch satisfy `m ≡ 0` or `15 (mod 20)`. -/
theorem mod_twenty_obstruction_of_mod_four_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 4 = 2) :
    m % 20 = 0 ∨ m % 20 = 15 := by
  have h4 : m % 4 = 0 ∨ m % 4 = 3 := mod_four_obstruction hsol
  have h5 : m % 5 = 0 := mod_five_obstruction_of_mod_four_eq_two hsol hk
  have hm20lt : m % 20 < 20 := Nat.mod_lt _ (by decide)
  interval_cases hm20 : m % 20
  · left
    rfl
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · right
    rfl
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega

private lemma zmod7_pow_eq_sq_of_mod_six_eq_two (a : ZMod 7) {k : ℕ}
    (hk : k % 6 = 2) : a ^ k = a ^ 2 := by
  have hk' : ∃ t : ℕ, k = 6 * t + 2 := by
    refine ⟨k / 6, ?_⟩
    omega
  rcases hk' with ⟨t, rfl⟩
  fin_cases a
  · simp
  · simp
  · have h6 : ((2 : ZMod 7) ^ 6) = 1 := by decide
    calc
      (2 : ZMod 7) ^ (6 * t + 2) = ((2 : ZMod 7) ^ (6 * t)) * ((2 : ZMod 7) ^ 2) := by
        rw [pow_add]
      _ = (((2 : ZMod 7) ^ 6) ^ t) * ((2 : ZMod 7) ^ 2) := by
        rw [pow_mul]
      _ = (2 : ZMod 7) ^ 2 := by simp [h6]
  · have h6 : ((3 : ZMod 7) ^ 6) = 1 := by decide
    calc
      (3 : ZMod 7) ^ (6 * t + 2) = ((3 : ZMod 7) ^ (6 * t)) * ((3 : ZMod 7) ^ 2) := by
        rw [pow_add]
      _ = (((3 : ZMod 7) ^ 6) ^ t) * ((3 : ZMod 7) ^ 2) := by
        rw [pow_mul]
      _ = (3 : ZMod 7) ^ 2 := by simp [h6]
  · have h6 : ((4 : ZMod 7) ^ 6) = 1 := by decide
    calc
      (4 : ZMod 7) ^ (6 * t + 2) = ((4 : ZMod 7) ^ (6 * t)) * ((4 : ZMod 7) ^ 2) := by
        rw [pow_add]
      _ = (((4 : ZMod 7) ^ 6) ^ t) * ((4 : ZMod 7) ^ 2) := by
        rw [pow_mul]
      _ = (4 : ZMod 7) ^ 2 := by simp [h6]
  · have h6 : ((5 : ZMod 7) ^ 6) = 1 := by decide
    calc
      (5 : ZMod 7) ^ (6 * t + 2) = ((5 : ZMod 7) ^ (6 * t)) * ((5 : ZMod 7) ^ 2) := by
        rw [pow_add]
      _ = (((5 : ZMod 7) ^ 6) ^ t) * ((5 : ZMod 7) ^ 2) := by
        rw [pow_mul]
      _ = (5 : ZMod 7) ^ 2 := by simp [h6]
  · have h6 : ((6 : ZMod 7) ^ 6) = 1 := by decide
    calc
      (6 : ZMod 7) ^ (6 * t + 2) = ((6 : ZMod 7) ^ (6 * t)) * ((6 : ZMod 7) ^ 2) := by
        rw [pow_add]
      _ = (((6 : ZMod 7) ^ 6) ^ t) * ((6 : ZMod 7) ^ 2) := by
        rw [pow_mul]
      _ = (6 : ZMod 7) ^ 2 := by simp [h6]

private lemma powerSum_cast_zmod7_of_mod_six_eq_two (m k : ℕ) (hk : k % 6 = 2) :
    ((powerSum m k : ℕ) : ZMod 7) = ∑ i ∈ Finset.range m, (i : ZMod 7) ^ 2 := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 7) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 7) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 7) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (i : ZMod 7) ^ 2 := by
      simp_rw [zmod7_pow_eq_sq_of_mod_six_eq_two _ hk]

private lemma mod7_zero_of_even_poly (m : ℕ)
    (hpoly : (m : ZMod 7) * (2 * (m : ZMod 7) ^ 2 - 2 * (m : ZMod 7) + 1) = 0) :
    m % 7 = 0 := by
  have hm7lt : m % 7 < 7 := Nat.mod_lt _ (by decide)
  interval_cases hm7 : m % 7
  · rfl
  · exfalso
    have hm : m = 1 + 7 * (m / 7) := by
      simpa [hm7] using (Nat.mod_add_div m 7).symm
    have h7cast : ((7 * (m / 7) : ℕ) : ZMod 7) = 0 :=
      (ZMod.natCast_eq_zero_iff (7 * (m / 7)) 7).2 (dvd_mul_right 7 _)
    have hmcast : (m : ZMod 7) = 1 := by
      rw [hm]
      calc
        (((1 + 7 * (m / 7) : ℕ) : ZMod 7)) = (1 : ZMod 7) + ((7 * (m / 7) : ℕ) : ZMod 7) := by
          simp
        _ = 1 := by simp [h7cast]
    rw [hmcast] at hpoly
    have h10 : (1 : ZMod 7) * (2 * (1 : ZMod 7) ^ 2 - 2 * (1 : ZMod 7) + 1) ≠ 0 := by decide
    exact h10 hpoly
  · exfalso
    have hm : m = 2 + 7 * (m / 7) := by
      simpa [hm7] using (Nat.mod_add_div m 7).symm
    have h7cast : ((7 * (m / 7) : ℕ) : ZMod 7) = 0 :=
      (ZMod.natCast_eq_zero_iff (7 * (m / 7)) 7).2 (dvd_mul_right 7 _)
    have hmcast : (m : ZMod 7) = 2 := by
      rw [hm]
      calc
        (((2 + 7 * (m / 7) : ℕ) : ZMod 7)) = (2 : ZMod 7) + ((7 * (m / 7) : ℕ) : ZMod 7) := by
          simp
        _ = 2 := by simp [h7cast]
    rw [hmcast] at hpoly
    have h20 : (2 : ZMod 7) * (2 * (2 : ZMod 7) ^ 2 - 2 * (2 : ZMod 7) + 1) ≠ 0 := by decide
    exact h20 hpoly
  · exfalso
    have hm : m = 3 + 7 * (m / 7) := by
      simpa [hm7] using (Nat.mod_add_div m 7).symm
    have h7cast : ((7 * (m / 7) : ℕ) : ZMod 7) = 0 :=
      (ZMod.natCast_eq_zero_iff (7 * (m / 7)) 7).2 (dvd_mul_right 7 _)
    have hmcast : (m : ZMod 7) = 3 := by
      rw [hm]
      calc
        (((3 + 7 * (m / 7) : ℕ) : ZMod 7)) = (3 : ZMod 7) + ((7 * (m / 7) : ℕ) : ZMod 7) := by
          simp
        _ = 3 := by simp [h7cast]
    rw [hmcast] at hpoly
    have h30 : (3 : ZMod 7) * (2 * (3 : ZMod 7) ^ 2 - 2 * (3 : ZMod 7) + 1) ≠ 0 := by decide
    exact h30 hpoly
  · exfalso
    have hm : m = 4 + 7 * (m / 7) := by
      simpa [hm7] using (Nat.mod_add_div m 7).symm
    have h7cast : ((7 * (m / 7) : ℕ) : ZMod 7) = 0 :=
      (ZMod.natCast_eq_zero_iff (7 * (m / 7)) 7).2 (dvd_mul_right 7 _)
    have hmcast : (m : ZMod 7) = 4 := by
      rw [hm]
      calc
        (((4 + 7 * (m / 7) : ℕ) : ZMod 7)) = (4 : ZMod 7) + ((7 * (m / 7) : ℕ) : ZMod 7) := by
          simp
        _ = 4 := by simp [h7cast]
    rw [hmcast] at hpoly
    have h40 : (4 : ZMod 7) * (2 * (4 : ZMod 7) ^ 2 - 2 * (4 : ZMod 7) + 1) ≠ 0 := by decide
    exact h40 hpoly
  · exfalso
    have hm : m = 5 + 7 * (m / 7) := by
      simpa [hm7] using (Nat.mod_add_div m 7).symm
    have h7cast : ((7 * (m / 7) : ℕ) : ZMod 7) = 0 :=
      (ZMod.natCast_eq_zero_iff (7 * (m / 7)) 7).2 (dvd_mul_right 7 _)
    have hmcast : (m : ZMod 7) = 5 := by
      rw [hm]
      calc
        (((5 + 7 * (m / 7) : ℕ) : ZMod 7)) = (5 : ZMod 7) + ((7 * (m / 7) : ℕ) : ZMod 7) := by
          simp
        _ = 5 := by simp [h7cast]
    rw [hmcast] at hpoly
    have h50 : (5 : ZMod 7) * (2 * (5 : ZMod 7) ^ 2 - 2 * (5 : ZMod 7) + 1) ≠ 0 := by decide
    exact h50 hpoly
  · exfalso
    have hm : m = 6 + 7 * (m / 7) := by
      simpa [hm7] using (Nat.mod_add_div m 7).symm
    have h7cast : ((7 * (m / 7) : ℕ) : ZMod 7) = 0 :=
      (ZMod.natCast_eq_zero_iff (7 * (m / 7)) 7).2 (dvd_mul_right 7 _)
    have hmcast : (m : ZMod 7) = 6 := by
      rw [hm]
      calc
        (((6 + 7 * (m / 7) : ℕ) : ZMod 7)) = (6 : ZMod 7) + ((7 * (m / 7) : ℕ) : ZMod 7) := by
          simp
        _ = 6 := by simp [h7cast]
    rw [hmcast] at hpoly
    have h60 : (6 : ZMod 7) * (2 * (6 : ZMod 7) ^ 2 - 2 * (6 : ZMod 7) + 1) ≠ 0 := by decide
    exact h60 hpoly

/-- **Even mod-7 obstruction for `k ≡ 2 (mod 6)`.**

In this exponent class, any solution must satisfy `m ≡ 0 (mod 7)`. -/
theorem mod_seven_obstruction_of_mod_six_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 6 = 2) :
    m % 7 = 0 := by
  rcases hsol with ⟨hmpos, _hkpos, hEq⟩
  have hm1 : 1 ≤ m := by omega
  have hpow : ((m ^ k : ℕ) : ZMod 7) = (m : ZMod 7) ^ 2 := by
    calc
      ((m ^ k : ℕ) : ZMod 7) = (m : ZMod 7) ^ k := by simp [Nat.cast_pow]
      _ = (m : ZMod 7) ^ 2 := zmod7_pow_eq_sq_of_mod_six_eq_two (m : ZMod 7) hk
  have hsum : ((powerSum m k : ℕ) : ZMod 7) = ∑ i ∈ Finset.range m, (i : ZMod 7) ^ 2 := by
    exact powerSum_cast_zmod7_of_mod_six_eq_two m k hk
  have hEqCast : (m : ZMod 7) ^ 2 = ∑ i ∈ Finset.range m, (i : ZMod 7) ^ 2 := by
    calc
      (m : ZMod 7) ^ 2 = ((m ^ k : ℕ) : ZMod 7) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 7) := by
        exact congrArg (fun t : ℕ => (t : ZMod 7)) hEq.symm
      _ = ∑ i ∈ Finset.range m, (i : ZMod 7) ^ 2 := hsum
  have hsqNatCast :
      (∑ i ∈ Finset.range m, (i : ZMod 7) ^ 2) = ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 7) := by
    simp [Nat.cast_pow]
  have hsixNat : 6 * (∑ i ∈ Finset.range m, i ^ 2) = m * (m - 1) * (2 * m - 1) :=
    six_mul_sum_range_sq_nat m
  have hsixCast :
      (((6 : ℕ) : ZMod 7) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 7)) =
        (m * (m - 1) * (2 * m - 1) : ℕ) := by
    calc
      (((6 : ℕ) : ZMod 7) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 7)) =
          ((6 * (∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ℕ) : ZMod 7) := by simp
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := by
        exact congrArg (fun t : ℕ => (t : ZMod 7)) hsixNat
  have hEq6 :
      (((6 : ℕ) : ZMod 7) * ((m : ZMod 7) ^ 2)) =
        (m * (m - 1) * (2 * m - 1) : ℕ) := by
    calc
      (((6 : ℕ) : ZMod 7) * ((m : ZMod 7) ^ 2)) =
          (((6 : ℕ) : ZMod 7) * (∑ i ∈ Finset.range m, (i : ZMod 7) ^ 2)) := by
        rw [hEqCast]
      _ = (((6 : ℕ) : ZMod 7) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 7)) := by
        rw [hsqNatCast]
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := hsixCast
  have hm2 : 1 ≤ 2 * m := by nlinarith [hmpos]
  have hEq6' :
      (((6 : ℕ) : ZMod 7) * ((m : ZMod 7) ^ 2)) =
        (m : ZMod 7) * ((m : ZMod 7) - 1) * (2 * (m : ZMod 7) - 1) := by
    calc
      (((6 : ℕ) : ZMod 7) * ((m : ZMod 7) ^ 2)) = (m * (m - 1) * (2 * m - 1) : ℕ) := hEq6
      _ = (m : ZMod 7) * ((m : ZMod 7) - 1) * (2 * (m : ZMod 7) - 1) := by
        simp [Nat.cast_sub hm1, Nat.cast_sub hm2]
  have hmain :
      (m : ZMod 7) * ((m : ZMod 7) - 1) * (2 * (m : ZMod 7) - 1) -
        (((6 : ℕ) : ZMod 7) * ((m : ZMod 7) ^ 2)) = 0 := by
    exact sub_eq_zero.mpr hEq6'.symm
  have hrew9 :
      (m : ZMod 7) * ((m : ZMod 7) - 1) * (2 * (m : ZMod 7) - 1) -
          (((6 : ℕ) : ZMod 7) * ((m : ZMod 7) ^ 2)) =
        (m : ZMod 7) * (2 * (m : ZMod 7) ^ 2 - 9 * (m : ZMod 7) + 1) := by
    ring
  have hpoly9 : (m : ZMod 7) * (2 * (m : ZMod 7) ^ 2 - 9 * (m : ZMod 7) + 1) = 0 := by
    rw [hrew9] at hmain
    exact hmain
  have h9 : (9 : ZMod 7) = 2 := by decide
  have hpoly : (m : ZMod 7) * (2 * (m : ZMod 7) ^ 2 - 2 * (m : ZMod 7) + 1) = 0 := by
    simpa [h9] using hpoly9
  exact mod7_zero_of_even_poly m hpoly

private lemma zmod13_pow_eq_sq_of_mod_twelve_eq_two (a : ZMod 13) {k : ℕ}
    (hk : k % 12 = 2) : a ^ k = a ^ 2 := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hk' : ∃ t : ℕ, k = 12 * t + 2 := by
    refine ⟨k / 12, ?_⟩
    omega
  rcases hk' with ⟨t, rfl⟩
  have h12 : a ^ 12 = (if a ≠ 0 then (1 : ZMod 13) else 0) := by
    simpa using (ZMod.pow_card_sub_one (p := 13) a)
  calc
    a ^ (12 * t + 2) = (a ^ (12 * t)) * (a ^ 2) := by
      rw [pow_add]
    _ = (a ^ 12) ^ t * (a ^ 2) := by
      rw [pow_mul]
    _ = (if a ≠ 0 then (1 : ZMod 13) else 0) ^ t * (a ^ 2) := by
      rw [h12]
    _ = a ^ 2 := by
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha]

private lemma powerSum_cast_zmod13_of_mod_twelve_eq_two (m k : ℕ) (hk : k % 12 = 2) :
    ((powerSum m k : ℕ) : ZMod 13) = ∑ i ∈ Finset.range m, (i : ZMod 13) ^ 2 := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 13) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 13) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 13) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (i : ZMod 13) ^ 2 := by
      simp_rw [zmod13_pow_eq_sq_of_mod_twelve_eq_two _ hk]

private lemma mod13_zero_of_even_poly (m : ℕ)
    (hpoly : (m : ZMod 13) * (2 * (m : ZMod 13) ^ 2 - 9 * (m : ZMod 13) + 1) = 0) :
    m % 13 = 0 := by
  have hroots : ∀ x : ZMod 13, x * (2 * x ^ 2 - 9 * x + 1) = 0 → x = 0 := by
    decide
  have hmz : (m : ZMod 13) = 0 := hroots (m : ZMod 13) hpoly
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff m 13).1 hmz)

/-- **Even mod-13 obstruction for `k ≡ 2 (mod 12)`.**

In this exponent class, any solution must satisfy `m ≡ 0 (mod 13)`. -/
theorem mod_thirteen_obstruction_of_mod_twelve_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 12 = 2) :
    m % 13 = 0 := by
  rcases hsol with ⟨hmpos, _hkpos, hEq⟩
  have hm1 : 1 ≤ m := by omega
  have hpow : ((m ^ k : ℕ) : ZMod 13) = (m : ZMod 13) ^ 2 := by
    calc
      ((m ^ k : ℕ) : ZMod 13) = (m : ZMod 13) ^ k := by simp [Nat.cast_pow]
      _ = (m : ZMod 13) ^ 2 := zmod13_pow_eq_sq_of_mod_twelve_eq_two (m : ZMod 13) hk
  have hsum : ((powerSum m k : ℕ) : ZMod 13) = ∑ i ∈ Finset.range m, (i : ZMod 13) ^ 2 := by
    exact powerSum_cast_zmod13_of_mod_twelve_eq_two m k hk
  have hEqCast : (m : ZMod 13) ^ 2 = ∑ i ∈ Finset.range m, (i : ZMod 13) ^ 2 := by
    calc
      (m : ZMod 13) ^ 2 = ((m ^ k : ℕ) : ZMod 13) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 13) := by
        exact congrArg (fun t : ℕ => (t : ZMod 13)) hEq.symm
      _ = ∑ i ∈ Finset.range m, (i : ZMod 13) ^ 2 := hsum
  have hsqNatCast :
      (∑ i ∈ Finset.range m, (i : ZMod 13) ^ 2) =
        ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 13) := by
    simp [Nat.cast_pow]
  have hsixNat : 6 * (∑ i ∈ Finset.range m, i ^ 2) = m * (m - 1) * (2 * m - 1) :=
    six_mul_sum_range_sq_nat m
  have hsixCast :
      (((6 : ℕ) : ZMod 13) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 13)) =
        (m * (m - 1) * (2 * m - 1) : ℕ) := by
    calc
      (((6 : ℕ) : ZMod 13) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 13)) =
          ((6 * (∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ℕ) : ZMod 13) := by simp
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := by
        exact congrArg (fun t : ℕ => (t : ZMod 13)) hsixNat
  have hEq6 :
      (((6 : ℕ) : ZMod 13) * ((m : ZMod 13) ^ 2)) =
        (m * (m - 1) * (2 * m - 1) : ℕ) := by
    calc
      (((6 : ℕ) : ZMod 13) * ((m : ZMod 13) ^ 2)) =
          (((6 : ℕ) : ZMod 13) * (∑ i ∈ Finset.range m, (i : ZMod 13) ^ 2)) := by
        rw [hEqCast]
      _ = (((6 : ℕ) : ZMod 13) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 13)) := by
        rw [hsqNatCast]
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := hsixCast
  have hm2 : 1 ≤ 2 * m := by nlinarith [hmpos]
  have hEq6' :
      (((6 : ℕ) : ZMod 13) * ((m : ZMod 13) ^ 2)) =
        (m : ZMod 13) * ((m : ZMod 13) - 1) * (2 * (m : ZMod 13) - 1) := by
    calc
      (((6 : ℕ) : ZMod 13) * ((m : ZMod 13) ^ 2)) = (m * (m - 1) * (2 * m - 1) : ℕ) := hEq6
      _ = (m : ZMod 13) * ((m : ZMod 13) - 1) * (2 * (m : ZMod 13) - 1) := by
        simp [Nat.cast_sub hm1, Nat.cast_sub hm2]
  have hmain :
      (m : ZMod 13) * ((m : ZMod 13) - 1) * (2 * (m : ZMod 13) - 1) -
        (((6 : ℕ) : ZMod 13) * ((m : ZMod 13) ^ 2)) = 0 := by
    exact sub_eq_zero.mpr hEq6'.symm
  have hrew9 :
      (m : ZMod 13) * ((m : ZMod 13) - 1) * (2 * (m : ZMod 13) - 1) -
          (((6 : ℕ) : ZMod 13) * ((m : ZMod 13) ^ 2)) =
        (m : ZMod 13) * (2 * (m : ZMod 13) ^ 2 - 9 * (m : ZMod 13) + 1) := by
    ring
  have hpoly : (m : ZMod 13) * (2 * (m : ZMod 13) ^ 2 - 9 * (m : ZMod 13) + 1) = 0 := by
    rw [hrew9] at hmain
    exact hmain
  exact mod13_zero_of_even_poly m hpoly

private lemma zmod11_pow_eq_sq_of_mod_ten_eq_two (a : ZMod 11) {k : ℕ}
    (hk : k % 10 = 2) : a ^ k = a ^ 2 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hk' : ∃ t : ℕ, k = 10 * t + 2 := by
    refine ⟨k / 10, ?_⟩
    omega
  rcases hk' with ⟨t, rfl⟩
  have h10 : a ^ 10 = (if a ≠ 0 then (1 : ZMod 11) else 0) := by
    simpa using (ZMod.pow_card_sub_one (p := 11) a)
  calc
    a ^ (10 * t + 2) = (a ^ (10 * t)) * (a ^ 2) := by
      rw [pow_add]
    _ = (a ^ 10) ^ t * (a ^ 2) := by
      rw [pow_mul]
    _ = (if a ≠ 0 then (1 : ZMod 11) else 0) ^ t * (a ^ 2) := by
      rw [h10]
    _ = a ^ 2 := by
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha]

private lemma powerSum_cast_zmod11_of_mod_ten_eq_two (m k : ℕ) (hk : k % 10 = 2) :
    ((powerSum m k : ℕ) : ZMod 11) = ∑ i ∈ Finset.range m, (i : ZMod 11) ^ 2 := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 11) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 11) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 11) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (i : ZMod 11) ^ 2 := by
      simp_rw [zmod11_pow_eq_sq_of_mod_ten_eq_two _ hk]

private lemma mod11_zero_of_even_poly (m : ℕ)
    (hpoly : (m : ZMod 11) * (2 * (m : ZMod 11) ^ 2 - 9 * (m : ZMod 11) + 1) = 0) :
    m % 11 = 0 := by
  have hroots : ∀ x : ZMod 11, x * (2 * x ^ 2 - 9 * x + 1) = 0 → x = 0 := by
    decide
  have hmz : (m : ZMod 11) = 0 := hroots (m : ZMod 11) hpoly
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff m 11).1 hmz)

/-- **Even mod-11 obstruction for `k ≡ 2 (mod 10)`.**

In this exponent class, any solution must satisfy `m ≡ 0 (mod 11)`. -/
theorem mod_eleven_obstruction_of_mod_ten_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 10 = 2) :
    m % 11 = 0 := by
  rcases hsol with ⟨hmpos, _hkpos, hEq⟩
  have hm1 : 1 ≤ m := by omega
  have hpow : ((m ^ k : ℕ) : ZMod 11) = (m : ZMod 11) ^ 2 := by
    calc
      ((m ^ k : ℕ) : ZMod 11) = (m : ZMod 11) ^ k := by simp [Nat.cast_pow]
      _ = (m : ZMod 11) ^ 2 := zmod11_pow_eq_sq_of_mod_ten_eq_two (m : ZMod 11) hk
  have hsum : ((powerSum m k : ℕ) : ZMod 11) = ∑ i ∈ Finset.range m, (i : ZMod 11) ^ 2 := by
    exact powerSum_cast_zmod11_of_mod_ten_eq_two m k hk
  have hEqCast : (m : ZMod 11) ^ 2 = ∑ i ∈ Finset.range m, (i : ZMod 11) ^ 2 := by
    calc
      (m : ZMod 11) ^ 2 = ((m ^ k : ℕ) : ZMod 11) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 11) := by
        exact congrArg (fun t : ℕ => (t : ZMod 11)) hEq.symm
      _ = ∑ i ∈ Finset.range m, (i : ZMod 11) ^ 2 := hsum
  have hsqNatCast :
      (∑ i ∈ Finset.range m, (i : ZMod 11) ^ 2) =
        ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 11) := by
    simp [Nat.cast_pow]
  have hsixNat : 6 * (∑ i ∈ Finset.range m, i ^ 2) = m * (m - 1) * (2 * m - 1) :=
    six_mul_sum_range_sq_nat m
  have hsixCast :
      (((6 : ℕ) : ZMod 11) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 11)) =
        (m * (m - 1) * (2 * m - 1) : ℕ) := by
    calc
      (((6 : ℕ) : ZMod 11) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 11)) =
          ((6 * (∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ℕ) : ZMod 11) := by simp
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := by
        exact congrArg (fun t : ℕ => (t : ZMod 11)) hsixNat
  have hEq6 :
      (((6 : ℕ) : ZMod 11) * ((m : ZMod 11) ^ 2)) =
        (m * (m - 1) * (2 * m - 1) : ℕ) := by
    calc
      (((6 : ℕ) : ZMod 11) * ((m : ZMod 11) ^ 2)) =
          (((6 : ℕ) : ZMod 11) * (∑ i ∈ Finset.range m, (i : ZMod 11) ^ 2)) := by
        rw [hEqCast]
      _ = (((6 : ℕ) : ZMod 11) * ((∑ i ∈ Finset.range m, i ^ 2 : ℕ) : ZMod 11)) := by
        rw [hsqNatCast]
      _ = (m * (m - 1) * (2 * m - 1) : ℕ) := hsixCast
  have hm2 : 1 ≤ 2 * m := by nlinarith [hmpos]
  have hEq6' :
      (((6 : ℕ) : ZMod 11) * ((m : ZMod 11) ^ 2)) =
        (m : ZMod 11) * ((m : ZMod 11) - 1) * (2 * (m : ZMod 11) - 1) := by
    calc
      (((6 : ℕ) : ZMod 11) * ((m : ZMod 11) ^ 2)) = (m * (m - 1) * (2 * m - 1) : ℕ) := hEq6
      _ = (m : ZMod 11) * ((m : ZMod 11) - 1) * (2 * (m : ZMod 11) - 1) := by
        simp [Nat.cast_sub hm1, Nat.cast_sub hm2]
  have hmain :
      (m : ZMod 11) * ((m : ZMod 11) - 1) * (2 * (m : ZMod 11) - 1) -
        (((6 : ℕ) : ZMod 11) * ((m : ZMod 11) ^ 2)) = 0 := by
    exact sub_eq_zero.mpr hEq6'.symm
  have hrew9 :
      (m : ZMod 11) * ((m : ZMod 11) - 1) * (2 * (m : ZMod 11) - 1) -
          (((6 : ℕ) : ZMod 11) * ((m : ZMod 11) ^ 2)) =
        (m : ZMod 11) * (2 * (m : ZMod 11) ^ 2 - 9 * (m : ZMod 11) + 1) := by
    ring
  have hpoly : (m : ZMod 11) * (2 * (m : ZMod 11) ^ 2 - 9 * (m : ZMod 11) + 1) = 0 := by
    rw [hrew9] at hmain
    exact hmain
  exact mod11_zero_of_even_poly m hpoly

/-- Combining `k ≡ 2 (mod 4)` mod-5 and `k ≡ 2 (mod 6)` mod-7 obstructions.

If `k ≡ 2 (mod 12)`, then every solution satisfies `m ≡ 0 (mod 35)`. -/
theorem mod_thirtyfive_obstruction_of_mod_twelve_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 12 = 2) :
    m % 35 = 0 := by
  have hk4 : k % 4 = 2 := by omega
  have hk6 : k % 6 = 2 := by omega
  have h5 : m % 5 = 0 := mod_five_obstruction_of_mod_four_eq_two hsol hk4
  have h7 : m % 7 = 0 := mod_seven_obstruction_of_mod_six_eq_two hsol hk6
  have h5dvd : 5 ∣ m := Nat.dvd_of_mod_eq_zero h5
  have h7dvd : 7 ∣ m := Nat.dvd_of_mod_eq_zero h7
  have h35dvd : 35 ∣ m := by
    have hcop : Nat.Coprime 5 7 := by decide
    have hmul : 5 * 7 ∣ m := hcop.mul_dvd_of_dvd_of_dvd h5dvd h7dvd
    simpa [Nat.mul_comm] using hmul
  exact Nat.mod_eq_zero_of_dvd h35dvd

private lemma mod4_of_three_mul_eq_zero (a : ℕ) (h : (3 * a) % 4 = 0) :
    a % 4 = 0 := by
  have ha4lt : a % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases ha : a % 4
  · rfl
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega

private lemma mod4_of_three_mul_eq_three (a : ℕ) (h : (3 * a) % 4 = 3) :
    a % 4 = 1 := by
  have ha4lt : a % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases ha : a % 4
  · exfalso
    omega
  · rfl
  · exfalso
    omega
  · exfalso
    omega

/-- Combining the `k ≡ 2 (mod 12)` mod-35 obstruction with the global mod-4 obstruction.

Solutions in this branch satisfy `m ≡ 0` or `35 (mod 140)`. -/
theorem mod_one_forty_obstruction_of_mod_twelve_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 12 = 2) :
    m % 140 = 0 ∨ m % 140 = 35 := by
  have h35 : m % 35 = 0 := mod_thirtyfive_obstruction_of_mod_twelve_eq_two hsol hk
  have h4 : m % 4 = 0 ∨ m % 4 = 3 := mod_four_obstruction hsol
  let a : ℕ := m / 35
  have hm : m = 35 * a := by
    simp [a]
    simpa [h35] using (Nat.mod_add_div m 35).symm
  have hm4eq : m % 4 = (3 * a) % 4 := by
    rw [hm, Nat.mul_mod]
    norm_num
  rcases h4 with h40 | h43
  · left
    have h3a0 : (3 * a) % 4 = 0 := by simpa [hm4eq] using h40
    have ha0 : a % 4 = 0 := mod4_of_three_mul_eq_zero a h3a0
    have ha : a = 4 * (a / 4) := by
      simpa [ha0] using (Nat.mod_add_div a 4).symm
    rw [hm, ha]
    have h140dvd : 140 ∣ 35 * (4 * (a / 4)) := by
      refine ⟨a / 4, ?_⟩
      ring
    exact Nat.mod_eq_zero_of_dvd h140dvd
  · right
    have h3a3 : (3 * a) % 4 = 3 := by simpa [hm4eq] using h43
    have ha1 : a % 4 = 1 := mod4_of_three_mul_eq_three a h3a3
    have ha : a = 1 + 4 * (a / 4) := by
      simpa [ha1] using (Nat.mod_add_div a 4).symm
    rw [hm, ha]
    have hm140 : (35 * (1 + 4 * (a / 4))) % 140 = 35 := by
      have hdecomp : 35 * (1 + 4 * (a / 4)) = 35 + 140 * (a / 4) := by ring
      rw [hdecomp]
      omega
    exact hm140

/-- Adding the `k ≡ 2 (mod 12)` mod-13 obstruction to the mod-35 chain.

In this branch, every solution satisfies `m ≡ 0 (mod 455)`. -/
theorem mod_four_hundred_fifty_five_obstruction_of_mod_twelve_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 12 = 2) :
    m % 455 = 0 := by
  have h35 : m % 35 = 0 := mod_thirtyfive_obstruction_of_mod_twelve_eq_two hsol hk
  have h13 : m % 13 = 0 := mod_thirteen_obstruction_of_mod_twelve_eq_two hsol hk
  have h35dvd : 35 ∣ m := Nat.dvd_of_mod_eq_zero h35
  have h13dvd : 13 ∣ m := Nat.dvd_of_mod_eq_zero h13
  have h455dvd : 455 ∣ m := by
    have hcop : Nat.Coprime 35 13 := by decide
    have hmul : 35 * 13 ∣ m := hcop.mul_dvd_of_dvd_of_dvd h35dvd h13dvd
    simpa [Nat.mul_comm] using hmul
  exact Nat.mod_eq_zero_of_dvd h455dvd

/-- Combining the `k ≡ 2 (mod 12)` mod-455 obstruction with the global mod-4 obstruction.

Solutions in this branch satisfy `m ≡ 0` or `455 (mod 1820)`. -/
theorem mod_one_thousand_eight_hundred_twenty_obstruction_of_mod_twelve_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 12 = 2) :
    m % 1820 = 0 ∨ m % 1820 = 455 := by
  have h455 : m % 455 = 0 := mod_four_hundred_fifty_five_obstruction_of_mod_twelve_eq_two hsol hk
  have h4 : m % 4 = 0 ∨ m % 4 = 3 := mod_four_obstruction hsol
  let a : ℕ := m / 455
  have hm : m = 455 * a := by
    simp [a]
    simpa [h455] using (Nat.mod_add_div m 455).symm
  have hm4eq : m % 4 = (3 * a) % 4 := by
    rw [hm, Nat.mul_mod]
    norm_num
  rcases h4 with h40 | h43
  · left
    have h3a0 : (3 * a) % 4 = 0 := by simpa [hm4eq] using h40
    have ha0 : a % 4 = 0 := mod4_of_three_mul_eq_zero a h3a0
    have ha : a = 4 * (a / 4) := by
      simpa [ha0] using (Nat.mod_add_div a 4).symm
    rw [hm, ha]
    have h1820dvd : 1820 ∣ 455 * (4 * (a / 4)) := by
      refine ⟨a / 4, ?_⟩
      ring
    exact Nat.mod_eq_zero_of_dvd h1820dvd
  · right
    have h3a3 : (3 * a) % 4 = 3 := by simpa [hm4eq] using h43
    have ha1 : a % 4 = 1 := mod4_of_three_mul_eq_three a h3a3
    have ha : a = 1 + 4 * (a / 4) := by
      simpa [ha1] using (Nat.mod_add_div a 4).symm
    rw [hm, ha]
    have hm1820 : (455 * (1 + 4 * (a / 4))) % 1820 = 455 := by
      have hdecomp : 455 * (1 + 4 * (a / 4)) = 455 + 1820 * (a / 4) := by ring
      rw [hdecomp]
      omega
    exact hm1820

/-- Combining `k ≡ 2 (mod 12)` and `k ≡ 2 (mod 10)` branches.

If `k ≡ 2 (mod 60)`, then every solution satisfies `m ≡ 0 (mod 5005)`. -/
theorem mod_five_thousand_five_obstruction_of_mod_sixty_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 60 = 2) :
    m % 5005 = 0 := by
  have hk12 : k % 12 = 2 := by omega
  have hk10 : k % 10 = 2 := by omega
  have h455 : m % 455 = 0 := mod_four_hundred_fifty_five_obstruction_of_mod_twelve_eq_two hsol hk12
  have h11 : m % 11 = 0 := mod_eleven_obstruction_of_mod_ten_eq_two hsol hk10
  have h455dvd : 455 ∣ m := Nat.dvd_of_mod_eq_zero h455
  have h11dvd : 11 ∣ m := Nat.dvd_of_mod_eq_zero h11
  have h5005dvd : 5005 ∣ m := by
    have hcop : Nat.Coprime 455 11 := by decide
    have hmul : 455 * 11 ∣ m := hcop.mul_dvd_of_dvd_of_dvd h455dvd h11dvd
    simpa [Nat.mul_comm] using hmul
  exact Nat.mod_eq_zero_of_dvd h5005dvd

/-- Adding the global mod-4 obstruction to the `k ≡ 2 (mod 60)` mod-5005 branch.

Solutions in this branch satisfy `m ≡ 0` or `15015 (mod 20020)`. -/
theorem mod_twenty_thousand_twenty_obstruction_of_mod_sixty_eq_two {m k : ℕ}
    (hsol : IsSolution m k) (hk : k % 60 = 2) :
    m % 20020 = 0 ∨ m % 20020 = 15015 := by
  have h5005 : m % 5005 = 0 := mod_five_thousand_five_obstruction_of_mod_sixty_eq_two hsol hk
  have h4 : m % 4 = 0 ∨ m % 4 = 3 := mod_four_obstruction hsol
  let a : ℕ := m / 5005
  have hm : m = 5005 * a := by
    simp [a]
    simpa [h5005] using (Nat.mod_add_div m 5005).symm
  have hm4eq : m % 4 = a % 4 := by
    rw [hm, Nat.mul_mod]
    norm_num
  rcases h4 with h40 | h43
  · left
    have ha0 : a % 4 = 0 := by simpa [hm4eq] using h40
    have ha : a = 4 * (a / 4) := by
      simpa [ha0] using (Nat.mod_add_div a 4).symm
    rw [hm, ha]
    have h20020dvd : 20020 ∣ 5005 * (4 * (a / 4)) := by
      refine ⟨a / 4, ?_⟩
      ring
    exact Nat.mod_eq_zero_of_dvd h20020dvd
  · right
    have ha3 : a % 4 = 3 := by simpa [hm4eq] using h43
    have ha : a = 3 + 4 * (a / 4) := by
      simpa [ha3] using (Nat.mod_add_div a 4).symm
    rw [hm, ha]
    have hm20020 : (5005 * (3 + 4 * (a / 4))) % 20020 = 15015 := by
      have hdecomp : 5005 * (3 + 4 * (a / 4)) = 15015 + 20020 * (a / 4) := by ring
      rw [hdecomp]
      omega
    exact hm20020

private lemma zmod8_sq_eq_one_of_odd (i : ℕ) (hiodd : Odd i) :
    ((i : ZMod 8) ^ 2) = 1 := by
  have hi1 : 1 ≤ i ^ 2 := by
    rcases hiodd with ⟨q, rfl⟩
    have hpos : 0 < (2 * q + 1) ^ 2 := by positivity
    exact Nat.succ_le_of_lt hpos
  have h8dvd : 8 ∣ i ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hiodd
  have hzero : ((i ^ 2 - 1 : ℕ) : ZMod 8) = 0 :=
    (ZMod.natCast_eq_zero_iff (i ^ 2 - 1) 8).2 h8dvd
  have hsub : ((i ^ 2 - 1 : ℕ) : ZMod 8) = ((i : ZMod 8) ^ 2) - 1 := by
    simp [Nat.cast_sub hi1, Nat.cast_pow]
  have hsub' : ((i : ZMod 8) ^ 2) - 1 = 0 := by simpa [hsub] using hzero
  exact sub_eq_zero.mp hsub'

private lemma zmod8_pow_eq_self_of_odd (i k : ℕ) (hiodd : Odd i) (hkodd : Odd k) :
    ((i : ZMod 8) ^ k) = (i : ZMod 8) := by
  rcases hkodd with ⟨t, rfl⟩
  have hsq : ((i : ZMod 8) ^ 2) = 1 := zmod8_sq_eq_one_of_odd i hiodd
  calc
    (i : ZMod 8) ^ (2 * t + 1) = ((i : ZMod 8) ^ (2 * t)) * (i : ZMod 8) := by
      rw [pow_add, pow_one]
    _ = (((i : ZMod 8) ^ 2) ^ t) * (i : ZMod 8) := by
      rw [pow_mul]
    _ = (i : ZMod 8) := by simp [hsq]

private lemma zmod8_pow_eq_zero_of_even_ge_three (i k : ℕ) (hieven : Even i) (hk3 : 3 ≤ k) :
    ((i : ZMod 8) ^ k) = 0 := by
  have h2dvd : (2 : ℕ) ∣ i := by
    rcases hieven with ⟨q, rfl⟩
    exact ⟨q, by ring⟩
  have hpowdvd : (2 : ℕ) ^ k ∣ i ^ k := pow_dvd_pow_of_dvd h2dvd k
  have h2pow3dvd : (2 : ℕ) ^ 3 ∣ (2 : ℕ) ^ k := Nat.pow_dvd_pow 2 hk3
  have h8dvd : 8 ∣ i ^ k := by
    rw [← show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact dvd_trans h2pow3dvd hpowdvd
  have hzeroNat : ((i ^ k : ℕ) : ZMod 8) = 0 :=
    (ZMod.natCast_eq_zero_iff (i ^ k) 8).2 h8dvd
  simpa [Nat.cast_pow] using hzeroNat

private lemma zmod8_pow_eq_if_odd_of_odd_ge_three (i k : ℕ) (hkodd : Odd k) (hk3 : 3 ≤ k) :
    ((i : ZMod 8) ^ k) = if Odd i then (i : ZMod 8) else 0 := by
  by_cases hiodd : Odd i
  · simp [hiodd, zmod8_pow_eq_self_of_odd i k hiodd hkodd]
  · have hieven : Even i := Nat.not_odd_iff_even.mp hiodd
    simp [hiodd, zmod8_pow_eq_zero_of_even_ge_three i k hieven hk3]

private lemma powerSum_cast_zmod8_of_odd_ge_three (m k : ℕ) (hkodd : Odd k) (hk3 : 3 ≤ k) :
    ((powerSum m k : ℕ) : ZMod 8) = ∑ i ∈ Finset.range m, (if Odd i then (i : ZMod 8) else 0) := by
  unfold powerSum
  calc
    ((∑ i ∈ Finset.range m, i ^ k : ℕ) : ZMod 8) =
        ∑ i ∈ Finset.range m, ((i ^ k : ℕ) : ZMod 8) := by
      simp
    _ = ∑ i ∈ Finset.range m, (i : ZMod 8) ^ k := by
      simp [Nat.cast_pow]
    _ = ∑ i ∈ Finset.range m, (if Odd i then (i : ZMod 8) else 0) := by
      simp_rw [zmod8_pow_eq_if_odd_of_odd_ge_three _ _ hkodd hk3]

private lemma odd_indicator_sum_nat (m : ℕ) :
    (∑ i ∈ Finset.range m, if Odd i then i else 0) = (m / 2) ^ 2 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      set q : ℕ := m / 2
      by_cases hodd : Odd m
      · have hm : m = 2 * q + 1 := by
          calc
            m = 2 * (m / 2) + 1 := by
              simpa using (Nat.two_mul_div_two_add_one_of_odd hodd).symm
            _ = 2 * q + 1 := by simp [q]
        rw [if_pos hodd, hm]
        have hdivSucc : (2 * q + 1 + 1) / 2 = q + 1 := by omega
        rw [hdivSucc]
        ring
      · have heven : Even m := Nat.not_odd_iff_even.mp hodd
        have hm : m = 2 * q := by
          calc
            m = 2 * (m / 2) := by
              simpa using (Nat.two_mul_div_two_of_even heven).symm
            _ = 2 * q := by simp [q]
        rw [if_neg hodd, hm]
        have hdiv : (2 * q + 1) / 2 = q := by omega
        rw [hdiv]
        simp

private lemma odd_indicator_sum_cast_zmod8 (m : ℕ) :
    (∑ i ∈ Finset.range m, if Odd i then (i : ZMod 8) else 0) = ((m / 2) ^ 2 : ℕ) := by
  have hNat : (∑ i ∈ Finset.range m, if Odd i then i else 0) = (m / 2) ^ 2 :=
    odd_indicator_sum_nat m
  have hCast :
      (((∑ i ∈ Finset.range m, if Odd i then i else 0) : ℕ) : ZMod 8) = ((m / 2) ^ 2 : ℕ) := by
    exact congrArg (fun t : ℕ => (t : ZMod 8)) hNat
  simpa using hCast

private lemma zmod8_sq_four_mul (q : ℕ) :
    (((4 * q) ^ 2 : ℕ) : ZMod 8) = 0 := by
  have h8dvd : 8 ∣ (4 * q) ^ 2 := by
    refine ⟨2 * q ^ 2, ?_⟩
    ring
  exact (ZMod.natCast_eq_zero_iff ((4 * q) ^ 2) 8).2 h8dvd

private lemma zmod8_sq_one_add_four_mul (q : ℕ) :
    (((1 + 4 * q) ^ 2 : ℕ) : ZMod 8) = 1 := by
  have hEq : (1 + 4 * q) ^ 2 = 1 + 8 * (q + 2 * q ^ 2) := by ring
  rw [hEq]
  have hz : ((8 * (q + 2 * q ^ 2) : ℕ) : ZMod 8) = 0 :=
    (ZMod.natCast_eq_zero_iff (8 * (q + 2 * q ^ 2)) 8).2 (dvd_mul_right 8 _)
  calc
    (((1 + 8 * (q + 2 * q ^ 2) : ℕ) : ZMod 8)) =
        (1 : ZMod 8) + ((8 * (q + 2 * q ^ 2) : ℕ) : ZMod 8) := by
      simp
    _ = 1 := by simp [hz]

private lemma zmod8_sq_two_add_four_mul (q : ℕ) :
    (((2 + 4 * q) ^ 2 : ℕ) : ZMod 8) = 4 := by
  have hEq : (2 + 4 * q) ^ 2 = 4 + 8 * (2 * q + 2 * q ^ 2) := by ring
  rw [hEq]
  have hz : ((8 * (2 * q + 2 * q ^ 2) : ℕ) : ZMod 8) = 0 :=
    (ZMod.natCast_eq_zero_iff (8 * (2 * q + 2 * q ^ 2)) 8).2 (dvd_mul_right 8 _)
  calc
    (((4 + 8 * (2 * q + 2 * q ^ 2) : ℕ) : ZMod 8)) =
        (4 : ZMod 8) + ((8 * (2 * q + 2 * q ^ 2) : ℕ) : ZMod 8) := by
      simp
    _ = 4 := by simp [hz]

private lemma zmod8_sq_three_add_four_mul (q : ℕ) :
    (((3 + 4 * q) ^ 2 : ℕ) : ZMod 8) = 1 := by
  have hEq : (3 + 4 * q) ^ 2 = 1 + 8 * (1 + 3 * q + 2 * q ^ 2) := by ring
  rw [hEq]
  have hz : ((8 * (1 + 3 * q + 2 * q ^ 2) : ℕ) : ZMod 8) = 0 :=
    (ZMod.natCast_eq_zero_iff (8 * (1 + 3 * q + 2 * q ^ 2)) 8).2 (dvd_mul_right 8 _)
  calc
    (((1 + 8 * (1 + 3 * q + 2 * q ^ 2) : ℕ) : ZMod 8)) =
        (1 : ZMod 8) + ((8 * (1 + 3 * q + 2 * q ^ 2) : ℕ) : ZMod 8) := by
      simp
    _ = 1 := by simp [hz]

/-- **Third modular obstruction (odd exponents at least `3` force `m ≡ 0 (mod 8)`).** -/
theorem mod_eight_obstruction_of_odd_ge_three {m k : ℕ}
    (hsol : IsSolution m k) (hkodd : Odd k) (hk3 : 3 ≤ k) :
    m % 8 = 0 := by
  rcases hsol with ⟨_hmpos, _hk, hEq⟩
  have hpow : ((m ^ k : ℕ) : ZMod 8) = if Odd m then (m : ZMod 8) else 0 := by
    calc
      ((m ^ k : ℕ) : ZMod 8) = (m : ZMod 8) ^ k := by simp [Nat.cast_pow]
      _ = if Odd m then (m : ZMod 8) else 0 := zmod8_pow_eq_if_odd_of_odd_ge_three m k hkodd hk3
  have hsum : ((powerSum m k : ℕ) : ZMod 8) = ((m / 2) ^ 2 : ℕ) := by
    calc
      ((powerSum m k : ℕ) : ZMod 8) =
          ∑ i ∈ Finset.range m, if Odd i then (i : ZMod 8) else 0 :=
        powerSum_cast_zmod8_of_odd_ge_three m k hkodd hk3
      _ = ((m / 2) ^ 2 : ℕ) := odd_indicator_sum_cast_zmod8 m
  have hEqCast : (if Odd m then (m : ZMod 8) else 0) = ((m / 2) ^ 2 : ℕ) := by
    calc
      (if Odd m then (m : ZMod 8) else 0) = ((m ^ k : ℕ) : ZMod 8) := hpow.symm
      _ = ((powerSum m k : ℕ) : ZMod 8) := by
        exact congrArg (fun t : ℕ => (t : ZMod 8)) hEq.symm
      _ = ((m / 2) ^ 2 : ℕ) := hsum
  have hm8lt : m % 8 < 8 := Nat.mod_lt _ (by decide)
  interval_cases hm8 : m % 8
  · rfl
  · exfalso
    have hm : m = 1 + 8 * (m / 8) := by
      simpa [hm8] using (Nat.mod_add_div m 8).symm
    have hoddm : Odd m := by
      refine ⟨4 * (m / 8), ?_⟩
      omega
    have hleft : (if Odd m then (m : ZMod 8) else 0) = 1 := by
      have h8cast : ((8 * (m / 8) : ℕ) : ZMod 8) = 0 :=
        (ZMod.natCast_eq_zero_iff (8 * (m / 8)) 8).2 (dvd_mul_right 8 _)
      rw [if_pos hoddm, hm]
      calc
        (((1 + 8 * (m / 8) : ℕ) : ZMod 8)) =
            (1 : ZMod 8) + ((8 * (m / 8) : ℕ) : ZMod 8) := by
          simp
        _ = 1 := by simp [h8cast]
    have hhalf : m / 2 = 4 * (m / 8) := by
      rw [hm]
      omega
    have hright : (((m / 2) ^ 2 : ℕ) : ZMod 8) = 0 := by
      rw [hhalf]
      exact zmod8_sq_four_mul (m / 8)
    rw [hleft, hright] at hEqCast
    have h10 : (1 : ZMod 8) ≠ 0 := by decide
    exact h10 hEqCast
  · exfalso
    have hm : m = 2 + 8 * (m / 8) := by
      simpa [hm8] using (Nat.mod_add_div m 8).symm
    have hevenm : Even m := by
      refine ⟨1 + 4 * (m / 8), ?_⟩
      omega
    have hoddm : ¬Odd m := Nat.not_odd_iff_even.mpr hevenm
    have hleft : (if Odd m then (m : ZMod 8) else 0) = 0 := by
      simp [hoddm]
    have hhalf : m / 2 = 1 + 4 * (m / 8) := by
      rw [hm]
      omega
    have hright : (((m / 2) ^ 2 : ℕ) : ZMod 8) = 1 := by
      rw [hhalf]
      exact zmod8_sq_one_add_four_mul (m / 8)
    rw [hleft, hright] at hEqCast
    have h01 : (0 : ZMod 8) ≠ 1 := by decide
    exact h01 hEqCast
  · exfalso
    have hm : m = 3 + 8 * (m / 8) := by
      simpa [hm8] using (Nat.mod_add_div m 8).symm
    have hoddm : Odd m := by
      refine ⟨1 + 4 * (m / 8), ?_⟩
      omega
    have hleft : (if Odd m then (m : ZMod 8) else 0) = 3 := by
      have h8cast : ((8 * (m / 8) : ℕ) : ZMod 8) = 0 :=
        (ZMod.natCast_eq_zero_iff (8 * (m / 8)) 8).2 (dvd_mul_right 8 _)
      rw [if_pos hoddm, hm]
      calc
        (((3 + 8 * (m / 8) : ℕ) : ZMod 8)) =
            (3 : ZMod 8) + ((8 * (m / 8) : ℕ) : ZMod 8) := by
          simp
        _ = 3 := by simp [h8cast]
    have hhalf : m / 2 = 1 + 4 * (m / 8) := by
      rw [hm]
      omega
    have hright : (((m / 2) ^ 2 : ℕ) : ZMod 8) = 1 := by
      rw [hhalf]
      exact zmod8_sq_one_add_four_mul (m / 8)
    rw [hleft, hright] at hEqCast
    have h31 : (3 : ZMod 8) ≠ 1 := by decide
    exact h31 hEqCast
  · exfalso
    have hm : m = 4 + 8 * (m / 8) := by
      simpa [hm8] using (Nat.mod_add_div m 8).symm
    have hevenm : Even m := by
      refine ⟨2 + 4 * (m / 8), ?_⟩
      omega
    have hoddm : ¬Odd m := Nat.not_odd_iff_even.mpr hevenm
    have hleft : (if Odd m then (m : ZMod 8) else 0) = 0 := by
      simp [hoddm]
    have hhalf : m / 2 = 2 + 4 * (m / 8) := by
      rw [hm]
      omega
    have hright : (((m / 2) ^ 2 : ℕ) : ZMod 8) = 4 := by
      rw [hhalf]
      exact zmod8_sq_two_add_four_mul (m / 8)
    rw [hleft, hright] at hEqCast
    have h04 : (0 : ZMod 8) ≠ 4 := by decide
    exact h04 hEqCast
  · exfalso
    have hm : m = 5 + 8 * (m / 8) := by
      simpa [hm8] using (Nat.mod_add_div m 8).symm
    have hoddm : Odd m := by
      refine ⟨2 + 4 * (m / 8), ?_⟩
      omega
    have hleft : (if Odd m then (m : ZMod 8) else 0) = 5 := by
      have h8cast : ((8 * (m / 8) : ℕ) : ZMod 8) = 0 :=
        (ZMod.natCast_eq_zero_iff (8 * (m / 8)) 8).2 (dvd_mul_right 8 _)
      rw [if_pos hoddm, hm]
      calc
        (((5 + 8 * (m / 8) : ℕ) : ZMod 8)) =
            (5 : ZMod 8) + ((8 * (m / 8) : ℕ) : ZMod 8) := by
          simp
        _ = 5 := by simp [h8cast]
    have hhalf : m / 2 = 2 + 4 * (m / 8) := by
      rw [hm]
      omega
    have hright : (((m / 2) ^ 2 : ℕ) : ZMod 8) = 4 := by
      rw [hhalf]
      exact zmod8_sq_two_add_four_mul (m / 8)
    rw [hleft, hright] at hEqCast
    have h54 : (5 : ZMod 8) ≠ 4 := by decide
    exact h54 hEqCast
  · exfalso
    have hm : m = 6 + 8 * (m / 8) := by
      simpa [hm8] using (Nat.mod_add_div m 8).symm
    have hevenm : Even m := by
      refine ⟨3 + 4 * (m / 8), ?_⟩
      omega
    have hoddm : ¬Odd m := Nat.not_odd_iff_even.mpr hevenm
    have hleft : (if Odd m then (m : ZMod 8) else 0) = 0 := by
      simp [hoddm]
    have hhalf : m / 2 = 3 + 4 * (m / 8) := by
      rw [hm]
      omega
    have hright : (((m / 2) ^ 2 : ℕ) : ZMod 8) = 1 := by
      rw [hhalf]
      exact zmod8_sq_three_add_four_mul (m / 8)
    rw [hleft, hright] at hEqCast
    have h01 : (0 : ZMod 8) ≠ 1 := by decide
    exact h01 hEqCast
  · exfalso
    have hm : m = 7 + 8 * (m / 8) := by
      simpa [hm8] using (Nat.mod_add_div m 8).symm
    have hoddm : Odd m := by
      refine ⟨3 + 4 * (m / 8), ?_⟩
      omega
    have hleft : (if Odd m then (m : ZMod 8) else 0) = 7 := by
      have h8cast : ((8 * (m / 8) : ℕ) : ZMod 8) = 0 :=
        (ZMod.natCast_eq_zero_iff (8 * (m / 8)) 8).2 (dvd_mul_right 8 _)
      rw [if_pos hoddm, hm]
      calc
        (((7 + 8 * (m / 8) : ℕ) : ZMod 8)) =
            (7 : ZMod 8) + ((8 * (m / 8) : ℕ) : ZMod 8) := by
          simp
        _ = 7 := by simp [h8cast]
    have hhalf : m / 2 = 3 + 4 * (m / 8) := by
      rw [hm]
      omega
    have hright : (((m / 2) ^ 2 : ℕ) : ZMod 8) = 1 := by
      rw [hhalf]
      exact zmod8_sq_three_add_four_mul (m / 8)
    rw [hleft, hright] at hEqCast
    have h71 : (7 : ZMod 8) ≠ 1 := by decide
    exact h71 hEqCast

/-- Combining odd-mod-3 and odd-`k≥3` mod-8 obstructions:
such solutions must satisfy `m ≡ 0 (mod 24)`. -/
theorem mod_twentyfour_obstruction_of_odd_ge_three {m k : ℕ}
    (hsol : IsSolution m k) (hkodd : Odd k) (hk3 : 3 ≤ k) :
    m % 24 = 0 := by
  have h8 : m % 8 = 0 := mod_eight_obstruction_of_odd_ge_three hsol hkodd hk3
  have h3 : m % 3 = 0 := mod_three_obstruction_of_odd hsol hkodd
  have h8dvd : 8 ∣ m := Nat.dvd_of_mod_eq_zero h8
  have h3dvd : 3 ∣ m := Nat.dvd_of_mod_eq_zero h3
  have h24dvd : 24 ∣ m := by
    have hcop : Nat.Coprime 8 3 := by decide
    have hmul : 8 * 3 ∣ m := hcop.mul_dvd_of_dvd_of_dvd h8dvd h3dvd
    simpa [Nat.mul_comm] using hmul
  exact Nat.mod_eq_zero_of_dvd h24dvd

private lemma mod5_of_four_mul_mod5_zero (a : ℕ) (h : (4 * a) % 5 = 0) :
    a % 5 = 0 := by
  have ha5lt : a % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases ha : a % 5
  · rfl
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega

private lemma mod5_of_four_mul_mod5_three (a : ℕ) (h : (4 * a) % 5 = 3) :
    a % 5 = 2 := by
  have ha5lt : a % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases ha : a % 5
  · exfalso
    omega
  · exfalso
    omega
  · rfl
  · exfalso
    omega
  · exfalso
    omega

/-- Combining the odd-`k≥3` mod-24 obstruction with the `k ≡ 1 (mod 4)` mod-5 obstruction.

In this regime, `m` lies in residue class `0` or `48` modulo `120`. -/
theorem mod_one_twenty_obstruction_of_odd_ge_three_mod_four_eq_one {m k : ℕ}
    (hsol : IsSolution m k) (hkodd : Odd k) (hk3 : 3 ≤ k) (hk4 : k % 4 = 1) :
    m % 120 = 0 ∨ m % 120 = 48 := by
  have h24 : m % 24 = 0 := mod_twentyfour_obstruction_of_odd_ge_three hsol hkodd hk3
  have h5 : m % 5 = 0 ∨ m % 5 = 3 := mod_five_obstruction_of_mod_four_eq_one hsol hk4
  let a : ℕ := m / 24
  have hm : m = 24 * a := by
    simp [a]
    simpa [h24] using (Nat.mod_add_div m 24).symm
  have hm5eq : m % 5 = (4 * a) % 5 := by
    rw [hm]
    rw [Nat.mul_mod]
    norm_num
  rcases h5 with h50 | h53
  · left
    have h4a0 : (4 * a) % 5 = 0 := by simpa [hm5eq] using h50
    have ha0 : a % 5 = 0 := mod5_of_four_mul_mod5_zero a h4a0
    have ha : a = 5 * (a / 5) := by
      simpa [ha0] using (Nat.mod_add_div a 5).symm
    rw [hm, ha]
    have h120dvd : 120 ∣ 24 * (5 * (a / 5)) := by
      refine ⟨a / 5, ?_⟩
      ring
    exact Nat.mod_eq_zero_of_dvd h120dvd
  · right
    have h4a3 : (4 * a) % 5 = 3 := by simpa [hm5eq] using h53
    have ha2 : a % 5 = 2 := mod5_of_four_mul_mod5_three a h4a3
    have ha : a = 2 + 5 * (a / 5) := by
      simpa [ha2] using (Nat.mod_add_div a 5).symm
    rw [hm, ha]
    have hm120 : (24 * (2 + 5 * (a / 5))) % 120 = 48 := by
      have hdecomp : 24 * (2 + 5 * (a / 5)) = 48 + 120 * (a / 5) := by ring
      rw [hdecomp]
      omega
    exact hm120

/-- In the complementary odd branch `k ≡ 3 (mod 4)`, the mod-120 obstruction collapses
to a single residue class. -/
theorem mod_one_twenty_obstruction_of_odd_ge_three_mod_four_eq_three {m k : ℕ}
    (hsol : IsSolution m k) (hkodd : Odd k) (hk3 : 3 ≤ k) (hk4 : k % 4 = 3) :
    m % 120 = 0 := by
  have h24 : m % 24 = 0 := mod_twentyfour_obstruction_of_odd_ge_three hsol hkodd hk3
  have h5 : m % 5 = 0 := mod_five_obstruction_of_mod_four_eq_three hsol hk4
  have h24dvd : 24 ∣ m := Nat.dvd_of_mod_eq_zero h24
  have h5dvd : 5 ∣ m := Nat.dvd_of_mod_eq_zero h5
  have h120dvd : 120 ∣ m := by
    have hcop : Nat.Coprime 24 5 := by decide
    have hmul : 24 * 5 ∣ m := hcop.mul_dvd_of_dvd_of_dvd h24dvd h5dvd
    simpa [Nat.mul_comm] using hmul
  exact Nat.mod_eq_zero_of_dvd h120dvd

/-- Consolidated mod-120 obstruction for odd exponents `k ≥ 3`.

All such solutions satisfy `m ≡ 0` or `48 (mod 120)`. -/
theorem mod_one_twenty_obstruction_of_odd_ge_three {m k : ℕ}
    (hsol : IsSolution m k) (hkodd : Odd k) (hk3 : 3 ≤ k) :
    m % 120 = 0 ∨ m % 120 = 48 := by
  have hkmod2 : k % 2 = 1 := Nat.odd_iff.mp hkodd
  have hkmod4 : k % 4 = 1 ∨ k % 4 = 3 := (Nat.odd_mod_four_iff).mp hkmod2
  rcases hkmod4 with hk4 | hk4
  · exact mod_one_twenty_obstruction_of_odd_ge_three_mod_four_eq_one hsol hkodd hk3 hk4
  · left
    exact mod_one_twenty_obstruction_of_odd_ge_three_mod_four_eq_three hsol hkodd hk3 hk4

/-- If an odd-`k≥3` solution sits in residue class `48 (mod 120)`,
then necessarily `k ≡ 1 (mod 4)`. -/
theorem mod_one_twenty_eq_forty_eight_forces_k_mod_four_eq_one {m k : ℕ}
    (hsol : IsSolution m k) (hkodd : Odd k) (hk3 : 3 ≤ k) (hm120 : m % 120 = 48) :
    k % 4 = 1 := by
  have hkmod2 : k % 2 = 1 := Nat.odd_iff.mp hkodd
  have hkmod4 : k % 4 = 1 ∨ k % 4 = 3 := (Nat.odd_mod_four_iff).mp hkmod2
  rcases hkmod4 with hk4 | hk4
  · exact hk4
  · have h0 : m % 120 = 0 :=
      mod_one_twenty_obstruction_of_odd_ge_three_mod_four_eq_three hsol hkodd hk3 hk4
    rw [h0] at hm120
    omega

private lemma zmod_sub_one_reflect_eq_neg {m i : ℕ} (hi : i < m) :
    ((m - 1 - i : ℕ) : ZMod (m - 1)) = - (i : ZMod (m - 1)) := by
  have hi' : i ≤ m - 1 := Nat.le_pred_of_lt hi
  calc
    ((m - 1 - i : ℕ) : ZMod (m - 1)) =
        ((m - 1 : ℕ) : ZMod (m - 1)) - (i : ZMod (m - 1)) := by
      simp [Nat.cast_sub hi']
    _ = - (i : ZMod (m - 1)) := by
      simp

private lemma pred_dvd_two_powerSum_of_odd {m k : ℕ} (hkodd : Odd k) :
    (m - 1) ∣ 2 * powerSum m k := by
  have hcast :
      ((powerSum m k : ℕ) : ZMod (m - 1)) =
        ∑ i ∈ Finset.range m, (i : ZMod (m - 1)) ^ k := by
    unfold powerSum
    simp [Nat.cast_pow]
  have hreflect :
      (∑ i ∈ Finset.range m, (((m - 1 - i : ℕ) : ZMod (m - 1)) ^ k)) =
        ∑ i ∈ Finset.range m, (i : ZMod (m - 1)) ^ k := by
    simpa using (Finset.sum_range_reflect (fun i => (i : ZMod (m - 1)) ^ k) m)
  have hdouble :
      ((2 * powerSum m k : ℕ) : ZMod (m - 1)) =
        ∑ i ∈ Finset.range m,
          ((i : ZMod (m - 1)) ^ k + (((m - 1 - i : ℕ) : ZMod (m - 1)) ^ k)) := by
    calc
      ((2 * powerSum m k : ℕ) : ZMod (m - 1)) =
          ((powerSum m k : ℕ) : ZMod (m - 1)) + ((powerSum m k : ℕ) : ZMod (m - 1)) := by
        simp [two_mul]
      _ = (∑ i ∈ Finset.range m, (i : ZMod (m - 1)) ^ k) +
          (∑ i ∈ Finset.range m, (((m - 1 - i : ℕ) : ZMod (m - 1)) ^ k)) := by
        rw [hcast, ← hreflect]
      _ = ∑ i ∈ Finset.range m,
          ((i : ZMod (m - 1)) ^ k + (((m - 1 - i : ℕ) : ZMod (m - 1)) ^ k)) := by
        rw [Finset.sum_add_distrib]
  have hsummand :
      ∀ i ∈ Finset.range m,
        ((i : ZMod (m - 1)) ^ k + (((m - 1 - i : ℕ) : ZMod (m - 1)) ^ k)) = 0 := by
    intro i hi
    have hsub :
        (((m - 1 - i : ℕ) : ZMod (m - 1))) = - (i : ZMod (m - 1)) :=
      zmod_sub_one_reflect_eq_neg (Finset.mem_range.mp hi)
    rcases hkodd with ⟨t, rfl⟩
    rw [hsub]
    simp [pow_add, pow_mul]
  have hzero : ((2 * powerSum m k : ℕ) : ZMod (m - 1)) = 0 := by
    rw [hdouble]
    exact Finset.sum_eq_zero hsummand
  exact (ZMod.natCast_eq_zero_iff (2 * powerSum m k) (m - 1)).1 hzero

private lemma zmod4_pow_two_eq_zero_of_two_le {k : ℕ} (hk2 : 2 ≤ k) :
    ((2 : ZMod 4) ^ k) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk2
  have h20 : ((2 : ZMod 4) ^ 2) = 0 := by decide
  calc
    (2 : ZMod 4) ^ (2 + t) = ((2 : ZMod 4) ^ 2) * ((2 : ZMod 4) ^ t) := by
      rw [pow_add]
    _ = 0 := by simp [h20]

private lemma zmod4_pow_three_eq_three_of_odd {k : ℕ} (hkodd : Odd k) :
    ((3 : ZMod 4) ^ k) = 3 := by
  rcases hkodd with ⟨t, rfl⟩
  have h32 : ((3 : ZMod 4) ^ 2) = 1 := by decide
  calc
    (3 : ZMod 4) ^ (2 * t + 1) = ((3 : ZMod 4) ^ (2 * t)) * (3 : ZMod 4) := by
      rw [pow_add, pow_one]
    _ = (((3 : ZMod 4) ^ 2) ^ t) * (3 : ZMod 4) := by
      rw [pow_mul]
    _ = 3 := by simp [h32]

private lemma no_solution_m_three_of_odd_gt_one {k : ℕ}
    (hkodd : Odd k) (hk1 : 1 < k) :
    ¬ IsSolution 3 k := by
  intro hsol
  rcases hsol with ⟨_hmpos, hkpos, hEq⟩
  have hk2 : 2 ≤ k := by omega
  have hcast : ((powerSum 3 k : ℕ) : ZMod 4) = ((3 ^ k : ℕ) : ZMod 4) :=
    congrArg (fun t : ℕ => (t : ZMod 4)) hEq
  have hleft : ((powerSum 3 k : ℕ) : ZMod 4) = 1 := by
    unfold powerSum
    calc
      ((∑ i ∈ Finset.range 3, i ^ k : ℕ) : ZMod 4) =
          ∑ i ∈ Finset.range 3, (i : ZMod 4) ^ k := by
        simp [Nat.cast_pow]
      _ = (0 : ZMod 4) ^ k + 1 + (2 : ZMod 4) ^ k := by
        norm_num [Finset.sum_range_succ]
      _ = 1 := by
        have h2k : ((2 : ZMod 4) ^ k) = 0 := zmod4_pow_two_eq_zero_of_two_le hk2
        simp [h2k, hkpos.ne']
  have hright : ((3 ^ k : ℕ) : ZMod 4) = 3 := by
    simpa [Nat.cast_pow] using zmod4_pow_three_eq_three_of_odd hkodd
  rw [hleft, hright] at hcast
  have h13 : (1 : ZMod 4) ≠ 3 := by decide
  exact h13 hcast

/-- **Odd-exponent impossibility (except `k = 1`).**

If `k` is odd and `k > 1`, then there is no positive `m` with
`1^k + 2^k + ... + (m - 1)^k = m^k`. -/
theorem no_solution_of_odd_gt_one {m k : ℕ} (hkodd : Odd k) (hk1 : 1 < k) :
    ¬ IsSolution m k := by
  intro hsol
  have hsol0 : IsSolution m k := hsol
  rcases hsol with ⟨hmpos, hkpos, hEq⟩
  by_cases hm1 : m = 1
  · exact no_solution_one k (by simpa [hm1] using hsol0)
  have hmgt1 : 1 < m := lt_of_le_of_ne (Nat.succ_le_of_lt hmpos) (Ne.symm hm1)
  have hdiv : (m - 1) ∣ 2 * powerSum m k := pred_dvd_two_powerSum_of_odd hkodd
  have hdiv' : (m - 1) ∣ 2 * m ^ k := by simpa [hEq] using hdiv
  have hcop : Nat.Coprime (m - 1) m := by
    have hm_decomp : m = (m - 1) + 1 := by omega
    rw [hm_decomp]
    exact (Nat.coprime_self_add_right).2 (Nat.coprime_one_right (m - 1))
  have hcopPow : Nat.Coprime (m - 1) (m ^ k) := by
    exact (Nat.coprime_pow_right_iff hkpos (m - 1) m).2 hcop
  have hsmall : (m - 1) ∣ 2 := hcopPow.dvd_of_dvd_mul_right hdiv'
  have hm1le2 : m - 1 ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hsmall
  have hm2or3 : m = 2 ∨ m = 3 := by omega
  rcases hm2or3 with rfl | rfl
  · have hpowne : (2 ^ k : ℕ) ≠ 1 := by
      intro hpow
      have h21 : (2 : ℕ) = 1 := (pow_eq_one_iff_left hkpos.ne').1 hpow
      omega
    have hsum : powerSum 2 k = 1 := by
      unfold powerSum
      norm_num [Finset.sum_range_succ, hkpos.ne']
    have hpoweq : (2 ^ k : ℕ) = 1 := by
      rw [← hsum]
      exact hEq.symm
    exact hpowne hpoweq
  · exact no_solution_m_three_of_odd_gt_one hkodd hk1 (by simpa using hsol0)

/-- Any odd-exponent solution must satisfy `k = 1`. -/
theorem odd_solution_forces_k_eq_one {m k : ℕ}
    (hsol : IsSolution m k) (hkodd : Odd k) :
    k = 1 := by
  by_contra hkne1
  have hkpos : 0 < k := hsol.2.1
  have hk1 : 1 < k := by omega
  exact (no_solution_of_odd_gt_one hkodd hk1) hsol

/-- Odd-exponent solutions are exactly the classical one. -/
theorem odd_solution_unique {m k : ℕ}
    (hsol : IsSolution m k) (hkodd : Odd k) :
    m = 3 ∧ k = 1 := by
  have hk1 : k = 1 := odd_solution_forces_k_eq_one hsol hkodd
  refine ⟨?_, hk1⟩
  exact (solution_k_one_iff m).mp (by simpa [hk1] using hsol)

/-- Any non-classical solution must lie in the even, large-exponent branch. -/
theorem nontrivial_solution_even_ge_eight {m k : ℕ}
    (hsol : IsSolution m k) (hnon : ¬ (m = 3 ∧ k = 1)) :
    Even k ∧ 8 ≤ k := by
  have hkpos : 0 < k := hsol.2.1
  have hknotodd : ¬Odd k := by
    intro hkodd
    exact hnon (odd_solution_unique hsol hkodd)
  have hkeven : Even k := Nat.not_odd_iff_even.mp hknotodd
  have hkge8 : 8 ≤ k := by
    by_cases hk7 : k ≤ 7
    · exact (hnon (no_solution_k_le_seven hkpos hk7 hsol)).elim
    · omega
  exact ⟨hkeven, hkge8⟩

/-- Reduction theorem: every solution is either the classical one or in the even `k ≥ 8` branch. -/
theorem solution_split_classical_or_even_ge_eight {m k : ℕ}
    (hsol : IsSolution m k) :
    (m = 3 ∧ k = 1) ∨ (Even k ∧ 8 ≤ k) := by
  by_cases hclass : m = 3 ∧ k = 1
  · exact Or.inl hclass
  · exact Or.inr (nontrivial_solution_even_ge_eight hsol hclass)

/-- Stronger reduction: every non-classical solution lies in the even `k ≥ 10` branch. -/
theorem nontrivial_solution_even_ge_ten {m k : ℕ}
    (hsol : IsSolution m k) (hnon : ¬ (m = 3 ∧ k = 1)) :
    Even k ∧ 10 ≤ k := by
  have hkpos : 0 < k := hsol.2.1
  have hknotodd : ¬Odd k := by
    intro hkodd
    exact hnon (odd_solution_unique hsol hkodd)
  have hkeven : Even k := Nat.not_odd_iff_even.mp hknotodd
  have hkge10 : 10 ≤ k := by
    by_cases hk8 : k ≤ 8
    · exact (hnon (no_solution_k_le_eight hkpos hk8 hsol)).elim
    · rcases hkeven with ⟨t, rfl⟩
      have hgt8 : 8 < 2 * t := by
        omega
      omega
  exact ⟨hkeven, hkge10⟩

/-- Stronger split: every solution is either classical or in the even `k ≥ 10` branch. -/
theorem solution_split_classical_or_even_ge_ten {m k : ℕ}
    (hsol : IsSolution m k) :
    (m = 3 ∧ k = 1) ∨ (Even k ∧ 10 ≤ k) := by
  by_cases hclass : m = 3 ∧ k = 1
  · exact Or.inl hclass
  · exact Or.inr (nontrivial_solution_even_ge_ten hsol hclass)

/-- Combining the mod-4 and odd-mod-3 obstructions:
for odd exponents, `m` can only be `0` or `3` modulo `12`. -/
theorem mod_twelve_obstruction_of_odd {m k : ℕ} (hsol : IsSolution m k) (hkodd : Odd k) :
    m % 12 = 0 ∨ m % 12 = 3 := by
  have h4 : m % 4 = 0 ∨ m % 4 = 3 := mod_four_obstruction hsol
  have h3 : m % 3 = 0 := mod_three_obstruction_of_odd hsol hkodd
  have hm12lt : m % 12 < 12 := Nat.mod_lt _ (by decide)
  interval_cases hm12 : m % 12
  · left
    rfl
  · exfalso
    omega
  · exfalso
    omega
  · right
    rfl
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega
  · exfalso
    omega

end ErdosMoser
