import Erdos.ErdosMoser.Statement

/-!
# Erdos-Moser Equation: Modular Obstructions

This file starts the modular-arithmetic phase for the Erdos-Moser equation.

Main result in this pass:
- Any positive-exponent solution satisfies `m % 4 = 0 ∨ m % 4 = 3`.
- Any odd-exponent solution satisfies `m % 3 = 0`.
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
