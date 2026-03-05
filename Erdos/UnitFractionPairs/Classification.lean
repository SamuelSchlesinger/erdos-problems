/-
# Classification of Unit Fraction Pairs

Every pair (a, b) with (a + b) ∣ ab can be parameterized as follows:
let d = gcd(a, b), a = d·s, b = d·t with gcd(s, t) = 1.
Then (s + t) ∣ d, and setting m = d / (s + t), we get
  1/a + 1/b = 1/(m·s·t).

Conversely, for any s, t, m ≥ 1 with gcd(s, t) = 1,
the pair a = m·s·(s+t), b = m·t·(s+t) satisfies (a+b) ∣ ab.
-/
import Erdos.UnitFractionPairs.Statement

namespace UnitFractionPairs

/-! ## Coprimality lemmas -/

/-- If gcd(s, t) = 1 then gcd(s, s + t) = 1. -/
theorem coprime_self_add {s t : ℕ} (h : Nat.Coprime s t) :
    Nat.Coprime s (s + t) := by
  rwa [Nat.Coprime, Nat.add_comm, Nat.gcd_add_self_right]

/-- If gcd(s, t) = 1 then gcd(t, s + t) = 1. -/
theorem coprime_self_add' {s t : ℕ} (h : Nat.Coprime s t) :
    Nat.Coprime t (s + t) := by
  rw [Nat.Coprime, Nat.gcd_add_self_right]
  exact h.symm

/-- If gcd(s, t) = 1 then gcd(s * t, s + t) = 1. -/
theorem coprime_mul_sum {s t : ℕ} (h : Nat.Coprime s t) :
    Nat.Coprime (s * t) (s + t) :=
  Nat.Coprime.mul_left (coprime_self_add h) (coprime_self_add' h)

/-! ## Forward direction: classification of unit fraction pairs -/

/-- If (a + b) ∣ ab with d = gcd(a,b), a = ds, b = dt, gcd(s,t) = 1,
    then (s + t) ∣ d.

    Proof: (a+b) ∣ ab means d(s+t) ∣ d²st, so (s+t) ∣ d·s·t.
    Since gcd(s·t, s+t) = 1, we get (s+t) ∣ d. -/
theorem sum_dvd_gcd_of_pair {a b : ℕ} (ha : 0 < a) (_hb : 0 < b)
    (hpair : IsUnitFractionPair a b) :
    (a / Nat.gcd a b + b / Nat.gcd a b) ∣ Nat.gcd a b := by
  set d := Nat.gcd a b with hd_def
  set s := a / d
  set t := b / d
  unfold IsUnitFractionPair at hpair
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (by
    intro h; rw [hd_def, Nat.gcd_eq_zero_iff] at h; omega)
  have hd_dvd_a : d ∣ a := Nat.gcd_dvd_left a b
  have hd_dvd_b : d ∣ b := Nat.gcd_dvd_right a b
  have hds : d * s = a := Nat.mul_div_cancel' hd_dvd_a
  have hdt : d * t = b := Nat.mul_div_cancel' hd_dvd_b
  have hcop : Nat.Coprime s t := Nat.coprime_div_gcd_div_gcd hd_pos
  -- a + b = d * (s + t)
  have hab_sum : a + b = d * (s + t) := by
    calc a + b = d * s + d * t := by rw [hds, hdt]
    _ = d * (s + t) := by ring
  -- a * b = d * (d * (s * t))
  have hab_prod : a * b = d * (d * (s * t)) := by
    calc a * b = (d * s) * (d * t) := by rw [hds, hdt]
    _ = d * (d * (s * t)) := by ring
  rw [hab_sum, hab_prod] at hpair
  have h1 : (s + t) ∣ d * (s * t) :=
    (mul_dvd_mul_iff_left (show d ≠ 0 by omega)).mp hpair
  have h2 : (s + t) ∣ s * t * d := by rwa [mul_comm] at h1
  exact (coprime_mul_sum hcop).symm.dvd_of_dvd_mul_left h2

/-! ## Converse: parametric construction -/

/-- The parametric construction always gives a unit fraction pair.
    For any m, s, t, setting a = m·s·(s+t), b = m·t·(s+t) gives
    (a+b) ∣ ab, with quotient m·s·t. -/
theorem pair_of_params (m s t : ℕ) :
    IsUnitFractionPair (m * s * (s + t)) (m * t * (s + t)) := by
  unfold IsUnitFractionPair
  exact ⟨m * s * t, by ring⟩

/-- The parametric construction gives the right reciprocal sum:
    1/(m·s·(s+t)) + 1/(m·t·(s+t)) = 1/(m·s·t). -/
theorem pair_reciprocal_sum {m s t : ℕ} (hm : 0 < m) (hs : 0 < s) (ht : 0 < t) :
    (1 / (m * s * (s + t)) + 1 / (m * t * (s + t)) : ℚ) =
    1 / (m * s * t) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs' : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ht' : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hst' : (s : ℚ) + t ≠ 0 := by positivity
  field_simp
  ring

/-! ## Concrete unit fraction pairs

The simplest infinite family: for every m ≥ 1, the pair (3m, 6m) satisfies
1/(3m) + 1/(6m) = 1/(2m). This is the (s=1, t=2) family. -/

/-- (3m, 6m) is a unit fraction pair for all m. This is the s=1, t=2 instance
    of the parametric construction: a = m·1·3 = 3m, b = m·2·3 = 6m. -/
theorem pair_3m_6m (m : ℕ) : IsUnitFractionPair (3 * m) (6 * m) := by
  unfold IsUnitFractionPair
  exact ⟨2 * m, by ring⟩

/-- (4m, 12m) is a unit fraction pair for all m (s=1, t=3 family). -/
theorem pair_4m_12m (m : ℕ) : IsUnitFractionPair (4 * m) (12 * m) := by
  unfold IsUnitFractionPair
  exact ⟨3 * m, by ring⟩

/-- (10m, 15m) is a unit fraction pair for all m (s=2, t=3 family). -/
theorem pair_10m_15m (m : ℕ) : IsUnitFractionPair (10 * m) (15 * m) := by
  unfold IsUnitFractionPair
  exact ⟨6 * m, by ring⟩

/-- A PairFree set cannot contain both 3k and 6k (for k ≥ 1). -/
theorem pair_free_not_3k_6k {A : Finset ℕ} (hA : PairFree A) {k : ℕ}
    (hk : 0 < k) (h3 : 3 * k ∈ A) (h6 : 6 * k ∈ A) : False :=
  hA (3 * k) h3 (6 * k) h6 (by omega) (pair_3m_6m k)

/-- A PairFree set cannot contain both 4k and 12k (for k ≥ 1). -/
theorem pair_free_not_4k_12k {A : Finset ℕ} (hA : PairFree A) {k : ℕ}
    (hk : 0 < k) (h4 : 4 * k ∈ A) (h12 : 12 * k ∈ A) : False :=
  hA (4 * k) h4 (12 * k) h12 (by omega) (pair_4m_12m k)

/-- A PairFree set cannot contain both 10k and 15k (for k ≥ 1). -/
theorem pair_free_not_10k_15k {A : Finset ℕ} (hA : PairFree A) {k : ℕ}
    (hk : 0 < k) (h10 : 10 * k ∈ A) (h15 : 15 * k ∈ A) : False :=
  hA (10 * k) h10 (15 * k) h15 (by omega) (pair_10m_15m k)

end UnitFractionPairs
