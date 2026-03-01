/-
# Erdős-Straus: The Prime Factor Method

## Key Result

If n > 2 and n has a prime factor p ≡ 3 (mod 4), then the Erdős-Straus
conjecture holds for n.

Proof: Set c = p, d = p, x = (n+p)/4. Since n ≡ 1 mod 4 (the only remaining
hard case) and p ≡ 3 mod 4, we have 4 | (n+p). Then:
- m = nx, and p | m since p | n
- y = (p + m)/p = 1 + m/p (integer since p | m)
- z = nxy/p = (n/p)xy (integer since p | n)
- x < y < z (from n ≥ p and standard bounds)

Combined with the even case and mod-4 ≡ 3 case, this covers all n > 2
that have ANY prime factor ≡ 3 mod 4.
-/
import Erdos.ErdosStraus.Factorization

namespace ErdosStraus

/-! ## Main theorem: prime factor p ≡ 3 mod 4 suffices

For n ≡ 1 mod 4 with n > 2 and p | n with p prime and p ≡ 3 mod 4:
set c = p, d = p, x = (n+p)/4, y = (p + nx)/p, z = nxy/p.
Then 4/n = 1/x + 1/y + 1/z with x < y < z. -/

/-- If n ≡ 1 mod 4, n > 2, and p is a prime ≡ 3 mod 4 with p | n, then
    the Erdős-Straus conjecture holds for n.

    This is a key structural result: it reduces the conjecture to n whose
    prime factorization consists entirely of primes ≡ 1 mod 4. -/
theorem prime_factor_3_mod_4 (n p : ℕ) (hn : 2 < n) (hmod4 : n % 4 = 1)
    (hp_prime : Nat.Prime p) (hp_mod : p % 4 = 3) (hp_dvd : p ∣ n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  -- Setup: c = p, d = p, x = (n+p)/4
  set x := (n + p) / 4
  have hp_pos : 0 < p := hp_prime.pos
  have hp_ge3 : 3 ≤ p := by omega
  -- 4 | (n+p) since n ≡ 1 mod 4 and p ≡ 3 mod 4
  have h_div4 : 4 ∣ n + p := by omega
  have hx_eq : 4 * x = n + p := by omega
  have hx_pos : 0 < x := by omega
  -- m = n * x, and p | m since p | n
  set m := n * x
  have hm_dvd_p : p ∣ m := dvd_mul_of_dvd_left hp_dvd x
  -- p | (p + m) since p | m
  have hy_div : p ∣ (p + m) := by
    exact dvd_add (dvd_refl p) hm_dvd_p
  -- y = (p + m) / p = 1 + m/p
  set y := (p + m) / p
  have h2 : p * y = p + n * x := by
    change p * ((p + m) / p) = p + n * x
    rw [Nat.mul_div_cancel' hy_div]
  -- p | nxy since p | n
  have hz_div : p ∣ (n * x * y) := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp_dvd x) y
  -- z = nxy / p
  set z := n * x * y / p
  have h3 : p * z = n * x * y := by
    change p * (n * x * y / p) = n * x * y
    exact Nat.mul_div_cancel' hz_div
  -- Positivity
  have hpm_pos : 0 < p + m := by omega
  have hy_pos : 0 < y := Nat.div_pos (Nat.le_of_dvd hpm_pos hy_div) hp_pos
  have hnxy_pos : 0 < n * x * y := Nat.mul_pos (Nat.mul_pos (by omega) hx_pos) hy_pos
  have hz_pos : 0 < z := Nat.div_pos (Nat.le_of_dvd hnxy_pos hz_div) hp_pos
  -- Ordering: x < y
  have h_ord1 : x < y := by
    -- From h2: p*y = p + n*x. So p*y - p = n*x, i.e., p*(y-1) = n*x.
    -- x < y iff p*x < p*y = p + n*x iff p*x - n*x < p iff x*(p-n) < p.
    -- Since p | n and n > 2, we have n ≥ p. If n = p: x = (p+p)/4 = p/2,
    -- and p*y = p + p*x = p(1+x), so y = 1 + x > x. ✓
    -- If n > p: p - n < 0, so x*(p-n) < 0 < p. ✓
    -- In Lean, we work with: p*y = p + n*x, so p*y > p*x iff n*x > p*x - p,
    -- i.e., p + n*x > p*x, i.e., p > (p-n)*x. Since n ≥ p, p - n ≤ 0 in ℤ.
    -- In ℕ, this is n*x + p > p*x, which we prove via n ≥ p.
    have hn_ge_p : p ≤ n := Nat.le_of_dvd (by omega) hp_dvd
    -- p * y = p + n * x ≥ p + p * x = p * (1 + x) > p * x
    -- So y ≥ 1 + x > x
    -- We show p * (x + 1) ≤ p * y, then cancel p
    -- p * x < p * y since p * y = p + n*x ≥ p + p*x > p*x (for x ≥ 1)
    -- Hence x < y by left-cancellation of p
    have hpx_le_nx : p * x ≤ n * x := Nat.mul_le_mul_right x hn_ge_p
    have hpx_lt_py : p * x < p * y := by nlinarith
    exact (Nat.mul_lt_mul_left hp_pos).mp hpx_lt_py
  -- Ordering: y < z
  have h_ord2 : y < z := by
    -- p*z = n*x*y. y < z iff p*y < p*z = n*x*y iff p < n*x.
    -- n*x = m. Since n ≥ p ≥ 3 and x ≥ 1: n*x ≥ 3.
    -- Actually n ≥ 3 and x ≥ (n+p)/4 ≥ (3+3)/4 ≥ 1, but we need n*x > p.
    -- n*x ≥ p*x (since n ≥ p) = p*(n+p)/4. For p ≥ 3: p*(p+p)/4 = p²/2 > p.
    -- More simply: n*x ≥ n ≥ p + 1... no, n could equal p.
    -- If n = p: x = 2p/4 = p/2. n*x = p²/2. p²/2 > p iff p > 2, which holds. ✓
    have hn_ge_p : p ≤ n := Nat.le_of_dvd (by omega) hp_dvd
    have hx_ge : (n + p) / 4 = x := rfl
    -- nx ≥ p * x = p * (n + p) / 4 ≥ p * (p + p) / 4 = p * p / 2
    -- For p ≥ 3: p²/2 ≥ 9/2 = 4 > ... well we just need nx > p.
    -- Simpler: p * y = p + nx, so nx = p*y - p = p*(y - 1).
    -- p * z = nx * y = p * (y - 1) * y.
    -- So z = (y - 1) * y = y² - y > y for y ≥ 3.
    -- y ≥ 3 since y > x ≥ (n+p)/4 ≥ (p+p)/4 = p/2 ≥ 3/2, so x ≥ 2, y ≥ 3.
    -- Actually, let's prove: z = (y-1)*y from h2, h3.
    have hpy : p * y = p + n * x := h2
    have hpz : p * z = n * x * y := h3
    -- From hpy: n * x = p * y - p = p * (y - 1)
    have hnx : n * x = p * (y - 1) := by
      -- We rewrite p*(y-1) + p = p*y to get p*(y-1) = p*y - p = n*x
      have : p * (y - 1) + p = p * y := by
        rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right p hy_pos)]
      omega
    -- From hpz: p * z = p * (y - 1) * y
    have : p * z = p * (y - 1) * y := by rw [← hnx]; exact h3
    -- So z = (y - 1) * y
    have hz_eq : z = (y - 1) * y := by
      have hpz_eq : p * z = p * ((y - 1) * y) := by
        rw [mul_assoc] at this
        exact this
      exact Nat.mul_left_cancel hp_pos hpz_eq
    -- y < (y-1)*y iff y < y² - y iff 0 < y² - 2y = y(y-2)
    -- This holds for y ≥ 3.
    have hy_ge3 : 3 ≤ y := by
      -- x ≥ 2 (since (n+p)/4 ≥ (3+3)/4 = 1, but actually n > 2 and p ≥ 3
      -- gives n + p ≥ 6, x ≥ 1. Need x ≥ 2.)
      -- n ≥ p ≥ 3 and n > 2, so n ≥ 3. n + p ≥ 6.
      -- But x = (n+p)/4 could be 1 if n+p < 8.
      -- n ≥ 3, p ≥ 3: n + p ≥ 6. x = (n+p)/4 ≥ 1. (6/4 = 1)
      -- For x = 1: y > 1, so y ≥ 2. But we need y ≥ 3.
      -- From hpy: p*y = p + nx. If x = 1: p*y = p + n, y = 1 + n/p ≥ 1 + 1 = 2.
      -- y ≥ 3 iff n/p ≥ 2 iff n ≥ 2p iff... n could be p, giving y = 2.
      -- If n = p = 3: 4/3. x = (3+3)/4 = 1. But n = 3 > 2 and n%4 = 3 ≠ 1.
      -- Contradiction with hmod4! So n ≥ 5 (since n ≡ 1 mod 4, n ≥ 5).
      -- p ≡ 3 mod 4 and p | n with n ≡ 1 mod 4. If p = n then n ≡ 3 mod 4,
      -- contradiction. So n > p, meaning n ≥ 2p (since p | n and n > p).
      -- n ≥ 2p ≥ 6. x = (n+p)/4 ≥ (2p+p)/4 = 3p/4 ≥ 9/4 ≥ 2 (for p ≥ 3).
      -- Then py = p + nx ≥ p + 2p·2 = 5p. y ≥ 5 ≥ 3. Actually that's overkill.
      have : n ≠ p := by
        intro heq; rw [heq] at hmod4; omega
      have hn_ge_2p : n ≥ 2 * p := by
        obtain ⟨k, hk⟩ := hp_dvd
        have hk_ne_1 : k ≠ 1 := by
          intro h; subst h; simp at hk; omega
        have hk_ne_0 : k ≠ 0 := by
          intro h; subst h; simp at hk; omega
        have hk_ge_2 : k ≥ 2 := by omega
        nlinarith
      -- x = (n+p)/4 ≥ (2p+p)/4 = 3p/4 ≥ 9/4 ≥ 2 (since p ≥ 3)
      have hx_ge_2 : x ≥ 2 := by
        have : n + p ≥ 3 * p := by omega
        have : 4 * x = n + p := hx_eq
        have : 3 * p ≥ 9 := by omega
        omega
      -- p*y = p + n*x ≥ p + 2p*2 = 5p, so y ≥ 5 ≥ 3
      -- More precisely: p*y = p + n*x, y = (p + n*x) / p
      -- n*x ≥ 2p*2 = 4p, so p*y ≥ p + 4p = 5p, so y ≥ 5
      have : n * x ≥ 2 * p * 2 := by nlinarith
      -- p * y = p + n * x ≥ p + 4p = 5p
      have : p * y ≥ 5 * p := by nlinarith
      -- therefore y ≥ 5 (since p > 0)
      have : y ≥ 5 := Nat.le_of_mul_le_mul_left (by nlinarith) hp_pos
      omega
    rw [hz_eq]
    -- y < (y - 1) * y for y ≥ 3
    -- (y - 1) * y ≥ 2 * y > y
    have hym1 : (y - 1) ≥ 2 := by omega
    have : 2 * y ≤ (y - 1) * y := Nat.mul_le_mul_right y hym1
    omega
  -- Apply the core identity
  exact ⟨x, y, z, by omega, h_ord1, h_ord2,
    (core_identity n x y z p p (by omega) hx_pos hy_pos hz_pos hp_pos hx_eq h2 h3).symm⟩

/-! ## Consequence: only primes ≡ 1 mod 4 are hard

The conjecture for general n reduces to n whose prime factors are all ≡ 1 mod 4.
For such n, n ≡ 1 mod 4 automatically (product of numbers ≡ 1 mod 4 is ≡ 1 mod 4).
-/

end ErdosStraus
