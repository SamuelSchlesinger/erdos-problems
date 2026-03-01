/-
# Erdős-Straus: The Factorization Approach

## Key Algebraic Identity

For positive naturals n, x, y, z, c, d satisfying:
  (1) 4x = n + c       (choice of first denominator)
  (2) cy = d + nx       (second denominator from factorization)
  (3) dz = nxy          (third denominator from factorization)

We have: 1/x + 1/y + 1/z = 4/n.

Proof sketch: 1/x + 1/y + d/(nxy) = 1/x + (nx + d)/(nxy) = 1/x + cy/(nxy)
            = (ny + cy)/(nxy) = (n+c)y/(nxy) = (n+c)/(nx) = 4x/(nx) = 4/n.

The number-theoretic problem is: given n, find c, d such that x = (n+c)/4 is
a positive integer, y = (d + nx)/c is a positive integer, z = nxy/d is a
positive integer, and 1 ≤ x < y < z.
-/
import Erdos.ErdosStraus.Statement

namespace ErdosStraus

/-! ## The Core Identity -/

/-- The fundamental equation: under the three relations 4x = n+c, cy = d+nx,
    dz = nxy, we have 1/x + 1/y + 1/z = 4/n. -/
theorem core_identity (n x y z c d : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hd : 0 < d)
    (h1 : 4 * x = n + c)
    (h2 : c * y = d + n * x)
    (h3 : d * z = n * x * y) :
    (1 / (x : ℚ) + 1 / y + 1 / z : ℚ) = 4 / n := by
  have hxq : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hzq : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Cast the ℕ relations to ℚ
  have h1q : 4 * (x : ℚ) = n + c := by exact_mod_cast h1
  have h2q : (c : ℚ) * y = d + n * x := by exact_mod_cast h2
  have h3q : (d : ℚ) * z = n * x * y := by exact_mod_cast h3
  -- We prove the identity directly using field_simp then linear_combination
  -- with the three hypotheses h1q, h2q, h3q.
  field_simp
  -- After field_simp, the goal is a polynomial identity over ℚ that follows
  -- from h1q (4x = n+c), h2q (cy = d+nx), h3q (dz = nxy).
  linear_combination (-(↑y : ℚ) * ↑z) * h1q + (-(↑z : ℚ)) * h2q + (-1 : ℚ) * h3q

/-! ## Sufficient Condition Theorem -/

/-- The main reduction: if we find c, d giving valid x, y, z, the conjecture holds. -/
theorem of_factorization_witnesses
    (n c d : ℕ) (hn : 2 < n) (_hc : 0 < c) (hd : 0 < d)
    -- x = (n+c)/4 is a positive integer
    (hx_div : 4 ∣ n + c)
    (hx_pos : 0 < (n + c) / 4)
    -- y = (d + n*x)/c is a positive integer
    (hy_div : c ∣ d + n * ((n + c) / 4))
    -- z = n*x*y/d is a positive integer
    (hz_div : d ∣ n * ((n + c) / 4) * ((d + n * ((n + c) / 4)) / c))
    -- Ordering
    (h_ord1 : (n + c) / 4 < (d + n * ((n + c) / 4)) / c)
    (h_ord2 : (d + n * ((n + c) / 4)) / c <
              n * ((n + c) / 4) * ((d + n * ((n + c) / 4)) / c) / d) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  set x := (n + c) / 4
  set y := (d + n * x) / c
  set z := n * x * y / d
  have h1 : 4 * x = n + c := by omega
  have h2 : c * y = d + n * x := by
    change c * ((d + n * x) / c) = d + n * x
    exact Nat.mul_div_cancel' hy_div
  have h3 : d * z = n * x * y := by
    change d * (n * x * y / d) = n * x * y
    exact Nat.mul_div_cancel' hz_div
  refine ⟨x, y, z, by omega, h_ord1, h_ord2, ?_⟩
  have hy_pos : 0 < y := by omega
  have hz_pos : 0 < z := by omega
  exact (core_identity n x y z c d (by omega) hx_pos hy_pos hz_pos hd h1 h2 h3).symm

/-! ## Application: n = 13 as a test case

4/13 = 1/4 + 1/18 + 1/468.
Here c = 3, x = 4, m = 52, d = 2, y = 18, z = 468. -/

/-- The Erdős-Straus conjecture holds for n = 13. -/
theorem erdos_straus_13 :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / (13 : ℕ) : ℚ) = 1 / x + 1 / y + 1 / z := by
  exact ⟨4, 18, 468, by omega, by omega, by omega, by norm_num⟩

/-! ## Application: n ≡ 13 (mod 24) via the c=3 factorization

For n ≡ 13 mod 24: x = (n+3)/4, m = n(n+3)/4. Since n ≡ 5 mod 8,
(n+3)/4 is even, so m is even, and d = 2 satisfies d ≡ 2 ≡ -m mod 3. -/

/-- For n ≡ 13 mod 24 with n > 2, the Erdős-Straus conjecture holds.

    Proof: Use c = 3, d = 2. Then x = (n+3)/4, y = (2 + n(n+3)/4)/3,
    z = n(n+3)/4 · y / 2. The key is that m = n(n+3)/4 is even (since
    n ≡ 5 mod 8 makes (n+3)/4 even), so d = 2 | m² and 3 | (2 + m)
    since m ≡ 1 mod 3. -/
theorem mod24_eq13_case (n : ℕ) (hn : 2 < n) (hmod : n % 24 = 13) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  -- Use c = 3, d = 2
  set x := (n + 3) / 4
  set m := n * x
  have hx_val : 4 * x = n + 3 := by omega
  -- m = n * (n+3)/4. For n ≡ 13 mod 24, m is even and m ≡ 1 mod 3
  have hm_even : 2 ∣ m := by
    -- n ≡ 5 mod 8, so n+3 ≡ 0 mod 8, so x = (n+3)/4 is even
    have : 2 ∣ x := by omega
    exact dvd_mul_of_dvd_right this n
  -- 3 | (2 + m): m ≡ 1 mod 3, so 2 + m ≡ 0 mod 3
  have hm_mod3 : m % 3 = 1 := by
    -- m = n * x, and n ≡ 1 mod 3, x ≡ 1 mod 3
    have hn3 : n % 3 = 1 := by omega
    have hx3 : x % 3 = 1 := by omega
    change (n * x) % 3 = 1
    rw [Nat.mul_mod, hn3, hx3]
  have hy_div : 3 ∣ (2 + m) := by omega
  set y := (2 + m) / 3
  have h2 : 3 * y = 2 + n * x := by omega
  -- z = n*x*y/2
  have hz_div : 2 ∣ (n * x * y) := by
    exact dvd_mul_of_dvd_left hm_even y
  set z := n * x * y / 2
  have h3 : 2 * z = n * x * y := by omega
  -- Ordering: x < y < z
  have hx_pos : 0 < x := by omega
  have hy_pos : 0 < y := by omega
  have hz_pos : 0 < z := by
    -- z = n*x*y/2, and 2 | n*x*y, and n*x*y > 0
    have : 0 < n * x * y := Nat.mul_pos (Nat.mul_pos (by omega) hx_pos) hy_pos
    omega
  have h_ord1 : x < y := by
    -- 3*y = 2 + n*x (from h2). Need x < y.
    -- Since n ≥ 4 and x ≥ 1: n*x ≥ 4*x > 3*x, so 3*y = 2+n*x > 3*x.
    have hx_ge : 4 ≤ x := by omega
    have hn_ge : 13 ≤ n := by omega
    have h_nx_bound : 13 * x ≤ n * x := Nat.mul_le_mul_right x hn_ge
    omega
  have h_ord2 : y < z := by
    -- 2*z = n*x*y. Need y < z, i.e. 2*y < 2*z = n*x*y, i.e. 2 < n*x.
    -- n*x ≥ 13*4 = 52 > 2
    have hx_ge : 4 ≤ x := by omega
    have hn_ge : 13 ≤ n := by omega
    have h_nx_ge : 3 ≤ n * x := by
      calc n * x ≥ 13 * 4 := Nat.mul_le_mul hn_ge hx_ge
        _ = 52 := by norm_num
        _ ≥ 3 := by norm_num
    -- 2*y < n*x*y since 2 < n*x and y > 0
    -- Equivalently: (n*x - 2) * y > 0, but in ℕ: n*x*y = (n*x) * y ≥ 3 * y > 2 * y
    have h3y : 3 * y ≤ n * x * y := Nat.mul_le_mul_right y h_nx_ge
    omega
  exact ⟨x, y, z, by omega, h_ord1, h_ord2,
    (core_identity n x y z 3 2 (by omega) hx_pos hy_pos hz_pos (by omega)
      hx_val h2 h3).symm⟩

end ErdosStraus
