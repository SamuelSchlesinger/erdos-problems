/-
# Erdős-Straus: The Divisor Factorization Method

## Key Equation

For 4/n = 1/x + 1/y + 1/z with x = (n+c)/4 and m = nx, the equation
  1/y + 1/z = c/m
rearranges to:
  (cy - m)(cz - m) = m²

So solutions correspond to factorizations m² = u·v where:
  - u ≡ v ≡ -m (mod c)
  - 0 < u < m < v  (for the ordering y < z)
  - y = (m + u)/c, z = (m + v)/c

This reduces the Erdős-Straus conjecture to a question about
divisors of perfect squares in specific residue classes.

## References

- Mordell, L. J. (1967). "Diophantine Equations." Academic Press.
- Elsholtz, C. and Tao, T. (2013). "Counting the number of solutions to the
  Erdős-Straus equation on unit fractions." J. Aust. Math. Soc., 94(1), 50–105.
-/
import Erdos.ErdosStraus.Factorization

namespace ErdosStraus

/-! ## Helper: deriving v ≡ -m (mod c) from u ≡ -m (mod c) -/

/-- If u·v = m² and c | (u + m) and gcd(c, u) = 1, then c | (v + m).

    This is the key auxiliary: we only need to find ONE factor u with
    the right congruence; the complementary factor v automatically
    has the same congruence.

    Proof: u(v + m) = uv + um = m² + um = m(m + u). Since c | (m + u),
    we get c | u(v + m). Since gcd(c, u) = 1, we conclude c | (v + m). -/
lemma dvd_v_add_m (c m u v : ℕ)
    (huv : u * v = m * m) (hu_mod : c ∣ u + m) (hcu : Nat.Coprime c u) :
    c ∣ v + m := by
  -- The identity u(v + m) = m(u + m) follows from uv = m²
  have key : u * (v + m) = m * (u + m) := by nlinarith
  -- c | m(u + m) since c | (u + m)
  have h : c ∣ u * (v + m) := by rw [key]; exact dvd_mul_of_dvd_right hu_mod m
  -- gcd(c, u) = 1 lets us cancel u
  rw [mul_comm] at h
  exact hcu.dvd_of_dvd_mul_right h

/-! ## The m² = uv factorization theorem -/

/-- The m² factorization method: if m = n(n+c)/4 and m² = uv with
    u ≡ -m (mod c), gcd(c, u) = 1, and 0 < u < m, then the
    Erdős-Straus conjecture holds for n.

    This captures the key algebraic insight that decompositions
    4/n = 1/x + 1/y + 1/z (with x = (n+c)/4) correspond to
    factorizations of m² with congruence constraints. -/
theorem of_m_sq_factorization (n c m u v : ℕ) (hn : 2 < n) (hc : 0 < c)
    (hcn : c ≤ n)
    (h4 : 4 ∣ n + c)
    (hm : m = n * ((n + c) / 4))
    (huv : u * v = m * m)
    (hu_pos : 0 < u) (hu_lt : u < m)
    (hu_mod : c ∣ u + m)
    (hcu : Nat.Coprime c u) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  -- Derive v ≡ -m mod c from the helper lemma
  have hv_mod : c ∣ v + m := dvd_v_add_m c m u v huv hu_mod hcu
  -- Eliminate m in favor of n * x where x = (n + c) / 4
  set x := (n + c) / 4
  -- After `set`, hm : m = n * x. Now substitute to eliminate m entirely.
  subst hm
  -- Set up remaining witnesses (all hypotheses now use `n * x` instead of `m`)
  set y := (u + n * x) / c
  set z := (v + n * x) / c
  -- Basic facts
  have hx_eq : 4 * x = n + c := by omega
  have hx_pos : 0 < x := by omega
  have hnx_pos : 0 < n * x := Nat.mul_pos (by omega) hx_pos
  -- Positivity of v
  have hv_pos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · rw [h, Nat.mul_zero] at huv
      linarith [Nat.mul_pos hnx_pos hnx_pos]
    · exact h
  -- Exact division equalities
  have hy_eq : c * y = u + n * x := Nat.mul_div_cancel' hu_mod
  have hz_eq : c * z = v + n * x := Nat.mul_div_cancel' hv_mod
  -- Positivity of y, z
  have hy_pos : 0 < y := by
    have : 0 < u + n * x := by omega
    exact Nat.div_pos (Nat.le_of_dvd this hu_mod) hc
  have hz_pos : 0 < z := by
    have : 0 < v + n * x := by omega
    exact Nat.div_pos (Nat.le_of_dvd this hv_mod) hc
  -- Key algebraic identity: u * z = n * x * y
  -- Proof: c·(u·z) = u·(c·z) = u·(v+nx) = nx·(u+nx) = nx·(c·y) = c·(nx·y)
  have huz : u * z = n * x * y := by
    suffices c * (u * z) = c * (n * x * y) from Nat.mul_left_cancel hc this
    calc c * (u * z) = u * (c * z) := by ring
      _ = u * (v + n * x) := by rw [hz_eq]
      _ = n * x * (u + n * x) := by nlinarith [huv]
      _ = n * x * (c * y) := by rw [← hy_eq]
      _ = c * (n * x * y) := by ring
  -- Ordering: x < y
  have hx_lt_y : x < y := by
    -- c·y = u + nx ≥ 1 + nx > nx ≥ cx (since n ≥ c)
    have : c * x ≤ n * x := Nat.mul_le_mul_right x hcn
    have : c * x < c * y := by nlinarith [hu_pos]
    exact (Nat.mul_lt_mul_left hc).mp this
  -- Ordering: y < z
  have hy_lt_z : y < z := by
    -- u < nx implies v > nx (since uv = (nx)²), so u + nx < v + nx, so y < z
    have hv_gt : n * x < v := by
      by_contra h
      push_neg at h
      have h1 : u * v ≤ u * (n * x) := Nat.mul_le_mul_left u h
      have h2 : u * (n * x) < n * x * (n * x) := by nlinarith [hu_lt]
      nlinarith
    have : c * y < c * z := by omega
    exact (Nat.mul_lt_mul_left hc).mp this
  -- Apply core_identity with d = u
  exact ⟨x, y, z, by omega, hx_lt_y, hy_lt_z,
    (core_identity n x y z c u (by omega) hx_pos hy_pos hz_pos hu_pos hx_eq hy_eq huz).symm⟩

/-! ## Test case: n = 73 via c = 7

4/73: With c = 7, x = (73+7)/4 = 20, m = 73·20 = 1460.
m² = 2131600 = 10 · 213160. u = 10 ≡ 3 ≡ -1460 (mod 7).
y = (10 + 1460)/7 = 210. z = (213160 + 1460)/7 = 30660.
Check: 1/20 + 1/210 + 1/30660 = 4/73. -/

/-- The Erdős-Straus conjecture holds for n = 73. -/
theorem erdos_straus_73 :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / (73 : ℕ) : ℚ) = 1 / x + 1 / y + 1 / z := by
  exact of_m_sq_factorization 73 7 1460 10 213160
    (by omega) (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by decide)

end ErdosStraus
