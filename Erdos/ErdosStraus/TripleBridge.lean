/-
# Erdős-Straus → Unit Fraction Triples Bridge

This file establishes formal connections between Problem #242 (Erdős-Straus
conjecture) and Problem #302 (unit fraction triples).

The key algebraic link: any Erdős-Straus solution 4/n = 1/x + 1/y + 1/z
rearranges to 1/y + 1/z = (4x − n)/(nx). When (4x − n) divides nx, this
residual is the unit fraction 1/a where a = nx/(4x − n), giving the unit
fraction triple (a, y, z).

The even-case identity 4/(2m) = 1/m + 1/(m+1) + 1/(m(m+1)) specializes to
the consecutive triple 1/m = 1/(m+1) + 1/(m(m+1)), providing a concrete
infinite family of triples.

Note: The general bridge is conditional on the divisibility (4x − n) | nx.
Not all Erdős-Straus solutions satisfy this (the Schinzel barrier
(Schinzel, 1956) for parametric families means many solutions have
(4x − n)/(nx) as a non-unit fraction), but when divisibility holds,
the algebraic connection is exact.

Reference: https://www.erdosproblems.com/242, https://www.erdosproblems.com/302
-/
import Erdos.ErdosStraus.Statement
import Erdos.UnitFractionTriples.Statement

namespace ErdosStraus

open UnitFractionTriples

/-- For every m ≥ 2, the consecutive integers m, m+1, m(m+1) form a unit
    fraction triple: 1/m = 1/(m+1) + 1/(m(m+1)).

    This infinite family shows every integer ≥ 2 participates in a unit
    fraction triple (Problem #302). The identity arises from partial
    fractions: 1/(m(m+1)) = 1/m − 1/(m+1). -/
theorem consecutive_triple (m : ℕ) (hm : 2 ≤ m) :
    IsUnitFractionTriple m (m + 1) (m * (m + 1)) := by
  refine ⟨by omega, by omega, by positivity, ?_⟩
  have : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (m : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- For any Erdős-Straus witness at n > 2, we have n < 4x. This is because
    1/y + 1/z > 0 (since y, z ≥ 2), so 4/n = 1/x + 1/y + 1/z > 1/x,
    giving 4x > n by cross-multiplication. -/
theorem witness_4x_gt_n {n : ℕ} (hn : 2 < n) (w : Witness n) : n < 4 * w.x := by
  by_contra h; push_neg at h
  have hx := w.hx; have hxy := w.hxy; have hyz := w.hyz
  have hy_pos : 0 < w.y := by omega
  have hz_pos : 0 < w.z := by omega
  -- 1/y + 1/z > 0
  have hsum_pos : (0 : ℚ) < 1 / ↑w.y + 1 / ↑w.z :=
    add_pos (div_pos one_pos (Nat.cast_pos.mpr hy_pos))
            (div_pos one_pos (Nat.cast_pos.mpr hz_pos))
  -- But 1/y + 1/z = 4/n - 1/x ≤ 0 when 4x ≤ n
  have hsub : (1 / ↑w.y + 1 / ↑w.z : ℚ) = 4 / ↑n - 1 / ↑w.x := by
    linarith [w.heq]
  -- Show 4/n - 1/x ≤ 0
  have h_nonpos : (4 / ↑n - 1 / ↑w.x : ℚ) ≤ 0 := by
    have h1 : (↑n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : (↑w.x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_sub_div _ _ h1 h2]
    apply div_nonpos_of_nonpos_of_nonneg
    · have : (4 * ↑w.x : ℚ) ≤ ↑n := by exact_mod_cast h
      linarith
    · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

/-- For any Erdős-Straus witness w at n > 2, the pair (y, z) satisfies
    1/y + 1/z = (4x − n)/(nx) in ℚ.

    This residual identity is the algebraic bridge between Erdős-Straus (#242)
    and unit fraction triples (#302): rearranging 4/n = 1/x + 1/y + 1/z
    gives 1/y + 1/z = 4/n − 1/x = (4x − n)/(nx). When the numerator
    divides the denominator, this becomes a unit fraction 1/a, making
    (a, y, z) a unit fraction triple. -/
theorem erdos_straus_residual {n : ℕ} (hn : 2 < n) (w : Witness n) :
    (1 / ↑w.y + 1 / ↑w.z : ℚ) = (4 * ↑w.x - ↑n) / (↑n * ↑w.x) := by
  have : (↑n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (↑w.x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [w.hx])
  have : (↑w.y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [w.hx, w.hxy])
  have : (↑w.z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [w.hx, w.hxy, w.hyz])
  have heq := w.heq
  field_simp at heq ⊢
  linarith

/-- Given an Erdős-Straus witness w for n > 2 satisfying the divisibility
    condition (4x − n) ∣ nx, the quotient a = nx/(4x − n) yields a unit
    fraction triple: 1/a = 1/y + 1/z.

    This is a conditional bridge between #242 and #302: not every
    Erdős-Straus solution satisfies the divisibility condition (the general
    residual (4x − n)/(nx) need not be a unit fraction), but when it does,
    the connection is exact. The Schinzel barrier (Schinzel, 1956) means
    that parametric families cannot produce divisibility for all primes
    p ≡ 1 (mod 24). -/
theorem erdos_straus_generates_triple {n : ℕ} (hn : 2 < n) (w : Witness n)
    (hdvd : (4 * w.x - n) ∣ (n * w.x)) :
    IsUnitFractionTriple (n * w.x / (4 * w.x - n)) w.y w.z := by
  set d := 4 * w.x - n with hd_def
  set a := n * w.x / d with ha_def
  have h4x : n < 4 * w.x := witness_4x_gt_n hn w
  have hd_pos : 0 < d := by omega
  have hx_pos : 0 < w.x := by linarith [w.hx]
  have hy_pos : 0 < w.y := by linarith [w.hx, w.hxy]
  have hz_pos : 0 < w.z := by linarith [w.hx, w.hxy, w.hyz]
  have hnx_pos : 0 < n * w.x := Nat.mul_pos (by omega) hx_pos
  have ha_pos : 0 < a := Nat.div_pos (Nat.le_of_dvd hnx_pos hdvd) hd_pos
  have hda : a * d = n * w.x := Nat.div_mul_cancel hdvd
  refine ⟨ha_pos, hy_pos, hz_pos, ?_⟩
  -- Need: 1/a = 1/y + 1/z
  -- From erdos_straus_residual: 1/y + 1/z = (4x - n)/(nx)
  -- Since a * d = nx, we have (4x - n)/(nx) = d/(a*d) = 1/a
  have hresidual := erdos_straus_residual hn w
  have ha_ne : (↑a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_ne : (↑n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hx_ne : (↑w.x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd_cast : (↑d : ℚ) = 4 * ↑w.x - ↑n := by
    have : d + n = 4 * w.x := by omega
    have : (↑d : ℚ) + ↑n = 4 * ↑w.x := by exact_mod_cast this
    linarith
  have hda_q : (↑a : ℚ) * ↑d = ↑n * ↑w.x := by exact_mod_cast hda
  rw [hresidual, ← hd_cast]
  -- Goal: 1/a = d/(n*x), which follows from a*d = n*x
  field_simp
  linarith [hda_q]

/-- The even-case Erdős-Straus solution generates the consecutive triple
    via the general bridge.

    For n = 2m with m ≥ 2, the witness (x, y, z) = (m, m+1, m(m+1))
    satisfies 4x − n = 4m − 2m = 2m and nx = 2m², so the bridge quotient
    is a = 2m²/(2m) = m, recovering the consecutive triple
    1/m = 1/(m+1) + 1/(m(m+1)).

    This demonstrates that `erdos_straus_generates_triple` and
    `consecutive_triple` are connected: the simplest Erdős-Straus solutions
    (even case) produce the simplest unit fraction triples (consecutive). -/
theorem even_erdos_straus_bridge (m : ℕ) (hm : 2 ≤ m) :
    IsUnitFractionTriple (2 * m * m / (4 * m - 2 * m)) (m + 1) (m * (m + 1)) := by
  -- The bridge quotient simplifies: 2m² / (4m - 2m) = 2m²/2m = m
  have hsimp : 2 * m * m / (4 * m - 2 * m) = m := by
    have : 4 * m - 2 * m = 2 * m := by omega
    rw [this]
    exact Nat.mul_div_cancel_left m (by omega)
  rw [hsimp]
  exact consecutive_triple m hm

end ErdosStraus
