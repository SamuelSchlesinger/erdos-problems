/-
# Classification of Unit Fraction Triples

The factor identity (b-a)*(c-a) = a² from UpperHalf.lean reveals that
unit fraction triples 1/a = 1/b + 1/c with a < b ≤ c are in bijection
with factorizations a² = d₁ · d₂ with 1 ≤ d₁ ≤ d₂.

Given such a factorization, b = a + d₁ and c = a + d₂.
Conversely, given a triple, d₁ = b - a and d₂ = c - a.

This fully classifies all triples containing a given a:
the number of triples is τ(a²), the number of divisors of a².
-/
import Erdos.UnitFractionTriples.UpperHalf

namespace UnitFractionTriples

/-- **Construction of triples from factorizations of a².**

    If a² = d₁ * d₂ with d₁, d₂ ≥ 1, then setting b = a + d₁ and
    c = a + d₂ gives a * (b + c) = b * c. -/
theorem triple_of_sq_factorization {a d₁ d₂ : ℕ}
    (_ha : 0 < a) (_hd₁ : 0 < d₁) (_hd₂ : 0 < d₂)
    (hfact : d₁ * d₂ = a ^ 2) :
    a * ((a + d₁) + (a + d₂)) = (a + d₁) * (a + d₂) := by
  -- Expand: LHS = a * (2a + d₁ + d₂) = 2a² + a*d₁ + a*d₂
  -- RHS = a² + a*d₂ + a*d₁ + d₁*d₂ = a² + a*d₁ + a*d₂ + a²
  -- So RHS = 2a² + a*d₁ + a*d₂ = LHS
  nlinarith

/-- **Extraction of factorization from a triple.**

    If 1/a = 1/b + 1/c with a < b and a < c (positive naturals),
    then b - a and c - a are positive, and
    (b - a) * (c - a) = a². -/
theorem sq_factorization_of_triple {a b c : ℕ}
    (ha : 0 < a) (hab : a < b) (hac : a < c)
    (htrip : a * (b + c) = b * c) :
    0 < b - a ∧ 0 < c - a ∧ (b - a) * (c - a) = a ^ 2 :=
  ⟨by omega, by omega, triple_factor_identity ha hab hac htrip⟩

/-- **The triple-divisor correspondence (forward direction).**

    Every divisor d of a² with 1 ≤ d ≤ a gives a triple:
    b = a + d, c = a + a²/d, and 1/a = 1/b + 1/c.

    The condition d ≤ a ensures b ≤ c (since a²/d ≥ a). -/
theorem triple_from_divisor {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hdvd : d ∣ a ^ 2) (hda : d ≤ a) :
    let b := a + d
    let c := a + a ^ 2 / d
    a * (b + c) = b * c ∧ a < b ∧ a < c ∧ b ≤ c := by
  set b := a + d
  set c := a + a ^ 2 / d
  have hd2 := Nat.div_pos (Nat.le_of_dvd (by positivity) hdvd) hd
  have hfact : d * (a ^ 2 / d) = a ^ 2 := Nat.mul_div_cancel' hdvd
  refine ⟨triple_of_sq_factorization ha hd hd2 hfact, by omega, by omega, ?_⟩
  -- b ≤ c iff d ≤ a²/d iff d² ≤ a²
  apply Nat.add_le_add_left
  -- Need: d ≤ a²/d. Since d² ≤ a² (from d ≤ a) and d | a²
  have hd_sq : d * d ≤ a ^ 2 := by nlinarith
  exact Nat.le_div_iff_mul_le hd |>.mpr hd_sq

/-- The number of triples 1/a = 1/b + 1/c with b ≤ c equals the
    number of divisors d of a² with d ≤ a. This counts them:
    each such d gives b = a + d, c = a + a²/d. -/
theorem triple_count_eq_divisor_count (a : ℕ) (ha : 0 < a) :
    (Finset.filter (fun d => d ≤ a) (Nat.divisors (a ^ 2))).card =
    (Finset.filter (fun bc : ℕ × ℕ =>
      a * (bc.1 + bc.2) = bc.1 * bc.2 ∧ a < bc.1 ∧ bc.1 ≤ bc.2)
      (Finset.Icc (a + 1) (a + a ^ 2) ×ˢ Finset.Icc (a + 1) (a + a ^ 2))).card := by
  -- Build the bijection d ↦ (a + d, a + a²/d)
  apply Finset.card_bij (fun d _ => (a + d, a + a ^ 2 / d))
  · -- Maps into the target
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hda⟩ := hd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by positivity)
    obtain ⟨htrip, hab, _, hbc⟩ := triple_from_divisor ha hd_pos hdvd hda
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, htrip, hab, hbc⟩
    · have : d ≤ a ^ 2 := by nlinarith
      omega
    · have := Nat.div_le_self (a ^ 2) d
      omega
  · -- Injective
    intro d₁ hd₁ d₂ hd₂ heq
    simp only [Prod.mk.injEq] at heq
    omega
  · -- Surjective
    intro ⟨b, c⟩ hbc
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hbc
    obtain ⟨⟨⟨hba_lb, _⟩, ⟨_, _⟩⟩, htrip, hab, hbc'⟩ := hbc
    use b - a
    have hac : a < c := by
      by_contra h
      push_neg at h
      -- If c ≤ a, then since b > a and c ≤ a ≤ b, but hbc' : b ≤ c gives b ≤ a, contradiction
      omega
    have hfact := triple_factor_identity ha hab hac htrip
    have hba_pos : 0 < b - a := by omega
    have hba_dvd : (b - a) ∣ a ^ 2 := ⟨c - a, by linarith⟩
    have hdiv_eq : a ^ 2 / (b - a) = c - a :=
      Nat.div_eq_of_eq_mul_left hba_pos (by linarith)
    -- b - a ≤ a: from (b-a)² ≤ (b-a)*(c-a) = a² (since b ≤ c)
    have hba_le : b - a ≤ a := by
      nlinarith [hfact, show b - a ≤ c - a by omega]
    refine ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hba_dvd, by positivity⟩, hba_le⟩, ?_⟩
    -- (a + (b-a), a + a²/(b-a)) = (b, c)
    rw [hdiv_eq]
    ext <;> simp <;> omega

/-- **Every unit fraction triple has an even element.**

    For any triple 1/a = 1/b + 1/c with a < b and a < c (positive naturals),
    at least one of a, b, c is even.

    *Proof*: If a and b are both odd, then b + c has the same parity as c.
    If c is odd: a*(b+c) = odd*even = even, but b*c = odd*odd = odd.
    If c is even: a*(b+c) = odd*odd = odd, but b*c = odd*even = even.
    Either way, a*(b+c) ≠ b*c, contradicting the triple equation.

    This explains why every triple family {c·k, d·k, e·k} must have at
    least one even multiplier — no family can be coprime to 6 in all
    components. This is a structural barrier to extending the S+T family
    approach for tightening the 9/10 upper bound. -/
theorem triple_has_even_element {a b c : ℕ} (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (_hab : a < b) (_hac : a < c)
    (htrip : a * (b + c) = b * c) :
    Even a ∨ Even b ∨ Even c := by
  by_contra h
  push_neg at h
  obtain ⟨ha_odd, hb_odd, hc_odd⟩ := h
  rw [Nat.not_even_iff_odd] at ha_odd hb_odd hc_odd
  -- b + c is even (odd + odd), so a*(b+c) is even.
  -- But b*c is odd (odd*odd). Since a*(b+c) = b*c, even = odd: contradiction.
  have hprod_even : Even (a * (b + c)) := (hb_odd.add_odd hc_odd).mul_left a
  have hprod_odd : Odd (b * c) := hb_odd.mul hc_odd
  rw [htrip] at hprod_even
  obtain ⟨p, hp⟩ := hprod_even
  obtain ⟨q, hq⟩ := hprod_odd
  omega

/-- **If the smallest element of a triple is odd, both larger elements are even.**

    For any triple 1/a = 1/b + 1/c with a < b and a < c, if a is odd then
    both b and c are even.

    *Proof*: From the factor identity (b-a)(c-a) = a², if a is odd then a²
    is odd, so both (b-a) and (c-a) must be odd (an even factor would make
    the product even). Then b = a + (b-a) = odd + odd = even, and similarly
    for c. -/
theorem triple_odd_smallest_forces_even {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hac : a < c)
    (htrip : a * (b + c) = b * c) (ha_odd : ¬Even a) :
    Even b ∧ Even c := by
  rw [Nat.not_even_iff_odd] at ha_odd
  have hfact := triple_factor_identity ha hab hac htrip
  -- a² is odd
  have ha2_odd : Odd (a ^ 2) := by rw [sq]; exact ha_odd.mul ha_odd
  -- Helper: if one factor of (b-a)*(c-a) is even, the product is even,
  -- contradicting a² being odd.
  have no_even_ba : ¬Even (b - a) := by
    intro ⟨m, hm⟩
    obtain ⟨q, hq⟩ := ha2_odd
    have h1 := hfact; rw [hm, hq] at h1
    -- h1 : (m + m) * (c - a) = 2 * q + 1
    rw [add_mul] at h1
    -- h1 : m * (c-a) + m * (c-a) = 2 * q + 1, i.e., 2t = 2q+1
    omega
  have no_even_ca : ¬Even (c - a) := by
    intro ⟨m, hm⟩
    obtain ⟨q, hq⟩ := ha2_odd
    have h1 := hfact; rw [hm, hq] at h1
    -- h1 : (b - a) * (m + m) = 2 * q + 1
    rw [mul_add] at h1
    -- h1 : (b-a)*m + (b-a)*m = 2 * q + 1, i.e., 2t = 2q+1
    omega
  -- Both b-a and c-a are odd, so b and c are even (odd + odd = even).
  rw [Nat.not_even_iff_odd] at no_even_ba no_even_ca
  exact ⟨by rw [show b = a + (b - a) from by omega]; exact ha_odd.add_odd no_even_ba,
         by rw [show c = a + (c - a) from by omega]; exact ha_odd.add_odd no_even_ca⟩

end UnitFractionTriples
