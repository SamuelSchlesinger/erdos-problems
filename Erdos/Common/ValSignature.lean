/-
# P-adic Valuation Signature Infrastructure

Generic tools for p-adic valuation arguments in packing bound proofs.

The core pattern: multipliers c₁, c₂, … map parameter a to elements c_i·a.
The valuation v_p(c_i·a) = v_p(c_i) + v_p(a) shifts by a known constant.
Signature functions (v_p mod k) that are injective on {c₁,…,cₙ} prove
the gadgets are pairwise disjoint.

This library provides:
1. **Shift lemma**: v_p(c·a) = v_p(c) + v_p(a) (convenient interface)
2. **Parity transfer**: Even/Odd propagation through multiplication
3. **Mod-k transfer**: v_p(c·a) mod k from v_p(c) mod k and v_p(a) mod k
4. **Concrete valuations**: simp lemmas for v_p(c) on small constants
-/
import Mathlib

namespace ValSignature

/-! ### Section 1: Shift lemma -/

/-- v_p(c·a) = v_p(c) + v_p(a) for c ≠ 0, a ≠ 0. Convenient wrapper. -/
theorem padicVal_mul_shift (p : ℕ) [hp : Fact (Nat.Prime p)]
    {c a : ℕ} (hc : c ≠ 0) (ha : a ≠ 0) :
    padicValNat p (c * a) = padicValNat p c + padicValNat p a :=
  padicValNat.mul hc ha

/-! ### Section 2: Parity transfer -/

/-- If v_p(c) is odd and v_p(a) is even, then v_p(c·a) is odd. -/
theorem padicVal_mul_flip_even (p : ℕ) [hp : Fact (Nat.Prime p)]
    {c a : ℕ} (hc : c ≠ 0) (ha : a ≠ 0)
    (hodd_c : Odd (padicValNat p c))
    (heven_a : Even (padicValNat p a)) :
    ¬Even (padicValNat p (c * a)) := by
  rw [padicValNat.mul hc ha]
  obtain ⟨j, hj⟩ := hodd_c
  obtain ⟨k, hk⟩ := heven_a
  rw [hj, hk]; intro ⟨m, hm⟩; omega

/-- If v_p(c) is even and v_p(a) is even, then v_p(c·a) is even. -/
theorem padicVal_mul_preserve_even (p : ℕ) [hp : Fact (Nat.Prime p)]
    {c a : ℕ} (hc : c ≠ 0) (ha : a ≠ 0)
    (heven_c : Even (padicValNat p c))
    (heven_a : Even (padicValNat p a)) :
    Even (padicValNat p (c * a)) := by
  rw [padicValNat.mul hc ha]
  exact heven_c.add heven_a

/-- If v_p(c) = 0 and v_p(a) is even, then v_p(c·a) is even. -/
theorem padicVal_mul_zero_preserve_even (p : ℕ) [hp : Fact (Nat.Prime p)]
    {c a : ℕ} (hc : c ≠ 0) (ha : a ≠ 0)
    (hzero_c : padicValNat p c = 0)
    (heven_a : Even (padicValNat p a)) :
    Even (padicValNat p (c * a)) := by
  rw [padicValNat.mul hc ha, hzero_c, zero_add]; exact heven_a

/-- If v_p(c) = 0 and v_p(a) is odd, then v_p(c·a) is odd. -/
theorem padicVal_mul_zero_preserve_odd (p : ℕ) [hp : Fact (Nat.Prime p)]
    {c a : ℕ} (hc : c ≠ 0) (ha : a ≠ 0)
    (hzero_c : padicValNat p c = 0)
    (hodd_a : ¬Even (padicValNat p a)) :
    ¬Even (padicValNat p (c * a)) := by
  rw [padicValNat.mul hc ha, hzero_c, zero_add]; exact hodd_a

/-! ### Section 3: Mod-k transfer -/

/-- v_p(c·a) mod k = (v_p(c) + v_p(a)) mod k. -/
theorem padicVal_mul_mod (p : ℕ) [hp : Fact (Nat.Prime p)]
    {c a : ℕ} (hc : c ≠ 0) (ha : a ≠ 0) (k : ℕ) :
    padicValNat p (c * a) % k = (padicValNat p c + padicValNat p a) % k := by
  rw [padicValNat.mul hc ha]

/-- If k ∣ v_p(c) and k ∣ v_p(a), then k ∣ v_p(c·a). -/
theorem padicVal_mul_dvd (p : ℕ) [hp : Fact (Nat.Prime p)]
    {c a : ℕ} (hc : c ≠ 0) (ha : a ≠ 0) (k : ℕ)
    (hdvd_c : k ∣ padicValNat p c)
    (hdvd_a : k ∣ padicValNat p a) :
    k ∣ padicValNat p (c * a) := by
  rw [padicValNat.mul hc ha]; exact Dvd.dvd.add hdvd_c hdvd_a

/-- If v_p(c) = 0 and k ∣ v_p(a), then k ∣ v_p(c·a). -/
theorem padicVal_mul_zero_dvd (p : ℕ) [hp : Fact (Nat.Prime p)]
    {c a : ℕ} (hc : c ≠ 0) (ha : a ≠ 0) (k : ℕ)
    (hzero_c : padicValNat p c = 0)
    (hdvd_a : k ∣ padicValNat p a) :
    k ∣ padicValNat p (c * a) := by
  rw [padicValNat.mul hc ha, hzero_c, zero_add]; exact hdvd_a

/-! ### Section 4: Concrete valuation facts

Simp lemmas for v_p(c) where c is a small constant. -/

-- v₂ valuations
@[simp] theorem v2_1 : padicValNat 2 1 = 0 := by simp
@[simp] theorem v2_2 : padicValNat 2 2 = 1 := by simp
@[simp] theorem v2_3 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v2_4 : padicValNat 2 4 = 2 := by
  have : padicValNat 2 (2 * 2) = padicValNat 2 2 + padicValNat 2 2 :=
    padicValNat.mul (by decide) (by decide)
  simp at this ⊢; linarith
@[simp] theorem v2_5 : padicValNat 2 5 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v2_6 : padicValNat 2 6 = 1 := by
  have : padicValNat 2 (2 * 3) = padicValNat 2 2 + padicValNat 2 3 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v2_2, v2_3, add_zero] at this; exact this
@[simp] theorem v2_12 : padicValNat 2 12 = 2 := by
  have : padicValNat 2 (4 * 3) = padicValNat 2 4 + padicValNat 2 3 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v2_4, v2_3, add_zero] at this; exact this
@[simp] theorem v2_20 : padicValNat 2 20 = 2 := by
  have : padicValNat 2 (4 * 5) = padicValNat 2 4 + padicValNat 2 5 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v2_4, v2_5, add_zero] at this; exact this

-- v₃ valuations
@[simp] theorem v3_2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v3_3 : padicValNat 3 3 = 1 := by simp
@[simp] theorem v3_4 : padicValNat 3 4 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v3_5 : padicValNat 3 5 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v3_6 : padicValNat 3 6 = 1 := by
  have : padicValNat 3 (2 * 3) = padicValNat 3 2 + padicValNat 3 3 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v3_2, v3_3, zero_add] at this; exact this
@[simp] theorem v3_12 : padicValNat 3 12 = 1 := by
  have : padicValNat 3 (4 * 3) = padicValNat 3 4 + padicValNat 3 3 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v3_4, v3_3, zero_add] at this; exact this
@[simp] theorem v3_20 : padicValNat 3 20 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)

-- v₅ valuations
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

@[simp] theorem v5_4 : padicValNat 5 4 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v5_5 : padicValNat 5 5 = 1 := by simp
@[simp] theorem v5_12 : padicValNat 5 12 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v5_15 : padicValNat 5 15 = 1 := by
  have : padicValNat 5 (3 * 5) = padicValNat 5 3 + padicValNat 5 5 :=
    padicValNat.mul (by decide) (by decide)
  simp only [show padicValNat 5 3 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    v5_5, zero_add] at this; exact this
@[simp] theorem v5_20 : padicValNat 5 20 = 1 := by
  have : padicValNat 5 (4 * 5) = padicValNat 5 4 + padicValNat 5 5 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v5_4, v5_5, zero_add] at this; exact this
@[simp] theorem v5_28 : padicValNat 5 28 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v5_36 : padicValNat 5 36 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v5_44 : padicValNat 5 44 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v5_45 : padicValNat 5 45 = 1 := by
  have : padicValNat 5 (9 * 5) = padicValNat 5 9 + padicValNat 5 5 :=
    padicValNat.mul (by decide) (by decide)
  simp only [show padicValNat 5 9 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    v5_5, zero_add] at this; exact this
@[simp] theorem v5_60 : padicValNat 5 60 = 1 := by
  have : padicValNat 5 (12 * 5) = padicValNat 5 12 + padicValNat 5 5 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v5_12, v5_5, zero_add] at this; exact this
@[simp] theorem v5_77 : padicValNat 5 77 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)

-- Additional v₂ valuations for barrier analysis multipliers
@[simp] theorem v2_15 : padicValNat 2 15 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v2_28 : padicValNat 2 28 = 2 := by
  have : padicValNat 2 (4 * 7) = padicValNat 2 4 + padicValNat 2 7 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v2_4, show padicValNat 2 7 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    add_zero] at this; exact this
@[simp] theorem v2_36 : padicValNat 2 36 = 2 := by
  have : padicValNat 2 (4 * 9) = padicValNat 2 4 + padicValNat 2 9 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v2_4, show padicValNat 2 9 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    add_zero] at this; exact this
@[simp] theorem v2_44 : padicValNat 2 44 = 2 := by
  have : padicValNat 2 (4 * 11) = padicValNat 2 4 + padicValNat 2 11 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v2_4, show padicValNat 2 11 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    add_zero] at this; exact this
@[simp] theorem v2_45 : padicValNat 2 45 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v2_60 : padicValNat 2 60 = 2 := by
  have : padicValNat 2 (4 * 15) = padicValNat 2 4 + padicValNat 2 15 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v2_4, v2_15, add_zero] at this; exact this
@[simp] theorem v2_77 : padicValNat 2 77 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)

-- Additional v₃ valuations for barrier analysis multipliers
@[simp] theorem v3_15 : padicValNat 3 15 = 1 := by
  have : padicValNat 3 (3 * 5) = padicValNat 3 3 + padicValNat 3 5 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v3_3, v3_5, add_zero] at this; exact this
@[simp] theorem v3_28 : padicValNat 3 28 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v3_9 : padicValNat 3 9 = 2 := by
  have h9 : padicValNat 3 (3 * 3) = padicValNat 3 3 + padicValNat 3 3 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v3_3] at h9; exact h9
@[simp] theorem v3_36 : padicValNat 3 36 = 2 := by
  have : padicValNat 3 (4 * 9) = padicValNat 3 4 + padicValNat 3 9 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v3_4, v3_9, zero_add] at this; exact this
@[simp] theorem v3_44 : padicValNat 3 44 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v3_45 : padicValNat 3 45 = 2 := by
  have : padicValNat 3 (9 * 5) = padicValNat 3 9 + padicValNat 3 5 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v3_9, v3_5, add_zero] at this; exact this
@[simp] theorem v3_60 : padicValNat 3 60 = 1 := by
  have : padicValNat 3 (12 * 5) = padicValNat 3 12 + padicValNat 3 5 :=
    padicValNat.mul (by decide) (by decide)
  simp only [v3_12, v3_5, add_zero] at this; exact this
@[simp] theorem v3_77 : padicValNat 3 77 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)

-- v₇ valuations
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

@[simp] theorem v7_28 : padicValNat 7 28 = 1 := by
  have : padicValNat 7 (4 * 7) = padicValNat 7 4 + padicValNat 7 7 :=
    padicValNat.mul (by decide) (by decide)
  simp only [show padicValNat 7 4 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    show padicValNat 7 7 = 1 from by simp, zero_add] at this; exact this
@[simp] theorem v7_44 : padicValNat 7 44 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
@[simp] theorem v7_77 : padicValNat 7 77 = 1 := by
  have : padicValNat 7 (7 * 11) = padicValNat 7 7 + padicValNat 7 11 :=
    padicValNat.mul (by decide) (by decide)
  simp only [show padicValNat 7 7 = 1 from by simp,
    show padicValNat 7 11 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    add_zero] at this; exact this

-- v₁₁ valuations
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

@[simp] theorem v11_44 : padicValNat 11 44 = 1 := by
  have : padicValNat 11 (4 * 11) = padicValNat 11 4 + padicValNat 11 11 :=
    padicValNat.mul (by decide) (by decide)
  simp only [show padicValNat 11 4 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    show padicValNat 11 11 = 1 from by simp, zero_add] at this; exact this
@[simp] theorem v11_77 : padicValNat 11 77 = 1 := by
  have : padicValNat 11 (7 * 11) = padicValNat 11 7 + padicValNat 11 11 :=
    padicValNat.mul (by decide) (by decide)
  simp only [show padicValNat 11 7 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    show padicValNat 11 11 = 1 from by simp, zero_add] at this; exact this

end ValSignature
