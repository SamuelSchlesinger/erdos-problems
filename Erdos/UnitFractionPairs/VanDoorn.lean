/-
# Van Doorn's 25/28 Upper Bound for Pair-Free Sets

Two independent families of unit fraction pairs:
- **S-family**: S_a = {3a, 6a} with 1/(3a) + 1/(6a) = 1/(2a)
- **T-family**: T_a = {4a, 12a} with 1/(4a) + 1/(12a) = 1/(3a)

Parameter predicate VDParam(a): 3 ∣ v₂(a) ∧ v₃(a) even.
Equivalently, a = 8^b · 9^c · d with gcd(d,6) = 1.

The (v₂ mod 3, v₃ mod 2) signature distinguishes all four multipliers:
  - 3:  (0, 1)
  - 6:  (1, 1)
  - 4:  (2, 0)
  - 12: (2, 1)

Disjointness:
- S-pairs pairwise disjoint (v₂ mod 3 injective: 0 ≠ 1)
- T-pairs pairwise disjoint (v₃ mod 2 injective: 0 ≠ 1)
- S and T cross-disjoint (v₂ mod 3: {0,1} ∩ {2} = ∅)

Combined: A.card + |D_S| + |D_T| ≤ N where D_S ⊆ [1,N/6], D_T ⊆ [1,N/12].
Density of VDParam ≈ 3/7, so |D_S| ≈ N/14 and |D_T| ≈ N/28.
Total: A.card ≤ N − N/14 − N/28 = 25N/28.

Reference: van Doorn, erdosproblems.com/327
-/
import Erdos.UnitFractionPairs.UpperBound
import Erdos.UnitFractionPairs.Density
import Erdos.Common.PackingBound
import Erdos.Common.ValSignature

namespace UnitFractionPairs

/-! ### Section 1: VDParam predicate -/

/-- VDParam(a) holds when 3 ∣ v₂(a) and v₃(a) is even.
    Equivalently, a = 8^b · 9^c · d where gcd(d,6) = 1. -/
def VDParam (a : ℕ) : Prop :=
  3 ∣ padicValNat 2 a ∧ Even (padicValNat 3 a)

instance : DecidablePred VDParam := fun a =>
  inferInstanceAs (Decidable (3 ∣ padicValNat 2 a ∧ Even (padicValNat 3 a)))

/-! ### Section 2: Valuation transfer lemmas

For each multiplier c ∈ {3, 4, 6, 12} and relevant prime p, we use
ValSignature simp lemmas for v_p(c) and `padicValNat.mul` for the shift. -/

/-! #### Mod-3 transfer for v₂ -/

/-- v₂(3·a) ≡ 0 (mod 3) when 3 ∣ v₂(a). -/
private lemma v2_three_mul_mod3 {a : ℕ} (ha : a ≠ 0) (h3 : 3 ∣ padicValNat 2 a) :
    3 ∣ padicValNat 2 (3 * a) := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_3, zero_add]; exact h3

/-- v₂(6·a) ≡ 1 (mod 3) when 3 ∣ v₂(a), so ¬(3 ∣ v₂(6a)). -/
private lemma v2_six_mul_not_mod3 {a : ℕ} (ha : a ≠ 0) (h3 : 3 ∣ padicValNat 2 a) :
    ¬(3 ∣ padicValNat 2 (6 * a)) := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_6]
  obtain ⟨k, hk⟩ := h3; rw [hk]; intro ⟨m, hm⟩; omega

/-- v₂(4·a) ≡ 2 (mod 3) when 3 ∣ v₂(a), so ¬(3 ∣ v₂(4a)). -/
private lemma v2_four_mul_not_mod3 {a : ℕ} (ha : a ≠ 0) (h3 : 3 ∣ padicValNat 2 a) :
    ¬(3 ∣ padicValNat 2 (4 * a)) := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_4]
  obtain ⟨k, hk⟩ := h3; rw [hk]; intro ⟨m, hm⟩; omega

/-- v₂(12·a) ≡ 2 (mod 3) when 3 ∣ v₂(a), so ¬(3 ∣ v₂(12a)). -/
private lemma v2_twelve_mul_not_mod3 {a : ℕ} (ha : a ≠ 0) (h3 : 3 ∣ padicValNat 2 a) :
    ¬(3 ∣ padicValNat 2 (12 * a)) := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_12]
  obtain ⟨k, hk⟩ := h3; rw [hk]; intro ⟨m, hm⟩; omega

/-! #### Mod-2 transfer for v₃ -/

/-- v₃(4·a) is even when v₃(a) is even. -/
private lemma v3_four_mul_even {a : ℕ} (ha : a ≠ 0) (hev : Even (padicValNat 3 a)) :
    Even (padicValNat 3 (4 * a)) :=
  ValSignature.padicVal_mul_zero_preserve_even 3 (by decide) ha ValSignature.v3_4 hev

/-- v₃(12·a) is odd when v₃(a) is even. -/
private lemma v3_twelve_mul_odd {a : ℕ} (ha : a ≠ 0) (hev : Even (padicValNat 3 a)) :
    ¬Even (padicValNat 3 (12 * a)) :=
  ValSignature.padicVal_mul_flip_even 3 (by decide) ha ⟨0, by simp [ValSignature.v3_12]⟩ hev

/-! ### Section 3: S-family intra-disjointness

The valuation signature (v₂ mod 3) distinguishes the S-multipliers:
  - 3a: v₂ ≡ 0 mod 3
  - 6a: v₂ ≡ 1 mod 3
So if c₁·a₁ = c₂·a₂ with VDParam, then c₁ = c₂, hence a₁ = a₂. -/

/-- For distinct a₁, a₂ with VDParam, the pairs {3a₁, 6a₁} and
    {3a₂, 6a₂} are disjoint. -/
theorem vd_s_pairs_disjoint {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hne : a₁ ≠ a₂) (hv₁ : VDParam a₁) (hv₂ : VDParam a₂) :
    Disjoint ({3*a₁, 6*a₁} : Finset ℕ) {3*a₂, 6*a₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  have ha₁' : a₁ ≠ 0 := by omega
  have ha₂' : a₂ ≠ 0 := by omega
  rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h
  · exact hne (by omega)
  · have h1 := v2_three_mul_mod3 ha₁' hv₁.1
    rw [h] at h1; exact v2_six_mul_not_mod3 ha₂' hv₂.1 h1
  · have h1 := v2_six_mul_not_mod3 ha₁' hv₁.1
    rw [h] at h1; exact h1 (v2_three_mul_mod3 ha₂' hv₂.1)
  · exact hne (by omega)

/-! ### Section 4: T-family intra-disjointness

The valuation signature (v₃ mod 2) distinguishes the T-multipliers:
  - 4a:  v₃ even
  - 12a: v₃ odd
So if c₁·a₁ = c₂·a₂ with VDParam, then c₁ = c₂, hence a₁ = a₂. -/

/-- For distinct a₁, a₂ with VDParam, the pairs {4a₁, 12a₁} and
    {4a₂, 12a₂} are disjoint. -/
theorem vd_t_pairs_disjoint {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hne : a₁ ≠ a₂) (hv₁ : VDParam a₁) (hv₂ : VDParam a₂) :
    Disjoint ({4*a₁, 12*a₁} : Finset ℕ) {4*a₂, 12*a₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  have ha₁' : a₁ ≠ 0 := by omega
  have ha₂' : a₂ ≠ 0 := by omega
  rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h
  · exact hne (by omega)
  · have h1 := v3_four_mul_even ha₁' hv₁.2
    rw [h] at h1; exact v3_twelve_mul_odd ha₂' hv₂.2 h1
  · have h1 := v3_twelve_mul_odd ha₁' hv₁.2
    rw [h] at h1; exact h1 (v3_four_mul_even ha₂' hv₂.2)
  · exact hne (by omega)

/-! ### Section 5: Cross-family disjointness

Every S-element has v₂ ≡ 0 or 1 (mod 3). Every T-element has v₂ ≡ 2 (mod 3).
For cases where both sides have v₂ ≢ 0 (mod 3), we use direct arithmetic
on the valuation equation to derive a contradiction via omega. -/

/-- S-pairs and T-pairs are cross-disjoint. -/
theorem vd_s_t_cross_disjoint {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hv₁ : VDParam a₁) (hv₂ : VDParam a₂) :
    Disjoint ({3*a₁, 6*a₁} : Finset ℕ) {4*a₂, 12*a₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  have ha₁' : a₁ ≠ 0 := by omega
  have ha₂' : a₂ ≠ 0 := by omega
  obtain ⟨j, hj⟩ := hv₁.1
  obtain ⟨k, hk⟩ := hv₂.1
  rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h
  · have := v2_three_mul_mod3 ha₁' hv₁.1
    rw [h] at this; exact v2_four_mul_not_mod3 ha₂' hv₂.1 this
  · have := v2_three_mul_mod3 ha₁' hv₁.1
    rw [h] at this; exact v2_twelve_mul_not_mod3 ha₂' hv₂.1 this
  · have hv2_eq : padicValNat 2 (6 * a₁) = padicValNat 2 (4 * a₂) := by rw [h]
    rw [padicValNat.mul (by decide) ha₁', ValSignature.v2_6,
        padicValNat.mul (by decide) ha₂', ValSignature.v2_4, hj, hk] at hv2_eq; omega
  · have hv2_eq : padicValNat 2 (6 * a₁) = padicValNat 2 (12 * a₂) := by rw [h]
    rw [padicValNat.mul (by decide) ha₁', ValSignature.v2_6,
        padicValNat.mul (by decide) ha₂', ValSignature.v2_12, hj, hk] at hv2_eq; omega

/-! ### Section 6: Triangle overlap barrier

The triangle family from gadget mining (`{60d,120d,180d}` with `gcd(d,6)=1`) is
not cross-disjoint from the full van Doorn S/T families:
- It always overlaps T at `60d = 12*(5d)` (for `N ≥ 180`, witness `d = 1`).
- It overlaps S at `120d = 3*(40d)` (for `N ≥ 240`, witness `d = 1`).

So any three-family improvement must either trim parameter sets or use
overlap-aware counting (not plain disjoint-family packing). -/

/-- `5` satisfies `VDParam` (`v₂(5)=0`, `v₃(5)=0`). -/
private theorem vdparam_five : VDParam 5 := by
  unfold VDParam
  simp [ValSignature.v2_5, ValSignature.v3_5]

/-- If `d` is coprime to `6`, then `5d` satisfies `VDParam`. -/
private theorem vdparam_five_mul_of_coprime6 {d : ℕ}
    (hcop : Nat.Coprime d 6) : VDParam (5 * d) := by
  unfold VDParam
  have hd2 : ¬(2 ∣ d) := by
    intro h2
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hcop
  have hd3 : ¬(3 ∣ d) := by
    intro h3
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) h3 (by decide : 3 ∣ 6)) hcop
  by_cases hd0 : d = 0
  · subst hd0
    simp
  · have hv2 : padicValNat 2 (5 * d) = 0 := by
      rw [padicValNat.mul (by decide) hd0, ValSignature.v2_5,
        padicValNat.eq_zero_of_not_dvd hd2, zero_add]
    have hv3 : padicValNat 3 (5 * d) = 0 := by
      rw [padicValNat.mul (by decide) hd0, ValSignature.v3_5,
        padicValNat.eq_zero_of_not_dvd hd3, zero_add]
    simp [hv2, hv3]

/-- `40` satisfies `VDParam` (`v₂(40)=3`, `v₃(40)=0`). -/
private theorem vdparam_forty : VDParam 40 := by
  unfold VDParam
  have hv2 : padicValNat 2 40 = 3 := by
    calc
      padicValNat 2 40 = padicValNat 2 (2 * 20) := by norm_num
      _ = padicValNat 2 2 + padicValNat 2 20 := by
        rw [padicValNat.mul (by decide) (by decide)]
      _ = 3 := by simp [ValSignature.v2_20]
  have hv3 : padicValNat 3 40 = 0 := by
    calc
      padicValNat 3 40 = padicValNat 3 (2 * 20) := by norm_num
      _ = padicValNat 3 2 + padicValNat 3 20 := by
        rw [padicValNat.mul (by decide) (by decide)]
      _ = 0 := by simp [ValSignature.v3_2, ValSignature.v3_20]
  rw [hv2, hv3]
  exact ⟨⟨1, rfl⟩, by simp⟩

/-- If `d` is coprime to `6`, then `40d` satisfies `VDParam`. -/
private theorem vdparam_forty_mul_of_coprime6 {d : ℕ}
    (hcop : Nat.Coprime d 6) : VDParam (40 * d) := by
  unfold VDParam
  have hd2 : ¬(2 ∣ d) := by
    intro h2
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hcop
  have hd3 : ¬(3 ∣ d) := by
    intro h3
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) h3 (by decide : 3 ∣ 6)) hcop
  by_cases hd0 : d = 0
  · subst hd0
    simp
  · have h20d0 : 20 * d ≠ 0 := by omega
    have hv2d : padicValNat 2 d = 0 := padicValNat.eq_zero_of_not_dvd hd2
    have hv3d : padicValNat 3 d = 0 := padicValNat.eq_zero_of_not_dvd hd3
    have hv2 : padicValNat 2 (40 * d) = 3 := by
      have h40 : 40 * d = 2 * (20 * d) := by omega
      rw [h40, padicValNat.mul (by decide) h20d0, padicValNat.mul (by decide) hd0]
      simp [ValSignature.v2_20, hv2d]
    have hv3 : padicValNat 3 (40 * d) = 0 := by
      have h40 : 40 * d = 2 * (20 * d) := by omega
      rw [h40, padicValNat.mul (by decide) h20d0, padicValNat.mul (by decide) hd0]
      simp [ValSignature.v3_2, ValSignature.v3_20, hv3d]
    rw [hv2, hv3]
    exact ⟨⟨1, rfl⟩, by simp⟩

/-- If `d` is coprime to `6`, then `45d` satisfies `VDParam`. -/
private theorem vdparam_fortyfive_mul_of_coprime6 {d : ℕ}
    (hcop : Nat.Coprime d 6) : VDParam (45 * d) := by
  unfold VDParam
  have hd2 : ¬(2 ∣ d) := by
    intro h2
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hcop
  have hd3 : ¬(3 ∣ d) := by
    intro h3
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) h3 (by decide : 3 ∣ 6)) hcop
  by_cases hd0 : d = 0
  · subst hd0
    simp
  · have hv2d : padicValNat 2 d = 0 := padicValNat.eq_zero_of_not_dvd hd2
    have hv3d : padicValNat 3 d = 0 := padicValNat.eq_zero_of_not_dvd hd3
    have hv2 : padicValNat 2 (45 * d) = 0 := by
      rw [padicValNat.mul (by decide) hd0, ValSignature.v2_45, hv2d, zero_add]
    have hv3 : padicValNat 3 (45 * d) = 2 := by
      rw [padicValNat.mul (by decide) hd0, ValSignature.v3_45, hv3d, add_zero]
    rw [hv2, hv3]
    exact ⟨⟨0, rfl⟩, by decide⟩

/-- If `d` is coprime to `6`, then `15d` is not a `VDParam` witness
    (its `v₃` parity is odd). -/
private theorem not_vdparam_fifteen_mul_of_coprime6 {d : ℕ}
    (hcop : Nat.Coprime d 6) : ¬VDParam (15 * d) := by
  intro hv
  have hd2 : ¬(2 ∣ d) := by
    intro h2
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hcop
  have hd3 : ¬(3 ∣ d) := by
    intro h3
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) h3 (by decide : 3 ∣ 6)) hcop
  have hd0 : d ≠ 0 := by
    intro hd0
    exact hd2 ⟨0, by simp [hd0]⟩
  have hv3 : padicValNat 3 (15 * d) = 1 := by
    rw [padicValNat.mul (by decide) hd0, ValSignature.v3_15,
      padicValNat.eq_zero_of_not_dvd hd3, add_zero]
  have hodd : ¬Even (padicValNat 3 (15 * d)) := by simp [hv3]
  exact hodd hv.2

/-- If `d` is coprime to `6`, then `10d` is not a `VDParam` witness
    (`v₂(10d)=1` is not divisible by `3`). -/
private theorem not_vdparam_ten_mul_of_coprime6 {d : ℕ}
    (hcop : Nat.Coprime d 6) : ¬VDParam (10 * d) := by
  intro hv
  have hd2 : ¬(2 ∣ d) := by
    intro h2
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hcop
  have hd0 : d ≠ 0 := by
    intro hd0
    exact hd2 ⟨0, by simp [hd0]⟩
  have h5d0 : 5 * d ≠ 0 := by omega
  have hv2d : padicValNat 2 d = 0 := padicValNat.eq_zero_of_not_dvd hd2
  have hv2 : padicValNat 2 (10 * d) = 1 := by
    have h10 : 10 * d = 2 * (5 * d) := by ring
    rw [h10, padicValNat.mul (by decide) h5d0,
      padicValNat.mul (by decide) hd0, ValSignature.v2_2, ValSignature.v2_5, hv2d, zero_add]
  have hndvd : ¬(3 ∣ padicValNat 2 (10 * d)) := by simp [hv2]
  exact hndvd hv.1

/-- If `d` is coprime to `6`, then `30d` is not a `VDParam` witness
    (`v₂(30d)=1` is not divisible by `3`). -/
private theorem not_vdparam_thirty_mul_of_coprime6 {d : ℕ}
    (hcop : Nat.Coprime d 6) : ¬VDParam (30 * d) := by
  intro hv
  have hd2 : ¬(2 ∣ d) := by
    intro h2
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hcop
  have hd0 : d ≠ 0 := by
    intro hd0
    exact hd2 ⟨0, by simp [hd0]⟩
  have h15d0 : 15 * d ≠ 0 := by omega
  have hv2d : padicValNat 2 d = 0 := padicValNat.eq_zero_of_not_dvd hd2
  have hv2 : padicValNat 2 (30 * d) = 1 := by
    have h30 : 30 * d = 2 * (15 * d) := by ring
    rw [h30, padicValNat.mul (by decide) h15d0,
      padicValNat.mul (by decide) hd0, ValSignature.v2_2, ValSignature.v2_15, hv2d, zero_add]
  have hndvd : ¬(3 ∣ padicValNat 2 (30 * d)) := by simp [hv2]
  exact hndvd hv.1

/-- If `d` is coprime to `6`, then `20d` is not a `VDParam` witness
    (`v₂(20d)=2` is not divisible by `3`). -/
private theorem not_vdparam_twenty_mul_of_coprime6 {d : ℕ}
    (hcop : Nat.Coprime d 6) : ¬VDParam (20 * d) := by
  intro hv
  have hd2 : ¬(2 ∣ d) := by
    intro h2
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hcop
  have hd0 : d ≠ 0 := by
    intro hd0
    exact hd2 ⟨0, by simp [hd0]⟩
  have hv2d : padicValNat 2 d = 0 := padicValNat.eq_zero_of_not_dvd hd2
  have hv2 : padicValNat 2 (20 * d) = 2 := by
    rw [padicValNat.mul (by decide) hd0, ValSignature.v2_20, hv2d, add_zero]
  have hndvd : ¬(3 ∣ padicValNat 2 (20 * d)) := by simp [hv2]
  exact hndvd hv.1

/-- If `d` is coprime to `6`, then `60d` is not a `VDParam` witness
    (`v₂(60d)=2` is not divisible by `3`). -/
private theorem not_vdparam_sixty_mul_of_coprime6 {d : ℕ}
    (hcop : Nat.Coprime d 6) : ¬VDParam (60 * d) := by
  intro hv
  have hd2 : ¬(2 ∣ d) := by
    intro h2
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) h2 (by decide : 2 ∣ 6)) hcop
  have hd0 : d ≠ 0 := by
    intro hd0
    exact hd2 ⟨0, by simp [hd0]⟩
  have hv2d : padicValNat 2 d = 0 := padicValNat.eq_zero_of_not_dvd hd2
  have hv2 : padicValNat 2 (60 * d) = 2 := by
    rw [padicValNat.mul (by decide) hd0, ValSignature.v2_60, hv2d, add_zero]
  have hndvd : ¬(3 ∣ padicValNat 2 (60 * d)) := by simp [hv2]
  exact hndvd hv.1

/-- Full triangle-union and full T-union are not disjoint once `N ≥ 180`
    (witness value `60`). -/
theorem vd_triangle_t_not_disjoint (N : ℕ) (hN : 180 ≤ N) :
    ¬ Disjoint
      (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ))) := by
  intro hdis
  have h1D : 1 ∈ (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6) := by
    have h1 : 1 ≤ N / 180 := by omega
    simp [h1]
  have h60_tri :
      60 ∈ (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨1, h1D, by simp⟩
  have h5D : 5 ∈ (Finset.Icc 1 (N / 12)).filter VDParam := by
    have h5 : 5 ≤ N / 12 := by omega
    simp [h5, vdparam_five]
  have h60_t :
      60 ∈ (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨5, h5D, by simp⟩
  exact (Finset.disjoint_left.mp hdis h60_tri h60_t).elim

/-- Full triangle-union and full S-union are not disjoint once `N ≥ 240`
    (witness value `120`). -/
theorem vd_triangle_s_not_disjoint (N : ℕ) (hN : 240 ≤ N) :
    ¬ Disjoint
      (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ))) := by
  intro hdis
  have h1D : 1 ∈ (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6) := by
    have h1 : 1 ≤ N / 180 := by omega
    simp [h1]
  have h120_tri :
      120 ∈ (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨1, h1D, by simp⟩
  have h40D : 40 ∈ (Finset.Icc 1 (N / 6)).filter VDParam := by
    have h40 : 40 ≤ N / 6 := by omega
    simp [h40, vdparam_forty]
  have h120_s :
      120 ∈ (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨40, h40D, by simp⟩
  exact (Finset.disjoint_left.mp hdis h120_tri h120_s).elim

/-- **Quantitative overlap with T-family.**

    Let
    `D△ = {d ∈ [1, N/180] : Nat.Coprime d 6}`,
    `U△ = ⋃_{d∈D△} {60d,120d,180d}`,
    `U_T = ⋃_{a∈[1,N/12], VDParam a} {4a,12a}`.

    Then `|U△ ∩ U_T| ≥ |D△|`.

    Proof: each `d ∈ D△` contributes the shared element `60d = 12*(5d)`,
    where `5d` is in the T-parameter set by coprime-to-6. -/
theorem vd_triangle_t_overlap_card_lb (N : ℕ) :
    ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card ≤
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card := by
  set Dtri := (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)
  set O := Dtri.image (fun d => 60 * d)
  have hcardO : O.card = Dtri.card :=
    Finset.card_image_of_injective Dtri (fun d1 d2 h =>
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 60) h)
  have hsub : O ⊆
      (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ))) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨d, hdD, rfl⟩
    have hd_mem : d ∈ Finset.Icc 1 (N / 180) ∧ Nat.Coprime d 6 := by
      simpa [Dtri] using (Finset.mem_filter.mp hdD)
    have hd_ge1 : 1 ≤ d := (Finset.mem_Icc.mp hd_mem.1).1
    have hd_le : d ≤ N / 180 := (Finset.mem_Icc.mp hd_mem.1).2
    have hdintri :
        60 * d ∈ (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) := by
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨d, by simpa [Dtri] using hdD, by simp⟩
    have h60d_le : 60 * d ≤ N := by
      have h180 : 180 * d ≤ 180 * (N / 180) := Nat.mul_le_mul_left 180 hd_le
      have h180N : 180 * (N / 180) ≤ N := Nat.mul_div_le N 180
      exact le_trans (by nlinarith) (le_trans h180 h180N)
    have h5_le : 5 * d ≤ N / 12 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 12)).2 ?_
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h60d_le
    have h5_ge1 : 1 ≤ 5 * d := by nlinarith
    have h5_mem : 5 * d ∈ (Finset.Icc 1 (N / 12)).filter VDParam := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_Icc.mpr ⟨h5_ge1, h5_le⟩, ?_⟩
      exact vdparam_five_mul_of_coprime6 hd_mem.2
    have hdint :
        60 * d ∈ (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
          (fun a => ({4 * a, 12 * a} : Finset ℕ))) := by
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨5 * d, h5_mem, ?_⟩
      have h60 : 60 * d = 12 * (5 * d) := by ring
      simp [h60]
    exact Finset.mem_inter.mpr ⟨hdintri, hdint⟩
  have hcard_le := Finset.card_le_card hsub
  have hDtri_eq : ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card = Dtri.card := by
    simp [Dtri]
  calc
    ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card = Dtri.card := hDtri_eq
    _ = O.card := hcardO.symm
    _ ≤ ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card := hcard_le

/-- **Stronger quantitative overlap with T-family.**

    Besides the `60d` overlap channel, there is an additional channel
    `180d = 4*(45d)` on the sub-band `d ≤ N/540`. Therefore:

    `|U△ ∩ U_T| ≥ |{d ≤ N/180 : gcd(d,6)=1}| + |{d ≤ N/540 : gcd(d,6)=1}|`. -/
theorem vd_triangle_t_overlap_card_lb_strong (N : ℕ) :
    ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card +
      ((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).card ≤
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card := by
  set Dtri := (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)
  set D540 := (Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)
  set O60 := Dtri.image (fun d => 60 * d)
  set O180 := D540.image (fun d => 180 * d)
  have hsubD : D540 ⊆ Dtri := by
    intro d hd
    have hd' : d ∈ Finset.Icc 1 (N / 540) ∧ Nat.Coprime d 6 := by
      simpa [D540] using (Finset.mem_filter.mp hd)
    have hle : d ≤ N / 180 := by
      have h540 : d * 540 ≤ N :=
        (Nat.le_div_iff_mul_le (by decide : 0 < 540)).mp (Finset.mem_Icc.mp hd'.1).2
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 180)).mpr (by nlinarith)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd'.1).1, hle⟩, hd'.2⟩
  have hcardO60 : O60.card = Dtri.card :=
    Finset.card_image_of_injective Dtri (fun d1 d2 h =>
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 60) h)
  have hcardO180 : O180.card = D540.card :=
    Finset.card_image_of_injective D540 (fun d1 d2 h =>
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 180) h)
  have hdisj : Disjoint O60 O180 := by
    rw [Finset.disjoint_left]
    intro x hx60 hx180
    rcases Finset.mem_image.mp hx60 with ⟨d1, hd1, hx1⟩
    rcases Finset.mem_image.mp hx180 with ⟨d2, hd2, hx2⟩
    have hd1c : Nat.Coprime d1 6 := by
      have hd1' : d1 ∈ Finset.Icc 1 (N / 180) ∧ Nat.Coprime d1 6 := by
        simpa [Dtri] using (Finset.mem_filter.mp hd1)
      exact hd1'.2
    have hd1_not3 : ¬(3 ∣ d1) := by
      intro h3
      exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) h3 (by decide : 3 ∣ 6)) hd1c
    have hEq : 60 * d1 = 180 * d2 := by simp [hx1, hx2]
    have h3dvd : 3 ∣ d1 := by
      refine ⟨d2, ?_⟩
      omega
    exact (hd1_not3 h3dvd).elim
  have hsub : O60 ∪ O180 ⊆
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx60 | hx180
    · rcases Finset.mem_image.mp hx60 with ⟨d, hdD, rfl⟩
      have hd_mem : d ∈ Finset.Icc 1 (N / 180) ∧ Nat.Coprime d 6 := by
        simpa [Dtri] using (Finset.mem_filter.mp hdD)
      have hd_ge1 : 1 ≤ d := (Finset.mem_Icc.mp hd_mem.1).1
      have hd_le : d ≤ N / 180 := (Finset.mem_Icc.mp hd_mem.1).2
      have hdintri :
          60 * d ∈ (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
            (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) := by
        refine Finset.mem_biUnion.mpr ?_
        exact ⟨d, by simpa [Dtri] using hdD, by simp⟩
      have h60d_le : 60 * d ≤ N := by
        have h180 : 180 * d ≤ 180 * (N / 180) := Nat.mul_le_mul_left 180 hd_le
        have h180N : 180 * (N / 180) ≤ N := Nat.mul_div_le N 180
        exact le_trans (by nlinarith) (le_trans h180 h180N)
      have h5_le : 5 * d ≤ N / 12 := by
        refine (Nat.le_div_iff_mul_le (by decide : 0 < 12)).2 ?_
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h60d_le
      have h5_ge1 : 1 ≤ 5 * d := by nlinarith
      have h5_mem : 5 * d ∈ (Finset.Icc 1 (N / 12)).filter VDParam := by
        refine Finset.mem_filter.mpr ?_
        refine ⟨Finset.mem_Icc.mpr ⟨h5_ge1, h5_le⟩, ?_⟩
        exact vdparam_five_mul_of_coprime6 hd_mem.2
      have hdint :
          60 * d ∈ (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
            (fun a => ({4 * a, 12 * a} : Finset ℕ))) := by
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨5 * d, h5_mem, ?_⟩
        have h60 : 60 * d = 12 * (5 * d) := by ring
        simp [h60]
      exact Finset.mem_inter.mpr ⟨hdintri, hdint⟩
    · rcases Finset.mem_image.mp hx180 with ⟨d, hdD, rfl⟩
      have hd_mem : d ∈ Finset.Icc 1 (N / 540) ∧ Nat.Coprime d 6 := by
        simpa [D540] using (Finset.mem_filter.mp hdD)
      have hd_ge1 : 1 ≤ d := (Finset.mem_Icc.mp hd_mem.1).1
      have hd_le : d ≤ N / 540 := (Finset.mem_Icc.mp hd_mem.1).2
      have hdintri :
          180 * d ∈ (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
            (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) := by
        have hdD' : d ∈ D540 := by simpa [D540] using hdD
        refine Finset.mem_biUnion.mpr ?_
        exact ⟨d, hsubD hdD', by simp⟩
      have h540d_le : 540 * d ≤ N := by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by decide : 0 < 540)).mp hd_le
      have h45_le : 45 * d ≤ N / 12 := by
        refine (Nat.le_div_iff_mul_le (by decide : 0 < 12)).2 ?_
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h540d_le
      have h45_ge1 : 1 ≤ 45 * d := by nlinarith
      have h45_mem : 45 * d ∈ (Finset.Icc 1 (N / 12)).filter VDParam := by
        refine Finset.mem_filter.mpr ?_
        refine ⟨Finset.mem_Icc.mpr ⟨h45_ge1, h45_le⟩, ?_⟩
        exact vdparam_fortyfive_mul_of_coprime6 hd_mem.2
      have hdint :
          180 * d ∈ (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
            (fun a => ({4 * a, 12 * a} : Finset ℕ))) := by
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨45 * d, h45_mem, ?_⟩
        have h180 : 180 * d = 4 * (45 * d) := by ring
        simp [h180]
      exact Finset.mem_inter.mpr ⟨hdintri, hdint⟩
  have hcard_le : (O60 ∪ O180).card ≤
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card :=
    Finset.card_le_card hsub
  have hcard_union : (O60 ∪ O180).card = O60.card + O180.card :=
    Finset.card_union_of_disjoint hdisj
  calc
    ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card +
      ((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).card
        = Dtri.card + D540.card := by simp [Dtri, D540]
    _ = O60.card + O180.card := by omega
    _ = (O60 ∪ O180).card := hcard_union.symm
    _ ≤ ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card := hcard_le

/-- For `N ≥ 540`, triangle-vs-T overlap has at least two elements. -/
theorem vd_triangle_t_overlap_card_ge_two (N : ℕ) (hN : 540 ≤ N) :
    2 ≤ ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card := by
  have hDtri_one : 1 ≤ ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card := by
    refine Finset.one_le_card.mpr ?_
    refine ⟨1, ?_⟩
    have h1 : 1 ≤ N / 180 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 180)).2 ?_
      exact le_trans (by decide : 180 ≤ 540) hN
    simp [h1]
  have hD540_one : 1 ≤ ((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).card := by
    refine Finset.one_le_card.mpr ?_
    refine ⟨1, ?_⟩
    have h1 : 1 ≤ N / 540 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 540)).2 hN
    simp [h1]
  have hcard :=
    vd_triangle_t_overlap_card_lb_strong N
  omega

/-- For `N ≥ 900`, triangle-vs-T overlap has at least three elements. -/
  theorem vd_triangle_t_overlap_card_ge_three (N : ℕ) (hN : 900 ≤ N) :
    3 ≤ ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card := by
  have hDtri_two : 2 ≤ ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card := by
    have h1 : 1 ≤ N / 180 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 180)).2 ?_
      exact le_trans (by decide : 180 ≤ 900) hN
    have h5 : 5 ≤ N / 180 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 180)).2 ?_
      exact le_trans (by decide : 900 ≤ 900) hN
    have hsub : ({1, 5} : Finset ℕ) ⊆ ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)) := by
      intro x hx
      have hx' : x = 1 ∨ x = 5 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx
      rcases hx' with rfl | rfl
      · simp [h1]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, h5⟩, by decide⟩
    have hcard := Finset.card_le_card hsub
    simpa using hcard
  have hD540_one : 1 ≤ ((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).card := by
    refine Finset.one_le_card.mpr ?_
    refine ⟨1, ?_⟩
    have h1 : 1 ≤ N / 540 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 540)).2 ?_
      exact le_trans (by decide : 540 ≤ 900) hN
    simp [h1]
  have hcard :=
    vd_triangle_t_overlap_card_lb_strong N
  omega

/-- **Quantitative overlap with S-family (low-parameter band).**

    Let
    `D_low = {d ∈ [1, N/240] : Nat.Coprime d 6}`,
    `U_low = ⋃_{d∈D_low} {60d,120d,180d}`,
    `U_S = ⋃_{a∈[1,N/6], VDParam a} {3a,6a}`.

    Then `|U_low ∩ U_S| ≥ |D_low|`.

    Proof: each `d ∈ D_low` contributes shared element
    `120d = 3*(40d)` with `40d` in the S-parameter set. -/
theorem vd_triangle_s_overlap_card_lb (N : ℕ) :
    ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card ≤
      ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)
  set O := Dlow.image (fun d => 120 * d)
  have hcardO : O.card = Dlow.card :=
    Finset.card_image_of_injective Dlow (fun d1 d2 h =>
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 120) h)
  have hsub : O ⊆
      (((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ))) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨d, hdD, rfl⟩
    have hd_mem : d ∈ Finset.Icc 1 (N / 240) ∧ Nat.Coprime d 6 := by
      simpa [Dlow] using (Finset.mem_filter.mp hdD)
    have hd_ge1 : 1 ≤ d := (Finset.mem_Icc.mp hd_mem.1).1
    have hd_le : d ≤ N / 240 := (Finset.mem_Icc.mp hd_mem.1).2
    have hdintri :
        120 * d ∈ (((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) := by
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨d, by simpa [Dlow] using hdD, by simp⟩
    have h240d_le : 240 * d ≤ N := by
      have h240 : 240 * d ≤ 240 * (N / 240) := Nat.mul_le_mul_left 240 hd_le
      have h240N : 240 * (N / 240) ≤ N := Nat.mul_div_le N 240
      exact le_trans h240 h240N
    have h40_le : 40 * d ≤ N / 6 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 6)).2 ?_
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h240d_le
    have h40_ge1 : 1 ≤ 40 * d := by nlinarith
    have h40_mem : 40 * d ∈ (Finset.Icc 1 (N / 6)).filter VDParam := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_Icc.mpr ⟨h40_ge1, h40_le⟩, ?_⟩
      exact vdparam_forty_mul_of_coprime6 hd_mem.2
    have hdins :
        120 * d ∈ (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
          (fun a => ({3 * a, 6 * a} : Finset ℕ))) := by
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨40 * d, h40_mem, ?_⟩
      have h120 : 120 * d = 3 * (40 * d) := by ring
      simp [h120]
    exact Finset.mem_inter.mpr ⟨hdintri, hdins⟩
  have hcard_le := Finset.card_le_card hsub
  have hDlow_eq : ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card = Dlow.card := by
    simp [Dlow]
  calc
    ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card = Dlow.card := hDlow_eq
    _ = O.card := hcardO.symm
    _ ≤ ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := hcard_le

/-- For `N ≥ 240`, triangle-vs-S overlap on the low band is nonempty. -/
theorem vd_triangle_s_overlap_card_pos (N : ℕ) (hN : 240 ≤ N) :
    1 ≤ ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
  have hDlow_one : 1 ≤ ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by
    refine Finset.one_le_card.mpr ?_
    refine ⟨1, ?_⟩
    have h1 : 1 ≤ N / 240 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 240)).2 hN
    simp [h1]
  have hcard :=
    vd_triangle_s_overlap_card_lb N
  omega

/-- For `N ≥ 1200`, low-band triangle-vs-S overlap has at least two elements. -/
theorem vd_triangle_s_overlap_card_ge_two (N : ℕ) (hN : 1200 ≤ N) :
    2 ≤ ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
  have hDlow_two : 2 ≤ ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by
    have h1 : 1 ≤ N / 240 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 240)).2 ?_
      exact le_trans (by decide : 240 ≤ 1200) hN
    have h5 : 5 ≤ N / 240 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 240)).2 ?_
      exact le_trans (by decide : 1200 ≤ 1200) hN
    have hsub : ({1, 5} : Finset ℕ) ⊆ ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)) := by
      intro x hx
      have hx' : x = 1 ∨ x = 5 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx
      rcases hx' with rfl | rfl
      · simp [h1]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, h5⟩, by decide⟩
    have hcard := Finset.card_le_card hsub
    simpa using hcard
  have hcard :=
    vd_triangle_s_overlap_card_lb N
  omega

/-- For `N ≥ 1680`, low-band triangle-vs-S overlap has at least three elements. -/
theorem vd_triangle_s_overlap_card_ge_three (N : ℕ) (hN : 1680 ≤ N) :
    3 ≤ ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
  have hDlow_three : 3 ≤ ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by
    have h1 : 1 ≤ N / 240 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 240)).2 ?_
      exact le_trans (by decide : 240 ≤ 1680) hN
    have h5 : 5 ≤ N / 240 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 240)).2 ?_
      exact le_trans (by decide : 1200 ≤ 1680) hN
    have h7 : 7 ≤ N / 240 := by
      refine (Nat.le_div_iff_mul_le (by decide : 0 < 240)).2 ?_
      exact le_trans (by decide : 1680 ≤ 1680) hN
    have hsub : ({1, 5, 7} : Finset ℕ) ⊆ ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)) := by
      intro x hx
      have hx' : x = 1 ∨ x = 5 ∨ x = 7 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx
      rcases hx' with rfl | rfl | rfl
      · simp [h1]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, h5⟩, by decide⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, h7⟩, by decide⟩
    have hcard := Finset.card_le_card hsub
    simpa using hcard
  have hcard :=
    vd_triangle_s_overlap_card_lb N
  omega

/-! ### Section 7: Finset infrastructure -/

/-- The S-pair {3a, 6a} has exactly 2 elements for a > 0. -/
private theorem s_pair_card_eq_two {a : ℕ} (ha : 0 < a) :
    ({3*a, 6*a} : Finset ℕ).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]; simp

/-- The T-pair {4a, 12a} has exactly 2 elements for a > 0. -/
private theorem t_pair_card_eq_two {a : ℕ} (ha : 0 < a) :
    ({4*a, 12*a} : Finset ℕ).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]; simp

/-- The S-pair {3a, 6a} ⊆ {1, …, N} when 6a ≤ N and a > 0. -/
private theorem s_pair_subset_Icc {a N : ℕ} (ha : 0 < a) (h6 : 6 * a ≤ N) :
    ({3*a, 6*a} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl <;> omega

/-- The T-pair {4a, 12a} ⊆ {1, …, N} when 12a ≤ N and a > 0. -/
private theorem t_pair_subset_Icc {a N : ℕ} (ha : 0 < a) (h12 : 12 * a ≤ N) :
    ({4*a, 12*a} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl <;> omega

/-- A pair-free set keeps at most 1 element from {3a, 6a}. -/
private theorem s_pair_inter_card_le_one {A : Finset ℕ} (hA : PairFree A)
    {a : ℕ} (ha : 0 < a) :
    (({3*a, 6*a} : Finset ℕ) ∩ A).card ≤ 1 := by
  suffices h : ∃ x ∈ ({3*a, 6*a} : Finset ℕ), x ∉ A by
    obtain ⟨x, hxS, hxA⟩ := h
    calc (({3*a, 6*a} : Finset ℕ) ∩ A).card
        ≤ (({3*a, 6*a} : Finset ℕ).erase x).card :=
          Finset.card_le_card fun b hb =>
            Finset.mem_erase.mpr ⟨fun h => by subst h; exact hxA (Finset.mem_inter.mp hb).2,
              (Finset.mem_inter.mp hb).1⟩
      _ = ({3*a, 6*a} : Finset ℕ).card - 1 := Finset.card_erase_of_mem hxS
      _ = 1 := by rw [s_pair_card_eq_two ha]
  by_contra h; push_neg at h
  exact pair_free_not_3k_6k hA ha (h _ (by simp)) (h _ (by simp))

/-- A pair-free set keeps at most 1 element from {4a, 12a}. -/
private theorem t_pair_inter_card_le_one {A : Finset ℕ} (hA : PairFree A)
    {a : ℕ} (ha : 0 < a) :
    (({4*a, 12*a} : Finset ℕ) ∩ A).card ≤ 1 := by
  suffices h : ∃ x ∈ ({4*a, 12*a} : Finset ℕ), x ∉ A by
    obtain ⟨x, hxT, hxA⟩ := h
    calc (({4*a, 12*a} : Finset ℕ) ∩ A).card
        ≤ (({4*a, 12*a} : Finset ℕ).erase x).card :=
          Finset.card_le_card fun b hb =>
            Finset.mem_erase.mpr ⟨fun h => by subst h; exact hxA (Finset.mem_inter.mp hb).2,
              (Finset.mem_inter.mp hb).1⟩
      _ = ({4*a, 12*a} : Finset ℕ).card - 1 := Finset.card_erase_of_mem hxT
      _ = 1 := by rw [t_pair_card_eq_two ha]
  by_contra h; push_neg at h
  exact pair_free_not_4k_12k hA ha (h _ (by simp)) (h _ (by simp))

/-! ### Section 8: Overlap-aware mixed bounds -/

/-- **Triangle + T mixed counting with explicit overlap penalty.**

    Let
    `D△ = {d ∈ [1,N/180] : Nat.Coprime d 6}`,
    `D_T = {a ∈ [1,N/12] : VDParam a}`,
    `U△ = ⋃_{d∈D△} {60d,120d,180d}`,
    `U_T = ⋃_{a∈D_T} {4a,12a}`.

    For pair-free `A ⊆ [1,N]`:

    `A.card + 2*|D△| + |D_T| ≤ N + |U△ ∩ U_T|`.

    This is the precise inclusion-exclusion loss when trying to combine
    triangle and T families without cross-disjointness. -/
theorem vd_triangle_t_overlap_penalty_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + 2 * ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card
      + ((Finset.Icc 1 (N / 12)).filter VDParam).card ≤
      N +
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
        (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
          (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card := by
  set Dtri := (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6) with hDtri
  set DT := (Finset.Icc 1 (N / 12)).filter VDParam with hDT
  let tri : ℕ → Finset ℕ := fun d => {60 * d, 120 * d, 180 * d}
  let tpair : ℕ → Finset ℕ := fun a => {4 * a, 12 * a}
  set Utri := Dtri.biUnion tri with hUtri
  set UT := DT.biUnion tpair with hUT
  set U := Utri ∪ UT with hU
  have hDtri_mem : ∀ d ∈ Dtri, 0 < d ∧ Nat.Coprime d 6 ∧ 180 * d ≤ N := by
    intro d hd
    simp only [hDtri, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨by omega, hd.2, by omega⟩
  have hDT_mem : ∀ a ∈ DT, 0 < a ∧ VDParam a ∧ 12 * a ≤ N := by
    intro a ha
    simp only [hDT, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have htri_pwd : (↑Dtri : Set ℕ).PairwiseDisjoint tri := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact triangles_disjoint_coprime6 hne
      (hDtri_mem d₁ (Finset.mem_coe.mp hd₁)).2.1
      (hDtri_mem d₂ (Finset.mem_coe.mp hd₂)).2.1
  have htri_card : ∀ d ∈ Dtri, (tri d).card = 3 := by
    intro d hd
    have hdpos : 0 < d := (hDtri_mem d hd).1
    have h60d_pos : 0 < 60 * d := by omega
    simpa [tri, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using triangle_card_eq_three h60d_pos
  have htri_inter : ∀ d ∈ Dtri, ((tri d) ∩ A).card ≤ 1 := by
    intro d hd
    have hdpos : 0 < d := (hDtri_mem d hd).1
    have h60d_pos : 0 < 60 * d := by omega
    have h60div : 60 ∣ 60 * d := ⟨d, by ring⟩
    simpa [tri, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using pair_free_triangle_inter_card_le_one hA h60d_pos h60div
  have ht_pwd : (↑DT : Set ℕ).PairwiseDisjoint tpair := by
    intro a₁ ha₁ a₂ ha₂ hne
    exact vd_t_pairs_disjoint
      (hDT_mem a₁ (Finset.mem_coe.mp ha₁)).1
      (hDT_mem a₂ (Finset.mem_coe.mp ha₂)).1
      hne
      (hDT_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
      (hDT_mem a₂ (Finset.mem_coe.mp ha₂)).2.1
  have ht_card : ∀ a ∈ DT, (tpair a).card = 2 := by
    intro a ha
    exact t_pair_card_eq_two (hDT_mem a ha).1
  have ht_inter : ∀ a ∈ DT, ((tpair a) ∩ A).card ≤ 1 := by
    intro a ha
    exact t_pair_inter_card_le_one hA (hDT_mem a ha).1
  have htriA : (Utri ∩ A).card ≤ Dtri.card := by
    rw [hUtri]
    have h := PackingBound.card_inter_biUnion_le Dtri tri A 1 htri_pwd htri_inter
    simpa using h
  have htA : (UT ∩ A).card ≤ DT.card := by
    rw [hUT]
    have h := PackingBound.card_inter_biUnion_le DT tpair A 1 ht_pwd ht_inter
    simpa using h
  have hUA : (U ∩ A).card ≤ Dtri.card + DT.card := by
    rw [hU, Finset.union_inter_distrib_right]
    calc
      ((Utri ∩ A) ∪ (UT ∩ A)).card ≤ (Utri ∩ A).card + (UT ∩ A).card :=
        Finset.card_union_le _ _
      _ ≤ Dtri.card + DT.card := Nat.add_le_add htriA htA
  have hUtri_sub : Utri ⊆ Finset.Icc 1 N := by
    rw [hUtri]
    refine Finset.biUnion_subset.mpr ?_
    intro d hd
    have hdpos : 0 < d := (hDtri_mem d hd).1
    have hN : 180 * d ≤ N := (hDtri_mem d hd).2.2
    intro x hx
    simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    rcases hx with rfl | rfl | rfl
    · refine ⟨by omega, ?_⟩
      exact le_trans (by nlinarith : 60 * d ≤ 180 * d) hN
    · refine ⟨by omega, ?_⟩
      exact le_trans (by nlinarith : 120 * d ≤ 180 * d) hN
    · exact ⟨by omega, hN⟩
  have hUT_sub : UT ⊆ Finset.Icc 1 N := by
    rw [hUT]
    refine Finset.biUnion_subset.mpr ?_
    intro a ha
    exact t_pair_subset_Icc (hDT_mem a ha).1 (hDT_mem a ha).2.2
  have hU_sub : U ⊆ Finset.Icc 1 N := by
    rw [hU]
    exact Finset.union_subset hUtri_sub hUT_sub
  have hAle : A.card ≤ (U ∩ A).card + (Finset.Icc 1 N \ U).card := by
    calc A.card
        ≤ (U ∩ A ∪ (Finset.Icc 1 N \ U)).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ U
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  have hsdiff : (Finset.Icc 1 N \ U).card + U.card = N := by
    rw [Finset.card_sdiff_add_card_eq_card hU_sub, hIcc]
  have hUtri_card : Utri.card = 3 * Dtri.card := by
    rw [hUtri]
    exact PackingBound.card_biUnion_const Dtri tri 3 htri_pwd htri_card
  have hUT_card : UT.card = 2 * DT.card := by
    rw [hUT]
    exact PackingBound.card_biUnion_const DT tpair 2 ht_pwd ht_card
  have hUnionInter :
      U.card +
        (Utri ∩ UT).card = Utri.card + UT.card := by
    rw [hU]
    exact Finset.card_union_add_card_inter Utri UT
  have hInter_def :
      (Utri ∩ UT).card =
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
        (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
          (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card := by
    simp [Utri, UT, hDtri, hDT, tri, tpair]
  omega

/-- Every triangle-vs-T overlap element lies in one of the two explicit channels:
    `60d` (`d ≤ N/180`) or `180d` (`d ≤ N/540`), with `d` coprime to `6`. -/
theorem vd_triangle_t_overlap_subset_channels (N : ℕ) :
    ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))) ⊆
      (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).image (fun d => 60 * d)) ∪
      (((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).image (fun d => 180 * d)) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx_tri, hx_t⟩
  rcases Finset.mem_biUnion.mp hx_tri with ⟨d, hdD, hxin_tri⟩
  rcases Finset.mem_biUnion.mp hx_t with ⟨a, haD, hxin_t⟩
  have hd_mem : d ∈ Finset.Icc 1 (N / 180) ∧ Nat.Coprime d 6 := by
    exact Finset.mem_filter.mp hdD
  have ha_mem : a ∈ Finset.Icc 1 (N / 12) ∧ VDParam a := by
    exact Finset.mem_filter.mp haD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxin_tri hxin_t
  rcases hxin_tri with rfl | rfl | rfl
  · rcases hxin_t with h4 | h12
    · have ha15 : a = 15 * d := by omega
      subst ha15
      exact False.elim ((not_vdparam_fifteen_mul_of_coprime6 hd_mem.2) ha_mem.2)
    · have ha5 : a = 5 * d := by omega
      subst ha5
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d, by simpa using hdD, rfl⟩)
  · rcases hxin_t with h4 | h12
    · have ha30 : a = 30 * d := by omega
      subst ha30
      exact False.elim ((not_vdparam_thirty_mul_of_coprime6 hd_mem.2) ha_mem.2)
    · have ha10 : a = 10 * d := by omega
      subst ha10
      exact False.elim ((not_vdparam_ten_mul_of_coprime6 hd_mem.2) ha_mem.2)
  · rcases hxin_t with h4 | h12
    · have ha45 : a = 45 * d := by omega
      subst ha45
      have hdIcc540 : d ∈ Finset.Icc 1 (N / 540) := by
        refine Finset.mem_Icc.mpr ?_
        refine ⟨(Finset.mem_Icc.mp hd_mem.1).1, ?_⟩
        have h45 : 45 * d ≤ N / 12 := by
          simpa using (Finset.mem_Icc.mp ha_mem.1).2
        have h540 : 540 * d ≤ N := by
          have h12 : 45 * d * 12 ≤ N :=
            (Nat.le_div_iff_mul_le (by decide : 0 < 12)).mp h45
          nlinarith
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 540)).2 (by simpa [Nat.mul_comm] using h540)
      have hdD540 : d ∈ (Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6) := by
        exact Finset.mem_filter.mpr ⟨hdIcc540, hd_mem.2⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hdD540, rfl⟩)
    · have ha15 : a = 15 * d := by omega
      subst ha15
      exact False.elim ((not_vdparam_fifteen_mul_of_coprime6 hd_mem.2) ha_mem.2)

/-- Upper bound matching the explicit channel decomposition for triangle-vs-T overlap. -/
theorem vd_triangle_t_overlap_card_le_strong (N : ℕ) :
    ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card ≤
      ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card +
      ((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).card := by
  set Dtri := (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)
  set D540 := (Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)
  set O60 := Dtri.image (fun d => 60 * d)
  set O180 := D540.image (fun d => 180 * d)
  have hdisj : Disjoint O60 O180 := by
    rw [Finset.disjoint_left]
    intro x hx60 hx180
    rcases Finset.mem_image.mp hx60 with ⟨d1, hd1, hx1⟩
    rcases Finset.mem_image.mp hx180 with ⟨d2, hd2, hx2⟩
    have hd1c : Nat.Coprime d1 6 := (Finset.mem_filter.mp hd1).2
    have hd1_not3 : ¬(3 ∣ d1) := by
      intro h3
      exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) h3 (by decide : 3 ∣ 6)) hd1c
    have hEq : 60 * d1 = 180 * d2 := by simp [hx1, hx2]
    have h3dvd : 3 ∣ d1 := by
      refine ⟨d2, ?_⟩
      omega
    exact (hd1_not3 h3dvd).elim
  have hsub : ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
      (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
      (fun a => ({4 * a, 12 * a} : Finset ℕ)))) ⊆ O60 ∪ O180 := by
    intro x hx
    have h := vd_triangle_t_overlap_subset_channels N hx
    simpa [O60, O180, Dtri, D540] using h
  have hcard_sub := Finset.card_le_card hsub
  have hcard_union : (O60 ∪ O180).card = O60.card + O180.card :=
    Finset.card_union_of_disjoint hdisj
  have hO60 : O60.card = Dtri.card :=
    Finset.card_image_of_injective Dtri (fun d1 d2 h =>
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 60) h)
  have hO180 : O180.card = D540.card :=
    Finset.card_image_of_injective D540 (fun d1 d2 h =>
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 180) h)
  calc
    ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card
        ≤ (O60 ∪ O180).card := hcard_sub
    _ = O60.card + O180.card := hcard_union
    _ = Dtri.card + D540.card := by rw [hO60, hO180]
    _ = ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card
        + ((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).card := by
          simp [Dtri, D540]

/-- Exact cardinality formula for triangle-vs-T overlap. -/
theorem vd_triangle_t_overlap_card_eq_strong (N : ℕ) :
    ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 12)).filter VDParam).biUnion
        (fun a => ({4 * a, 12 * a} : Finset ℕ)))).card =
      ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card +
      ((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).card := by
  apply le_antisymm
  · exact vd_triangle_t_overlap_card_le_strong N
  · exact vd_triangle_t_overlap_card_lb_strong N

/-- Low-band triangle-vs-S overlap lies entirely in the single channel `120d`. -/
theorem vd_triangle_s_overlap_subset_channel (N : ℕ) :
    ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))) ⊆
      (((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).image (fun d => 120 * d)) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx_tri, hx_s⟩
  rcases Finset.mem_biUnion.mp hx_tri with ⟨d, hdD, hxin_tri⟩
  rcases Finset.mem_biUnion.mp hx_s with ⟨a, haD, hxin_s⟩
  have hd_mem : d ∈ Finset.Icc 1 (N / 240) ∧ Nat.Coprime d 6 := Finset.mem_filter.mp hdD
  have ha_mem : a ∈ Finset.Icc 1 (N / 6) ∧ VDParam a := Finset.mem_filter.mp haD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxin_tri hxin_s
  rcases hxin_tri with rfl | rfl | rfl
  · rcases hxin_s with h3 | h6
    · have ha20 : a = 20 * d := by omega
      subst ha20
      exact False.elim ((not_vdparam_twenty_mul_of_coprime6 hd_mem.2) ha_mem.2)
    · have ha10 : a = 10 * d := by omega
      subst ha10
      exact False.elim ((not_vdparam_ten_mul_of_coprime6 hd_mem.2) ha_mem.2)
  · rcases hxin_s with h3 | h6
    · have ha40 : a = 40 * d := by omega
      subst ha40
      exact Finset.mem_image.mpr ⟨d, hdD, rfl⟩
    · have ha20 : a = 20 * d := by omega
      subst ha20
      exact False.elim ((not_vdparam_twenty_mul_of_coprime6 hd_mem.2) ha_mem.2)
  · rcases hxin_s with h3 | h6
    · have ha60 : a = 60 * d := by omega
      subst ha60
      exact False.elim ((not_vdparam_sixty_mul_of_coprime6 hd_mem.2) ha_mem.2)
    · have ha30 : a = 30 * d := by omega
      subst ha30
      exact False.elim ((not_vdparam_thirty_mul_of_coprime6 hd_mem.2) ha_mem.2)

/-- Upper bound matching the single-channel decomposition for low-band triangle-vs-S overlap. -/
theorem vd_triangle_s_overlap_card_le_strong (N : ℕ) :
    ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card ≤
      ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)
  set O120 := Dlow.image (fun d => 120 * d)
  have hsub : ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
      (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
      (fun a => ({3 * a, 6 * a} : Finset ℕ)))) ⊆ O120 := by
    intro x hx
    have h := vd_triangle_s_overlap_subset_channel N hx
    simpa [O120, Dlow] using h
  have hcard_sub := Finset.card_le_card hsub
  have hO120 : O120.card = Dlow.card :=
    Finset.card_image_of_injective Dlow (fun d1 d2 h =>
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 120) h)
  calc
    ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card
        ≤ O120.card := hcard_sub
    _ = Dlow.card := hO120
    _ = ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by simp [Dlow]

/-- Exact cardinality formula for low-band triangle-vs-S overlap. -/
theorem vd_triangle_s_overlap_card_eq_strong (N : ℕ) :
    ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card =
      ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by
  apply le_antisymm
  · exact vd_triangle_s_overlap_card_le_strong N
  · exact vd_triangle_s_overlap_card_lb N

/-- Full triangle-vs-S overlap lies entirely in the low-band channel `120d`
    with `d ≤ N/240`. -/
theorem vd_triangle_s_full_overlap_subset_channel (N : ℕ) :
    ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))) ⊆
      (((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).image (fun d => 120 * d)) := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx_tri, hx_s⟩
  rcases Finset.mem_biUnion.mp hx_tri with ⟨d, hdD, hxin_tri⟩
  rcases Finset.mem_biUnion.mp hx_s with ⟨a, haD, hxin_s⟩
  have hd_mem : d ∈ Finset.Icc 1 (N / 180) ∧ Nat.Coprime d 6 := Finset.mem_filter.mp hdD
  have ha_mem : a ∈ Finset.Icc 1 (N / 6) ∧ VDParam a := Finset.mem_filter.mp haD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxin_tri hxin_s
  rcases hxin_tri with rfl | rfl | rfl
  · rcases hxin_s with h3 | h6
    · have ha20 : a = 20 * d := by omega
      subst ha20
      exact False.elim ((not_vdparam_twenty_mul_of_coprime6 hd_mem.2) ha_mem.2)
    · have ha10 : a = 10 * d := by omega
      subst ha10
      exact False.elim ((not_vdparam_ten_mul_of_coprime6 hd_mem.2) ha_mem.2)
  · rcases hxin_s with h3 | h6
    · have ha40 : a = 40 * d := by omega
      subst ha40
      have hdIcc240 : d ∈ Finset.Icc 1 (N / 240) := by
        refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd_mem.1).1, ?_⟩
        have h40 : 40 * d ≤ N / 6 := by
          simpa using (Finset.mem_Icc.mp ha_mem.1).2
        have h240 : 240 * d ≤ N := by
          have h6 : 40 * d * 6 ≤ N :=
            (Nat.le_div_iff_mul_le (by decide : 0 < 6)).mp h40
          nlinarith
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 240)).2 (by simpa [Nat.mul_comm] using h240)
      have hdD240 : d ∈ (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6) := by
        exact Finset.mem_filter.mpr ⟨hdIcc240, hd_mem.2⟩
      exact Finset.mem_image.mpr ⟨d, hdD240, rfl⟩
    · have ha20 : a = 20 * d := by omega
      subst ha20
      exact False.elim ((not_vdparam_twenty_mul_of_coprime6 hd_mem.2) ha_mem.2)
  · rcases hxin_s with h3 | h6
    · have ha60 : a = 60 * d := by omega
      subst ha60
      exact False.elim ((not_vdparam_sixty_mul_of_coprime6 hd_mem.2) ha_mem.2)
    · have ha30 : a = 30 * d := by omega
      subst ha30
      exact False.elim ((not_vdparam_thirty_mul_of_coprime6 hd_mem.2) ha_mem.2)

/-- Upper bound matching the low-band channel decomposition for full triangle-vs-S overlap. -/
theorem vd_triangle_s_full_overlap_card_le_strong (N : ℕ) :
    ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card ≤
      ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)
  set O120 := Dlow.image (fun d => 120 * d)
  have hsub : ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
      (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
      (fun a => ({3 * a, 6 * a} : Finset ℕ)))) ⊆ O120 := by
    intro x hx
    have h := vd_triangle_s_full_overlap_subset_channel N hx
    simpa [O120, Dlow] using h
  have hcard_sub := Finset.card_le_card hsub
  have hO120 : O120.card = Dlow.card :=
    Finset.card_image_of_injective Dlow (fun d1 d2 h =>
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 120) h)
  calc
    ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card
        ≤ O120.card := hcard_sub
    _ = Dlow.card := hO120
    _ = ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by simp [Dlow]

/-- Lower bound: low-band overlap injects into full triangle-vs-S overlap. -/
theorem vd_triangle_s_full_overlap_card_lb (N : ℕ) :
    ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card ≤
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
  have hlow : ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card ≤
      ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card :=
    vd_triangle_s_overlap_card_lb N
  have hsub : ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
      (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
      (fun a => ({3 * a, 6 * a} : Finset ℕ)))) ⊆
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))) := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_tri_low, hx_s⟩
    have hx_tri_full :
        x ∈ (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) := by
      rcases Finset.mem_biUnion.mp hx_tri_low with ⟨d, hdLow, hxd⟩
      have hd_mem : d ∈ Finset.Icc 1 (N / 240) ∧ Nat.Coprime d 6 := Finset.mem_filter.mp hdLow
      have hdIcc180 : d ∈ Finset.Icc 1 (N / 180) := by
        refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd_mem.1).1, ?_⟩
        have h240 : d * 240 ≤ N :=
          (Nat.le_div_iff_mul_le (by decide : 0 < 240)).mp (Finset.mem_Icc.mp hd_mem.1).2
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 180)).2 (by nlinarith)
      have hdFull : d ∈ (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6) := by
        exact Finset.mem_filter.mpr ⟨hdIcc180, hd_mem.2⟩
      exact Finset.mem_biUnion.mpr ⟨d, hdFull, hxd⟩
    exact Finset.mem_inter.mpr ⟨hx_tri_full, hx_s⟩
  have hcard_sub : ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
      (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
      (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card ≤
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
      (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card :=
    Finset.card_le_card hsub
  exact le_trans hlow hcard_sub

/-- Exact cardinality formula for full triangle-vs-S overlap. -/
theorem vd_triangle_s_full_overlap_card_eq_strong (N : ℕ) :
    ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
        (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
      ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card =
      ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card := by
  apply le_antisymm
  · exact vd_triangle_s_full_overlap_card_le_strong N
  · exact vd_triangle_s_full_overlap_card_lb N

/-- **Full triangle + S mixed counting with overlap penalty.**

    Let
    `D△ = {d ∈ [1,N/180] : Nat.Coprime d 6}`,
    `D_S = {a ∈ [1,N/6] : VDParam a}`,
    `U△ = ⋃_{d∈D△} {60d,120d,180d}`,
    `U_S = ⋃_{a∈D_S} {3a,6a}`.

    For pair-free `A ⊆ [1,N]`:

    `A.card + 2*|D△| + |D_S| ≤ N + |U△ ∩ U_S|`. -/
theorem vd_triangle_s_full_overlap_penalty_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + 2 * ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card
      + ((Finset.Icc 1 (N / 6)).filter VDParam).card ≤
      N +
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
        (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
          (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
  set Dtri := (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6) with hDtri
  set DS := (Finset.Icc 1 (N / 6)).filter VDParam with hDS
  let tri : ℕ → Finset ℕ := fun d => {60 * d, 120 * d, 180 * d}
  let spair : ℕ → Finset ℕ := fun a => {3 * a, 6 * a}
  set Utri := Dtri.biUnion tri with hUtri
  set US := DS.biUnion spair with hUS
  set U := Utri ∪ US with hU
  have hDtri_mem : ∀ d ∈ Dtri, 0 < d ∧ Nat.Coprime d 6 ∧ 180 * d ≤ N := by
    intro d hd
    simp only [hDtri, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨by omega, hd.2, by omega⟩
  have hDS_mem : ∀ a ∈ DS, 0 < a ∧ VDParam a ∧ 6 * a ≤ N := by
    intro a ha
    simp only [hDS, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have htri_pwd : (↑Dtri : Set ℕ).PairwiseDisjoint tri := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact triangles_disjoint_coprime6 hne
      (hDtri_mem d₁ (Finset.mem_coe.mp hd₁)).2.1
      (hDtri_mem d₂ (Finset.mem_coe.mp hd₂)).2.1
  have htri_card : ∀ d ∈ Dtri, (tri d).card = 3 := by
    intro d hd
    have hdpos : 0 < d := (hDtri_mem d hd).1
    have h60d_pos : 0 < 60 * d := by omega
    simpa [tri, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using triangle_card_eq_three h60d_pos
  have htri_inter : ∀ d ∈ Dtri, ((tri d) ∩ A).card ≤ 1 := by
    intro d hd
    have hdpos : 0 < d := (hDtri_mem d hd).1
    have h60d_pos : 0 < 60 * d := by omega
    have h60div : 60 ∣ 60 * d := ⟨d, by ring⟩
    simpa [tri, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using pair_free_triangle_inter_card_le_one hA h60d_pos h60div
  have hs_pwd : (↑DS : Set ℕ).PairwiseDisjoint spair := by
    intro a₁ ha₁ a₂ ha₂ hne
    exact vd_s_pairs_disjoint
      (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).1
      (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).1
      hne
      (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
      (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).2.1
  have hs_card : ∀ a ∈ DS, (spair a).card = 2 := by
    intro a ha
    exact s_pair_card_eq_two (hDS_mem a ha).1
  have hs_inter : ∀ a ∈ DS, ((spair a) ∩ A).card ≤ 1 := by
    intro a ha
    exact s_pair_inter_card_le_one hA (hDS_mem a ha).1
  have htriA : (Utri ∩ A).card ≤ Dtri.card := by
    rw [hUtri]
    have h := PackingBound.card_inter_biUnion_le Dtri tri A 1 htri_pwd htri_inter
    simpa using h
  have hsA : (US ∩ A).card ≤ DS.card := by
    rw [hUS]
    have h := PackingBound.card_inter_biUnion_le DS spair A 1 hs_pwd hs_inter
    simpa using h
  have hUA : (U ∩ A).card ≤ Dtri.card + DS.card := by
    rw [hU, Finset.union_inter_distrib_right]
    calc
      ((Utri ∩ A) ∪ (US ∩ A)).card ≤ (Utri ∩ A).card + (US ∩ A).card :=
        Finset.card_union_le _ _
      _ ≤ Dtri.card + DS.card := Nat.add_le_add htriA hsA
  have hUtri_sub : Utri ⊆ Finset.Icc 1 N := by
    rw [hUtri]
    refine Finset.biUnion_subset.mpr ?_
    intro d hd
    have hdpos : 0 < d := (hDtri_mem d hd).1
    have hN : 180 * d ≤ N := (hDtri_mem d hd).2.2
    intro x hx
    simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    rcases hx with rfl | rfl | rfl
    · refine ⟨by omega, ?_⟩
      exact le_trans (by nlinarith : 60 * d ≤ 180 * d) hN
    · refine ⟨by omega, ?_⟩
      exact le_trans (by nlinarith : 120 * d ≤ 180 * d) hN
    · refine ⟨by omega, hN⟩
  have hUS_sub : US ⊆ Finset.Icc 1 N := by
    rw [hUS]
    refine Finset.biUnion_subset.mpr ?_
    intro a ha
    exact s_pair_subset_Icc (hDS_mem a ha).1 (hDS_mem a ha).2.2
  have hU_sub : U ⊆ Finset.Icc 1 N := by
    rw [hU]
    exact Finset.union_subset hUtri_sub hUS_sub
  have hAle : A.card ≤ (U ∩ A).card + (Finset.Icc 1 N \ U).card := by
    calc A.card
        ≤ (U ∩ A ∪ (Finset.Icc 1 N \ U)).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ U
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  have hsdiff : (Finset.Icc 1 N \ U).card + U.card = N := by
    rw [Finset.card_sdiff_add_card_eq_card hU_sub, hIcc]
  have hUtri_card : Utri.card = 3 * Dtri.card := by
    rw [hUtri]
    exact PackingBound.card_biUnion_const Dtri tri 3 htri_pwd htri_card
  have hUS_card : US.card = 2 * DS.card := by
    rw [hUS]
    exact PackingBound.card_biUnion_const DS spair 2 hs_pwd hs_card
  have hUnionInter :
      U.card +
        (Utri ∩ US).card = Utri.card + US.card := by
    rw [hU]
    exact Finset.card_union_add_card_inter Utri US
  have hInter_def :
      (Utri ∩ US).card =
      ((((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
        (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
          (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
    simp [Utri, US, hDtri, hDS, tri, spair]
  omega

/-- **Full triangle + S net bound after exact overlap substitution.**

    Using `vd_triangle_s_full_overlap_penalty_bound` and the exact full overlap
    formula `vd_triangle_s_full_overlap_card_eq_strong`, we get:

    `A.card + |D_S| + (2*|D△| - |D_low|) ≤ N`,

    where
    `D△ = {d ≤ N/180 : gcd(d,6)=1}`,
    `D_low = {d ≤ N/240 : gcd(d,6)=1}`,
    `D_S = {a ≤ N/6 : VDParam a}`. -/
theorem vd_triangle_s_full_net_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter VDParam).card +
      (2 * ((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card
        - ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card) ≤ N := by
  set Dtri := (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6) with hDtri
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6) with hDlow
  set DS := (Finset.Icc 1 (N / 6)).filter VDParam with hDS
  have hpen := vd_triangle_s_full_overlap_penalty_bound N A hA hAN
  have hover := vd_triangle_s_full_overlap_card_eq_strong N
  rw [hover] at hpen
  have hpen' : A.card + 2 * Dtri.card + DS.card ≤ N + Dlow.card := by
    simpa [Dtri, Dlow, DS] using hpen
  have hsub : Dlow ⊆ Dtri := by
    intro d hd
    have hd' : d ∈ Finset.Icc 1 (N / 240) ∧ Nat.Coprime d 6 := Finset.mem_filter.mp hd
    have hle : d ≤ N / 180 := by
      have h240 : d * 240 ≤ N :=
        (Nat.le_div_iff_mul_le (by decide : 0 < 240)).mp (Finset.mem_Icc.mp hd'.1).2
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 180)).2 (by nlinarith)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd'.1).1, hle⟩, hd'.2⟩
  have hle_cards : Dlow.card ≤ Dtri.card := Finset.card_le_card hsub
  have hle_two : Dlow.card ≤ 2 * Dtri.card := by omega
  have hmain : A.card + 2 * Dtri.card + DS.card ≤ N + Dlow.card := hpen'
  have hmain' : A.card + DS.card + (2 * Dtri.card - Dlow.card) + Dlow.card ≤ N + Dlow.card := by
    calc
      A.card + DS.card + (2 * Dtri.card - Dlow.card) + Dlow.card
          = A.card + 2 * Dtri.card + DS.card := by omega
      _ ≤ N + Dlow.card := hmain
  exact Nat.le_of_add_le_add_right hmain'

/-- **Low-band triangle + S mixed counting with overlap penalty.**

    Let
    `D_low = {d ∈ [1,N/240] : Nat.Coprime d 6}`,
    `D_S = {a ∈ [1,N/6] : VDParam a}`,
    `U_low = ⋃_{d∈D_low} {60d,120d,180d}`,
    `U_S = ⋃_{a∈D_S} {3a,6a}`.

    For pair-free `A ⊆ [1,N]`:

    `A.card + 2*|D_low| + |D_S| ≤ N + |U_low ∩ U_S|`. -/
theorem vd_triangle_s_overlap_penalty_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + 2 * ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card
      + ((Finset.Icc 1 (N / 6)).filter VDParam).card ≤
      N +
      ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
        (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
          (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6) with hDlow
  set DS := (Finset.Icc 1 (N / 6)).filter VDParam with hDS
  let tri : ℕ → Finset ℕ := fun d => {60 * d, 120 * d, 180 * d}
  let spair : ℕ → Finset ℕ := fun a => {3 * a, 6 * a}
  set Ulow := Dlow.biUnion tri with hUlow
  set US := DS.biUnion spair with hUS
  set U := Ulow ∪ US with hU
  have hDlow_mem : ∀ d ∈ Dlow, 0 < d ∧ Nat.Coprime d 6 ∧ 240 * d ≤ N := by
    intro d hd
    simp only [hDlow, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨by omega, hd.2, by omega⟩
  have hDS_mem : ∀ a ∈ DS, 0 < a ∧ VDParam a ∧ 6 * a ≤ N := by
    intro a ha
    simp only [hDS, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have htri_pwd : (↑Dlow : Set ℕ).PairwiseDisjoint tri := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact triangles_disjoint_coprime6 hne
      (hDlow_mem d₁ (Finset.mem_coe.mp hd₁)).2.1
      (hDlow_mem d₂ (Finset.mem_coe.mp hd₂)).2.1
  have htri_card : ∀ d ∈ Dlow, (tri d).card = 3 := by
    intro d hd
    have hdpos : 0 < d := (hDlow_mem d hd).1
    have h60d_pos : 0 < 60 * d := by omega
    simpa [tri, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using triangle_card_eq_three h60d_pos
  have htri_inter : ∀ d ∈ Dlow, ((tri d) ∩ A).card ≤ 1 := by
    intro d hd
    have hdpos : 0 < d := (hDlow_mem d hd).1
    have h60d_pos : 0 < 60 * d := by omega
    have h60div : 60 ∣ 60 * d := ⟨d, by ring⟩
    simpa [tri, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using pair_free_triangle_inter_card_le_one hA h60d_pos h60div
  have hs_pwd : (↑DS : Set ℕ).PairwiseDisjoint spair := by
    intro a₁ ha₁ a₂ ha₂ hne
    exact vd_s_pairs_disjoint
      (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).1
      (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).1
      hne
      (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
      (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).2.1
  have hs_card : ∀ a ∈ DS, (spair a).card = 2 := by
    intro a ha
    exact s_pair_card_eq_two (hDS_mem a ha).1
  have hs_inter : ∀ a ∈ DS, ((spair a) ∩ A).card ≤ 1 := by
    intro a ha
    exact s_pair_inter_card_le_one hA (hDS_mem a ha).1
  have hlowA : (Ulow ∩ A).card ≤ Dlow.card := by
    rw [hUlow]
    have h := PackingBound.card_inter_biUnion_le Dlow tri A 1 htri_pwd htri_inter
    simpa using h
  have hsA : (US ∩ A).card ≤ DS.card := by
    rw [hUS]
    have h := PackingBound.card_inter_biUnion_le DS spair A 1 hs_pwd hs_inter
    simpa using h
  have hUA : (U ∩ A).card ≤ Dlow.card + DS.card := by
    rw [hU, Finset.union_inter_distrib_right]
    calc
      ((Ulow ∩ A) ∪ (US ∩ A)).card ≤ (Ulow ∩ A).card + (US ∩ A).card :=
        Finset.card_union_le _ _
      _ ≤ Dlow.card + DS.card := Nat.add_le_add hlowA hsA
  have hUlow_sub : Ulow ⊆ Finset.Icc 1 N := by
    rw [hUlow]
    refine Finset.biUnion_subset.mpr ?_
    intro d hd
    have hdpos : 0 < d := (hDlow_mem d hd).1
    have hN : 240 * d ≤ N := (hDlow_mem d hd).2.2
    intro x hx
    simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    rcases hx with rfl | rfl | rfl
    · refine ⟨by omega, ?_⟩
      exact le_trans (by nlinarith : 60 * d ≤ 240 * d) hN
    · refine ⟨by omega, ?_⟩
      exact le_trans (by nlinarith : 120 * d ≤ 240 * d) hN
    · refine ⟨by omega, ?_⟩
      exact le_trans (by nlinarith : 180 * d ≤ 240 * d) hN
  have hUS_sub : US ⊆ Finset.Icc 1 N := by
    rw [hUS]
    refine Finset.biUnion_subset.mpr ?_
    intro a ha
    exact s_pair_subset_Icc (hDS_mem a ha).1 (hDS_mem a ha).2.2
  have hU_sub : U ⊆ Finset.Icc 1 N := by
    rw [hU]
    exact Finset.union_subset hUlow_sub hUS_sub
  have hAle : A.card ≤ (U ∩ A).card + (Finset.Icc 1 N \ U).card := by
    calc A.card
        ≤ (U ∩ A ∪ (Finset.Icc 1 N \ U)).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ U
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  have hsdiff : (Finset.Icc 1 N \ U).card + U.card = N := by
    rw [Finset.card_sdiff_add_card_eq_card hU_sub, hIcc]
  have hUlow_card : Ulow.card = 3 * Dlow.card := by
    rw [hUlow]
    exact PackingBound.card_biUnion_const Dlow tri 3 htri_pwd htri_card
  have hUS_card : US.card = 2 * DS.card := by
    rw [hUS]
    exact PackingBound.card_biUnion_const DS spair 2 hs_pwd hs_card
  have hUnionInter :
      U.card +
        (Ulow ∩ US).card = Ulow.card + US.card := by
    rw [hU]
    exact Finset.card_union_add_card_inter Ulow US
  have hInter_def :
      (Ulow ∩ US).card =
      ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
          (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ)))
        ∩
        (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
          (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := by
    simp [Ulow, US, hDlow, hDS, tri, spair]
  omega

/-- **Low-band triangle + S net bound after exact overlap substitution.**

    Using `vd_triangle_s_overlap_penalty_bound` and the exact overlap formula
    `vd_triangle_s_overlap_card_eq_strong`, we get:

    `A.card + |D_S| + |D_low| ≤ N`,

    where
    `D_low = {d ≤ N/240 : gcd(d,6)=1}`,
    `D_S = {a ≤ N/6 : VDParam a}`. -/
theorem vd_triangle_s_net_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter VDParam).card
      + ((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).card ≤ N := by
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6) with hDlow
  set DS := (Finset.Icc 1 (N / 6)).filter VDParam with hDS
  have hpen := vd_triangle_s_overlap_penalty_bound N A hA hAN
  have hover := vd_triangle_s_overlap_card_eq_strong N
  rw [hover] at hpen
  have hpen' : A.card + 2 * Dlow.card + DS.card ≤ N + Dlow.card := by
    simpa [Dlow, DS] using hpen
  have hmain' : A.card + DS.card + Dlow.card + Dlow.card ≤ N + Dlow.card := by
    calc
      A.card + DS.card + Dlow.card + Dlow.card
          = A.card + 2 * Dlow.card + DS.card := by omega
      _ ≤ N + Dlow.card := hpen'
  exact Nat.le_of_add_le_add_right hmain'

/-- For `N ≥ 240`, low-band overlap forces one explicit extra exclusion:
    `A.card + |D_S| + 1 ≤ N`. -/
theorem vd_triangle_s_net_bound_ge_one (N : ℕ) (A : Finset ℕ)
    (hN : 240 ≤ N) (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter VDParam).card + 1 ≤ N := by
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6) with hDlow
  set DS := (Finset.Icc 1 (N / 6)).filter VDParam with hDS
  have hnet := vd_triangle_s_net_bound N A hA hAN
  have hpos : 1 ≤ ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
      (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card := vd_triangle_s_overlap_card_pos N hN
  have hover := vd_triangle_s_overlap_card_eq_strong N
  have hDlow_one : 1 ≤ Dlow.card := by
    rw [hover] at hpos
    simpa [Dlow] using hpos
  have hnet' : A.card + DS.card + Dlow.card ≤ N := by
    simpa [Dlow, DS] using hnet
  omega

/-- For `N ≥ 1200`, low-band overlap forces two explicit exclusions:
    `A.card + |D_S| + 2 ≤ N`. -/
theorem vd_triangle_s_net_bound_ge_two (N : ℕ) (A : Finset ℕ)
    (hN : 1200 ≤ N) (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter VDParam).card + 2 ≤ N := by
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6) with hDlow
  set DS := (Finset.Icc 1 (N / 6)).filter VDParam with hDS
  have hnet := vd_triangle_s_net_bound N A hA hAN
  have hge : 2 ≤ ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
      (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card :=
    vd_triangle_s_overlap_card_ge_two N hN
  have hover := vd_triangle_s_overlap_card_eq_strong N
  have hDlow_two : 2 ≤ Dlow.card := by
    rw [hover] at hge
    simpa [Dlow] using hge
  have hnet' : A.card + DS.card + Dlow.card ≤ N := by
    simpa [Dlow, DS] using hnet
  omega

/-- For `N ≥ 1680`, low-band overlap forces three explicit exclusions:
    `A.card + |D_S| + 3 ≤ N`. -/
theorem vd_triangle_s_net_bound_ge_three (N : ℕ) (A : Finset ℕ)
    (hN : 1680 ≤ N) (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter VDParam).card + 3 ≤ N := by
  set Dlow := (Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6) with hDlow
  set DS := (Finset.Icc 1 (N / 6)).filter VDParam with hDS
  have hnet := vd_triangle_s_net_bound N A hA hAN
  have hge : 3 ≤ ((((Finset.Icc 1 (N / 240)).filter (Nat.Coprime · 6)).biUnion
      (fun d => ({60 * d, 120 * d, 180 * d} : Finset ℕ))) ∩
      (((Finset.Icc 1 (N / 6)).filter VDParam).biUnion
        (fun a => ({3 * a, 6 * a} : Finset ℕ)))).card :=
    vd_triangle_s_overlap_card_ge_three N hN
  have hover := vd_triangle_s_overlap_card_eq_strong N
  have hDlow_three : 3 ≤ Dlow.card := by
    rw [hover] at hge
    simpa [Dlow] using hge
  have hnet' : A.card + DS.card + Dlow.card ≤ N := by
    simpa [Dlow, DS] using hnet
  omega

/-- **Triangle + T net bound after exact overlap substitution.**

    Using `vd_triangle_t_overlap_penalty_bound` and the exact overlap formula
    `vd_triangle_t_overlap_card_eq_strong`, we get:

    `A.card + |D_T| + (|D△| - |D540|) ≤ N`,

    where
    `D△ = {d ≤ N/180 : gcd(d,6)=1}`,
    `D540 = {d ≤ N/540 : gcd(d,6)=1}`,
    `D_T = {a ≤ N/12 : VDParam a}`. -/
theorem vd_triangle_t_net_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 12)).filter VDParam).card +
      (((Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6)).card
        - ((Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6)).card) ≤ N := by
  set Dtri := (Finset.Icc 1 (N / 180)).filter (Nat.Coprime · 6) with hDtri
  set D540 := (Finset.Icc 1 (N / 540)).filter (Nat.Coprime · 6) with hD540
  set DT := (Finset.Icc 1 (N / 12)).filter VDParam with hDT
  have hpen := vd_triangle_t_overlap_penalty_bound N A hA hAN
  have hover := vd_triangle_t_overlap_card_eq_strong N
  rw [hover] at hpen
  have hpen' : A.card + 2 * Dtri.card + DT.card ≤ N + (Dtri.card + D540.card) := by
    simpa [Dtri, D540, DT] using hpen
  have hsub : D540 ⊆ Dtri := by
    intro d hd
    have hd' : d ∈ Finset.Icc 1 (N / 540) ∧ Nat.Coprime d 6 := Finset.mem_filter.mp hd
    have hle : d ≤ N / 180 := by
      have h540 : d * 540 ≤ N :=
        (Nat.le_div_iff_mul_le (by decide : 0 < 540)).mp (Finset.mem_Icc.mp hd'.1).2
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 180)).2 (by nlinarith)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd'.1).1, hle⟩, hd'.2⟩
  have hle_cards : D540.card ≤ Dtri.card := Finset.card_le_card hsub
  have hsub_add : (Dtri.card - D540.card) + D540.card = Dtri.card :=
    Nat.sub_add_cancel hle_cards
  have hmain : A.card + Dtri.card + DT.card ≤ N + D540.card := by
    omega
  have hmain' : A.card + DT.card + (Dtri.card - D540.card) + D540.card ≤ N + D540.card := by
    calc
      A.card + DT.card + (Dtri.card - D540.card) + D540.card
          = A.card + Dtri.card + DT.card := by omega
      _ ≤ N + D540.card := hmain
  exact Nat.le_of_add_le_add_right hmain'

/-! ### Section 8: Capstone counting theorem -/

/-- **Van Doorn's structural bound for pair-free sets.**

    For D_S = {a ∈ [1,N/6] : VDParam a} and D_T = {a ∈ [1,N/12] : VDParam a},
    all S-pairs and T-pairs are pairwise disjoint (within and across families),
    each forcing ≥1 exclusion from a pair-free set A ⊆ {1,…,N}.
    Combined: A.card + |D_S| + |D_T| ≤ N.

    Since the density of VDParam is 3/7 (from Prob(3|v₂) = 4/7, Prob(2|v₃) = 3/4),
    we get |D_S| ≈ 3N/42 = N/14 and |D_T| ≈ 3N/84 = N/28.
    Total: A.card ≤ N − N/14 − N/28 = N − 3N/28 = 25N/28 + o(N). -/
theorem van_doorn_pair_upper_bound (N : ℕ) (A : Finset ℕ)
    (hA : PairFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter VDParam).card
           + ((Finset.Icc 1 (N / 12)).filter VDParam).card ≤ N := by
  set D_S := (Finset.Icc 1 (N / 6)).filter VDParam with hDS_def
  set D_T := (Finset.Icc 1 (N / 12)).filter VDParam with hDT_def
  let s_pair : ℕ → Finset ℕ := fun a => {3*a, 6*a}
  let t_pair : ℕ → Finset ℕ := fun a => {4*a, 12*a}
  -- Properties of D_S and D_T members
  have hDS_mem : ∀ a ∈ D_S, 0 < a ∧ VDParam a ∧ 6 * a ≤ N := by
    intro a ha; simp only [hDS_def, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have hDT_mem : ∀ a ∈ D_T, 0 < a ∧ VDParam a ∧ 12 * a ≤ N := by
    intro a ha; simp only [hDT_def, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  -- Apply the generic two-family packing bound (s=2, r=1 for both)
  have h := PackingBound.two_family_bound N A D_S D_T s_pair t_pair 2 1 2 1
    (by omega) (by omega) hAN
    -- S-family pairwise disjoint
    (fun a₁ ha₁ a₂ ha₂ hne =>
      vd_s_pairs_disjoint (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).1
        (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).1 hne
        (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
        (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).2.1)
    -- S-family cardinality
    (fun a ha => s_pair_card_eq_two (hDS_mem a ha).1)
    -- S-family intersection bound
    (fun a ha => s_pair_inter_card_le_one hA (hDS_mem a ha).1)
    -- S-family ⊆ Icc
    (Finset.biUnion_subset.mpr fun a ha =>
      s_pair_subset_Icc (hDS_mem a ha).1 (hDS_mem a ha).2.2)
    -- T-family pairwise disjoint
    (fun a₁ ha₁ a₂ ha₂ hne =>
      vd_t_pairs_disjoint (hDT_mem a₁ (Finset.mem_coe.mp ha₁)).1
        (hDT_mem a₂ (Finset.mem_coe.mp ha₂)).1 hne
        (hDT_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
        (hDT_mem a₂ (Finset.mem_coe.mp ha₂)).2.1)
    -- T-family cardinality
    (fun a ha => t_pair_card_eq_two (hDT_mem a ha).1)
    -- T-family intersection bound
    (fun a ha => t_pair_inter_card_le_one hA (hDT_mem a ha).1)
    -- T-family ⊆ Icc
    (Finset.biUnion_subset.mpr fun a ha =>
      t_pair_subset_Icc (hDT_mem a ha).1 (hDT_mem a ha).2.2)
    -- Cross-disjointness
    (by
      rw [Finset.disjoint_biUnion_left]
      intro a₁ ha₁; rw [Finset.disjoint_biUnion_right]; intro a₂ ha₂
      exact vd_s_t_cross_disjoint (hDS_mem a₁ ha₁).1 (hDT_mem a₂ ha₂).1
        (hDS_mem a₁ ha₁).2.1 (hDT_mem a₂ ha₂).2.1)
  -- two_family_bound gives A.card + (2-1)*|D_S| + (2-1)*|D_T| ≤ N
  omega

end UnitFractionPairs
