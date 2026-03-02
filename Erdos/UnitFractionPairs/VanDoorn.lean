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

/-! ### Section 6: Finset infrastructure -/

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

/-! ### Section 7: Capstone counting theorem -/

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
