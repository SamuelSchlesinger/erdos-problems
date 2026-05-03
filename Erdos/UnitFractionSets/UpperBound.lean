/-
# Upper Bounds on Sum-Free Sets

This file contains structural upper bounds for Problem 301.

First, since SumFree implies TripleFree (Problem 301 generalizes Problem 302),
every upper bound on triple-free sets immediately gives an upper bound on
sum-free sets. In particular, van Doorn's 9/10 bound transfers:

  f₃₀₁(N) ≤ f₃₀₂(N) ≤ (9/10 + o(1))N.

Second, a dedicated van Doorn gadget for sum-free sets recovers the stronger
known bound

  f₃₀₁(N) ≤ (25/28 + o(1))N.

Third, the extended-star and larger same-signature gadgets give new packing
inequalities with asymptotic shapes

  f₃₀₁(N) ≤ (149/168 + o(1))N.
  f₃₀₁(N) ≤ (145/168 + o(1))N.
-/
import Erdos.UnitFractionSets.Connections
import Erdos.UnitFractionSets.ExtendedStar
import Erdos.UnitFractionPairs.VanDoorn
import Erdos.UnitFractionTriples.VanDoorn
import Erdos.Common.PackingBound
import Erdos.Common.ValSignature

namespace UnitFractionSets

open UnitFractionTriples UnitFractionConnections
open UnitFractionPairs (VDParam)

/-! ### Dedicated van Doorn gadget for Problem 301

The site records Wouter van Doorn's stronger `25/28` upper bound for Problem 301.
Unlike the inherited `9/10` bound below, this uses the five-point gadget

`{2a, 3a, 4a, 6a, 12a}`.

For `a ≤ N/12`, a sum-free set can keep at most three of these five elements:
the triples `{2a,3a,6a}` and `{3a,4a,12a}` are forbidden, and if `3a` is omitted
then the remaining four still contain the length-three identity
`1/(2a)=1/(4a)+1/(6a)+1/(12a)`.

For `N/12 < a ≤ N/6`, the truncated gadget `{2a,3a,4a,6a}` still forces one
omission through `{2a,3a,6a}`. The same `VDParam` p-adic signature used in
Problem 327 makes these gadgets disjoint.
-/

private theorem not_sf_2_3_6 {A : Finset ℕ} (hA : SumFree A) {a : ℕ}
    (ha : 0 < a) (h2 : 2 * a ∈ A) (h3 : 3 * a ∈ A) (h6 : 6 * a ∈ A) : False :=
  triple_free_excludes_one (sumFree_implies_tripleFree hA) ha h2 h3 h6

/-- Helper: a sum-free set cannot contain `{3a,4a,12a}`. -/
private theorem not_sf_3_4_12 {A : Finset ℕ} (hA : SumFree A) {a : ℕ}
    (ha : 0 < a) (h3 : 3 * a ∈ A) (h4 : 4 * a ∈ A) (h12 : 12 * a ∈ A) :
    False := by
  have hS : ({4 * a, 12 * a} : Finset ℕ) ⊆ A.erase (3 * a) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with rfl | rfl <;> exact ⟨by omega, ‹_›⟩
  have hne : ({4 * a, 12 * a} : Finset ℕ).Nonempty := ⟨4 * a, by simp⟩
  have heq : (1 / (3 * a : ℕ) : ℚ) =
      ∑ b ∈ ({4 * a, 12 * a} : Finset ℕ), (1 / b : ℚ) := by
    have h4_not : (4 * a : ℕ) ∉ ({12 * a} : Finset ℕ) := by simp; omega
    rw [show ({4 * a, 12 * a} : Finset ℕ) = insert (4 * a) {12 * a} from rfl]
    rw [Finset.sum_insert h4_not, Finset.sum_singleton]
    push_cast
    have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  exact hA (3 * a) h3 _ hS hne heq

/-- Helper: a sum-free set cannot contain `{2a,4a,6a,12a}`. -/
private theorem not_sf_2_4_6_12 {A : Finset ℕ} (hA : SumFree A) {a : ℕ}
    (ha : 0 < a) (h2 : 2 * a ∈ A) (h4 : 4 * a ∈ A)
    (h6 : 6 * a ∈ A) (h12 : 12 * a ∈ A) : False := by
  have hS : ({4 * a, 6 * a, 12 * a} : Finset ℕ) ⊆ A.erase (2 * a) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by omega, ‹_›⟩
  have hne : ({4 * a, 6 * a, 12 * a} : Finset ℕ).Nonempty := ⟨4 * a, by simp⟩
  have heq : (1 / (2 * a : ℕ) : ℚ) =
      ∑ b ∈ ({4 * a, 6 * a, 12 * a} : Finset ℕ), (1 / b : ℚ) := by
    have h4_not : (4 * a : ℕ) ∉ ({6 * a, 12 * a} : Finset ℕ) := by simp; omega
    have h6_not : (6 * a : ℕ) ∉ ({12 * a} : Finset ℕ) := by simp; omega
    rw [show ({4 * a, 6 * a, 12 * a} : Finset ℕ) =
        insert (4 * a) (insert (6 * a) {12 * a}) from rfl]
    rw [Finset.sum_insert h4_not, Finset.sum_insert h6_not, Finset.sum_singleton]
    push_cast
    have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  exact hA (2 * a) h2 _ hS hne heq

private theorem vd_sum_full_gadget_card_eq_five {a : ℕ} (ha : 0 < a) :
    ({2 * a, 3 * a, 4 * a, 6 * a, 12 * a} : Finset ℕ).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

private theorem vd_sum_short_gadget_card_eq_four {a : ℕ} (ha : 0 < a) :
    ({2 * a, 3 * a, 4 * a, 6 * a} : Finset ℕ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

private theorem vd_sum_short_subset_full (a : ℕ) :
    ({2 * a, 3 * a, 4 * a, 6 * a} : Finset ℕ) ⊆
      ({2 * a, 3 * a, 4 * a, 6 * a, 12 * a} : Finset ℕ) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> simp

private theorem vd_sum_full_gadget_subset_Icc {a N : ℕ} (ha : 0 < a)
    (h12 : 12 * a ≤ N) :
    ({2 * a, 3 * a, 4 * a, 6 * a, 12 * a} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem vd_sum_short_gadget_subset_Icc {a N : ℕ} (ha : 0 < a)
    (h6 : 6 * a ≤ N) :
    ({2 * a, 3 * a, 4 * a, 6 * a} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl | rfl <;> omega

private lemma card_inter_le_of_one_not_mem {S A : Finset ℕ} {x : ℕ}
    (hxS : x ∈ S) (hxA : x ∉ A) :
    (S ∩ A).card + 1 ≤ S.card := by
  have hsub : S ∩ A ⊆ S.erase x := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun h => by subst h; exact hxA (Finset.mem_inter.mp hy).2,
      (Finset.mem_inter.mp hy).1⟩
  calc (S ∩ A).card + 1
      ≤ (S.erase x).card + 1 := Nat.add_le_add_right (Finset.card_le_card hsub) 1
    _ = S.card := by
      have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hxS⟩
      rw [Finset.card_erase_of_mem hxS]
      exact Nat.sub_add_cancel hpos

private lemma card_inter_le_of_two_not_mem {S A : Finset ℕ} {x y : ℕ}
    (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y) (hxA : x ∉ A) (hyA : y ∉ A) :
    (S ∩ A).card + 2 ≤ S.card := by
  have hdisj : Disjoint (S ∩ A) ({x, y} : Finset ℕ) := by
    rw [Finset.disjoint_right]
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [hxA]
    · simp [hyA]
  have hpair : ({x, y} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy])]
    simp
  have hsub : S ∩ A ∪ {x, y} ⊆ S :=
    Finset.union_subset Finset.inter_subset_left (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption)
  calc (S ∩ A).card + 2
      = (S ∩ A).card + ({x, y} : Finset ℕ).card := by rw [hpair]
    _ = (S ∩ A ∪ {x, y}).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ S.card := Finset.card_le_card hsub

/-- A sum-free set keeps at most three elements from `{2a,3a,4a,6a,12a}`. -/
theorem sum_free_inter_vd_sum_full_gadget_le_three {A : Finset ℕ} (hA : SumFree A)
    {a : ℕ} (ha : 0 < a) :
    (({2 * a, 3 * a, 4 * a, 6 * a, 12 * a} : Finset ℕ) ∩ A).card ≤ 3 := by
  set G := ({2 * a, 3 * a, 4 * a, 6 * a, 12 * a} : Finset ℕ) with hG
  have hGcard : G.card = 5 := by simpa [hG] using vd_sum_full_gadget_card_eq_five ha
  suffices ∃ x y, x ∈ G ∧ y ∈ G ∧ x ≠ y ∧ x ∉ A ∧ y ∉ A by
    obtain ⟨x, y, hxG, hyG, hxy, hxA, hyA⟩ := this
    have h := card_inter_le_of_two_not_mem hxG hyG hxy hxA hyA
    omega
  by_cases h3 : 3 * a ∈ A
  · have h26 : ∃ x, (x = 2 * a ∨ x = 6 * a) ∧ x ∉ A := by
      by_cases h2 : 2 * a ∈ A
      · have h6 : 6 * a ∉ A := fun h6 => not_sf_2_3_6 hA ha h2 h3 h6
        exact ⟨6 * a, Or.inr rfl, h6⟩
      · exact ⟨2 * a, Or.inl rfl, h2⟩
    have h412 : ∃ y, (y = 4 * a ∨ y = 12 * a) ∧ y ∉ A := by
      by_cases h4 : 4 * a ∈ A
      · have h12 : 12 * a ∉ A := fun h12 => not_sf_3_4_12 hA ha h3 h4 h12
        exact ⟨12 * a, Or.inr rfl, h12⟩
      · exact ⟨4 * a, Or.inl rfl, h4⟩
    obtain ⟨x, hx, hxA⟩ := h26
    obtain ⟨y, hy, hyA⟩ := h412
    refine ⟨x, y, ?_, ?_, ?_, hxA, hyA⟩
    · rcases hx with rfl | rfl <;> simp [hG]
    · rcases hy with rfl | rfl <;> simp [hG]
    · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
  · have hrest : ∃ y, (y = 2 * a ∨ y = 4 * a ∨ y = 6 * a ∨ y = 12 * a) ∧ y ∉ A := by
      by_cases h2 : 2 * a ∈ A
      · by_cases h4 : 4 * a ∈ A
        · by_cases h6 : 6 * a ∈ A
          · by_cases h12 : 12 * a ∈ A
            · exact (not_sf_2_4_6_12 hA ha h2 h4 h6 h12).elim
            · exact ⟨12 * a, Or.inr (Or.inr (Or.inr rfl)), h12⟩
          · exact ⟨6 * a, Or.inr (Or.inr (Or.inl rfl)), h6⟩
        · exact ⟨4 * a, Or.inr (Or.inl rfl), h4⟩
      · exact ⟨2 * a, Or.inl rfl, h2⟩
    obtain ⟨y, hy, hyA⟩ := hrest
    refine ⟨3 * a, y, by simp [hG], ?_, ?_, h3, hyA⟩
    · rcases hy with rfl | rfl | rfl | rfl <;> simp [hG]
    · rcases hy with rfl | rfl | rfl | rfl <;> omega

/-- A sum-free set keeps at most three elements from the truncated gadget
`{2a,3a,4a,6a}`. -/
theorem sum_free_inter_vd_sum_short_gadget_le_three {A : Finset ℕ} (hA : SumFree A)
    {a : ℕ} (ha : 0 < a) :
    (({2 * a, 3 * a, 4 * a, 6 * a} : Finset ℕ) ∩ A).card ≤ 3 := by
  set G := ({2 * a, 3 * a, 4 * a, 6 * a} : Finset ℕ) with hG
  have hGcard : G.card = 4 := by simpa [hG] using vd_sum_short_gadget_card_eq_four ha
  suffices ∃ x, x ∈ G ∧ x ∉ A by
    obtain ⟨x, hxG, hxA⟩ := this
    have h := card_inter_le_of_one_not_mem hxG hxA
    omega
  by_cases h2 : 2 * a ∈ A
  · by_cases h3 : 3 * a ∈ A
    · by_cases h6 : 6 * a ∈ A
      · exact (not_sf_2_3_6 hA ha h2 h3 h6).elim
      · exact ⟨6 * a, by simp [hG], h6⟩
    · exact ⟨3 * a, by simp [hG], h3⟩
  · exact ⟨2 * a, by simp [hG], h2⟩

/-! ### P-adic disjointness of the `VDParam` five-point gadgets -/

private theorem vd_v2_mod3_two {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 2 (2 * a) % 3 = 1 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_2]
  obtain ⟨k, hk⟩ := hv.1
  rw [hk]
  omega

private theorem vd_v2_mod3_three {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 2 (3 * a) % 3 = 0 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_3, zero_add]
  exact Nat.dvd_iff_mod_eq_zero.mp hv.1

private theorem vd_v2_mod3_four {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 2 (4 * a) % 3 = 2 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_4]
  obtain ⟨k, hk⟩ := hv.1
  rw [hk]
  omega

private theorem vd_v2_mod3_six {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 2 (6 * a) % 3 = 1 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_6]
  obtain ⟨k, hk⟩ := hv.1
  rw [hk]
  omega

private theorem vd_v2_mod3_twelve {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 2 (12 * a) % 3 = 2 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v2_12]
  obtain ⟨k, hk⟩ := hv.1
  rw [hk]
  omega

private theorem vd_v3_mod2_two {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 3 (2 * a) % 2 = 0 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v3_2, zero_add]
  exact Nat.even_iff.mp hv.2

private theorem vd_v3_mod2_three {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 3 (3 * a) % 2 = 1 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v3_3]
  obtain ⟨k, hk⟩ := hv.2
  rw [hk]
  omega

private theorem vd_v3_mod2_four {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 3 (4 * a) % 2 = 0 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v3_4, zero_add]
  exact Nat.even_iff.mp hv.2

private theorem vd_v3_mod2_six {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 3 (6 * a) % 2 = 1 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v3_6]
  obtain ⟨k, hk⟩ := hv.2
  rw [hk]
  omega

private theorem vd_v3_mod2_twelve {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    padicValNat 3 (12 * a) % 2 = 1 := by
  rw [padicValNat.mul (by decide) ha, ValSignature.v3_12]
  obtain ⟨k, hk⟩ := hv.2
  rw [hk]
  omega

private def vdSig (n : ℕ) : ℕ × ℕ :=
  (padicValNat 2 n % 3, padicValNat 3 n % 2)

private theorem vdSig_two {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    vdSig (2 * a) = (1, 0) := by
  simp [vdSig, vd_v2_mod3_two ha hv, vd_v3_mod2_two ha hv]

private theorem vdSig_three {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    vdSig (3 * a) = (0, 1) := by
  simp [vdSig, vd_v2_mod3_three ha hv, vd_v3_mod2_three ha hv]

private theorem vdSig_four {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    vdSig (4 * a) = (2, 0) := by
  simp [vdSig, vd_v2_mod3_four ha hv, vd_v3_mod2_four ha hv]

private theorem vdSig_six {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    vdSig (6 * a) = (1, 1) := by
  simp [vdSig, vd_v2_mod3_six ha hv, vd_v3_mod2_six ha hv]

private theorem vdSig_twelve {a : ℕ} (ha : a ≠ 0) (hv : VDParam a) :
    vdSig (12 * a) = (2, 1) := by
  simp [vdSig, vd_v2_mod3_twelve ha hv, vd_v3_mod2_twelve ha hv]

set_option linter.unusedSimpArgs false in
theorem vd_sum_full_gadgets_disjoint {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hne : a₁ ≠ a₂) (hv₁ : VDParam a₁) (hv₂ : VDParam a₂) :
    Disjoint ({2 * a₁, 3 * a₁, 4 * a₁, 6 * a₁, 12 * a₁} : Finset ℕ)
      ({2 * a₂, 3 * a₂, 4 * a₂, 6 * a₂, 12 * a₂} : Finset ℕ) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  have ha₁' : a₁ ≠ 0 := by omega
  have ha₂' : a₂ ≠ 0 := by omega
  rcases hx₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hx₂ with h | h | h | h | h
  all_goals
    first
    | exact hne (by omega)
    | have hsig := congrArg vdSig h
      simp [vdSig_two ha₁' hv₁, vdSig_three ha₁' hv₁, vdSig_four ha₁' hv₁,
        vdSig_six ha₁' hv₁, vdSig_twelve ha₁' hv₁, vdSig_two ha₂' hv₂,
        vdSig_three ha₂' hv₂, vdSig_four ha₂' hv₂, vdSig_six ha₂' hv₂,
        vdSig_twelve ha₂' hv₂] at hsig

theorem sum_free_van_doorn_25_28_bound (N : ℕ) (A : Finset ℕ)
    (hA : SumFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + 2 * ((Finset.Icc 1 (N / 12)).filter VDParam).card
      + ((Finset.Icc (N / 12 + 1) (N / 6)).filter VDParam).card ≤ N := by
  set D_full := (Finset.Icc 1 (N / 12)).filter VDParam with hDfull
  set D_short := (Finset.Icc (N / 12 + 1) (N / 6)).filter VDParam with hDshort
  let full : ℕ → Finset ℕ := fun a => {2 * a, 3 * a, 4 * a, 6 * a, 12 * a}
  let short : ℕ → Finset ℕ := fun a => {2 * a, 3 * a, 4 * a, 6 * a}
  have hfull_mem : ∀ a ∈ D_full, 0 < a ∧ VDParam a ∧ 12 * a ≤ N := by
    intro a ha
    simp only [hDfull, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have hshort_mem : ∀ a ∈ D_short, 0 < a ∧ VDParam a ∧ 6 * a ≤ N := by
    intro a ha
    simp only [hDshort, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have h := PackingBound.two_family_bound N A D_full D_short full short 5 3 4 3
    (by omega) (by omega) hAN
    (fun a₁ ha₁ a₂ ha₂ hne =>
      vd_sum_full_gadgets_disjoint (hfull_mem a₁ (Finset.mem_coe.mp ha₁)).1
        (hfull_mem a₂ (Finset.mem_coe.mp ha₂)).1 hne
        (hfull_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
        (hfull_mem a₂ (Finset.mem_coe.mp ha₂)).2.1)
    (fun a ha => vd_sum_full_gadget_card_eq_five (hfull_mem a ha).1)
    (fun a ha => sum_free_inter_vd_sum_full_gadget_le_three hA (hfull_mem a ha).1)
    (Finset.biUnion_subset.mpr fun a ha =>
      vd_sum_full_gadget_subset_Icc (hfull_mem a ha).1 (hfull_mem a ha).2.2)
    (fun a₁ ha₁ a₂ ha₂ hne =>
      (vd_sum_full_gadgets_disjoint (hshort_mem a₁ (Finset.mem_coe.mp ha₁)).1
        (hshort_mem a₂ (Finset.mem_coe.mp ha₂)).1 hne
        (hshort_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
        (hshort_mem a₂ (Finset.mem_coe.mp ha₂)).2.1).mono
          (vd_sum_short_subset_full a₁) (vd_sum_short_subset_full a₂))
    (fun a ha => vd_sum_short_gadget_card_eq_four (hshort_mem a ha).1)
    (fun a ha => sum_free_inter_vd_sum_short_gadget_le_three hA (hshort_mem a ha).1)
    (Finset.biUnion_subset.mpr fun a ha =>
      vd_sum_short_gadget_subset_Icc (hshort_mem a ha).1 (hshort_mem a ha).2.2)
    (by
      rw [Finset.disjoint_biUnion_left]
      intro a₁ ha₁
      rw [Finset.disjoint_biUnion_right]
      intro a₂ ha₂
      have ha₁_mem := hfull_mem a₁ ha₁
      have ha₂_mem := hshort_mem a₂ ha₂
      have hne : a₁ ≠ a₂ := by
        intro hEq
        subst hEq
        simp only [hDfull, Finset.mem_filter, Finset.mem_Icc] at ha₁
        simp only [hDshort, Finset.mem_filter, Finset.mem_Icc] at ha₂
        omega
      exact (vd_sum_full_gadgets_disjoint ha₁_mem.1 ha₂_mem.1 hne ha₁_mem.2.1
        ha₂_mem.2.1).mono (by intro x hx; exact hx) (vd_sum_short_subset_full a₂))
  simpa using h

/-! ### Extended-star improvement over `25/28`

The seven-point extended star from `ExtendedStar.lean` has a stronger local
deficit: a sum-free set keeps at most four of
`{2a,3a,4a,6a,10a,12a,15a}`. The extra multipliers require one more signature
coordinate, so we index by the densest class

`v₂(a) ≡ 0 (mod 3)`, `v₃(a) ≡ 0 (mod 2)`, `v₅(a) ≡ 0 (mod 2)`.

Using the full star for `a ≤ N/15` and the useful truncations up to
`12a`, `10a`, and `6a` gives the finite packing inequality below. The weighted
asymptotic density of the four parameter bands is `19/168`, so this is the
structural source of a `149/168 + o(1)` upper bound.
-/

/-- Extended-star parameter class: the densest signature class that separates
the multipliers `{2,3,4,6,10,12,15}`. -/
def ExtParam (a : ℕ) : Prop :=
  3 ∣ padicValNat 2 a ∧ Even (padicValNat 3 a) ∧ Even (padicValNat 5 a)

instance : DecidablePred ExtParam := fun a =>
  inferInstanceAs
    (Decidable (3 ∣ padicValNat 2 a ∧ Even (padicValNat 3 a) ∧
      Even (padicValNat 5 a)))

private def extSum15 (a : ℕ) : Finset ℕ :=
  {2 * a, 3 * a, 4 * a, 6 * a, 10 * a, 12 * a, 15 * a}

private def extSum12 (a : ℕ) : Finset ℕ :=
  {2 * a, 3 * a, 4 * a, 6 * a, 10 * a, 12 * a}

private def extSum10 (a : ℕ) : Finset ℕ :=
  {2 * a, 3 * a, 4 * a, 6 * a, 10 * a}

private def extSum6 (a : ℕ) : Finset ℕ :=
  {2 * a, 3 * a, 4 * a, 6 * a}

private theorem ext_v2_10 : padicValNat 2 10 = 1 := by
  have h : padicValNat 2 (2 * 5) = padicValNat 2 2 + padicValNat 2 5 :=
    padicValNat.mul (by decide) (by decide)
  simpa [ValSignature.v2_2, ValSignature.v2_5] using h

private theorem ext_v3_10 : padicValNat 3 10 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

private theorem ext_v5_2 : padicValNat 5 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
private theorem ext_v5_3 : padicValNat 5 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)

private theorem ext_v5_6 : padicValNat 5 6 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

private theorem ext_v5_10 : padicValNat 5 10 = 1 := by
  have h : padicValNat 5 (2 * 5) = padicValNat 5 2 + padicValNat 5 5 :=
    padicValNat.mul (by decide) (by decide)
  simpa [ext_v5_2, ValSignature.v5_5] using h

private def extSig (n : ℕ) : ℕ × ℕ × ℕ :=
  (padicValNat 2 n % 3, padicValNat 3 n % 2, padicValNat 5 n % 2)

private theorem extSig_of_vals {c a v₂ v₃ v₅ : ℕ} (hc : c ≠ 0) (ha : a ≠ 0)
    (h₂ : padicValNat 2 c = v₂) (h₃ : padicValNat 3 c = v₃)
    (h₅ : padicValNat 5 c = v₅) (hv : ExtParam a) :
    extSig (c * a) = (v₂ % 3, v₃ % 2, v₅ % 2) := by
  have h2mod : padicValNat 2 (c * a) % 3 = v₂ % 3 := by
    rw [padicValNat.mul hc ha, h₂]
    obtain ⟨k, hk⟩ := hv.1
    rw [hk]
    omega
  have h3mod : padicValNat 3 (c * a) % 2 = v₃ % 2 := by
    rw [padicValNat.mul hc ha, h₃]
    obtain ⟨k, hk⟩ := hv.2.1
    rw [hk]
    omega
  have h5mod : padicValNat 5 (c * a) % 2 = v₅ % 2 := by
    rw [padicValNat.mul hc ha, h₅]
    obtain ⟨k, hk⟩ := hv.2.2
    rw [hk]
    omega
  simp [extSig, h2mod, h3mod, h5mod]

private theorem extSig_two {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (2 * a) = (1, 0, 0) := by
  have h := extSig_of_vals (c := 2) (a := a) (v₂ := 1) (v₃ := 0) (v₅ := 0)
    (by decide) ha ValSignature.v2_2 ValSignature.v3_2 ext_v5_2 hv
  simpa using h

private theorem extSig_three {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (3 * a) = (0, 1, 0) := by
  have h := extSig_of_vals (c := 3) (a := a) (v₂ := 0) (v₃ := 1) (v₅ := 0)
    (by decide) ha ValSignature.v2_3 ValSignature.v3_3 ext_v5_3 hv
  simpa using h

private theorem extSig_four {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (4 * a) = (2, 0, 0) := by
  have h := extSig_of_vals (c := 4) (a := a) (v₂ := 2) (v₃ := 0) (v₅ := 0)
    (by decide) ha ValSignature.v2_4 ValSignature.v3_4 ValSignature.v5_4 hv
  simpa using h

private theorem extSig_six {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (6 * a) = (1, 1, 0) := by
  have h := extSig_of_vals (c := 6) (a := a) (v₂ := 1) (v₃ := 1) (v₅ := 0)
    (by decide) ha ValSignature.v2_6 ValSignature.v3_6 ext_v5_6 hv
  simpa using h

private theorem extSig_ten {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (10 * a) = (1, 0, 1) := by
  have h := extSig_of_vals (c := 10) (a := a) (v₂ := 1) (v₃ := 0) (v₅ := 1)
    (by decide) ha ext_v2_10 ext_v3_10 ext_v5_10 hv
  simpa using h

private theorem extSig_twelve {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (12 * a) = (2, 1, 0) := by
  have h := extSig_of_vals (c := 12) (a := a) (v₂ := 2) (v₃ := 1) (v₅ := 0)
    (by decide) ha ValSignature.v2_12 ValSignature.v3_12 ValSignature.v5_12 hv
  simpa using h

private theorem extSig_fifteen {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (15 * a) = (0, 1, 1) := by
  have h := extSig_of_vals (c := 15) (a := a) (v₂ := 0) (v₃ := 1) (v₅ := 1)
    (by decide) ha ValSignature.v2_15 ValSignature.v3_15 ValSignature.v5_15 hv
  simpa using h

private theorem extSig_five {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (5 * a) = (0, 0, 1) := by
  have h := extSig_of_vals (c := 5) (a := a) (v₂ := 0) (v₃ := 0) (v₅ := 1)
    (by decide) ha ValSignature.v2_5 ValSignature.v3_5 ValSignature.v5_5 hv
  simpa using h

private theorem extSig_twenty {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (20 * a) = (2, 0, 1) := by
  have h := extSig_of_vals (c := 20) (a := a) (v₂ := 2) (v₃ := 0) (v₅ := 1)
    (by decide) ha ValSignature.v2_20 ValSignature.v3_20 ValSignature.v5_20 hv
  simpa using h

private theorem ext_v2_30 : padicValNat 2 30 = 1 := by
  have h : padicValNat 2 (2 * 15) = padicValNat 2 2 + padicValNat 2 15 :=
    padicValNat.mul (by decide) (by decide)
  simpa [ValSignature.v2_2, ValSignature.v2_15] using h

private theorem ext_v3_30 : padicValNat 3 30 = 1 := by
  have h : padicValNat 3 (3 * 10) = padicValNat 3 3 + padicValNat 3 10 :=
    padicValNat.mul (by decide) (by decide)
  simpa [ValSignature.v3_3, ext_v3_10] using h

private theorem ext_v5_30 : padicValNat 5 30 = 1 := by
  have h : padicValNat 5 (6 * 5) = padicValNat 5 6 + padicValNat 5 5 :=
    padicValNat.mul (by decide) (by decide)
  simpa [ext_v5_6, ValSignature.v5_5] using h

private theorem extSig_thirty {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (30 * a) = (1, 1, 1) := by
  have h := extSig_of_vals (c := 30) (a := a) (v₂ := 1) (v₃ := 1) (v₅ := 1)
    (by decide) ha ext_v2_30 ext_v3_30 ext_v5_30 hv
  simpa using h

private theorem extSig_sixty {a : ℕ} (ha : a ≠ 0) (hv : ExtParam a) :
    extSig (60 * a) = (2, 1, 1) := by
  have h := extSig_of_vals (c := 60) (a := a) (v₂ := 2) (v₃ := 1) (v₅ := 1)
    (by decide) ha ValSignature.v2_60 ValSignature.v3_60 ValSignature.v5_60 hv
  simpa using h

set_option linter.unusedSimpArgs false in
theorem ext_sum_full_gadgets_disjoint {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hne : a₁ ≠ a₂) (hv₁ : ExtParam a₁) (hv₂ : ExtParam a₂) :
    Disjoint (extSum15 a₁) (extSum15 a₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [extSum15, Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  have ha₁' : a₁ ≠ 0 := by omega
  have ha₂' : a₂ ≠ 0 := by omega
  rcases hx₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hx₂ with h | h | h | h | h | h | h
  all_goals
    first
    | exact hne (by omega)
    | have hsig := congrArg extSig h
      simp [extSig_two ha₁' hv₁, extSig_three ha₁' hv₁, extSig_four ha₁' hv₁,
        extSig_six ha₁' hv₁, extSig_ten ha₁' hv₁, extSig_twelve ha₁' hv₁,
        extSig_fifteen ha₁' hv₁, extSig_two ha₂' hv₂, extSig_three ha₂' hv₂,
        extSig_four ha₂' hv₂, extSig_six ha₂' hv₂, extSig_ten ha₂' hv₂,
        extSig_twelve ha₂' hv₂, extSig_fifteen ha₂' hv₂] at hsig

private theorem extSum15_card_eq_seven {a : ℕ} (ha : 0 < a) :
    (extSum15 a).card = 7 := by
  simpa [extSum15] using extended_star_card_eq_seven ha

private theorem extSum12_card_eq_six {a : ℕ} (ha : 0 < a) :
    (extSum12 a).card = 6 := by
  rw [show extSum12 a = ({2 * a, 3 * a, 4 * a, 6 * a, 10 * a, 12 * a} :
    Finset ℕ) from rfl]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

private theorem extSum10_card_eq_five {a : ℕ} (ha : 0 < a) :
    (extSum10 a).card = 5 := by
  rw [show extSum10 a = ({2 * a, 3 * a, 4 * a, 6 * a, 10 * a} : Finset ℕ) from rfl]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

private theorem extSum6_card_eq_four {a : ℕ} (ha : 0 < a) :
    (extSum6 a).card = 4 := by
  simpa [extSum6] using vd_sum_short_gadget_card_eq_four ha

private theorem extSum12_subset_15 (a : ℕ) : extSum12 a ⊆ extSum15 a := by
  intro x hx
  simp only [extSum12, extSum15, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem extSum10_subset_15 (a : ℕ) : extSum10 a ⊆ extSum15 a := by
  intro x hx
  simp only [extSum10, extSum15, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem extSum6_subset_15 (a : ℕ) : extSum6 a ⊆ extSum15 a := by
  intro x hx
  simp only [extSum6, extSum15, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> simp

private theorem extSum15_subset_Icc {a N : ℕ} (ha : 0 < a) (h15 : 15 * a ≤ N) :
    extSum15 a ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [extSum15, Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem extSum12_subset_Icc {a N : ℕ} (ha : 0 < a) (h12 : 12 * a ≤ N) :
    extSum12 a ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [extSum12, Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem extSum10_subset_Icc {a N : ℕ} (ha : 0 < a) (h10 : 10 * a ≤ N) :
    extSum10 a ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [extSum10, Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem extSum6_subset_Icc {a N : ℕ} (ha : 0 < a) (h6 : 6 * a ≤ N) :
    extSum6 a ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [extSum6, Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl | rfl <;> omega

theorem sum_free_inter_extSum15_le_four {A : Finset ℕ} (hA : SumFree A)
    {a : ℕ} (ha : 0 < a) :
    (extSum15 a ∩ A).card ≤ 4 := by
  simpa [extSum15] using sum_free_inter_extended_star_le_four hA ha

theorem sum_free_inter_extSum12_le_four {A : Finset ℕ} (hA : SumFree A)
    {a : ℕ} (ha : 0 < a) :
    (extSum12 a ∩ A).card ≤ 4 := by
  calc
    (extSum12 a ∩ A).card ≤ (extSum15 a ∩ A).card :=
      Finset.card_le_card (by
        intro x hx
        exact Finset.mem_inter.mpr
          ⟨extSum12_subset_15 a (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)
    _ ≤ 4 := sum_free_inter_extSum15_le_four hA ha

theorem sum_free_inter_extSum10_le_four {A : Finset ℕ} (hA : SumFree A)
    {a : ℕ} (ha : 0 < a) :
    (extSum10 a ∩ A).card ≤ 4 := by
  calc
    (extSum10 a ∩ A).card ≤ (extSum15 a ∩ A).card :=
      Finset.card_le_card (by
        intro x hx
        exact Finset.mem_inter.mpr
          ⟨extSum10_subset_15 a (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)
    _ ≤ 4 := sum_free_inter_extSum15_le_four hA ha

theorem sum_free_inter_extSum6_le_three {A : Finset ℕ} (hA : SumFree A)
    {a : ℕ} (ha : 0 < a) :
    (extSum6 a ∩ A).card ≤ 3 := by
  simpa [extSum6] using sum_free_inter_vd_sum_short_gadget_le_three hA ha

private theorem ext_sum_family_pairwise_disjoint {D : Finset ℕ} {gadget : ℕ → Finset ℕ}
    (hmem : ∀ a ∈ D, 0 < a ∧ ExtParam a) (hsub : ∀ a, gadget a ⊆ extSum15 a) :
    (↑D : Set ℕ).PairwiseDisjoint gadget := by
  intro a₁ ha₁ a₂ ha₂ hne
  exact (ext_sum_full_gadgets_disjoint (hmem a₁ (Finset.mem_coe.mp ha₁)).1
    (hmem a₂ (Finset.mem_coe.mp ha₂)).1 hne
    (hmem a₁ (Finset.mem_coe.mp ha₁)).2
    (hmem a₂ (Finset.mem_coe.mp ha₂)).2).mono (hsub a₁) (hsub a₂)

private theorem ext_sum_family_cross_disjoint {D₁ D₂ : Finset ℕ}
    {gadget₁ gadget₂ : ℕ → Finset ℕ}
    (hmem₁ : ∀ a ∈ D₁, 0 < a ∧ ExtParam a)
    (hmem₂ : ∀ a ∈ D₂, 0 < a ∧ ExtParam a)
    (hne : ∀ a₁ ∈ D₁, ∀ a₂ ∈ D₂, a₁ ≠ a₂)
    (hsub₁ : ∀ a, gadget₁ a ⊆ extSum15 a)
    (hsub₂ : ∀ a, gadget₂ a ⊆ extSum15 a) :
    Disjoint (D₁.biUnion gadget₁) (D₂.biUnion gadget₂) := by
  rw [Finset.disjoint_biUnion_left]
  intro a₁ ha₁
  rw [Finset.disjoint_biUnion_right]
  intro a₂ ha₂
  exact (ext_sum_full_gadgets_disjoint (hmem₁ a₁ ha₁).1 (hmem₂ a₂ ha₂).1
    (hne a₁ ha₁ a₂ ha₂) (hmem₁ a₁ ha₁).2 (hmem₂ a₂ ha₂).2).mono
      (hsub₁ a₁) (hsub₂ a₂)

/-- Four-band extended-star packing. Asymptotically, the `ExtParam` class has
density `5/14`, and the four weighted bands contribute `19/168` forced
omissions. This is the finite Lean statement behind the improved
`149/168 + o(1)` bound. -/
theorem sum_free_extended_star_149_168_bound (N : ℕ) (A : Finset ℕ)
    (hA : SumFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + 3 * ((Finset.Icc 1 (N / 15)).filter ExtParam).card
      + 2 * ((Finset.Icc (N / 15 + 1) (N / 12)).filter ExtParam).card
      + ((Finset.Icc (N / 12 + 1) (N / 10)).filter ExtParam).card
      + ((Finset.Icc (N / 10 + 1) (N / 6)).filter ExtParam).card ≤ N := by
  set D15 := (Finset.Icc 1 (N / 15)).filter ExtParam with hD15
  set D12 := (Finset.Icc (N / 15 + 1) (N / 12)).filter ExtParam with hD12
  set D10 := (Finset.Icc (N / 12 + 1) (N / 10)).filter ExtParam with hD10
  set D6 := (Finset.Icc (N / 10 + 1) (N / 6)).filter ExtParam with hD6
  have h15_mem : ∀ a ∈ D15, 0 < a ∧ ExtParam a ∧ 15 * a ≤ N := by
    intro a ha
    simp only [hD15, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have h12_mem : ∀ a ∈ D12, 0 < a ∧ ExtParam a ∧ 12 * a ≤ N := by
    intro a ha
    simp only [hD12, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have h10_mem : ∀ a ∈ D10, 0 < a ∧ ExtParam a ∧ 10 * a ≤ N := by
    intro a ha
    simp only [hD10, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have h6_mem : ∀ a ∈ D6, 0 < a ∧ ExtParam a ∧ 6 * a ≤ N := by
    intro a ha
    simp only [hD6, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have h15_mem' : ∀ a ∈ D15, 0 < a ∧ ExtParam a := fun a ha =>
    ⟨(h15_mem a ha).1, (h15_mem a ha).2.1⟩
  have h12_mem' : ∀ a ∈ D12, 0 < a ∧ ExtParam a := fun a ha =>
    ⟨(h12_mem a ha).1, (h12_mem a ha).2.1⟩
  have h10_mem' : ∀ a ∈ D10, 0 < a ∧ ExtParam a := fun a ha =>
    ⟨(h10_mem a ha).1, (h10_mem a ha).2.1⟩
  have h6_mem' : ∀ a ∈ D6, 0 < a ∧ ExtParam a := fun a ha =>
    ⟨(h6_mem a ha).1, (h6_mem a ha).2.1⟩
  have hne15_12 : ∀ a₁ ∈ D15, ∀ a₂ ∈ D12, a₁ ≠ a₂ := by
    intro a₁ ha₁ a₂ ha₂ hEq
    subst hEq
    simp only [hD15, hD12, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
    omega
  have hne15_10 : ∀ a₁ ∈ D15, ∀ a₂ ∈ D10, a₁ ≠ a₂ := by
    intro a₁ ha₁ a₂ ha₂ hEq
    subst hEq
    simp only [hD15, hD10, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
    omega
  have hne15_6 : ∀ a₁ ∈ D15, ∀ a₂ ∈ D6, a₁ ≠ a₂ := by
    intro a₁ ha₁ a₂ ha₂ hEq
    subst hEq
    simp only [hD15, hD6, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
    omega
  have hne12_10 : ∀ a₁ ∈ D12, ∀ a₂ ∈ D10, a₁ ≠ a₂ := by
    intro a₁ ha₁ a₂ ha₂ hEq
    subst hEq
    simp only [hD12, hD10, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
    omega
  have hne12_6 : ∀ a₁ ∈ D12, ∀ a₂ ∈ D6, a₁ ≠ a₂ := by
    intro a₁ ha₁ a₂ ha₂ hEq
    subst hEq
    simp only [hD12, hD6, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
    omega
  have hne10_6 : ∀ a₁ ∈ D10, ∀ a₂ ∈ D6, a₁ ≠ a₂ := by
    intro a₁ ha₁ a₂ ha₂ hEq
    subst hEq
    simp only [hD10, hD6, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
    omega
  have h := PackingBound.four_family_bound N A D15 D12 D10 D6 extSum15 extSum12
    extSum10 extSum6 7 4 6 4 5 4 4 3
    (by omega) (by omega) (by omega) (by omega) hAN
    (ext_sum_family_pairwise_disjoint h15_mem' fun _ => fun _ hx => hx)
    (fun a ha => extSum15_card_eq_seven (h15_mem a ha).1)
    (fun a ha => sum_free_inter_extSum15_le_four hA (h15_mem a ha).1)
    (Finset.biUnion_subset.mpr fun a ha =>
      extSum15_subset_Icc (h15_mem a ha).1 (h15_mem a ha).2.2)
    (ext_sum_family_pairwise_disjoint h12_mem' extSum12_subset_15)
    (fun a ha => extSum12_card_eq_six (h12_mem a ha).1)
    (fun a ha => sum_free_inter_extSum12_le_four hA (h12_mem a ha).1)
    (Finset.biUnion_subset.mpr fun a ha =>
      extSum12_subset_Icc (h12_mem a ha).1 (h12_mem a ha).2.2)
    (ext_sum_family_pairwise_disjoint h10_mem' extSum10_subset_15)
    (fun a ha => extSum10_card_eq_five (h10_mem a ha).1)
    (fun a ha => sum_free_inter_extSum10_le_four hA (h10_mem a ha).1)
    (Finset.biUnion_subset.mpr fun a ha =>
      extSum10_subset_Icc (h10_mem a ha).1 (h10_mem a ha).2.2)
    (ext_sum_family_pairwise_disjoint h6_mem' extSum6_subset_15)
    (fun a ha => extSum6_card_eq_four (h6_mem a ha).1)
    (fun a ha => sum_free_inter_extSum6_le_three hA (h6_mem a ha).1)
    (Finset.biUnion_subset.mpr fun a ha =>
      extSum6_subset_Icc (h6_mem a ha).1 (h6_mem a ha).2.2)
    (ext_sum_family_cross_disjoint h15_mem' h12_mem' hne15_12
      (fun _ => fun _ hx => hx) extSum12_subset_15)
    (ext_sum_family_cross_disjoint h15_mem' h10_mem' hne15_10
      (fun _ => fun _ hx => hx) extSum10_subset_15)
    (ext_sum_family_cross_disjoint h15_mem' h6_mem' hne15_6
      (fun _ => fun _ hx => hx) extSum6_subset_15)
    (ext_sum_family_cross_disjoint h12_mem' h10_mem' hne12_10
      extSum12_subset_15 extSum10_subset_15)
    (ext_sum_family_cross_disjoint h12_mem' h6_mem' hne12_6
      extSum12_subset_15 extSum6_subset_15)
    (ext_sum_family_cross_disjoint h10_mem' h6_mem' hne10_6
      extSum10_subset_15 extSum6_subset_15)
  simpa [hD15, hD12, hD10, hD6] using h

/-! ### Larger same-signature gadget

The larger multiplier gadget

`{2,3,4,5,6,10,12,15,20,30,60}·a`

uses the same `ExtParam` signature as the extended star. A fixed finite
certificate over the eleven multipliers shows that the useful prefixes force
omissions

`1,1,2,3,4,4,5`

at cutoffs `6,10,12,15,20,30,60`, respectively. Since `ExtParam` has density
`5/14`, the weighted deficit is `23/168`, giving the finite packing theorem
behind an asymptotic `145/168 + o(1)` upper bound. -/

-- TODO: Revisit the healthier band jump inside the same `{2,3,5}` signature
-- class. The current proof spends its largest cutoff at `60`; a cleaner
-- intermediate jump may recover more local obstruction before changing
-- signature moduli.

private def largeMul (i : Fin 11) : ℕ :=
  ![2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60] i

private abbrev idx2 : Fin 11 := ⟨0, by decide⟩
private abbrev idx3 : Fin 11 := ⟨1, by decide⟩
private abbrev idx4 : Fin 11 := ⟨2, by decide⟩
private abbrev idx5 : Fin 11 := ⟨3, by decide⟩
private abbrev idx6 : Fin 11 := ⟨4, by decide⟩
private abbrev idx10 : Fin 11 := ⟨5, by decide⟩
private abbrev idx12 : Fin 11 := ⟨6, by decide⟩
private abbrev idx15 : Fin 11 := ⟨7, by decide⟩
private abbrev idx20 : Fin 11 := ⟨8, by decide⟩
private abbrev idx30 : Fin 11 := ⟨9, by decide⟩
private abbrev idx60 : Fin 11 := ⟨10, by decide⟩

private theorem largeMul_injective : Function.Injective largeMul := by
  decide

private theorem largeMul_pos (i : Fin 11) : 0 < largeMul i := by
  fin_cases i <;> decide

private theorem largeMul_mul_injective {a : ℕ} (ha : 0 < a) :
    Function.Injective fun i : Fin 11 => largeMul i * a := by
  intro i j h
  exact largeMul_injective (Nat.eq_of_mul_eq_mul_right ha h)

private def largePrefix (c : ℕ) : Finset (Fin 11) :=
  Finset.univ.filter fun i => largeMul i ≤ c

private def largeGadget (c a : ℕ) : Finset ℕ :=
  (largePrefix c).image fun i => largeMul i * a

private theorem largeGadget_card_eq_prefix_card {c a : ℕ} (ha : 0 < a) :
    (largeGadget c a).card = (largePrefix c).card := by
  simpa [largeGadget] using
    Finset.card_image_of_injective (largePrefix c) (largeMul_mul_injective ha)

private theorem largeGadget_subset_sixty {c a : ℕ} (hc : c ≤ 60) :
    largeGadget c a ⊆ largeGadget 60 a := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  have hle : largeMul i ≤ c := by
    simpa [largePrefix] using (Finset.mem_filter.mp hi).2
  simp [largePrefix, hle.trans hc]

private theorem largeGadget_subset_Icc {c a N : ℕ} (ha : 0 < a) (hcN : c * a ≤ N) :
    largeGadget c a ⊆ Finset.Icc 1 N := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  have hle : largeMul i ≤ c := by
    simpa [largePrefix] using (Finset.mem_filter.mp hi).2
  have hmul : largeMul i * a ≤ c * a := Nat.mul_le_mul_right a hle
  simp only [Finset.mem_Icc]
  exact ⟨by nlinarith [largeMul_pos i, ha], hmul.trans hcN⟩

private theorem large_preimage_image_eq (A : Finset ℕ) (c a : ℕ) :
    ((largePrefix c).filter fun i => largeMul i * a ∈ A).image
        (fun i => largeMul i * a) =
      largeGadget c a ∩ A := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩,
        (Finset.mem_filter.mp hi).2⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxg, hxA⟩
    rcases Finset.mem_image.mp hxg with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hxA⟩, rfl⟩

private theorem large_preimage_card_eq_inter {A : Finset ℕ} {c a : ℕ} (ha : 0 < a) :
    ((largePrefix c).filter fun i => largeMul i * a ∈ A).card =
      (largeGadget c a ∩ A).card := by
  rw [← large_preimage_image_eq A c a]
  exact (Finset.card_image_of_injective
    ((largePrefix c).filter fun i => largeMul i * a ∈ A)
    (largeMul_mul_injective ha)).symm

/-- Generic scaled reciprocal obstruction indexed by multiplier positions. -/
private theorem not_sf_index_identity {A : Finset ℕ} (hA : SumFree A) {a : ℕ}
    (ha : 0 < a) {target : Fin 11} {Ridx : Finset (Fin 11)}
    (htargetA : largeMul target * a ∈ A)
    (hRidxA : ∀ i ∈ Ridx, largeMul i * a ∈ A)
    (htarget_not_R : target ∉ Ridx) (hRnonempty : Ridx.Nonempty)
    (hid : (1 / (largeMul target : ℚ)) =
      ∑ i ∈ Ridx, (1 / (largeMul i : ℚ))) : False := by
  let S : Finset ℕ := Ridx.image fun i => largeMul i * a
  have hSsubset : S ⊆ A.erase (largeMul target * a) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rw [Finset.mem_erase]
    exact ⟨fun hEq => by
      have hit : i = target := largeMul_mul_injective ha hEq
      exact htarget_not_R (hit ▸ hi), hRidxA i hi⟩
  have hSnonempty : S.Nonempty := by
    obtain ⟨i, hi⟩ := hRnonempty
    exact ⟨largeMul i * a, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hsum_image :
      (∑ b ∈ S, (1 / b : ℚ)) =
        ∑ i ∈ Ridx, (1 / (largeMul i * a : ℕ) : ℚ) := by
    dsimp [S]
    rw [Finset.sum_image]
    intro i _ j _ hEq
    exact largeMul_mul_injective ha hEq
  have hscaled :
      (1 / (largeMul target * a : ℕ) : ℚ) =
        ∑ i ∈ Ridx, (1 / (largeMul i * a : ℕ) : ℚ) := by
    have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have htargetQ : (largeMul target : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (largeMul_pos target))
    have htarget_scale :
        (1 / (largeMul target * a : ℕ) : ℚ) =
          (1 / (a : ℚ)) * (1 / (largeMul target : ℚ)) := by
      push_cast
      field_simp [haQ, htargetQ]
    calc
      (1 / (largeMul target * a : ℕ) : ℚ)
          = (1 / (a : ℚ)) * (1 / (largeMul target : ℚ)) := htarget_scale
      _ = (1 / (a : ℚ)) * (∑ i ∈ Ridx, (1 / (largeMul i : ℚ))) := by
        rw [hid]
      _ = ∑ i ∈ Ridx, (1 / (a : ℚ)) * (1 / (largeMul i : ℚ)) := by
        rw [Finset.mul_sum]
      _ = ∑ i ∈ Ridx, (1 / (largeMul i * a : ℕ) : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        have hiQ : (largeMul i : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt (largeMul_pos i))
        symm
        push_cast
        field_simp [haQ, hiQ]
  exact hA (largeMul target * a) htargetA S hSsubset hSnonempty
    (hscaled.trans hsum_image.symm)

/-- The finite obstruction certificate for the eleven-multiplier gadget.
Each listed edge is a reciprocal identity, and every too-large prefix subset
contains one of these edges. -/
private def largeBadEdges : Finset (Finset (Fin 11)) :=
  {{idx2, idx3, idx6}, {idx3, idx4, idx12}, {idx2, idx3, idx10, idx15},
    {idx6, idx10, idx15}, {idx3, idx5, idx12, idx20},
    {idx2, idx5, idx6, idx12, idx20}, {idx4, idx5, idx20},
    {idx4, idx6, idx12}, {idx4, idx10, idx12, idx15},
    {idx5, idx12, idx15, idx20}, {idx4, idx5, idx30, idx60},
    {idx20, idx30, idx60}, {idx10, idx12, idx60},
    {idx5, idx12, idx15, idx30, idx60}}

set_option linter.style.nativeDecide false in
private theorem largeBadEdge_forbidden {A : Finset ℕ} (hA : SumFree A) {a : ℕ}
    (ha : 0 < a) {E : Finset (Fin 11)} (hE : E ∈ largeBadEdges)
    (hEA : ∀ i ∈ E, largeMul i * a ∈ A) : False := by
  simp only [largeBadEdges, Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · refine not_sf_index_identity hA ha (target := idx2) (Ridx := {idx3, idx6})
      (hEA idx2 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx3, idx6} : Finset (Fin 11)) ⊆ {idx2, idx3, idx6}) hi)
    · norm_num [largeMul, idx2, idx3, idx6]
  · refine not_sf_index_identity hA ha (target := idx3) (Ridx := {idx4, idx12})
      (hEA idx3 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx4, idx12} : Finset (Fin 11)) ⊆ {idx3, idx4, idx12}) hi)
    · norm_num [largeMul, idx3, idx4, idx12]
  · refine not_sf_index_identity hA ha (target := idx2) (Ridx := {idx3, idx10, idx15})
      (hEA idx2 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx3, idx10, idx15} : Finset (Fin 11)) ⊆ {idx2, idx3, idx10, idx15}) hi)
    · norm_num [largeMul, idx2, idx3, idx10, idx15]
  · refine not_sf_index_identity hA ha (target := idx6) (Ridx := {idx10, idx15})
      (hEA idx6 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx10, idx15} : Finset (Fin 11)) ⊆ {idx6, idx10, idx15}) hi)
    · norm_num [largeMul, idx6, idx10, idx15]
  · refine not_sf_index_identity hA ha (target := idx3) (Ridx := {idx5, idx12, idx20})
      (hEA idx3 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx5, idx12, idx20} : Finset (Fin 11)) ⊆ {idx3, idx5, idx12, idx20}) hi)
    · norm_num [largeMul, idx3, idx5, idx12, idx20]
  · refine not_sf_index_identity hA ha (target := idx2)
      (Ridx := {idx5, idx6, idx12, idx20}) (hEA idx2 (by native_decide))
      ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx5, idx6, idx12, idx20} : Finset (Fin 11)) ⊆
          {idx2, idx5, idx6, idx12, idx20}) hi)
    · norm_num [largeMul, idx2, idx5, idx6, idx12, idx20]
  · refine not_sf_index_identity hA ha (target := idx4) (Ridx := {idx5, idx20})
      (hEA idx4 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx5, idx20} : Finset (Fin 11)) ⊆ {idx4, idx5, idx20}) hi)
    · norm_num [largeMul, idx4, idx5, idx20]
  · refine not_sf_index_identity hA ha (target := idx4) (Ridx := {idx6, idx12})
      (hEA idx4 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx6, idx12} : Finset (Fin 11)) ⊆ {idx4, idx6, idx12}) hi)
    · norm_num [largeMul, idx4, idx6, idx12]
  · refine not_sf_index_identity hA ha (target := idx4) (Ridx := {idx10, idx12, idx15})
      (hEA idx4 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx10, idx12, idx15} : Finset (Fin 11)) ⊆ {idx4, idx10, idx12, idx15}) hi)
    · norm_num [largeMul, idx4, idx10, idx12, idx15]
  · refine not_sf_index_identity hA ha (target := idx5) (Ridx := {idx12, idx15, idx20})
      (hEA idx5 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx12, idx15, idx20} : Finset (Fin 11)) ⊆ {idx5, idx12, idx15, idx20}) hi)
    · norm_num [largeMul, idx5, idx12, idx15, idx20]
  · refine not_sf_index_identity hA ha (target := idx4) (Ridx := {idx5, idx30, idx60})
      (hEA idx4 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx5, idx30, idx60} : Finset (Fin 11)) ⊆ {idx4, idx5, idx30, idx60}) hi)
    · norm_num [largeMul, idx4, idx5, idx30, idx60]
  · refine not_sf_index_identity hA ha (target := idx20) (Ridx := {idx30, idx60})
      (hEA idx20 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx30, idx60} : Finset (Fin 11)) ⊆ {idx20, idx30, idx60}) hi)
    · norm_num [largeMul, idx20, idx30, idx60]
  · refine not_sf_index_identity hA ha (target := idx10) (Ridx := {idx12, idx60})
      (hEA idx10 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx12, idx60} : Finset (Fin 11)) ⊆ {idx10, idx12, idx60}) hi)
    · norm_num [largeMul, idx10, idx12, idx60]
  · refine not_sf_index_identity hA ha (target := idx5) (Ridx := {idx12, idx15, idx30, idx60})
      (hEA idx5 (by native_decide)) ?_ (by native_decide) (by native_decide) ?_
    · intro i hi
      exact hEA i ((by native_decide :
        ({idx12, idx15, idx30, idx60} : Finset (Fin 11)) ⊆
          {idx5, idx12, idx15, idx30, idx60}) hi)
    · norm_num [largeMul, idx5, idx12, idx15, idx30, idx60]

private def largeCutoff (i : Fin 7) : ℕ :=
  ![60, 30, 20, 15, 12, 10, 6] i

private def largeSize (i : Fin 7) : ℕ :=
  ![11, 10, 9, 8, 7, 6, 5] i

private def largeKeep (i : Fin 7) : ℕ :=
  ![6, 6, 5, 5, 5, 5, 4] i

private def largeLo (N : ℕ) (i : Fin 7) : ℕ :=
  ![1, N / 60 + 1, N / 30 + 1, N / 20 + 1, N / 15 + 1, N / 12 + 1,
    N / 10 + 1] i

private def largeHi (N : ℕ) (i : Fin 7) : ℕ :=
  ![N / 60, N / 30, N / 20, N / 15, N / 12, N / 10, N / 6] i

private def largeBand (N : ℕ) (i : Fin 7) : Finset ℕ :=
  (Finset.Icc (largeLo N i) (largeHi N i)).filter ExtParam

private theorem largePrefix_card_eq_size (i : Fin 7) :
    (largePrefix (largeCutoff i)).card = largeSize i := by
  fin_cases i <;> decide

private theorem largeCutoff_le_sixty (i : Fin 7) : largeCutoff i ≤ 60 := by
  fin_cases i <;> decide

private theorem largeKeep_le_size (i : Fin 7) : largeKeep i ≤ largeSize i := by
  fin_cases i <;> decide

set_option linter.style.nativeDecide false in
/-- Closed finite check of the prefix hitting certificate. The computation is
over `Fin 11`, not over an unbounded domain. -/
private theorem large_prefix_hitting (i : Fin 7) :
    ∀ S : Finset (Fin 11), S ⊆ largePrefix (largeCutoff i) →
      largeKeep i < S.card → ∃ E ∈ largeBadEdges, E ⊆ S := by
  fin_cases i <;> native_decide

private theorem largeGadget_inter_le_keep {A : Finset ℕ} (hA : SumFree A)
    {a : ℕ} (ha : 0 < a) (i : Fin 7) :
    (largeGadget (largeCutoff i) a ∩ A).card ≤ largeKeep i := by
  let S := (largePrefix (largeCutoff i)).filter fun j => largeMul j * a ∈ A
  have hcard : S.card = (largeGadget (largeCutoff i) a ∩ A).card := by
    simpa [S] using
      large_preimage_card_eq_inter (A := A) (c := largeCutoff i) (a := a) ha
  by_contra hle
  have hgt : largeKeep i < S.card := by omega
  obtain ⟨E, hE, hES⟩ := large_prefix_hitting i S (Finset.filter_subset _ _) hgt
  exact largeBadEdge_forbidden hA ha hE fun j hj => by
    exact (Finset.mem_filter.mp (hES hj)).2

set_option linter.style.setOption false in
set_option linter.flexible false

set_option linter.flexible false in
private theorem largeBand_mem {N : ℕ} (i : Fin 7) {a : ℕ}
    (ha : a ∈ largeBand N i) :
    0 < a ∧ ExtParam a ∧ largeCutoff i * a ≤ N := by
  fin_cases i
  · simp [largeBand, largeLo, largeHi, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by change 60 * a ≤ N; omega⟩
  · simp [largeBand, largeLo, largeHi, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by change 30 * a ≤ N; omega⟩
  · simp [largeBand, largeLo, largeHi, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by change 20 * a ≤ N; omega⟩
  · simp [largeBand, largeLo, largeHi, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by change 15 * a ≤ N; omega⟩
  · simp [largeBand, largeLo, largeHi, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by change 12 * a ≤ N; omega⟩
  · simp [largeBand, largeLo, largeHi, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by change 10 * a ≤ N; omega⟩
  · simp [largeBand, largeLo, largeHi, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by change 6 * a ≤ N; omega⟩

set_option linter.flexible false in
private theorem largeBand_param_ne {N : ℕ} {i j : Fin 7} (hij : i ≠ j)
    {a₁ a₂ : ℕ} (ha₁ : a₁ ∈ largeBand N i) (ha₂ : a₂ ∈ largeBand N j) :
    a₁ ≠ a₂ := by
  fin_cases i <;> fin_cases j <;>
    simp [largeBand, largeLo, largeHi, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂ <;>
    try contradiction
  all_goals
    intro hEq
    subst hEq
    omega

set_option linter.unusedSimpArgs false in
set_option linter.flexible false in
private theorem large_sum_full_gadgets_disjoint {a₁ a₂ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hne : a₁ ≠ a₂)
    (hv₁ : ExtParam a₁) (hv₂ : ExtParam a₂) :
    Disjoint (largeGadget 60 a₁) (largeGadget 60 a₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  rcases Finset.mem_image.mp hx₁ with ⟨i, _hi, rfl⟩
  rcases Finset.mem_image.mp hx₂ with ⟨j, _hj, hEq⟩
  have ha₁' : a₁ ≠ 0 := by omega
  have ha₂' : a₂ ≠ 0 := by omega
  fin_cases i <;> fin_cases j <;> simp [largeMul] at hEq <;>
  first
  | exact hne (by omega)
  | have hsig := congrArg extSig hEq
    simp [largeMul, extSig_two ha₁' hv₁, extSig_three ha₁' hv₁,
      extSig_four ha₁' hv₁, extSig_five ha₁' hv₁, extSig_six ha₁' hv₁,
      extSig_ten ha₁' hv₁, extSig_twelve ha₁' hv₁, extSig_fifteen ha₁' hv₁,
      extSig_twenty ha₁' hv₁, extSig_thirty ha₁' hv₁, extSig_sixty ha₁' hv₁,
      extSig_two ha₂' hv₂, extSig_three ha₂' hv₂, extSig_four ha₂' hv₂,
      extSig_five ha₂' hv₂, extSig_six ha₂' hv₂, extSig_ten ha₂' hv₂,
      extSig_twelve ha₂' hv₂, extSig_fifteen ha₂' hv₂, extSig_twenty ha₂' hv₂,
      extSig_thirty ha₂' hv₂, extSig_sixty ha₂' hv₂] at hsig

/-- Seven-band packing bound from the larger same-signature gadget. The weighted
prefix deficits are `5,4,4,3,2,1,1` on the bands ending at
`60,30,20,15,12,10,6`, giving asymptotic shape `145/168 + o(1)`. -/
theorem sum_free_large_same_signature_145_168_bound (N : ℕ) (A : Finset ℕ)
    (hA : SumFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ∑ i : Fin 7, (largeSize i - largeKeep i) * (largeBand N i).card ≤ N := by
  let J : Finset (Fin 7) := Finset.univ
  let gadget : Fin 7 → ℕ → Finset ℕ := fun i a => largeGadget (largeCutoff i) a
  have h := PackingBound.indexed_family_bound N A J (largeBand N) gadget largeSize largeKeep
    (fun i _ => largeKeep_le_size i) hAN
    (by
      intro i _hi a₁ ha₁ a₂ ha₂ hne
      have hm₁ := largeBand_mem i (Finset.mem_coe.mp ha₁)
      have hm₂ := largeBand_mem i (Finset.mem_coe.mp ha₂)
      exact (large_sum_full_gadgets_disjoint hm₁.1 hm₂.1 hne hm₁.2.1 hm₂.2.1).mono
        (largeGadget_subset_sixty (largeCutoff_le_sixty i))
        (largeGadget_subset_sixty (largeCutoff_le_sixty i)))
    (by
      intro i _hi a ha
      have hm := largeBand_mem i ha
      calc
        (gadget i a).card = (largePrefix (largeCutoff i)).card :=
          largeGadget_card_eq_prefix_card hm.1
        _ = largeSize i := largePrefix_card_eq_size i)
    (by
      intro i _hi a ha
      exact largeGadget_inter_le_keep hA (largeBand_mem i ha).1 i)
    (by
      intro i _hi
      exact Finset.biUnion_subset.mpr fun a ha =>
        largeGadget_subset_Icc (largeBand_mem i ha).1 (largeBand_mem i ha).2.2)
    (by
      intro i _hi j _hj hij
      rw [Finset.disjoint_biUnion_left]
      intro a₁ ha₁
      rw [Finset.disjoint_biUnion_right]
      intro a₂ ha₂
      have hm₁ := largeBand_mem i ha₁
      have hm₂ := largeBand_mem j ha₂
      have hne : a₁ ≠ a₂ := largeBand_param_ne hij ha₁ ha₂
      exact (large_sum_full_gadgets_disjoint hm₁.1 hm₂.1 hne hm₁.2.1 hm₂.2.1).mono
        (largeGadget_subset_sixty (largeCutoff_le_sixty i))
        (largeGadget_subset_sixty (largeCutoff_le_sixty j)))
  simpa [J] using h

/-- **Van Doorn's 9/10 bound transfers to sum-free sets.**

    Since SumFree A implies TripleFree A, the structural bound
    A.card + |D_S| + |D_T| ≤ N from van Doorn's triple-free analysis
    applies directly to any sum-free set A ⊆ {1, …, N}.

    Combined with the density estimates |D_S| ≈ N/18 and |D_T| ≈ N/120,
    this gives f₃₀₁(N) ≤ 9N/10 + o(N). -/
theorem sum_free_van_doorn_upper_bound (N : ℕ) (A : Finset ℕ)
    (hA : SumFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter SParam).card
           + ((Finset.Icc 1 (N / 20)).filter TParam).card ≤ N :=
  van_doorn_upper_bound N A (sumFree_implies_tripleFree hA) hAN

end UnitFractionSets
