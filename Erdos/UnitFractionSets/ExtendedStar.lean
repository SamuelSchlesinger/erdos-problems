/-
# Extended Star Analysis: Sum-Free vs Triple-Free Gadget Gap

The **extended star** E_d = {2d, 3d, 4d, 6d, 10d, 12d, 15d} is a 7-element gadget
that exposes the structural gap between triple-free (Problem #302) and sum-free
(Problem #301) avoidance at the gadget level.

**Triple violations** (k = 2):
  1/(2d) = 1/(3d) + 1/(6d)
  1/(3d) = 1/(4d) + 1/(12d)
  1/(4d) = 1/(6d) + 1/(12d)
  1/(6d) = 1/(10d) + 1/(15d)

A triple-free set can keep at most 5 of the 7 elements (e.g., {2d, 3d, 10d, 12d, 15d}).

**Additional sum-free violations** (k = 3):
  1/(2d) = 1/(3d) + 1/(10d) + 1/(15d)
  1/(2d) = 1/(4d) + 1/(6d) + 1/(12d)
  1/(3d) = 1/(6d) + 1/(10d) + 1/(15d)
  1/(4d) = 1/(10d) + 1/(12d) + 1/(15d)

A sum-free set can keep at most 4 of the 7 elements.

This demonstrates that sum-free avoidance is strictly more restrictive than
triple-free avoidance at the gadget level, providing a systematic explanation
for why Problem #301 should have tighter density bounds than Problem #302.

Reference: https://www.erdosproblems.com/301
-/
import Erdos.UnitFractionSets.Connections
import Erdos.UnitFractionTriples.StarNeighborhood

namespace UnitFractionSets

open UnitFractionTriples

/-! ### k = 3 sum identities in the extended star

These are the four identities involving three reciprocals that create
additional sum-free obstructions beyond the triple (k = 2) violations. -/

/-- **Sum identity**: 1/(2d) = 1/(3d) + 1/(10d) + 1/(15d).

    Verification: 1/3 + 1/10 + 1/15 = 10/30 + 3/30 + 2/30 = 15/30 = 1/2. -/
theorem sum_identity_2_3_10_15 (d : ℕ) (hd : 0 < d) :
    (1 / (2 * d) : ℚ) = 1 / (3 * d) + 1 / (10 * d) + 1 / (15 * d) := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp; ring

/-- **Sum identity**: 1/(2d) = 1/(4d) + 1/(6d) + 1/(12d).

    Verification: 1/4 + 1/6 + 1/12 = 3/12 + 2/12 + 1/12 = 6/12 = 1/2. -/
theorem sum_identity_2_4_6_12 (d : ℕ) (hd : 0 < d) :
    (1 / (2 * d) : ℚ) = 1 / (4 * d) + 1 / (6 * d) + 1 / (12 * d) := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp; ring

/-- **Sum identity**: 1/(3d) = 1/(6d) + 1/(10d) + 1/(15d).

    Verification: 1/6 + 1/10 + 1/15 = 5/30 + 3/30 + 2/30 = 10/30 = 1/3. -/
theorem sum_identity_3_6_10_15 (d : ℕ) (hd : 0 < d) :
    (1 / (3 * d) : ℚ) = 1 / (6 * d) + 1 / (10 * d) + 1 / (15 * d) := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp; ring

/-- **Sum identity**: 1/(4d) = 1/(10d) + 1/(12d) + 1/(15d).

    Verification: 1/10 + 1/12 + 1/15 = 6/60 + 5/60 + 4/60 = 15/60 = 1/4. -/
theorem sum_identity_4_10_12_15 (d : ℕ) (hd : 0 < d) :
    (1 / (4 * d) : ℚ) = 1 / (10 * d) + 1 / (12 * d) + 1 / (15 * d) := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp; ring

/-! ### Triple identity for {6, 10, 15} -/

/-- The triple identity 1/(6d) = 1/(10d) + 1/(15d) for all d > 0. -/
theorem triple_6_10_15 (d : ℕ) (hd : 0 < d) :
    IsUnitFractionTriple (6 * d) (10 * d) (15 * d) := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [triple_iff_div (by omega) (by omega) (by omega)]
  ring

/-! ### Extended star cardinality -/

/-- The extended star {2d, 3d, 4d, 6d, 10d, 12d, 15d} has exactly 7 elements
    for d > 0. -/
theorem extended_star_card_eq_seven {d : ℕ} (hd : 0 < d) :
    ({2*d, 3*d, 4*d, 6*d, 10*d, 12*d, 15*d} : Finset ℕ).card = 7 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

/-! ### Sum-free hitting-set bound: at most 4 from each extended star

The proof strategy: for each sum-free violation pattern, we derive that
certain elements of the extended star cannot all be in A. By chaining these
violations, we find 3 distinct elements of E not in A, giving card ≤ 4. -/

/-- Helper: a sum-free set cannot contain {2d, 3d, 10d, 15d} (via k=3 identity). -/
private theorem not_sf_2_3_10_15 {A : Finset ℕ} (hA : SumFree A) {d : ℕ} (hd : 0 < d)
    (h2 : 2 * d ∈ A) (h3 : 3 * d ∈ A) (h10 : 10 * d ∈ A) (h15 : 15 * d ∈ A) : False := by
  have hS : ({3 * d, 10 * d, 15 * d} : Finset ℕ) ⊆ A.erase (2 * d) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by omega, ‹_›⟩
  have hne : ({3 * d, 10 * d, 15 * d} : Finset ℕ).Nonempty := ⟨3 * d, by simp⟩
  have heq : (1 / (2 * d : ℕ) : ℚ) =
      ∑ b ∈ ({3 * d, 10 * d, 15 * d} : Finset ℕ), (1 / b : ℚ) := by
    have h3_not : (3 * d : ℕ) ∉ ({10 * d, 15 * d} : Finset ℕ) := by simp; omega
    have h10_not : (10 * d : ℕ) ∉ ({15 * d} : Finset ℕ) := by simp; omega
    rw [show ({3 * d, 10 * d, 15 * d} : Finset ℕ) =
        insert (3 * d) (insert (10 * d) {15 * d}) from rfl]
    rw [Finset.sum_insert h3_not, Finset.sum_insert h10_not, Finset.sum_singleton]
    push_cast; rw [sum_identity_2_3_10_15 d hd]; ring
  exact hA (2 * d) h2 _ hS hne heq

/-- Helper: a sum-free set cannot contain {2d, 4d, 6d, 12d} (via k=3 identity). -/
private theorem not_sf_2_4_6_12 {A : Finset ℕ} (hA : SumFree A) {d : ℕ} (hd : 0 < d)
    (h2 : 2 * d ∈ A) (h4 : 4 * d ∈ A) (h6 : 6 * d ∈ A) (h12 : 12 * d ∈ A) : False := by
  have hS : ({4 * d, 6 * d, 12 * d} : Finset ℕ) ⊆ A.erase (2 * d) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by omega, ‹_›⟩
  have hne : ({4 * d, 6 * d, 12 * d} : Finset ℕ).Nonempty := ⟨4 * d, by simp⟩
  have heq : (1 / (2 * d : ℕ) : ℚ) =
      ∑ b ∈ ({4 * d, 6 * d, 12 * d} : Finset ℕ), (1 / b : ℚ) := by
    have h4_not : (4 * d : ℕ) ∉ ({6 * d, 12 * d} : Finset ℕ) := by simp; omega
    have h6_not : (6 * d : ℕ) ∉ ({12 * d} : Finset ℕ) := by simp; omega
    rw [show ({4 * d, 6 * d, 12 * d} : Finset ℕ) =
        insert (4 * d) (insert (6 * d) {12 * d}) from rfl]
    rw [Finset.sum_insert h4_not, Finset.sum_insert h6_not, Finset.sum_singleton]
    push_cast; rw [sum_identity_2_4_6_12 d hd]; ring
  exact hA (2 * d) h2 _ hS hne heq

/-- Helper: a sum-free set cannot contain {3d, 6d, 10d, 15d} (via k=3 identity). -/
private theorem not_sf_3_6_10_15 {A : Finset ℕ} (hA : SumFree A) {d : ℕ} (hd : 0 < d)
    (h3 : 3 * d ∈ A) (h6 : 6 * d ∈ A) (h10 : 10 * d ∈ A) (h15 : 15 * d ∈ A) : False := by
  have hS : ({6 * d, 10 * d, 15 * d} : Finset ℕ) ⊆ A.erase (3 * d) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by omega, ‹_›⟩
  have hne : ({6 * d, 10 * d, 15 * d} : Finset ℕ).Nonempty := ⟨6 * d, by simp⟩
  have heq : (1 / (3 * d : ℕ) : ℚ) =
      ∑ b ∈ ({6 * d, 10 * d, 15 * d} : Finset ℕ), (1 / b : ℚ) := by
    have h6_not : (6 * d : ℕ) ∉ ({10 * d, 15 * d} : Finset ℕ) := by simp; omega
    have h10_not : (10 * d : ℕ) ∉ ({15 * d} : Finset ℕ) := by simp; omega
    rw [show ({6 * d, 10 * d, 15 * d} : Finset ℕ) =
        insert (6 * d) (insert (10 * d) {15 * d}) from rfl]
    rw [Finset.sum_insert h6_not, Finset.sum_insert h10_not, Finset.sum_singleton]
    push_cast; rw [sum_identity_3_6_10_15 d hd]; ring
  exact hA (3 * d) h3 _ hS hne heq

/-- Helper: a sum-free set cannot contain {4d, 10d, 12d, 15d} (via k=3 identity). -/
private theorem not_sf_4_10_12_15 {A : Finset ℕ} (hA : SumFree A) {d : ℕ} (hd : 0 < d)
    (h4 : 4 * d ∈ A) (h10 : 10 * d ∈ A) (h12 : 12 * d ∈ A) (h15 : 15 * d ∈ A) : False := by
  have hS : ({10 * d, 12 * d, 15 * d} : Finset ℕ) ⊆ A.erase (4 * d) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by omega, ‹_›⟩
  have hne : ({10 * d, 12 * d, 15 * d} : Finset ℕ).Nonempty := ⟨10 * d, by simp⟩
  have heq : (1 / (4 * d : ℕ) : ℚ) =
      ∑ b ∈ ({10 * d, 12 * d, 15 * d} : Finset ℕ), (1 / b : ℚ) := by
    have h10_not : (10 * d : ℕ) ∉ ({12 * d, 15 * d} : Finset ℕ) := by simp; omega
    have h12_not : (12 * d : ℕ) ∉ ({15 * d} : Finset ℕ) := by simp; omega
    rw [show ({10 * d, 12 * d, 15 * d} : Finset ℕ) =
        insert (10 * d) (insert (12 * d) {15 * d}) from rfl]
    rw [Finset.sum_insert h10_not, Finset.sum_insert h12_not, Finset.sum_singleton]
    push_cast; rw [sum_identity_4_10_12_15 d hd]; ring
  exact hA (4 * d) h4 _ hS hne heq

/-- If three distinct elements of a finset S are not in A,
    then (S ∩ A).card + 3 ≤ S.card. -/
private lemma card_inter_le_of_three_not_mem {S A : Finset ℕ} {x y z : ℕ}
    (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxA : x ∉ A) (hyA : y ∉ A) (hzA : z ∉ A) :
    (S ∩ A).card + 3 ≤ S.card := by
  have hdisj : Disjoint (S ∩ A) ({x, y, z} : Finset ℕ) := by
    rw [Finset.disjoint_right]
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp [hxA]
    · simp [hyA]
    · simp [hzA]
  have htrip : ({x, y, z} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz])]
    rw [Finset.card_insert_of_notMem (by simp [hyz])]
    simp
  have hsub : S ∩ A ∪ {x, y, z} ⊆ S :=
    Finset.union_subset Finset.inter_subset_left (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption)
  calc (S ∩ A).card + 3
      = (S ∩ A).card + ({x, y, z} : Finset ℕ).card := by rw [htrip]
    _ = (S ∩ A ∪ {x, y, z}).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ S.card := Finset.card_le_card hsub

/-- **Sum-free hitting-set bound.** A sum-free set keeps at most 4 elements
    from the extended star {2d, 3d, 4d, 6d, 10d, 12d, 15d}.

    The proof shows that every 5-element subset of the extended star contains
    a complete sum-free violation (either a k=2 triple or a k=3 identity).
    We find three distinct excluded elements by case-splitting on the
    8 violation patterns. -/
theorem sum_free_inter_extended_star_le_four {A : Finset ℕ} (hA : SumFree A)
    {d : ℕ} (hd : 0 < d) :
    (({2*d, 3*d, 4*d, 6*d, 10*d, 12*d, 15*d} : Finset ℕ) ∩ A).card ≤ 4 := by
  set E := ({2*d, 3*d, 4*d, 6*d, 10*d, 12*d, 15*d} : Finset ℕ) with hE_def
  -- SumFree → TripleFree
  have hTF : TripleFree A :=
    UnitFractionConnections.sumFree_implies_tripleFree hA
  have hE7 : E.card = 7 := extended_star_card_eq_seven hd
  -- It suffices to find 3 distinct elements of E not in A.
  suffices ∃ x y z, x ∈ E ∧ y ∈ E ∧ z ∈ E ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ∉ A ∧ y ∉ A ∧ z ∉ A by
    obtain ⟨x, y, z, hxE, hyE, hzE, hxy, hxz, hyz, hxA, hyA, hzA⟩ := this
    have h := card_inter_le_of_three_not_mem hxE hyE hzE hxy hxz hyz hxA hyA hzA
    omega
  -- The 4 triple violations: {2,3,6}, {3,4,12}, {4,6,12}, {6,10,15}
  -- The 4 sum violations: {2,3,10,15}, {2,4,6,12}, {3,6,10,15}, {4,10,12,15}
  -- We find excluded elements by chaining violations.
  -- Start from the triple {2d, 3d, 6d}: at least one is missing.
  by_cases h2 : 2 * d ∈ A
  · by_cases h3 : 3 * d ∈ A
    · -- 2d, 3d ∈ A → 6d ∉ A (triple {2,3,6})
      have h6 : 6 * d ∉ A := fun h6 => triple_free_excludes_one hTF hd h2 h3 h6
      -- Now from {3,4,12}: either 4d or 12d ∉ A
      by_cases h4 : 4 * d ∈ A
      · -- 3d, 4d ∈ A → 12d ∉ A (triple {3,4,12})
        have h12 : 12 * d ∉ A := fun h12 =>
          hTF _ h3 _ h4 _ h12 (by omega) (by omega) (by omega) (triple_3a_4a_12a d hd)
        -- Now from sum identity {2,3,10,15}: either 10d or 15d ∉ A
        by_cases h10 : 10 * d ∈ A
        · have h15 : 15 * d ∉ A := fun h15 => not_sf_2_3_10_15 hA hd h2 h3 h10 h15
          exact ⟨6*d, 12*d, 15*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h6, h12, h15⟩
        · exact ⟨6*d, 10*d, 12*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h6, h10, h12⟩
      · -- 4d ∉ A
        by_cases h10 : 10 * d ∈ A
        · have h15 : 15 * d ∉ A := fun h15 => not_sf_2_3_10_15 hA hd h2 h3 h10 h15
          exact ⟨4*d, 6*d, 15*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h4, h6, h15⟩
        · exact ⟨4*d, 6*d, 10*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h4, h6, h10⟩
    · -- 3d ∉ A
      by_cases h4 : 4 * d ∈ A
      · by_cases h6 : 6 * d ∈ A
        · -- 4d, 6d ∈ A → 12d ∉ A (triple {4,6,12})
          have h12 : 12 * d ∉ A := fun h12 =>
            hTF _ h4 _ h6 _ h12 (by omega) (by omega) (by omega) (triple_4a_6a_12a d hd)
          by_cases h10 : 10 * d ∈ A
          · have h15 : 15 * d ∉ A := fun h15 =>
              hTF _ h6 _ h10 _ h15 (by omega) (by omega) (by omega) (triple_6_10_15 d hd)
            exact ⟨3*d, 12*d, 15*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h3, h12, h15⟩
          · exact ⟨3*d, 10*d, 12*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h3, h10, h12⟩
        · -- 3d, 6d ∉ A; need one more
          by_cases h10 : 10 * d ∈ A
          · by_cases h12 : 12 * d ∈ A
            · by_cases h15 : 15 * d ∈ A
              · exact (not_sf_4_10_12_15 hA hd h4 h10 h12 h15).elim
              · exact ⟨3*d, 6*d, 15*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
                  by omega, by omega, by omega, h3, h6, h15⟩
            · exact ⟨3*d, 6*d, 12*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
                by omega, by omega, by omega, h3, h6, h12⟩
          · exact ⟨3*d, 6*d, 10*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h3, h6, h10⟩
      · -- 3d, 4d ∉ A; need one more
        by_cases h6 : 6 * d ∈ A
        · by_cases h10 : 10 * d ∈ A
          · have h15 : 15 * d ∉ A := fun h15 =>
              hTF _ h6 _ h10 _ h15 (by omega) (by omega) (by omega) (triple_6_10_15 d hd)
            exact ⟨3*d, 4*d, 15*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h3, h4, h15⟩
          · exact ⟨3*d, 4*d, 10*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h3, h4, h10⟩
        · exact ⟨3*d, 4*d, 6*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h3, h4, h6⟩
  · -- 2d ∉ A
    by_cases h3 : 3 * d ∈ A
    · by_cases h4 : 4 * d ∈ A
      · -- 3d, 4d ∈ A → 12d ∉ A (triple {3,4,12})
        have h12 : 12 * d ∉ A := fun h12 =>
          hTF _ h3 _ h4 _ h12 (by omega) (by omega) (by omega) (triple_3a_4a_12a d hd)
        by_cases h6 : 6 * d ∈ A
        · by_cases h10 : 10 * d ∈ A
          · have h15 : 15 * d ∉ A := fun h15 =>
              hTF _ h6 _ h10 _ h15 (by omega) (by omega) (by omega) (triple_6_10_15 d hd)
            exact ⟨2*d, 12*d, 15*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h2, h12, h15⟩
          · exact ⟨2*d, 10*d, 12*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h2, h10, h12⟩
        · exact ⟨2*d, 6*d, 12*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h2, h6, h12⟩
      · -- 2d, 4d ∉ A; need one more
        by_cases h6 : 6 * d ∈ A
        · by_cases h10 : 10 * d ∈ A
          · have h15 : 15 * d ∉ A := fun h15 =>
              hTF _ h6 _ h10 _ h15 (by omega) (by omega) (by omega) (triple_6_10_15 d hd)
            exact ⟨2*d, 4*d, 15*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h2, h4, h15⟩
          · exact ⟨2*d, 4*d, 10*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
              by omega, by omega, by omega, h2, h4, h10⟩
        · exact ⟨2*d, 4*d, 6*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h2, h4, h6⟩
    · -- 2d, 3d ∉ A; need one more
      by_cases h4 : 4 * d ∈ A
      · by_cases h6 : 6 * d ∈ A
        · have h12 : 12 * d ∉ A := fun h12 =>
            hTF _ h4 _ h6 _ h12 (by omega) (by omega) (by omega) (triple_4a_6a_12a d hd)
          exact ⟨2*d, 3*d, 12*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h2, h3, h12⟩
        · exact ⟨2*d, 3*d, 6*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
            by omega, by omega, by omega, h2, h3, h6⟩
      · exact ⟨2*d, 3*d, 4*d, by simp [hE_def], by simp [hE_def], by simp [hE_def],
          by omega, by omega, by omega, h2, h3, h4⟩

/-! ### Triple-free 5-element subset

The subset {2d, 3d, 10d, 12d, 15d} avoids all 4 triple violations:
  - {2,3,6}: 6d is missing
  - {3,4,12}: 4d is missing
  - {4,6,12}: 4d and 6d are missing
  - {6,10,15}: 6d is missing
-/

set_option maxHeartbeats 400000 in
-- Lean 4.27 needs a larger heartbeat budget for this finite 5^3 case split.
/-- **Triple-free 5-element witness.** The set {2d, 3d, 10d, 12d, 15d} is
    triple-free (it avoids all 4 triple violations in the extended star).
    This demonstrates that triple-free sets can keep 5 of the 7 elements.

    The 4 triple violations are {2,3,6}, {3,4,12}, {4,6,12}, {6,10,15}.
    By excluding 4d and 6d, all four violations are broken. -/
theorem triple_free_extended_star_five (d : ℕ) (hd : 0 < d) :
    TripleFree ({2*d, 3*d, 10*d, 12*d, 15*d} : Finset ℕ) := by
  intro a ha b hb c hc hab hac hbc htrip
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  obtain ⟨_, _, _, heq⟩ := htrip
  rw [triple_iff_div (by rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega)
      (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> omega)
      (by rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega)] at heq
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  simp_all <;> nlinarith

/-- **Structural gap witness.** The 5-element subset {2d, 3d, 10d, 12d, 15d}
    is triple-free but NOT sum-free (for d > 0).

    The k=3 identity 1/(2d) = 1/(3d) + 1/(10d) + 1/(15d) provides a sum-free
    violation within this 5-element set. This demonstrates, at the gadget level,
    that sum-free avoidance is strictly more restrictive than triple-free
    avoidance: the maximum triple-free subset of the extended star has 5 elements,
    but the maximum sum-free subset has only 4 elements.

    Unlike the Cambie counterexample (which is an ad-hoc violation), this gadget
    analysis is systematic: it identifies a *family of obstructions* parameterized
    by d that explains why sum-free sets must be smaller. -/
theorem sum_free_strictly_more_restrictive (d : ℕ) (hd : 0 < d) :
    TripleFree ({2*d, 3*d, 10*d, 12*d, 15*d} : Finset ℕ) ∧
    ¬SumFree ({2*d, 3*d, 10*d, 12*d, 15*d} : Finset ℕ) := by
  refine ⟨triple_free_extended_star_five d hd, ?_⟩
  intro hsf
  have h2 : 2 * d ∈ ({2*d, 3*d, 10*d, 12*d, 15*d} : Finset ℕ) := by simp
  have hS : ({3*d, 10*d, 15*d} : Finset ℕ) ⊆
      ({2*d, 3*d, 10*d, 12*d, 15*d} : Finset ℕ).erase (2 * d) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with rfl | rfl | rfl <;> constructor <;> simp_all <;> omega
  have hne : ({3*d, 10*d, 15*d} : Finset ℕ).Nonempty := ⟨3*d, by simp⟩
  have heq : (1 / (2 * d : ℕ) : ℚ) =
      ∑ b ∈ ({3*d, 10*d, 15*d} : Finset ℕ), (1 / b : ℚ) := by
    have h3_not : (3 * d : ℕ) ∉ ({10 * d, 15 * d} : Finset ℕ) := by simp; omega
    have h10_not : (10 * d : ℕ) ∉ ({15 * d} : Finset ℕ) := by simp; omega
    rw [show ({3*d, 10*d, 15*d} : Finset ℕ) =
        insert (3*d) (insert (10*d) {15*d}) from rfl]
    rw [Finset.sum_insert h3_not, Finset.sum_insert h10_not, Finset.sum_singleton]
    push_cast; rw [sum_identity_2_3_10_15 d hd]; ring
  exact hsf (2 * d) h2 _ hS hne heq

end UnitFractionSets
