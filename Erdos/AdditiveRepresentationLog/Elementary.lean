import Erdos.AdditiveRepresentationLog.Statement

/-
# Elementary Facts for Erdős Problem 66

This file records the first basic facts about the representation-count function
for problem `#66`: membership in the finite representation set, vanishing for
the empty set, monotonicity under set inclusion, and symmetry under swapping the
two summands.
-/
namespace AdditiveRepresentationLog

@[simp] theorem mem_sumRepPairs {A : Set ℕ} {n : ℕ} {ab : ℕ × ℕ} :
    ab ∈ sumRepPairs A n ↔ ab.1 ∈ A ∧ ab.2 ∈ A ∧ ab.1 + ab.2 = n := by
  classical
  constructor
  · intro hab
    have h :
        (ab.1 ≤ n ∧ ab.2 ≤ n) ∧
          ab.1 ∈ A ∧ ab.2 ∈ A ∧ ab.1 + ab.2 = n := by
      simpa [sumRepPairs] using hab
    exact h.2
  · intro hab
    have ha_bound : ab.1 < n + 1 := by omega
    have hb_bound : ab.2 < n + 1 := by omega
    simp [sumRepPairs, ha_bound, hb_bound, hab.1, hab.2.1, hab.2.2]

/-- The empty set has no additive representations. -/
@[simp] theorem sumRep_empty (n : ℕ) : sumRep (∅ : Set ℕ) n = 0 := by
  rw [sumRep]
  apply Finset.card_eq_zero.mpr
  ext ab
  simp

/-- Enlarging the set cannot reduce the number of additive representations. -/
theorem sumRep_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    sumRep A n ≤ sumRep B n := by
  unfold sumRep
  exact Finset.card_le_card fun ab hab => by
    rw [mem_sumRepPairs] at hab ⊢
    exact ⟨hAB hab.1, hAB hab.2.1, hab.2.2⟩

/-- Swapping the two summands preserves membership in the representation set. -/
theorem swap_mem_sumRepPairs_iff {A : Set ℕ} {n a b : ℕ} :
    (b, a) ∈ sumRepPairs A n ↔ (a, b) ∈ sumRepPairs A n := by
  rw [mem_sumRepPairs, mem_sumRepPairs]
  constructor
  · intro h
    exact ⟨h.2.1, h.1, by simpa [Nat.add_comm] using h.2.2⟩
  · intro h
    exact ⟨h.2.1, h.1, by simpa [Nat.add_comm] using h.2.2⟩

end AdditiveRepresentationLog
