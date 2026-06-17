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

/-- The finite "window" of `A` below `n`: the elements of `A` in `{0, 1, …, n}`.

Every additive representation of `n` from `A` has both coordinates in this set,
which is the key to the quadratic upper bound on `sumRep` (Erdős #66). -/
noncomputable def windowBelow (A : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter fun a => a ∈ A

@[simp] theorem mem_windowBelow {A : Set ℕ} {n a : ℕ} :
    a ∈ windowBelow A n ↔ a ≤ n ∧ a ∈ A := by
  classical
  unfold windowBelow
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h; exact ⟨by omega, h.2⟩
  · intro h; exact ⟨by omega, h.2⟩

/-- Every additive representation of `n` lives in the square of the window
`windowBelow A n`, since `a + b = n` forces `a, b ≤ n`. -/
theorem sumRepPairs_subset_windowBelow_product (A : Set ℕ) (n : ℕ) :
    sumRepPairs A n ⊆ windowBelow A n ×ˢ windowBelow A n := by
  intro ab hab
  rw [mem_sumRepPairs] at hab
  obtain ⟨ha, hb, hsum⟩ := hab
  rw [Finset.mem_product]
  refine ⟨?_, ?_⟩
  · rw [mem_windowBelow]; exact ⟨by omega, ha⟩
  · rw [mem_windowBelow]; exact ⟨by omega, hb⟩

/-- **Erdős #66 quadratic upper bound.** The number of ordered additive
representations of `n` from `A` is at most the square of the number of elements
of `A` in `{0, 1, …, n}`.

Indeed every pair `(a, b)` with `a, b ∈ A` and `a + b = n` has `a, b ≤ n`, so it
belongs to `windowBelow A n ×ˢ windowBelow A n`, a set of size
`(windowBelow A n).card ^ 2`. -/
theorem sumRep_le_windowBelow_card_sq (A : Set ℕ) (n : ℕ) :
    sumRep A n ≤ (windowBelow A n).card ^ 2 := by
  unfold sumRep
  calc
    (sumRepPairs A n).card
        ≤ (windowBelow A n ×ˢ windowBelow A n).card :=
          Finset.card_le_card (sumRepPairs_subset_windowBelow_product A n)
    _ = (windowBelow A n).card * (windowBelow A n).card :=
          Finset.card_product _ _
    _ = (windowBelow A n).card ^ 2 := by rw [sq]

end AdditiveRepresentationLog
