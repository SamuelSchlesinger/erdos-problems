/-
# Generic Pair-Gadget Helpers

The packing-bound arguments in `VanDoorn.lean`, `UpperBoundImprovement.lean`,
and elsewhere all need three structural facts about a pair `{x, y}`:

1. `|{x, y}| = 2` (when `x ≠ y`).
2. `{x, y} ⊆ [1, N]` (when both elements lie in `[1, N]`).
3. For any pair-free `A` and any unit-fraction pair `(x, y)`, `|{x, y} ∩ A| ≤ 1`.

These are GENERIC and reused across every concrete forbidden-pair family
(`{3a, 6a}`, `{4a, 12a}`, `{6m, 30m}`, etc.). This file extracts them as
public lemmas so multiple files can share them without duplication.
-/

import Erdos.UnitFractionPairs.Statement

namespace UnitFractionPairs

/-- For distinct `x, y`, the pair `{x, y}` has cardinality `2`. -/
theorem pair_card_eq_two {x y : ℕ} (h : x ≠ y) :
    ({x, y} : Finset ℕ).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simp; exact h), Finset.card_singleton]

/-- For `x, y` both in `[1, N]`, the pair `{x, y}` is contained in `[1, N]`. -/
theorem pair_subset_Icc {x y N : ℕ} (hx_lo : 1 ≤ x) (hx_hi : x ≤ N)
    (hy_lo : 1 ≤ y) (hy_hi : y ≤ N) :
    ({x, y} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> rw [Finset.mem_Icc] <;> omega

/-- For a pair-free set `A` and a unit-fraction pair `(x, y)` with `x ≠ y`,
the intersection `{x, y} ∩ A` has at most `1` element. -/
theorem pair_inter_card_le_one_of_pair {A : Finset ℕ} (hA : PairFree A)
    {x y : ℕ} (hxy : IsUnitFractionPair x y) (hne : x ≠ y) :
    (({x, y} : Finset ℕ) ∩ A).card ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  have h_card_ge : (({x, y} : Finset ℕ) ∩ A).card ≥ 2 := by omega
  have h_sub : ({x, y} : Finset ℕ) ∩ A ⊆ ({x, y} : Finset ℕ) :=
    Finset.inter_subset_left
  have h_card_le : (({x, y} : Finset ℕ) ∩ A).card ≤ ({x, y} : Finset ℕ).card :=
    Finset.card_le_card h_sub
  rw [pair_card_eq_two hne] at h_card_le
  have h_eq : (({x, y} : Finset ℕ) ∩ A).card = 2 := by omega
  -- Both x, y ∈ A: from |{x,y} ∩ A| = 2 = |{x,y}|, the intersection IS {x,y}.
  have h_both : ({x, y} : Finset ℕ) ⊆ A :=
    (Finset.eq_of_subset_of_card_le h_sub (by rw [pair_card_eq_two hne, h_eq])).symm ▸
      Finset.inter_subset_right
  have hxA : x ∈ A := h_both (by simp)
  have hyA : y ∈ A := h_both (by simp)
  exact hA x hxA y hyA hne hxy

end UnitFractionPairs
