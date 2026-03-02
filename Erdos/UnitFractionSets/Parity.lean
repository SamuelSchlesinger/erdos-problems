/-
# Parity and Sum-Free Sets

The odd numbers are NOT sum-free (unlike the triple case):
1/3 = 1/5 + 1/9 + 1/45 gives a concrete counterexample with all
elements odd and distinct.

This corrects the intuition that the parity obstruction for triples
(Problem #302, `no_triple_both_odd`) lifts to arbitrary-length sums
(Problem #301). It does not: the parity argument only blocks
representations with an EVEN number of terms.

The identity 1/3 = 1/5 + 1/9 + 1/45 uses k = 3 (odd number of terms),
which is exactly where the parity obstruction fails.

Reference: https://www.erdosproblems.com/301
-/
import Erdos.UnitFractionSets.Statement

namespace UnitFractionSets

/-- **Odd numbers are NOT sum-free.**

    The identity 1/3 = 1/5 + 1/9 + 1/45 shows that a set of four
    distinct odd numbers can violate the sum-free property.

    Verification: 1/5 + 1/9 + 1/45 = 9/45 + 5/45 + 1/45 = 15/45 = 1/3. ✓

    This contrasts with the triple-free case (Problem #302), where
    odd numbers are always triple-free (`no_triple_both_odd`). The
    difference: the parity obstruction works for k = 2 (even) but
    fails for k = 3 (odd). Clearing denominators in 1/a = Σ 1/bᵢ
    gives ∏ bⱼ = a · Σᵢ ∏_{j≠i} bⱼ, where both sides are odd when
    all elements are odd and k is odd, so no contradiction arises. -/
theorem odd_not_sum_free :
    ∃ (A : Finset ℕ), (∀ a ∈ A, ¬Even a) ∧ ¬SumFree A := by
  refine ⟨{3, 5, 9, 45}, ?_, ?_⟩
  · -- All elements are odd
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · -- Not sum-free: 1/3 = 1/5 + 1/9 + 1/45
    intro hsf
    -- Build the witness: a = 3, S = {5, 9, 45}
    have hS : ({5, 9, 45} : Finset ℕ) ⊆ ({3, 5, 9, 45} : Finset ℕ).erase 3 := by
      intro x hx
      rw [Finset.mem_erase]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> omega
    have hne : ({5, 9, 45} : Finset ℕ).Nonempty := ⟨5, by simp⟩
    -- The key equation: 1/3 = 1/5 + 1/9 + 1/45
    have heq : (1 / 3 : ℚ) = ∑ b ∈ ({5, 9, 45} : Finset ℕ), (1 / b : ℚ) := by
      rw [show ({5, 9, 45} : Finset ℕ) = insert 5 (insert 9 {45}) from rfl]
      rw [Finset.sum_insert (show (5 : ℕ) ∉ insert 9 ({45} : Finset ℕ) by decide)]
      rw [Finset.sum_insert (show (9 : ℕ) ∉ ({45} : Finset ℕ) by decide)]
      rw [Finset.sum_singleton]
      push_cast
      norm_num
    exact absurd heq (hsf 3 (by simp) {5, 9, 45} hS hne)

end UnitFractionSets
