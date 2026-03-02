/-
# The Cambie Construction is NOT Sum-Free

Stijn Cambie's 5/8 construction for triple-free sets (Problem #302)
does NOT lift to sum-free sets (Problem #301).

The Cambie set: odd integers in {1, …, ⌊N/4⌋} together with the
upper half {⌊N/2⌋+1, …, N}.

For triples (k = 2), this set is protected by two independent barriers:
- **Parity**: odd + odd = even ≠ divides odd × odd = odd
- **Magnitude**: elements > N/2 have reciprocals < 2/N, too small to pair up

For sum-free violations with k ≥ 3 terms, BOTH barriers break down:
- Parity fails for odd k (sum of odd-many odd products is odd, no contradiction)
- Magnitude fails because three reciprocals from (N/2, N] can sum to ≥ 4/N

Counterexample: 1/15 = 1/36 + 1/45 + 1/60, where a = 15 is odd and ≤ N/4 = 15
for N = 60, and b₁ = 36, b₂ = 45, b₃ = 60 are all in (30, 60].

This demonstrates a genuine structural gap between Problems #301 and #302.

Reference: https://www.erdosproblems.com/301
-/
import Erdos.UnitFractionSets.Statement
import Erdos.UnitFractionTriples.Cambie

namespace UnitFractionSets

open UnitFractionTriples

/-- **The Cambie set is NOT sum-free for N = 60.**

    The identity 1/15 = 1/36 + 1/45 + 1/60 provides a concrete
    sum-free violation in `cambieSet 60`:

    - 15 is odd and in {1, …, 15} = {1, …, ⌊60/4⌋}
    - 36, 45, 60 ∈ {31, …, 60} = {⌊60/2⌋+1, …, 60}

    Verification: 1/36 + 1/45 + 1/60 = 5/180 + 4/180 + 3/180 = 12/180 = 1/15. ✓

    This shows the Cambie 5/8 lower bound for triple-free sets
    (Problem #302) does NOT transfer to sum-free sets (Problem #301).
    The obstruction uses k = 3 terms — exactly the regime where both
    the parity and magnitude barriers break down. -/
theorem cambie_not_sum_free : ¬SumFree (cambieSet 60) := by
  intro hsf
  -- Step 1: 15 ∈ cambieSet 60 (odd, in Icc 1 15)
  have h15 : 15 ∈ cambieSet 60 := by
    simp only [cambieSet, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    left; constructor
    · omega
    · decide
  -- Step 2: {36, 45, 60} ⊆ (cambieSet 60).erase 15
  have hS : ({36, 45, 60} : Finset ℕ) ⊆ (cambieSet 60).erase 15 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    constructor
    · rcases hx with rfl | rfl | rfl <;> omega
    · simp only [cambieSet, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      rcases hx with rfl | rfl | rfl <;> right <;> omega
  -- Step 3: S is nonempty
  have hne : ({36, 45, 60} : Finset ℕ).Nonempty := ⟨36, by simp⟩
  -- Step 4: 1/15 = 1/36 + 1/45 + 1/60
  have heq : (1 / 15 : ℚ) = ∑ b ∈ ({36, 45, 60} : Finset ℕ), (1 / b : ℚ) := by
    rw [show ({36, 45, 60} : Finset ℕ) = insert 36 (insert 45 {60}) from rfl]
    rw [Finset.sum_insert (show (36 : ℕ) ∉ insert 45 ({60} : Finset ℕ) by decide)]
    rw [Finset.sum_insert (show (45 : ℕ) ∉ ({60} : Finset ℕ) by decide)]
    rw [Finset.sum_singleton]
    push_cast; norm_num
  -- Contradiction with sum-free hypothesis
  exact absurd heq (hsf 15 h15 {36, 45, 60} hS hne)

/-- **The Cambie set fails for infinitely many N.**

    For any odd m ≥ 1, the scaled identity
    1/(15m) = 1/(36m) + 1/(45m) + 1/(60m)
    sits inside `cambieSet (60 * m)`, since:

    - 15m is odd (product of odd numbers) and 15m ≤ (60m)/4 = 15m
    - 36m, 45m, 60m > (60m)/2 = 30m and ≤ 60m

    This shows the Cambie construction is NOT an isolated failure at N = 60
    but fails for all N = 60m with m odd (N = 60, 180, 300, 420, …). -/
theorem cambie_not_sum_free_family (m : ℕ) (hm : 0 < m) (hm_odd : ¬Even m) :
    ¬SumFree (cambieSet (60 * m)) := by
  intro hsf
  -- Natural division facts
  have h4 : 60 * m / 4 = 15 * m := by omega
  have h2 : 60 * m / 2 = 30 * m := by omega
  -- Step 1: 15m ∈ cambieSet (60m) — odd and in Icc 1 (15m)
  have h15m : 15 * m ∈ cambieSet (60 * m) := by
    simp only [cambieSet, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, h4]
    left; constructor
    · omega
    · -- 15m is odd because 15 and m are both odd
      rw [Nat.not_even_iff_odd]
      exact Odd.mul (by decide : Odd 15) (Nat.not_even_iff_odd.mp hm_odd)
  -- Step 2: {36m, 45m, 60m} ⊆ (cambieSet (60m)).erase (15m)
  have hS : ({36 * m, 45 * m, 60 * m} : Finset ℕ) ⊆ (cambieSet (60 * m)).erase (15 * m) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    constructor
    · rcases hx with rfl | rfl | rfl <;> omega
    · simp only [cambieSet, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, h2]
      rcases hx with rfl | rfl | rfl <;> right <;> omega
  -- Step 3: S is nonempty
  have hne : ({36 * m, 45 * m, 60 * m} : Finset ℕ).Nonempty := ⟨36 * m, by simp⟩
  -- Step 4: 1/(15m) = 1/(36m) + 1/(45m) + 1/(60m)
  have heq : (1 / (15 * m) : ℚ) =
      ∑ b ∈ ({36 * m, 45 * m, 60 * m} : Finset ℕ), (1 / b : ℚ) := by
    have hm36 : (36 * m : ℕ) ∉ insert (45 * m) ({60 * m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hm45 : (45 * m : ℕ) ∉ ({60 * m} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    rw [show ({36 * m, 45 * m, 60 * m} : Finset ℕ) =
        insert (36 * m) (insert (45 * m) {60 * m}) from rfl]
    rw [Finset.sum_insert hm36, Finset.sum_insert hm45, Finset.sum_singleton]
    push_cast
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  have contra := hsf (15 * m) h15m {36 * m, 45 * m, 60 * m} hS hne
  push_cast [Nat.cast_mul] at contra
  exact absurd heq contra

/-- **Structural gap: the Cambie set is triple-free but not sum-free.**

    This is a direct corollary: `cambie_triple_free` shows the Cambie set
    always avoids triples, while `cambie_not_sum_free` exhibits a sum
    representation in `cambieSet 60`. This witnesses a genuine structural
    difference between Problems #302 and #301. -/
theorem cambie_triple_free_but_not_sum_free :
    TripleFree (cambieSet 60) ∧ ¬SumFree (cambieSet 60) :=
  ⟨cambie_triple_free 60, cambie_not_sum_free⟩

end UnitFractionSets
