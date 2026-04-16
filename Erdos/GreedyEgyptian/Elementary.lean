import Erdos.GreedyEgyptian.Statement

/- 
# Elementary Facts About Restricted Greedy Egyptian Fractions

This file records the first structural facts for problem `#282`: the minimal
greedy choice is unique, every positive greedy step keeps the remainder
nonnegative and strictly decreases the current value, the odd numbers form an
infinite denominator set, and every unit fraction `1 / n` with `n ∈ A`
terminates in one greedy step. In particular, every odd unit fraction already
lies in the terminating region for Stein's odd-denominator problem.
-/
namespace GreedyEgyptian

@[simp] theorem mem_oddNumbers {n : ℕ} :
    n ∈ OddNumbers ↔ Odd n := by
  rfl

/-- Minimal greedy choices are unique. -/
theorem greedyChoice_unique {A : Set ℕ} {x : ℚ} {m n : ℕ}
    (hm : GreedyChoice A x m) (hn : GreedyChoice A x n) :
    m = n := by
  apply le_antisymm
  · exact hm.2 n hn.1.1 hn.1.2
  · exact hn.2 m hm.1.1 hm.1.2

/-- For a positive input, every greedy choice has positive denominator. -/
theorem greedyChoice_pos {A : Set ℕ} {x : ℚ} {n : ℕ}
    (hx : 0 < x) (h : GreedyChoice A x n) :
    0 < n := by
  have hix : 0 < (1 : ℚ) / x := by
    positivity
  have hnq : (0 : ℚ) < n := lt_of_lt_of_le hix h.1.2
  exact_mod_cast hnq

/-- The eligible bound `1 / x ≤ n` is equivalent to `1 / n ≤ x` once `x > 0`
and `n > 0`. -/
theorem one_div_le_of_greedyChoice {A : Set ℕ} {x : ℚ} {n : ℕ}
    (hx : 0 < x) (h : GreedyChoice A x n) :
    (1 : ℚ) / n ≤ x := by
  have hnq : 0 < (n : ℚ) := by
    exact_mod_cast greedyChoice_pos hx h
  exact (one_div_le hx hnq).mp h.1.2

/-- A positive greedy step never overshoots below `0`. -/
theorem greedyRemainder_nonneg {A : Set ℕ} {x : ℚ} {n : ℕ}
    (hx : 0 < x) (h : GreedyChoice A x n) :
    0 ≤ GreedyRemainder x n := by
  have hle : (1 : ℚ) / n ≤ x := one_div_le_of_greedyChoice hx h
  unfold GreedyRemainder
  linarith

/-- A positive greedy step strictly decreases the current value. -/
theorem greedyRemainder_lt_self {A : Set ℕ} {x : ℚ} {n : ℕ}
    (hx : 0 < x) (h : GreedyChoice A x n) :
    GreedyRemainder x n < x := by
  have hnq : 0 < (n : ℚ) := by
    exact_mod_cast greedyChoice_pos hx h
  have hdiv : (0 : ℚ) < 1 / n := by
    positivity
  unfold GreedyRemainder
  linarith

/-- Consequently any positive greedy step lands in the nonnegative reals. -/
theorem step_nonneg {A : Set ℕ} {x y : ℚ} (hx : 0 < x)
    (hstep : GreedyStep A x y) :
    0 ≤ y := by
  rcases hstep with ⟨n, hchoice, rfl⟩
  exact greedyRemainder_nonneg hx hchoice

/-- Consequently any positive greedy step strictly decreases the current input. -/
theorem step_lt_self {A : Set ℕ} {x y : ℚ} (hx : 0 < x)
    (hstep : GreedyStep A x y) :
    y < x := by
  rcases hstep with ⟨n, hchoice, rfl⟩
  exact greedyRemainder_lt_self hx hchoice

/-- The odd numbers form an infinite denominator set. -/
theorem oddNumbers_infinite : Set.Infinite OddNumbers := by
  have hrange : Set.Infinite (Set.range fun k : ℕ => 2 * k + 1) :=
    Set.infinite_range_of_injective (fun m n hmn => by omega)
  refine hrange.mono ?_
  rintro _ ⟨k, rfl⟩
  exact odd_two_mul_add_one k

/-- An odd unit fraction has odd reduced denominator. -/
theorem hasOddDenominator_unitFraction {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) :
    HasOddDenominator (1 / n : ℚ) := by
  rw [HasOddDenominator, one_div, Rat.inv_natCast_den_of_pos hn]
  exact hodd

/-- If `x = 1 / n` and `n ∈ A`, then the greedy algorithm immediately chooses
`n`. -/
theorem greedyChoice_unitFraction {A : Set ℕ} {n : ℕ}
    (hn : 0 < n) (hA : n ∈ A) :
    GreedyChoice A (1 / n : ℚ) n := by
  refine ⟨⟨hA, ?_⟩, ?_⟩
  · have h : ((1 : ℚ) / (1 / n : ℚ)) = n := by
      field_simp [hn.ne']
    rw [h]
  · intro m hmA hm
    have h : ((1 : ℚ) / (1 / n : ℚ)) = n := by
      field_simp [hn.ne']
    rw [h] at hm
    exact_mod_cast hm

/-- A unit fraction `1 / n` with `n ∈ A` takes one greedy step to `0`. -/
theorem greedyStep_unitFraction {A : Set ℕ} {n : ℕ}
    (hn : 0 < n) (hA : n ∈ A) :
    GreedyStep A (1 / n : ℚ) 0 := by
  refine ⟨n, greedyChoice_unitFraction hn hA, ?_⟩
  unfold GreedyRemainder
  ring_nf

/-- Therefore every unit fraction `1 / n` with `n ∈ A` terminates in one step. -/
theorem greedyTerminatesIn_one_unitFraction {A : Set ℕ} {n : ℕ}
    (hn : 0 < n) (hA : n ∈ A) :
    GreedyTerminatesIn A 1 (1 / n : ℚ) := by
  exact GreedyTerminatesIn.succ (greedyStep_unitFraction hn hA)
    GreedyTerminatesIn.zero

/-- Consequently every unit fraction `1 / n` with `n ∈ A` lies in the
terminating region. -/
theorem greedyTerminates_unitFraction {A : Set ℕ} {n : ℕ}
    (hn : 0 < n) (hA : n ∈ A) :
    GreedyTerminates A (1 / n : ℚ) := by
  exact ⟨1, greedyTerminatesIn_one_unitFraction hn hA⟩

/-- In particular, every odd unit fraction terminates on the odd numbers. -/
theorem greedyTerminates_odd_unitFraction {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) :
    GreedyTerminates OddNumbers (1 / n : ℚ) := by
  exact greedyTerminates_unitFraction hn (by simpa [OddNumbers] using hodd)

/-- This places every odd unit fraction inside the general terminating-pairs
set from problem `#282`. -/
theorem oddUnitFraction_mem_terminatingPairs {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) :
    ((1 / n : ℚ), OddNumbers) ∈ TerminatingPairs := by
  simpa [TerminatingPairs] using greedyTerminates_odd_unitFraction hn hodd

end GreedyEgyptian
