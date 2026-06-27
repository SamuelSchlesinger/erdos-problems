import Erdos.SquarefreePowerTwo.Statement

/- 
# Elementary Facts for Erdős Problem 11

This file records basic witness constructors and threshold bookkeeping for the
squarefree-plus-power-of-two representation in problem `#11`.

Reference: https://www.erdosproblems.com/11
-/

namespace SquarefreePowerTwo

/-- Unfolding the representation predicate gives exactly the expected witnesses:
a squarefree number and an exponent of `2`. -/
theorem hasSquarefreePowerTwoRepresentation_iff {n : ℕ} :
    HasSquarefreePowerTwoRepresentation n ↔
      ∃ q k : ℕ, Squarefree q ∧ n = q + 2 ^ k :=
  Iff.rfl

/-- A squarefree number `q` immediately gives a representation of
`q + 2 ^ k`. -/
theorem hasSquarefreePowerTwoRepresentation_add_pow_two {q k : ℕ}
    (hq : Squarefree q) :
    HasSquarefreePowerTwoRepresentation (q + 2 ^ k) := ⟨q, k, hq, rfl⟩

/-- Access a squarefree witness from any representation. -/
theorem HasSquarefreePowerTwoRepresentation.exists_squarefree {n : ℕ}
    (h : HasSquarefreePowerTwoRepresentation n) :
    ∃ q : ℕ, Squarefree q ∧ ∃ k : ℕ, n = q + 2 ^ k := by
  rcases h with ⟨q, k, hq, hsum⟩
  exact ⟨q, hq, k, hsum⟩

/-- Access the exponent witness from any representation. -/
theorem HasSquarefreePowerTwoRepresentation.exists_power {n : ℕ}
    (h : HasSquarefreePowerTwoRepresentation n) :
    ∃ k : ℕ, ∃ q : ℕ, Squarefree q ∧ n = q + 2 ^ k := by
  rcases h with ⟨q, k, hq, hsum⟩
  exact ⟨k, q, hq, hsum⟩

/-- In every representation, the power-of-two summand is at most the represented
integer. -/
theorem HasSquarefreePowerTwoRepresentation.exists_power_le {n : ℕ}
    (h : HasSquarefreePowerTwoRepresentation n) :
    ∃ k : ℕ, 2 ^ k ≤ n := by
  rcases h with ⟨q, k, _hq, rfl⟩
  exact ⟨k, Nat.le_add_left (2 ^ k) q⟩

/-- The threshold form for odd integers is monotone in the threshold: once all
odd `n ≥ N` are representable, the same is true above any larger `M`. -/
theorem OddRepresentableFrom.mono {N M : ℕ}
    (hN : OddRepresentableFrom N) (hNM : N ≤ M) :
    OddRepresentableFrom M := by
  intro n hMn hnodd
  exact hN n (hNM.trans hMn) hnodd

/-- The eventual odd statement can be repackaged with any larger threshold. -/
theorem eventuallyOddRepresentable_of_threshold {N : ℕ}
    (hN : OddRepresentableFrom N) :
    EventuallyOddRepresentable := ⟨N, hN⟩

/-- The threshold form for the `4 ∤ n` variant is monotone in the threshold. -/
theorem NotDivisibleByFourRepresentableFrom.mono {N M : ℕ}
    (hN : NotDivisibleByFourRepresentableFrom N) (hNM : N ≤ M) :
    NotDivisibleByFourRepresentableFrom M := by
  intro n hMn hfour
  exact hN n (hNM.trans hMn) hfour

/-- The eventual `4 ∤ n` variant can be repackaged from a concrete threshold. -/
theorem eventuallyNotDivisibleByFourRepresentable_of_threshold {N : ℕ}
    (hN : NotDivisibleByFourRepresentableFrom N) :
    EventuallyNotDivisibleByFourRepresentable := ⟨N, hN⟩

/-- Every odd eventual threshold also works as an `Erdos11` proof, by definition
of the main package. -/
theorem erdos11_of_eventuallyOddRepresentable
    (h : EventuallyOddRepresentable) : Erdos11 := h

/-- The integer `3` has the representation `3 = 1 + 2 ^ 1`. -/
theorem hasSquarefreePowerTwoRepresentation_three :
    HasSquarefreePowerTwoRepresentation 3 := by
  refine ⟨1, 1, ?_, ?_⟩ <;> norm_num

/-- The integer `5` has the representation `5 = 1 + 2 ^ 2`. -/
theorem hasSquarefreePowerTwoRepresentation_five :
    HasSquarefreePowerTwoRepresentation 5 := by
  refine ⟨1, 2, ?_, ?_⟩ <;> norm_num

/-- The integer `7` has the representation `7 = 5 + 2 ^ 1`. -/
theorem hasSquarefreePowerTwoRepresentation_seven :
    HasSquarefreePowerTwoRepresentation 7 := by
  refine ⟨5, 1, ?_, ?_⟩
  · exact (show Nat.Prime 5 by norm_num).squarefree
  · norm_num

end SquarefreePowerTwo
