import Erdos.InverseGoldbach.Statement

open Set

/-!
# Elementary Parity Obstructions for the Inverse Goldbach Problem

If `A + B` eventually agrees with the prime numbers, then it cannot contain
arbitrarily large even integers. This immediately rules out the possibility that
both `A` and `B` contain infinitely many even elements, or that both contain
infinitely many odd elements.
-/
namespace InverseGoldbach

/-- A set which eventually agrees with the primes contains no sufficiently large
even number. -/
theorem agreesWithPrimesEventually_no_large_even {S : Set ℕ}
    (hS : AgreesWithPrimesEventually S) :
    ∃ N, ∀ n ≥ N, Even n → n ∉ S := by
  rcases hS with ⟨N, hN⟩
  refine ⟨max N 3, ?_⟩
  intro n hn hEven hnS
  have hprime : Nat.Prime n := (hN n (le_trans (le_max_left N 3) hn)).1 hnS
  have hge3 : 3 ≤ n := le_trans (le_max_right N 3) hn
  have hne2 : n ≠ 2 := by
    omega
  have hodd : Odd n := hprime.odd_of_ne_two hne2
  exact (Nat.not_even_iff_odd.mpr hodd) hEven

/-- If both `A` and `B` contain infinitely many even elements, then `A + B`
contains arbitrarily large even numbers. -/
theorem exists_large_even_of_infinite_even_parts {A B : Set ℕ}
    (hA : (evenPart A).Infinite) (hB : (evenPart B).Infinite) :
    ∀ N, ∃ n ≥ N, n ∈ pairSumset A B ∧ Even n := by
  intro N
  obtain ⟨a, ha, hagt⟩ := (Set.infinite_iff_exists_gt.mp hA) N
  obtain ⟨b, hb⟩ := hB.nonempty
  refine ⟨a + b, le_trans (Nat.le_of_lt hagt) (Nat.le_add_right a b), ?_, ?_⟩
  · exact ⟨a, ha.1, b, hb.1, rfl⟩
  · exact ha.2.add hb.2

/-- If both `A` and `B` contain infinitely many odd elements, then `A + B`
contains arbitrarily large even numbers. -/
theorem exists_large_even_of_infinite_odd_parts {A B : Set ℕ}
    (hA : (oddPart A).Infinite) (hB : (oddPart B).Infinite) :
    ∀ N, ∃ n ≥ N, n ∈ pairSumset A B ∧ Even n := by
  intro N
  obtain ⟨a, ha, hagt⟩ := (Set.infinite_iff_exists_gt.mp hA) N
  obtain ⟨b, hb⟩ := hB.nonempty
  refine ⟨a + b, le_trans (Nat.le_of_lt hagt) (Nat.le_add_right a b), ?_, ?_⟩
  · exact ⟨a, ha.1, b, hb.1, rfl⟩
  · exact ha.2.add_odd hb.2

/-- An eventual-prime sumset cannot have infinitely many even summands on both
sides. -/
theorem not_both_infinite_even_of_eventually_primes {A B : Set ℕ}
    (hAB : AgreesWithPrimesEventually (pairSumset A B)) :
    ¬ ((evenPart A).Infinite ∧ (evenPart B).Infinite) := by
  rintro ⟨hA, hB⟩
  obtain ⟨N, hN⟩ := agreesWithPrimesEventually_no_large_even hAB
  obtain ⟨n, hn, hmem, hEven⟩ := exists_large_even_of_infinite_even_parts hA hB N
  exact hN n hn hEven hmem

/-- An eventual-prime sumset cannot have infinitely many odd summands on both
sides. -/
theorem not_both_infinite_odd_of_eventually_primes {A B : Set ℕ}
    (hAB : AgreesWithPrimesEventually (pairSumset A B)) :
    ¬ ((oddPart A).Infinite ∧ (oddPart B).Infinite) := by
  rintro ⟨hA, hB⟩
  obtain ⟨N, hN⟩ := agreesWithPrimesEventually_no_large_even hAB
  obtain ⟨n, hn, hmem, hEven⟩ := exists_large_even_of_infinite_odd_parts hA hB N
  exact hN n hn hEven hmem

/-- Combined parity obstruction: an eventual-prime sumset cannot have the same
parity appear infinitely often on both sides. -/
theorem parity_obstruction_of_eventually_primes {A B : Set ℕ}
    (hAB : AgreesWithPrimesEventually (pairSumset A B)) :
    ¬ ((evenPart A).Infinite ∧ (evenPart B).Infinite) ∧
      ¬ ((oddPart A).Infinite ∧ (oddPart B).Infinite) := by
  exact ⟨not_both_infinite_even_of_eventually_primes hAB,
    not_both_infinite_odd_of_eventually_primes hAB⟩

end InverseGoldbach
