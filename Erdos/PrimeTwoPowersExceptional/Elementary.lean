import Erdos.PrimeTwoPowersExceptional.Statement

/-!
# Elementary Facts for Erdős Problem 9

This file proves the first complete facts about the exceptional set for problem
`#9`: `1` is exceptional, exceptional numbers are odd, and represented numbers
are not exceptional.

Reference: https://www.erdosproblems.com/9
-/

namespace PrimeTwoPowersExceptional

/--
The integer `1` cannot be represented as `p + 2^k + 2^l`: a prime is at least
`2`, and each power of two is at least `1`, so every represented number is at
least `4`.
-/
theorem not_representable_one : ¬ Representable 1 := by
  rintro ⟨p, k, l, hp, hsum⟩
  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have hl1 : 1 ≤ 2 ^ l := Nat.one_le_pow l 2 (by norm_num)
  omega

/-- The first exceptional integer in Erdős problem `#9` is `1`. -/
theorem one_exceptional : Exceptional 1 := by
  refine ⟨?_, by norm_num, not_representable_one⟩
  norm_num

/-- Equivalently, `1` belongs to the exceptional set `A`. -/
theorem one_mem_exceptionalSet : 1 ∈ exceptionalSet :=
  one_exceptional

/-- Every exceptional number is odd, by definition of the exceptional set. -/
theorem odd_of_exceptional {n : ℕ} (hn : Exceptional n) : Odd n :=
  hn.1

/-- Every member of the exceptional set is odd. -/
theorem odd_of_mem_exceptionalSet {n : ℕ} (hn : n ∈ exceptionalSet) : Odd n :=
  odd_of_exceptional hn

/-- Exceptional numbers have no representation as a prime plus two powers of two. -/
theorem not_representable_of_exceptional {n : ℕ} (hn : Exceptional n) :
    ¬ Representable n :=
  hn.2.2

/-- A represented number is not exceptional. -/
theorem not_exceptional_of_representable {n : ℕ} (hn : Representable n) :
    ¬ Exceptional n := by
  intro hExceptional
  exact not_representable_of_exceptional hExceptional hn

/-- A represented number is not a member of the exceptional set. -/
theorem not_mem_exceptionalSet_of_representable {n : ℕ} (hn : Representable n) :
    n ∉ exceptionalSet :=
  not_exceptional_of_representable hn

end PrimeTwoPowersExceptional
