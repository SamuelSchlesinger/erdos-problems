/- 
# Modular Obstructions for Consecutive Powerful Triples

This file records the first local obstructions for Erdős problem #364. They do
not solve the problem, but they show that any hypothetical triple of
consecutive powerful numbers is forced into very sparse residue classes.
-/
import Erdos.ConsecutivePowerful.Statement

namespace ConsecutivePowerful

/-- A number congruent to `2 mod 4` cannot be powerful: it is divisible by `2`
    but not by `2^2`. -/
theorem not_powerful_of_mod_four_eq_two {n : ℕ} (hmod : n % 4 = 2) :
    ¬Powerful n := by
  intro hn
  have h2 : 2 ∣ n := by omega
  have h4 : 4 ∣ n := by
    have hsquare := hn.2 2 Nat.prime_two h2
    simpa using hsquare
  omega

/-- **Trivial local obstruction.**

There are no four consecutive powerful numbers, because one of them must be
`2 mod 4`. -/
theorem no_four_consecutive_powerful (n : ℕ) :
    ¬(Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) ∧ Powerful (n + 3)) := by
  intro hfour
  have hm4lt : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hm4 : n % 4
  · exact not_powerful_of_mod_four_eq_two (n := n + 2) (by omega) hfour.2.2.1
  · exact not_powerful_of_mod_four_eq_two (n := n + 1) (by omega) hfour.2.1
  · exact not_powerful_of_mod_four_eq_two (n := n) hm4 hfour.1
  · exact not_powerful_of_mod_four_eq_two (n := n + 3) (by omega) hfour.2.2.2

/-- In any hypothetical consecutive powerful triple, the starting point must be
    `3 mod 4`. Equivalently, the middle term is the unique even term and is
    divisible by `4`. -/
theorem consecutive_powerful_triple_mod_four {n : ℕ}
    (htriple : ConsecutivePowerfulTriple n) :
    n % 4 = 3 := by
  have hm4lt : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hm4 : n % 4
  · exfalso
    exact not_powerful_of_mod_four_eq_two (n := n + 2) (by omega) htriple.2.2
  · exfalso
    exact not_powerful_of_mod_four_eq_two (n := n + 1) (by omega) htriple.2.1
  · exfalso
    exact not_powerful_of_mod_four_eq_two (n := n) hm4 htriple.1
  · omega

/-- In any hypothetical consecutive powerful triple, the unique multiple of `3`
    among `n`, `n+1`, `n+2` is automatically a multiple of `9`. This forces the
    start to lie in one of three residue classes modulo `9`. -/
theorem consecutive_powerful_triple_mod_nine {n : ℕ}
    (htriple : ConsecutivePowerfulTriple n) :
    n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
  have hm3lt : n % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hm3 : n % 3
  · left
    have h3 : 3 ∣ n := by omega
    have h9 : 9 ∣ n := by
      have hsquare := htriple.1.2 3 Nat.prime_three h3
      simpa using hsquare
    omega
  · right
    left
    have h3 : 3 ∣ n + 2 := by omega
    have h9 : 9 ∣ n + 2 := by
      have hsquare := htriple.2.2.2 3 Nat.prime_three h3
      simpa using hsquare
    omega
  · right
    right
    have h3 : 3 ∣ n + 1 := by omega
    have h9 : 9 ∣ n + 1 := by
      have hsquare := htriple.2.1.2 3 Nat.prime_three h3
      simpa using hsquare
    omega

/-- **First combined residue obstruction.**

Any hypothetical triple of consecutive powerful numbers must start in one of
the three residue classes `7`, `27`, or `35` modulo `36`. This is the Chinese
remainder combination of the mod-`4` and mod-`9` obstructions. -/
theorem consecutive_powerful_triple_mod_thirtysix {n : ℕ}
    (htriple : ConsecutivePowerfulTriple n) :
    n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 := by
  have h4 : n % 4 = 3 := consecutive_powerful_triple_mod_four htriple
  have h9 : n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8 :=
    consecutive_powerful_triple_mod_nine htriple
  omega

end ConsecutivePowerful
