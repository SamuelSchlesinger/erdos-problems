/- 
# Erdős Problem 364: Consecutive Powerful Triples

Erdős asked whether there are any triples of consecutive positive integers all
of which are powerful, i.e. every prime divisor appears to exponent at least
two.

Mahler observed that consecutive powerful *pairs* exist infinitely often, so
the length-three case is the first rigid obstruction problem.

Reference: https://www.erdosproblems.com/364
-/
import Mathlib

namespace ConsecutivePowerful

/-- A positive natural number is *powerful* if every prime divisor divides it
    to second order. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- `n` starts a triple of consecutive powerful numbers. -/
def ConsecutivePowerfulTriple (n : ℕ) : Prop :=
  Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2)

/-- Erdős problem #364 asks whether such a triple exists. -/
def ConsecutivePowerfulTripleExists : Prop :=
  ∃ n : ℕ, ConsecutivePowerfulTriple n

end ConsecutivePowerful
