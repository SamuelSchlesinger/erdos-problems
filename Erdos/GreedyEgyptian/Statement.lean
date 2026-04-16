/- 
# Erdős Problem 282: Greedy Egyptian Fractions with Restricted Denominators

Let `A ⊆ ℕ` and `x ∈ (0, 1) ∩ ℚ`. The restricted greedy Egyptian algorithm
chooses the least `n ∈ A` with `1 / x ≤ n` and replaces `x` by `x - 1 / n`.

Problem `#282` asks whether this process always terminates when `A` is the set
of odd numbers and `x` has odd denominator, and more generally asks for a
description of the terminating pairs `(x, A)`.

Reference: https://www.erdosproblems.com/282
-/
import Mathlib

namespace GreedyEgyptian

/-- A denominator `n ∈ A` is eligible for the greedy step at `x` if it lies in
`A` and is at least `1 / x`. -/
def EligibleDenom (A : Set ℕ) (x : ℚ) (n : ℕ) : Prop :=
  n ∈ A ∧ (1 : ℚ) / x ≤ n

/-- A greedy choice is an eligible denominator that is minimal among all
eligible denominators in `A`. -/
def GreedyChoice (A : Set ℕ) (x : ℚ) (n : ℕ) : Prop :=
  EligibleDenom A x n ∧ ∀ m, m ∈ A → (1 : ℚ) / x ≤ m → n ≤ m

/-- The remainder after subtracting `1 / n` from `x`. -/
def GreedyRemainder (x : ℚ) (n : ℕ) : ℚ :=
  x - 1 / n

/-- One greedy step replaces `x` by the remainder coming from a minimal
eligible denominator. -/
def GreedyStep (A : Set ℕ) (x y : ℚ) : Prop :=
  ∃ n : ℕ, GreedyChoice A x n ∧ y = GreedyRemainder x n

/-- The restricted greedy algorithm terminates in exactly `k` steps if repeated
greedy steps reduce the current value to `0` after `k` steps. -/
inductive GreedyTerminatesIn (A : Set ℕ) : ℕ → ℚ → Prop
  | zero : GreedyTerminatesIn A 0 0
  | succ {k : ℕ} {x y : ℚ} :
      GreedyStep A x y →
      GreedyTerminatesIn A k y →
      GreedyTerminatesIn A (k + 1) x

/-- The restricted greedy algorithm terminates at `x` if it terminates in some
finite number of steps. -/
def GreedyTerminates (A : Set ℕ) (x : ℚ) : Prop :=
  ∃ k : ℕ, GreedyTerminatesIn A k x

/-- The set of odd positive integers. This is Stein's special case in problem
`#282`. -/
def OddNumbers : Set ℕ := {n : ℕ | Odd n}

/-- A rational has odd denominator if its reduced denominator is odd. -/
def HasOddDenominator (x : ℚ) : Prop :=
  Odd (Rat.den x)

/-- Stein's special case of Erdős problem `#282`: the odd-denominator greedy
algorithm should terminate for every rational in `(0, 1)` with odd
denominator. -/
def SteinOddGreedyConjecture : Prop :=
  ∀ x : ℚ, 0 < x → x < 1 → HasOddDenominator x → GreedyTerminates OddNumbers x

/-- The set of all input pairs `(x, A)` on which the restricted greedy
algorithm terminates. The general form of problem `#282` asks for a useful
description of this set. -/
def TerminatingPairs : Set (ℚ × Set ℕ) :=
  {p | GreedyTerminates p.2 p.1}

end GreedyEgyptian
