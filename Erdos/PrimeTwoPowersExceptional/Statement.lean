import Mathlib

/-!
# Erdős Problem 9: Prime Plus Two Powers of Two

Let `A` be the set of all odd integers at least `1` which are not of the form
`p + 2^k + 2^l`, where `p` is prime and `k,l >= 0`.  Erdős asked whether the
upper density of `A` is positive.

This file records the statement-level objects: the representation predicate,
the exceptional set, a counting function, and a tail formulation of positive
upper density.

Reference: https://www.erdosproblems.com/9
-/

namespace PrimeTwoPowersExceptional

/--
`Representable n` means that `n` has the form `p + 2^k + 2^l`, with `p` prime
and `k,l` natural numbers.  Since exponents are natural numbers, this is exactly
the condition `k,l >= 0` from the problem statement.
-/
def Representable (n : ℕ) : Prop :=
  ∃ p k l : ℕ, Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l

/--
The exceptional predicate from Erdős problem `#9`: `n` is odd, at least `1`, and
has no representation as a prime plus two powers of two.
-/
def Exceptional (n : ℕ) : Prop :=
  Odd n ∧ 1 ≤ n ∧ ¬ Representable n

/-- The exceptional set `A` from Erdős problem `#9`. -/
def exceptionalSet : Set ℕ :=
  {n | Exceptional n}

@[simp] theorem mem_exceptionalSet {n : ℕ} :
    n ∈ exceptionalSet ↔ Exceptional n :=
  Iff.rfl

/--
`countUpTo S N` is the number of elements of `S` in the interval `[1, N]`.
It is noncomputable because it uses `Set.ncard`, rather than a decidable filter
over the unbounded predicate defining this problem.
-/
noncomputable def countUpTo (S : Set ℕ) (N : ℕ) : ℕ :=
  (S ∩ Set.Icc 1 N).ncard

/-- The counting function for the exceptional set of problem `#9`. -/
noncomputable def exceptionalCountUpTo (N : ℕ) : ℕ :=
  countUpTo exceptionalSet N

/--
A direct tail formulation of positive upper density: some positive constant `c`
is achieved by the normalized counting function along arbitrarily large values
of `n`.
-/
def UpperDensityPositive (S : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
    c ≤ ((countUpTo S n : ℝ) / (n : ℝ))

/-- Erdős problem `#9`: is the upper density of the exceptional set positive? -/
def Erdos9Question : Prop :=
  UpperDensityPositive exceptionalSet

end PrimeTwoPowersExceptional
