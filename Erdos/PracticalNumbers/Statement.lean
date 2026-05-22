/-
# Erdős Problem 18: Practical Numbers

A positive integer `m` is *practical* if every integer `n` with
`1 ≤ n ≤ m` can be written as a sum of distinct divisors of `m`.

For a practical number `m`, Erdős asks for small uniform bounds `h(m)` on how
many divisors are needed in these representations, especially for infinitely
many practical numbers and for factorials.

Reference: https://www.erdosproblems.com/18
-/
import Mathlib

namespace PracticalNumbers

/-- `DivisorRepresentation m n` means that `n` is a sum of distinct divisors
of `m`. The finset `S` records exactly which divisors are used, so distinctness
is built into the finite-set representation. -/
def DivisorRepresentation (m n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ m.divisors ∧ S.sum id = n

/-- `BoundedDivisorRepresentation m k n` means that `n` is represented as a sum
of at most `k` distinct divisors of `m`. -/
def BoundedDivisorRepresentation (m k n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ m.divisors ∧ S.card ≤ k ∧ S.sum id = n

/-- A practical number is positive and represents every target
`1 ≤ n ≤ m` as a sum of distinct divisors. Including the endpoint is equivalent
to the page's `n < m` convention for positive `m`, since `m` itself is a
divisor, and it matches the usual definition of the auxiliary quantity `h(m)`. -/
def IsPractical (m : ℕ) : Prop :=
  0 < m ∧ ∀ n : ℕ, 1 ≤ n → n ≤ m → DivisorRepresentation m n

/-- `hBound m k` says that `m` is practical and `k` divisors always suffice in
the defining range `1 ≤ n ≤ m`. -/
def hBound (m k : ℕ) : Prop :=
  IsPractical m ∧ ∀ n : ℕ, 1 ≤ n → n ≤ m → BoundedDivisorRepresentation m k n

/-- `hValue m k` packages the assertion that `k` is the least uniform divisor
count bound for `m`. This is the formal version of the quantity called `h(m)`
on the problem page. -/
def hValue (m k : ℕ) : Prop :=
  hBound m k ∧ ∀ j : ℕ, hBound m j → k ≤ j

/-- A flexible finite version of the "infinitely many practical numbers with
small `h`" question: the function `bound` can later be instantiated with a
concrete polylogarithmic majorant. -/
def InfinitelyManyPracticalWithHAtMost (bound : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ m k : ℕ, N < m ∧ hValue m k ∧ k ≤ bound m

/-- A flexible factorial version of Erdős's question: eventually `h(n!)` is at
most the chosen comparison function `bound n`. -/
def FactorialHEventuallyAtMost (bound : ℕ → ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ k : ℕ, hValue n.factorial k ∧ k ≤ bound n

end PracticalNumbers
