import Mathlib

/-!
# Erdős Problem 10: A Prime Plus Boundedly Many Powers of Two

Erdős asked whether there is a fixed natural number `k` such that every
sufficiently large integer can be written as a prime plus at most `k` powers of
`2`.

We model the finite collection of powers of two by a list of exponents.  This
allows repeated powers, so `[e, e]` represents the contribution `2^e + 2^e`.

Reference: https://www.erdosproblems.com/10
-/

namespace PrimeBoundedTwoPowers

/-- The sum of the powers of two whose exponents occur in the finite list
`exps`.  Lists are used only as a concrete finite container; the order of the
exponents has no mathematical significance here. -/
def twoPowerSum (exps : List ℕ) : ℕ :=
  (exps.map fun e => 2 ^ e).sum

/-- `PrimePlusPowersOfTwoRep k n` says that `n` is a prime plus at most `k`
powers of two.  The list `exps` records the powers `2^e` that are used, with
multiplicity. -/
def PrimePlusPowersOfTwoRep (k n : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ ∃ exps : List ℕ,
    exps.length ≤ k ∧ p + twoPowerSum exps = n

/-- A representation using exactly `m` powers of two. -/
def PrimePlusExactlyPowersOfTwoRep (m n : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ ∃ exps : List ℕ,
    exps.length = m ∧ p + twoPowerSum exps = n

/-- A representation as a prime plus exactly two powers of two. -/
abbrev PrimePlusExactlyTwoPowersRep (n : ℕ) : Prop :=
  PrimePlusExactlyPowersOfTwoRep 2 n

/-- For a fixed bound `k`, every sufficiently large natural number has a
representation as a prime plus at most `k` powers of two. -/
def EventuallyAllRepresentable (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → PrimePlusPowersOfTwoRep k n

/-- Erdős problem `#10`: some fixed number of powers of two suffices for all
sufficiently large integers. -/
def Erdos10Conjecture : Prop :=
  ∃ k : ℕ, EventuallyAllRepresentable k

end PrimeBoundedTwoPowers
