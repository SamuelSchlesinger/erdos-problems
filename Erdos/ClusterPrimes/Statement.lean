import Mathlib

/-!
# Erdos Problem 17: Cluster Primes

Erdos asks whether there are infinitely many primes `p` such that every even
number `n <= p - 3` can be represented as a difference `q1 - q2` of primes
bounded by `p`.

We state the natural-number bound as `n + 3 <= p`, which is equivalent to
`n <= p - 3` once `p >= 3` and avoids truncated subtraction at small `p`. The
difference equation itself is stated in `Int`, so `q1 - q2` is the ordinary
integer difference rather than truncated subtraction on `Nat`.

Reference: https://www.erdosproblems.com/17
-/

namespace ClusterPrimes

/--
`PrimeDifferenceWitness p n` says that `n` is realized as an integer difference
of two primes, both at most `p`.
-/
def PrimeDifferenceWitness (p n : Nat) : Prop :=
  Exists fun q1 : Nat =>
    Exists fun q2 : Nat =>
      Nat.Prime q1 /\ Nat.Prime q2 /\
        q1 <= p /\ q2 <= p /\ (q1 : Int) - (q2 : Int) = (n : Int)

/--
`p` is a cluster prime if it is prime and every even `n` in the range
`n + 3 <= p` has a prime-difference witness with both primes bounded by `p`.
-/
def IsClusterPrime (p : Nat) : Prop :=
  Nat.Prime p /\
    forall n : Nat, Even n -> n + 3 <= p -> PrimeDifferenceWitness p n

/-- Erdos problem `#17`: there are infinitely many cluster primes. -/
def Erdos17Conjecture : Prop :=
  {p : Nat | IsClusterPrime p}.Infinite

end ClusterPrimes
