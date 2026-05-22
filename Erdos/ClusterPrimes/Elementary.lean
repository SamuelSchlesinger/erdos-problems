import Erdos.ClusterPrimes.Statement

/-!
# Elementary Facts About Cluster Primes

This file records direct unpacking lemmas for the definitions in problem `#17`,
the monotonicity of a fixed prime-difference witness in the ambient bound, and
the complete small verification that `3` is a cluster prime.

Reference: https://www.erdosproblems.com/17
-/

namespace ClusterPrimes

/-- A cluster prime is, in particular, prime. -/
theorem isClusterPrime_prime {p : Nat} (hp : IsClusterPrime p) :
    Nat.Prime p :=
  hp.1

/-- Unpack the witness supplied by the cluster-prime property. -/
theorem isClusterPrime_witness {p n : Nat} (hp : IsClusterPrime p)
    (hnEven : Even n) (hnBound : n + 3 <= p) :
    PrimeDifferenceWitness p n :=
  hp.2 n hnEven hnBound

/--
The same prime-difference representation remains valid if the allowed prime
bound is increased.
-/
theorem PrimeDifferenceWitness.mono {p P n : Nat}
    (h : PrimeDifferenceWitness p n) (hpP : p <= P) :
    PrimeDifferenceWitness P n := by
  rcases h with ⟨q1, q2, hq1, hq2, hq1p, hq2p, hdiff⟩
  exact ⟨q1, q2, hq1, hq2, le_trans hq1p hpP, le_trans hq2p hpP, hdiff⟩

/-- The zero difference is witnessed by using the prime `2` twice. -/
theorem primeDifferenceWitness_zero_of_two_le {p : Nat} (hp : 2 <= p) :
    PrimeDifferenceWitness p 0 := by
  exact ⟨2, 2, Nat.prime_two, Nat.prime_two, hp, hp, by norm_num⟩

/-- The prime `3` is a cluster prime. -/
theorem isClusterPrime_three : IsClusterPrime 3 := by
  refine ⟨Nat.prime_three, ?_⟩
  intro n _hnEven hnBound
  have hn0 : n = 0 := by omega
  subst n
  exact primeDifferenceWitness_zero_of_two_le (by norm_num)

end ClusterPrimes
