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

/--
The prime `5` is a cluster prime.

The even numbers `n` with `n + 3 <= 5` are `n = 0` and `n = 2`.  We realize
`0 = 2 - 2` with the existing zero witness and `2 = 5 - 3` using the primes
`5` and `3`, both bounded by `5`.
-/
theorem isClusterPrime_five : IsClusterPrime 5 := by
  refine ⟨Nat.prime_five, ?_⟩
  intro n hnEven hnBound
  have hn2 : n <= 2 := by omega
  interval_cases n
  · exact primeDifferenceWitness_zero_of_two_le (by norm_num)
  · exact absurd hnEven (by decide)
  · exact ⟨5, 3, Nat.prime_five, Nat.prime_three, by norm_num, by norm_num, by norm_num⟩

/--
The prime `7` is a cluster prime.

The even numbers `n` with `n + 3 <= 7` are `n = 0`, `n = 2` and `n = 4`.  We
realize `0 = 2 - 2` with the existing zero witness, `2 = 5 - 3` and `4 = 7 - 3`,
all primes involved being bounded by `7`.
-/
theorem isClusterPrime_seven : IsClusterPrime 7 := by
  refine ⟨Nat.prime_seven, ?_⟩
  intro n hnEven hnBound
  have hn4 : n <= 4 := by omega
  interval_cases n
  · exact primeDifferenceWitness_zero_of_two_le (by norm_num)
  · exact absurd hnEven (by decide)
  · exact ⟨5, 3, Nat.prime_five, Nat.prime_three, by norm_num, by norm_num, by norm_num⟩
  · exact absurd hnEven (by decide)
  · exact ⟨7, 3, Nat.prime_seven, Nat.prime_three, by norm_num, by norm_num, by norm_num⟩

end ClusterPrimes
