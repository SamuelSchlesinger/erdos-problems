import Erdos.PrimeBoundedTwoPowers.Statement

/-!
# Elementary Facts for Erdős Problem 10

This file records the basic bookkeeping for representations of integers as a
prime plus boundedly many powers of two.  Increasing the allowed number of
powers preserves representability, primes use the empty list of powers, and an
exact two-power representation is automatically a representation for every
bound `k ≥ 2`.
-/

namespace PrimeBoundedTwoPowers

@[simp] theorem twoPowerSum_nil : twoPowerSum [] = 0 := by
  simp [twoPowerSum]

@[simp] theorem twoPowerSum_cons (e : ℕ) (exps : List ℕ) :
    twoPowerSum (e :: exps) = 2 ^ e + twoPowerSum exps := by
  simp [twoPowerSum]

/-- Allowing more powers of two cannot destroy a representation. -/
theorem primePlusPowersOfTwoRep_mono {k l n : ℕ} (hkl : k ≤ l)
    (hrep : PrimePlusPowersOfTwoRep k n) :
    PrimePlusPowersOfTwoRep l n := by
  rcases hrep with ⟨p, hp, exps, hlen, hsum⟩
  exact ⟨p, hp, exps, le_trans hlen hkl, hsum⟩

/-- The eventual property is monotone in the allowed number of powers. -/
theorem eventuallyAllRepresentable_mono {k l : ℕ} (hkl : k ≤ l)
    (h : EventuallyAllRepresentable k) :
    EventuallyAllRepresentable l := by
  rcases h with ⟨N, hN⟩
  exact ⟨N, fun n hn => primePlusPowersOfTwoRep_mono hkl (hN n hn)⟩

/-- Every prime is represented using no powers of two. -/
theorem prime_primePlusPowersOfTwoRep_zero {p : ℕ} (hp : Nat.Prime p) :
    PrimePlusPowersOfTwoRep 0 p := by
  refine ⟨p, hp, [], ?_, ?_⟩
  · simp
  · simp

/-- Consequently, every prime is represented for any allowed bound `k`. -/
theorem prime_primePlusPowersOfTwoRep {k p : ℕ} (hp : Nat.Prime p) :
    PrimePlusPowersOfTwoRep k p := by
  exact primePlusPowersOfTwoRep_mono (Nat.zero_le k)
    (prime_primePlusPowersOfTwoRep_zero hp)

/-- A representation with exactly `m` powers is also one with at most `k` powers
whenever `m ≤ k`. -/
theorem primePlusPowersOfTwoRep_of_exact {m k n : ℕ} (hmk : m ≤ k)
    (hrep : PrimePlusExactlyPowersOfTwoRep m n) :
    PrimePlusPowersOfTwoRep k n := by
  rcases hrep with ⟨p, hp, exps, hlen, hsum⟩
  refine ⟨p, hp, exps, ?_, hsum⟩
  rw [hlen]
  exact hmk

/-- In particular, an exact two-power representation is valid for every bound
`k ≥ 2`. -/
theorem primePlusPowersOfTwoRep_of_exact_two {k n : ℕ} (hk : 2 ≤ k)
    (hrep : PrimePlusExactlyTwoPowersRep n) :
    PrimePlusPowersOfTwoRep k n := by
  exact primePlusPowersOfTwoRep_of_exact hk hrep

end PrimeBoundedTwoPowers
