/-
# Erdős Problem 470: Weird Numbers

A positive integer n is *weird* if it is abundant (the sum of its proper
divisors exceeds n) but not pseudoperfect (n cannot be expressed as a sum
of any subset of its proper divisors).

Questions:
1. Do any odd weird numbers exist? ($10 Erdős prize)
2. Are there infinitely many primitive weird numbers?

Known results:
- The smallest weird number is 70
- Weird numbers have positive density (Benkoski & Erdős)
- No odd weird numbers exist below 10²¹ (Fang)
- Any odd weird number must have at least 6 prime factors (Liddy & Riedl)

Reference: https://www.erdosproblems.com/470
-/
import Mathlib

namespace WeirdNumbers

/-- A positive integer n is *abundant* if the sum of its proper divisors
    is at least n, i.e., σ(n) ≥ 2n. -/
def Abundant (n : ℕ) : Prop :=
  0 < n ∧ n ≤ (n.properDivisors.sum id)

/-- A positive integer n is *pseudoperfect* (or *semiperfect*) if it equals
    the sum of some subset of its proper divisors. -/
def Pseudoperfect (n : ℕ) : Prop :=
  ∃ S ∈ n.properDivisors.powerset, S.sum id = n

/-- A positive integer n is *weird* if it is abundant but not pseudoperfect:
    its proper divisors sum to more than n, yet no subset of them sums to
    exactly n. -/
def Weird (n : ℕ) : Prop :=
  Abundant n ∧ ¬Pseudoperfect n

/-- A weird number is *primitive* if none of its proper divisors is weird. -/
def PrimitiveWeird (n : ℕ) : Prop :=
  Weird n ∧ ∀ d ∈ n.properDivisors, ¬Weird d

/-- Erdős's first question: do any odd weird numbers exist? -/
def OddWeirdExists : Prop :=
  ∃ n : ℕ, Weird n ∧ ¬Even n

/-- Erdős's second question: are there infinitely many primitive weird numbers? -/
def InfinitelyManyPrimitiveWeird : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ PrimitiveWeird n

instance : DecidablePred Abundant := by
  intro n; unfold Abundant; infer_instance

instance : DecidablePred Pseudoperfect := by
  intro n; unfold Pseudoperfect; infer_instance

instance : DecidablePred Weird := by
  intro n; unfold Weird; infer_instance

instance : DecidablePred PrimitiveWeird := by
  intro n; unfold PrimitiveWeird; infer_instance

/-- 70 is the smallest weird number. This is a concrete computation
    that serves as a sanity check on our definitions. -/
theorem seventy_is_weird : Weird 70 := by native_decide

/-- No number less than 70 is weird. -/
theorem no_weird_below_70 : ∀ n < 70, ¬Weird n := by native_decide

/-- 70 is a *primitive* weird number: it is weird, and none of its
    proper divisors (1, 2, 5, 7, 10, 14, 35 — all < 70) is weird. -/
theorem seventy_is_primitive_weird : PrimitiveWeird 70 := by native_decide

/-- A perfect number (one whose proper divisors sum to exactly n) is
    pseudoperfect: just take S = n.properDivisors itself. -/
theorem perfect_implies_pseudoperfect {n : ℕ} (_hn : 0 < n)
    (hperf : n.properDivisors.sum id = n) : Pseudoperfect n :=
  ⟨n.properDivisors, Finset.mem_powerset.mpr (Finset.Subset.refl _), hperf⟩

/-- A perfect number is not weird: it is pseudoperfect (and may or
    may not be abundant, but either way the ¬Pseudoperfect clause
    of Weird fails). -/
theorem perfect_not_weird {n : ℕ} (hn : 0 < n)
    (hperf : n.properDivisors.sum id = n) : ¬Weird n := by
  intro ⟨_, hnp⟩
  exact hnp (perfect_implies_pseudoperfect hn hperf)

/-- A positive integer n is *deficient* if the sum of its proper divisors
    is less than n, i.e., σ(n) < 2n. -/
def Deficient (n : ℕ) : Prop :=
  0 < n ∧ (n.properDivisors.sum id) < n

/-- **Deficient numbers are not weird.**

    A deficient number has proper divisors summing to less than n,
    so it is not abundant. Since weird requires abundant, deficient
    numbers cannot be weird. -/
theorem deficient_not_weird {n : ℕ} (hdef : Deficient n) : ¬Weird n := by
  obtain ⟨_, hlt⟩ := hdef
  intro ⟨⟨_, hab⟩, _⟩
  exact absurd (lt_of_le_of_lt hab hlt) (lt_irrefl _)

/-- **Primes are not weird.**

    A prime p has properDivisors = {1}, so the sum of proper divisors
    is 1 < p. Hence p is deficient (far from abundant) and therefore
    not weird.

    This is a basic sanity check: the weird number phenomenon requires
    a rich divisor structure that primes completely lack. -/
theorem prime_not_weird {p : ℕ} (hp : Nat.Prime p) : ¬Weird p := by
  apply deficient_not_weird
  refine ⟨hp.pos, ?_⟩
  have h1 : p.properDivisors.sum id = 1 :=
    Nat.sum_properDivisors_eq_one_iff_prime.mpr hp
  have h2 := hp.one_lt
  omega

/-- **1 is not weird.**

    The number 1 has no proper divisors (properDivisors 1 = ∅), so the
    sum is 0 < 1 = n. It is deficient (and not even abundant). -/
theorem one_not_weird : ¬Weird 1 := by
  apply deficient_not_weird
  constructor
  · omega
  · show (1 : ℕ).properDivisors.sum id < 1
    native_decide

/-- **836 is the second-smallest weird number.** -/
theorem weird_836 : Weird 836 := by native_decide

/-- **836 is a primitive weird number.** -/
theorem primitive_weird_836 : PrimitiveWeird 836 := by native_decide

end WeirdNumbers
