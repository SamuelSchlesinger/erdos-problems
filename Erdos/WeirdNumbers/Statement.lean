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

end WeirdNumbers
