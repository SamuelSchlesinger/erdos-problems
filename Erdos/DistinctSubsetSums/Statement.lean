import Mathlib

/-!
# Erdős Problem #1: Distinct subset sums

A finite set `A ⊆ ℕ` has **distinct subset sums** if the `2^{|A|}` subsets of `A` all have
different sums. The powers of two `{1, 2, 4, …, 2^{n-1}}` are the standard example, with
largest element `2^{n-1}`. Erdős asked (offering \$500) whether this is essentially optimal:

> **Erdős Problem #1.** Is there a constant `c > 0` such that every set `A` with distinct
> subset sums has largest element at least `c · 2^{|A|}`?

This remains **open**. The trivial counting bound gives largest element `≥ (2^{|A|} − 1)/|A|`;
a second-moment argument of Erdős–Moser improves this to `≳ 2^{|A|}/√{|A|}` (the current best
constant is `1/√π − o(1)`, Elkies). We formalize the elementary bounds and the construction.

Reference: https://www.erdosproblems.com/1
-/

namespace DistinctSubsetSums

open Finset

/-- `A` has **distinct subset sums**: any two subsets of `A` with equal sum are equal. -/
def HasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ ⦃B⦄, B ⊆ A → ∀ ⦃C⦄, C ⊆ A → ∑ x ∈ B, x = ∑ x ∈ C, x → B = C

/-- **Erdős Problem #1** (\$500, open). There is an absolute constant `c > 0` such that every
finite set with distinct subset sums whose elements are all `≤ M` satisfies `c · 2^{|A|} ≤ M`
(i.e. the largest element is at least `c · 2^{|A|}`). -/
def Erdos1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A : Finset ℕ) (M : ℕ), HasDistinctSubsetSums A →
    (∀ x ∈ A, x ≤ M) → c * 2 ^ A.card ≤ (M : ℝ)

/-- The subset-sum map is injective on the powerset of a set with distinct subset sums. -/
theorem injOn_sum_of_hasDistinct {A : Finset ℕ} (h : HasDistinctSubsetSums A) :
    Set.InjOn (fun B : Finset ℕ => ∑ x ∈ B, x) (↑A.powerset) := by
  intro B hB C hC hBC
  rw [Finset.mem_coe, Finset.mem_powerset] at hB hC
  exact h hB hC hBC

end DistinctSubsetSums
