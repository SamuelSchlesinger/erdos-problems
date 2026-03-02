/-
# DivisorEgyptianFree: Unified Characterization of Weird Numbers

A positive integer n is `DivisorEgyptianFree` if no nonempty subset T of its
divisors (excluding 1) has reciprocals summing to 1: ¬∃ T ⊆ divisors(n) \ {1}
with ∑_{t ∈ T} 1/t = 1.

This predicate unifies the weird number definition with the unit-fraction
avoidance framework:

  **weird(n) ⟺ abundant(n) ∧ DivisorEgyptianFree(n)**

The forward direction uses the Egyptian fraction bridge (`pseudoperfect_iff_unit_sum`):
weird → not pseudoperfect → no unit-sum subset → DivisorEgyptianFree.

The backward direction: abundant + DivisorEgyptianFree → no unit-sum subset
→ not pseudoperfect → weird (since abundant ∧ ¬pseudoperfect = weird).

This connects Problem #470 (weird numbers) directly to the unit-fraction
avoidance universe of Problems #301/#302.

Reference: https://www.erdosproblems.com/470
-/
import Erdos.WeirdNumbers.EgyptianBridge

namespace WeirdNumbers

open Finset

/-- A positive integer n is **DivisorEgyptianFree** if no nonempty subset of
    its divisors (excluding 1) has reciprocals summing to exactly 1.

    This is the unit-fraction avoidance property that, combined with
    abundancy, characterizes weird numbers. -/
def DivisorEgyptianFree (n : ℕ) : Prop :=
  ¬∃ T ⊆ n.divisors, (1 : ℕ) ∉ T ∧ T.Nonempty ∧
    ∑ t ∈ T, (1 / (t : ℚ)) = 1

/-- **Weird ↔ Abundant ∧ DivisorEgyptianFree.**

    This is the master characterization connecting weird numbers to the
    unit-fraction avoidance framework.

    Forward: Weird → Abundant (by definition) and Weird → ¬Pseudoperfect
    → no unit-sum subset (by the Egyptian bridge) → DivisorEgyptianFree.

    Backward: Abundant ∧ DivisorEgyptianFree → Abundant ∧ no unit-sum subset
    → Abundant ∧ ¬Pseudoperfect (by the bridge) → Weird. -/
theorem weird_iff_abundant_egyptian_free {n : ℕ} (hn : 0 < n) :
    Weird n ↔ Abundant n ∧ DivisorEgyptianFree n := by
  constructor
  · -- Forward: weird → abundant ∧ DivisorEgyptianFree
    intro hw
    exact ⟨hw.1, weird_no_unit_sum hw⟩
  · -- Backward: abundant ∧ DivisorEgyptianFree → weird
    intro ⟨hab, hef⟩
    exact ⟨hab, fun hp =>
      hef ((pseudoperfect_iff_unit_sum hn).mp hp)⟩

/-- **Primes are DivisorEgyptianFree.**

    A prime p has divisors = {1, p}. The only nonempty T ⊆ divisors(p) \ {1}
    is T = {p}, and ∑_{t ∈ {p}} 1/t = 1/p ≠ 1 (since p ≥ 2).

    This is a sanity check: primes have too few divisors for any
    unit-fraction sum to work. -/
theorem prime_divisor_egyptian_free {p : ℕ} (hp : Nat.Prime p) :
    DivisorEgyptianFree p := by
  intro ⟨T, hTsub, h1, hTne, hTsum⟩
  -- T ⊆ p.divisors = {1, p} and 1 ∉ T, so T ⊆ {p}
  have hp_div : p.divisors = {1, p} := Nat.Prime.divisors hp
  -- Every element of T is p
  have hT_eq : ∀ t ∈ T, t = p := by
    intro t ht
    have := hTsub ht
    rw [hp_div] at this
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl
    · exact absurd ht h1
    · rfl
  -- T ⊆ {p}, so T.card ≤ 1, and T is nonempty, so T.card = 1
  have hTsub' : T ⊆ {p} := fun t ht => mem_singleton.mpr (hT_eq t ht)
  have hTcard : T.card = 1 := by
    have := hTne.card_pos
    have := card_le_card hTsub'
    simp at this; omega
  -- ∑_{t ∈ T} 1/t = 1/p, since all elements are p and T.card = 1
  have hTsum' : ∑ t ∈ T, (1 / (t : ℚ)) = 1 / (p : ℚ) := by
    have hcong : ∑ t ∈ T, (1 / (t : ℚ)) = ∑ _t ∈ T, (1 / (p : ℚ)) :=
      Finset.sum_congr rfl fun t ht => by rw [hT_eq t ht]
    rw [hcong, Finset.sum_const, hTcard]
    simp
  -- Now 1/p = 1 means p = 1, contradicting p prime (p ≥ 2)
  rw [hTsum'] at hTsum
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hp_eq : (p : ℚ) = 1 := by
    rw [div_eq_iff (ne_of_gt hp_pos)] at hTsum; linarith
  exact absurd (by exact_mod_cast hp_eq : p = 1) (Nat.Prime.one_lt hp).ne'

/-- **Perfect numbers are NOT DivisorEgyptianFree.**

    A perfect number n satisfies σ(n) = 2n, which gives
    ∑_{d > 1 | d ∣ n} 1/d = 1 (via `perfect_canonical_unit_sum`).
    So T = divisors(n) \ {1} witnesses a unit-fraction sum equal to 1.

    This shows perfect numbers lie on the opposite side of the
    DivisorEgyptianFree divide from weird numbers. -/
theorem perfect_not_divisor_egyptian_free {n : ℕ} (hn : 0 < n)
    (hperf : n.properDivisors.sum id = n) :
    ¬DivisorEgyptianFree n := by
  intro hef
  apply hef
  -- T = n.divisors.erase 1
  refine ⟨n.divisors.erase 1, erase_subset 1 n.divisors, ?_, ?_, ?_⟩
  · -- 1 ∉ T
    simp
  · -- T is nonempty: n ∈ divisors(n) and n ≠ 1 (since n has proper divisors summing to n ≥ 1)
    refine ⟨n, mem_erase.mpr ⟨?_, Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩⟩⟩
    -- n ≠ 1: if n = 1, then properDivisors = ∅ and sum = 0 ≠ 1
    intro h1; subst h1; simp at hperf
  · -- ∑_{t ∈ T} 1/t = 1
    exact perfect_canonical_unit_sum hn hperf

end WeirdNumbers
