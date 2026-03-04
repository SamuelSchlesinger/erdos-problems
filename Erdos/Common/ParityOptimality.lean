/-
# Parity Optimality for Unit Fraction Avoidance

For Problems #302 (triples) and #327 (pairs), odd numbers are avoidance-free
— achieving ⌈N/2⌉ elements. But what about even numbers?

This file formalizes the **parity asymmetry**: odd numbers are the unique
optimal single-parity class for #302 and #327, while neither parity class
works for #301 (sum-free).

Key results:
1. Even numbers contain violations for all three problem types
2. Even scaling lemma: triple structure on evens ≅ full structure at half scale
3. Parity asymmetry corollaries: odd uniquely optimal for #302/#327; neither for #301
-/
import Erdos.UnitFractionTriples.Cambie
import Erdos.UnitFractionPairs.Statement
import Erdos.UnitFractionSets.Parity
import Erdos.UnitFractionSets.Connections

namespace ParityOptimality

open UnitFractionTriples UnitFractionPairs UnitFractionSets UnitFractionConnections

/-! ## Section A: Even-class violations -/

/-- The triple (4, 6, 12) satisfies 1/4 = 1/6 + 1/12.

    Verification: 1/6 + 1/12 = 2/12 + 1/12 = 3/12 = 1/4. -/
theorem triple_4_6_12 : IsUnitFractionTriple 4 6 12 :=
  ⟨by omega, by omega, by omega, by norm_num⟩

/-- The pair (6, 12) satisfies (6 + 12) ∣ (6 · 12), i.e. 18 ∣ 72. -/
theorem pair_6_12 : IsUnitFractionPair 6 12 :=
  ⟨4, by norm_num⟩

/-- Even numbers in [1, 12] are NOT triple-free: the triple (4, 6, 12) lives there. -/
theorem even_numbers_not_triple_free :
    ¬TripleFree ((Finset.Icc 1 12).filter (fun n => Even n)) := by
  intro h
  have h4 : 4 ∈ (Finset.Icc 1 12).filter (fun n => Even n) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, ⟨2, by omega⟩⟩
  have h6 : 6 ∈ (Finset.Icc 1 12).filter (fun n => Even n) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, ⟨3, by omega⟩⟩
  have h12 : 12 ∈ (Finset.Icc 1 12).filter (fun n => Even n) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, ⟨6, by omega⟩⟩
  exact h 4 h4 6 h6 12 h12 (by omega) (by omega) (by omega) triple_4_6_12

/-- Even numbers in [1, 12] are NOT pair-free: the pair (6, 12) lives there. -/
theorem even_numbers_not_pair_free :
    ¬PairFree ((Finset.Icc 1 12).filter (fun n => Even n)) := by
  intro h
  have h6 : 6 ∈ (Finset.Icc 1 12).filter (fun n => Even n) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, ⟨3, by omega⟩⟩
  have h12 : 12 ∈ (Finset.Icc 1 12).filter (fun n => Even n) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, ⟨6, by omega⟩⟩
  exact h 6 h6 12 h12 (by omega) pair_6_12

/-- Even numbers in [1, 12] are NOT sum-free, since they're not even triple-free.
    (SumFree ⊂ TripleFree, so failure of TripleFree implies failure of SumFree.) -/
theorem even_numbers_not_sum_free :
    ¬SumFree ((Finset.Icc 1 12).filter (fun n => Even n)) :=
  fun hsf => even_numbers_not_triple_free (sumFree_implies_tripleFree hsf)

/-! ## Section B: Even scaling lemma -/

/-- **Even scaling preserves triple structure.**

    The equation 1/(2a) = 1/(2b) + 1/(2c) holds iff 1/a = 1/b + 1/c.
    Equivalently, even numbers {2, 4, …, 2M} have the same triple structure
    as {1, …, M}, so the maximum even-only triple-free subset of [1, 2M]
    has size f₃₀₂(M) — strictly less than ⌈2M/2⌉ = M for large M. -/
theorem triple_scale_iff {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsUnitFractionTriple (2 * a) (2 * b) (2 * c) ↔ IsUnitFractionTriple a b c := by
  constructor
  · rintro ⟨_, _, _, h⟩
    refine ⟨ha, hb, hc, ?_⟩
    rw [triple_iff_div ha hb hc]
    rw [triple_iff_div (by omega) (by omega) (by omega)] at h
    -- h : 2 * a * (2 * b + 2 * c) = 2 * b * (2 * c)
    -- i.e. 4 * a * (b + c) = 4 * b * c
    -- Goal: a * (b + c) = b * c
    have h4 : 4 * (a * (b + c)) = 4 * (b * c) := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) h4
  · rintro ⟨_, _, _, h⟩
    refine ⟨by omega, by omega, by omega, ?_⟩
    rw [triple_iff_div (by omega) (by omega) (by omega)]
    rw [triple_iff_div ha hb hc] at h
    -- h : a * (b + c) = b * c
    -- Goal: 2 * a * (2 * b + 2 * c) = 2 * b * (2 * c)
    nlinarith

/-- **Pair structure scales forward under doubling.**

    If (a + b) ∣ ab then (2a + 2b) ∣ (2a · 2b). The converse is false in
    general: (a + b) ∣ 4ab does not imply (a + b) ∣ ab when a + b is even. -/
theorem pair_of_pair_scale {a b : ℕ} (h : IsUnitFractionPair a b) :
    IsUnitFractionPair (2 * a) (2 * b) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨2 * k, by nlinarith⟩

/-! ## Section C: Filter bridge -/

/-- Bridge between the two odd-number filter conventions used across the codebase:
    `¬Even n` (used in #302) and `n % 2 = 1` (used in #327). -/
theorem odd_filter_equiv (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => ¬Even n) =
    (Finset.Icc 1 N).filter (fun n => n % 2 = 1) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.not_even_iff_odd, Nat.odd_iff]

/-! ## Section D: Parity asymmetry corollaries -/

/-- **Odd numbers are the unique optimal single-parity class for triple-free sets.**

    Odd numbers in [1, N] are always triple-free (parity obstruction on
    a(b+c) = bc forces one side even, the other odd). Even numbers fail:
    (4, 6, 12) is a triple with all elements even. -/
theorem odd_unique_triple_free_parity :
    (∀ N, TripleFree ((Finset.Icc 1 N).filter (fun n => ¬Even n))) ∧
    ¬TripleFree ((Finset.Icc 1 12).filter (fun n => Even n)) :=
  ⟨odd_numbers_triple_free, even_numbers_not_triple_free⟩

/-- **Odd numbers are the unique optimal single-parity class for pair-free sets.**

    Odd a, b have a + b even and a · b odd, so (a+b) ∤ ab. Even numbers
    fail: (6, 12) is a pair with 18 ∣ 72. -/
theorem odd_unique_pair_free_parity :
    (∀ N, PairFree ((Finset.Icc 1 N).filter (fun n => n % 2 = 1))) ∧
    ¬PairFree ((Finset.Icc 1 12).filter (fun n => Even n)) :=
  ⟨odd_numbers_pair_free, even_numbers_not_pair_free⟩

/-- **Neither parity class is sum-free.**

    Odd numbers fail: 1/3 = 1/5 + 1/9 + 1/45 with all terms odd
    (`odd_not_sum_free`). Even numbers fail: (4, 6, 12) is a triple,
    so the even numbers aren't even triple-free, let alone sum-free.
    This is the fundamental reason the N/2 lower bound for #301 requires
    the upper-half construction rather than a parity argument. -/
theorem neither_parity_sum_free :
    (∃ A : Finset ℕ, (∀ a ∈ A, ¬Even a) ∧ ¬SumFree A) ∧
    ¬SumFree ((Finset.Icc 1 12).filter (fun n => Even n)) :=
  ⟨odd_not_sum_free, even_numbers_not_sum_free⟩

end ParityOptimality
