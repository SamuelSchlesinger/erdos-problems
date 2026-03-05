/-
# Parity and Sum-Free Sets

The odd numbers are NOT sum-free (unlike the triple case):
1/3 = 1/5 + 1/9 + 1/45 gives a concrete counterexample with all
elements odd and distinct.

This corrects the intuition that the parity obstruction for triples
(Problem #302, `no_triple_both_odd`) lifts to arbitrary-length sums
(Problem #301). It does not: the parity argument only blocks
representations with an EVEN number of terms.

The identity 1/3 = 1/5 + 1/9 + 1/45 uses k = 3 (odd number of terms),
which is exactly where the parity obstruction fails.

Reference: https://www.erdosproblems.com/301
-/
import Erdos.UnitFractionSets.Statement

namespace UnitFractionSets

open scoped BigOperators

/-- **Even-length parity obstruction for odd denominators.**

    If `a` and all elements of `S` are odd, and `S` has even cardinality, then
    `1/a` cannot equal `∑_{b∈S} 1/b`.

    Proof sketch: clear denominators with `P = ∏_{b∈S} b`, obtaining
    `P = a * ∑_{b∈S} (P/b)`. Since all factors of `P` are odd, each quotient
    `P/b` is odd. An even number of odd terms has even sum, so the RHS is even
    (odd times even), but `P` is odd. Contradiction. -/
theorem odd_even_card_no_unit_sum {a : ℕ} {S : Finset ℕ}
    (ha_odd : Odd a) (hSodd : ∀ b ∈ S, Odd b) (hcard : Even S.card) :
    (1 / a : ℚ) ≠ ∑ b ∈ S, (1 / b : ℚ) := by
  intro heq
  let P : ℕ := ∏ b ∈ S, b
  have ha_ne_zero : a ≠ 0 := by
    intro h0
    exact (Nat.not_even_iff_odd.mpr ha_odd) (h0 ▸ (by decide : Even 0))
  have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha_ne_zero
  have hb0 : ∀ b ∈ S, (b : ℚ) ≠ 0 := by
    intro b hb
    have hb_ne_zero : b ≠ 0 := by
      intro h0
      exact (Nat.not_even_iff_odd.mpr (hSodd b hb)) (h0 ▸ (by decide : Even 0))
    exact Nat.cast_ne_zero.mpr hb_ne_zero
  have hmulQ : ((P : ℕ) : ℚ) = (a : ℚ) * ∑ b ∈ S, ((P / b : ℕ) : ℚ) := by
    let PNat : ℕ := P
    let PQ : ℚ := PNat
    have h1 : (1 : ℚ) = (a : ℚ) * ∑ b ∈ S, (1 / b : ℚ) := by
      have h1 := congrArg (fun q : ℚ => q * (a : ℚ)) heq
      simpa [ha0, mul_assoc, mul_comm, mul_left_comm] using h1
    have h2 : PQ = ((a : ℚ) * ∑ b ∈ S, (1 / b : ℚ)) * PQ := by
      have h2' := congrArg (fun q : ℚ => q * PQ) h1
      simpa [PQ] using h2'
    have h3 : PQ = (a : ℚ) * (PQ * ∑ b ∈ S, (1 / b : ℚ)) := by
      calc
        PQ = ((a : ℚ) * ∑ b ∈ S, (1 / b : ℚ)) * PQ := h2
        _ = (a : ℚ) * (PQ * ∑ b ∈ S, (1 / b : ℚ)) := by ring
    have h4 : PQ * ∑ b ∈ S, (1 / b : ℚ) = ∑ b ∈ S, (PQ / b) := by
      simp [PQ, Finset.mul_sum, div_eq_mul_inv, mul_comm]
    have h5 : ∑ b ∈ S, (PQ / b) = ∑ b ∈ S, ((PNat / b : ℕ) : ℚ) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      have hbP : b ∣ PNat := by
        exact Finset.dvd_prod_of_mem (fun x => x) hb
      have hb0' : (b : ℚ) ≠ 0 := hb0 b hb
      simp [PQ, Nat.cast_div hbP hb0']
    calc
      ((P : ℕ) : ℚ) = PQ := by simp [PQ, PNat, P]
      _ = (a : ℚ) * (PQ * ∑ b ∈ S, (1 / b : ℚ)) := h3
      _ = (a : ℚ) * ∑ b ∈ S, (PQ / b) := by rw [h4]
      _ = (a : ℚ) * ∑ b ∈ S, ((PNat / b : ℕ) : ℚ) := by rw [h5]
      _ = (a : ℚ) * ∑ b ∈ S, ((P / b : ℕ) : ℚ) := by simp [PNat]
  have hmulN : P = a * ∑ b ∈ S, P / b := by
    exact_mod_cast hmulQ
  have hPodd : Odd P := by
    classical
    unfold P
    revert hSodd
    refine Finset.induction_on S ?_ ?_
    · intro _
      simp
    · intro x T hx ih hOddAll
      have hxodd : Odd x := hOddAll x (by simp [hx])
      have hOddT : ∀ b ∈ T, Odd b := by
        intro b hb
        exact hOddAll b (by simp [hb])
      have hProdT : Odd (∏ b ∈ T, b) := ih hOddT
      simpa [Finset.prod_insert, hx] using Odd.mul hxodd hProdT
  have hquot_odd : ∀ b ∈ S, Odd (P / b) := by
    intro b hb
    by_contra hOdd
    have hEven : Even (P / b) := by
      rwa [Nat.not_odd_iff_even] at hOdd
    have hbP : b ∣ P := Finset.dvd_prod_of_mem (fun x => x) hb
    have hPeven : Even P := by
      have hEvenMul : Even (b * (P / b)) := (Nat.even_mul).2 (Or.inr hEven)
      simpa [Nat.mul_div_cancel' hbP] using hEvenMul
    exact (Nat.not_even_iff_odd.mpr hPodd) hPeven
  have hsum_even : Even (∑ b ∈ S, P / b) := by
    rw [Finset.even_sum_iff_even_card_odd]
    have hfilter : {x ∈ S | Odd (P / x)} = S := by
      ext x
      constructor
      · intro hx
        exact (Finset.mem_filter.mp hx).1
      · intro hxS
        exact Finset.mem_filter.mpr ⟨hxS, hquot_odd x hxS⟩
    rw [hfilter]
    exact hcard
  have hPeven : Even P := by
    have hEvenMul : Even (a * ∑ b ∈ S, P / b) := (Nat.even_mul).2 (Or.inr hsum_even)
    rw [← hmulN] at hEvenMul
    exact hEvenMul
  exact (Nat.not_even_iff_odd.mpr hPodd) hPeven

/-- Repackaged form of `odd_even_card_no_unit_sum` using `¬Even` assumptions. -/
theorem not_even_even_card_no_unit_sum {a : ℕ} {S : Finset ℕ}
    (ha : ¬Even a) (hS : ∀ b ∈ S, ¬Even b) (hcard : Even S.card) :
    (1 / a : ℚ) ≠ ∑ b ∈ S, (1 / b : ℚ) :=
  odd_even_card_no_unit_sum (Nat.not_even_iff_odd.mp ha)
    (fun b hb => Nat.not_even_iff_odd.mp (hS b hb)) hcard

/-- **Odd sets satisfy an even-length obstruction.**

    If every element of `A` is odd, then any witness `S ⊆ A.erase a` for
    `1/a = ∑_{b∈S} 1/b` must have odd cardinality. Equivalently, even-cardinality
    `S` are automatically forbidden. -/
theorem odd_set_even_card_obstruction {A : Finset ℕ}
    (hAodd : ∀ n ∈ A, ¬Even n) {a : ℕ} (ha : a ∈ A)
    {S : Finset ℕ} (hS : S ⊆ A.erase a) (hcard : Even S.card) :
    (1 / a : ℚ) ≠ ∑ b ∈ S, (1 / b : ℚ) := by
  refine not_even_even_card_no_unit_sum (hAodd a ha) ?_ hcard
  intro b hb
  exact hAodd b ((Finset.mem_erase.mp (hS hb)).2)

/-- **Odd-set witness lengths are forced odd.**

    If every element of `A` is odd and a representation
    `1/a = ∑_{b∈S} 1/b` occurs with `S ⊆ A.erase a`, then `S.card` is odd. -/
theorem odd_set_witness_card_odd {A : Finset ℕ}
    (hAodd : ∀ n ∈ A, ¬Even n) {a : ℕ} (ha : a ∈ A)
    {S : Finset ℕ} (hS : S ⊆ A.erase a)
    (heq : (1 / a : ℚ) = ∑ b ∈ S, (1 / b : ℚ)) :
    Odd S.card := by
  by_contra hOdd
  have hEven : Even S.card := Nat.not_odd_iff_even.mp hOdd
  exact (odd_set_even_card_obstruction hAodd ha hS hEven) heq

/-- **Odd numbers are NOT sum-free.**

    The identity 1/3 = 1/5 + 1/9 + 1/45 shows that a set of four
    distinct odd numbers can violate the sum-free property.

    Verification: 1/5 + 1/9 + 1/45 = 9/45 + 5/45 + 1/45 = 15/45 = 1/3. ✓

    This contrasts with the triple-free case (Problem #302), where
    odd numbers are always triple-free (`no_triple_both_odd`). The
    difference: the parity obstruction works for k = 2 (even) but
    fails for k = 3 (odd). Clearing denominators in 1/a = Σ 1/bᵢ
    gives ∏ bⱼ = a · Σᵢ ∏_{j≠i} bⱼ, where both sides are odd when
    all elements are odd and k is odd, so no contradiction arises. -/
theorem odd_not_sum_free :
    ∃ (A : Finset ℕ), (∀ a ∈ A, ¬Even a) ∧ ¬SumFree A := by
  refine ⟨{3, 5, 9, 45}, ?_, ?_⟩
  · -- All elements are odd
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide
  · -- Not sum-free: 1/3 = 1/5 + 1/9 + 1/45
    intro hsf
    -- Build the witness: a = 3, S = {5, 9, 45}
    have hS : ({5, 9, 45} : Finset ℕ) ⊆ ({3, 5, 9, 45} : Finset ℕ).erase 3 := by
      intro x hx
      rw [Finset.mem_erase]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> omega
    have hne : ({5, 9, 45} : Finset ℕ).Nonempty := ⟨5, by simp⟩
    -- The key equation: 1/3 = 1/5 + 1/9 + 1/45
    have heq : (1 / 3 : ℚ) = ∑ b ∈ ({5, 9, 45} : Finset ℕ), (1 / b : ℚ) := by
      rw [show ({5, 9, 45} : Finset ℕ) = insert 5 (insert 9 {45}) from rfl]
      rw [Finset.sum_insert (show (5 : ℕ) ∉ insert 9 ({45} : Finset ℕ) by decide)]
      rw [Finset.sum_insert (show (9 : ℕ) ∉ ({45} : Finset ℕ) by decide)]
      rw [Finset.sum_singleton]
      push_cast
      norm_num
    exact absurd heq (hsf 3 (by simp) {5, 9, 45} hS hne)

end UnitFractionSets
