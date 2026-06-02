import Erdos.DistinctSubsetSums.Statement

/-!
# Erdős Problem #1: elementary bounds

We prove the elementary lower bound on the largest element of a set with distinct subset sums,
together with the powers-of-two construction.

* `two_pow_card_le_card_mul_succ` : if `A` has distinct subset sums and every element is `≤ M`,
  then `2^{|A|} ≤ |A|·M + 1` (a counting bound: the `2^{|A|}` distinct subset sums all lie in
  `{0, …, |A|·M}`).
* `inv_card_mul_pred_le_of_hasDistinct` : the closed form `(2^{|A|} − 1)/|A| ≤ M`.
* `powersOfTwo_hasDistinctSubsetSums` etc. : the set `{2^0, …, 2^{n-1}}` has distinct subset
  sums, cardinality `n`, and largest element `2^{n-1}` — so the lower bound is tight up to the
  factor `|A|` that Erdős' conjecture (`Erdos1`) is about.
-/

namespace DistinctSubsetSums

open Finset

/-- **Counting lower bound.** If `A` has distinct subset sums and every element is `≤ M`, then
`2^{|A|} ≤ |A| · M + 1`: the `2^{|A|}` subset sums are distinct elements of `{0, 1, …, |A|·M}`. -/
theorem two_pow_card_le_card_mul_succ {A : Finset ℕ} {M : ℕ}
    (h : HasDistinctSubsetSums A) (hM : ∀ x ∈ A, x ≤ M) :
    2 ^ A.card ≤ A.card * M + 1 := by
  classical
  -- the image of the powerset under the sum map has `2^{|A|}` elements …
  have hcard : (A.powerset.image (fun B => ∑ x ∈ B, x)).card = 2 ^ A.card := by
    rw [Finset.card_image_of_injOn (injOn_sum_of_hasDistinct h), Finset.card_powerset]
  -- … and every such sum is `≤ |A|·M`, hence lands in `range (|A|·M + 1)`
  have hsub : A.powerset.image (fun B => ∑ x ∈ B, x) ⊆ Finset.range (A.card * M + 1) := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨B, hB, rfl⟩ := hs
    rw [Finset.mem_powerset] at hB
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc ∑ x ∈ B, x ≤ ∑ x ∈ A, x := Finset.sum_le_sum_of_subset hB
      _ ≤ ∑ _x ∈ A, M := Finset.sum_le_sum (fun x hx => hM x hx)
      _ = A.card * M := by rw [Finset.sum_const, smul_eq_mul]
  calc 2 ^ A.card = (A.powerset.image (fun B => ∑ x ∈ B, x)).card := hcard.symm
    _ ≤ (Finset.range (A.card * M + 1)).card := Finset.card_le_card hsub
    _ = A.card * M + 1 := Finset.card_range _

/-- **Closed-form lower bound.** A nonempty set with distinct subset sums and elements `≤ M`
has `(2^{|A|} − 1)/|A| ≤ M`; i.e. its largest element is at least `(2^{|A|} − 1)/|A|`. This is
the elementary partial result toward Erdős' conjecture `Erdos1` (which asks for `c · 2^{|A|}`). -/
theorem inv_card_mul_pred_le_of_hasDistinct {A : Finset ℕ} {M : ℕ}
    (h : HasDistinctSubsetSums A) (hM : ∀ x ∈ A, x ≤ M) (hne : A.Nonempty) :
    ((2 : ℝ) ^ A.card - 1) / A.card ≤ M := by
  have hpos : 0 < A.card := Finset.card_pos.mpr hne
  have key : 2 ^ A.card ≤ A.card * M + 1 := two_pow_card_le_card_mul_succ h hM
  have hcR : (0 : ℝ) < A.card := by exact_mod_cast hpos
  rw [div_le_iff₀ hcR]
  have keyR : (2 : ℝ) ^ A.card ≤ A.card * M + 1 := by exact_mod_cast key
  have hcomm : (A.card : ℝ) * M = (M : ℝ) * A.card := mul_comm _ _
  linarith [keyR, hcomm]

/-- **The powers-of-two construction.** For every `n`, the set `{2^0, …, 2^{n-1}}` has distinct
subset sums, cardinality `n`, and all elements `≤ 2^{n-1}`. So distinct-subset-sum sets of size
`n` exist with largest element exactly `2^{n-1}`, which is why Erdős' conjecture (`Erdos1`) is
sharp up to the constant: the counting lower bound `inv_card_mul_pred_le_of_hasDistinct` and this
construction sandwich the minimal largest element between `(2^n − 1)/n` and `2^{n-1}`. -/
theorem exists_hasDistinctSubsetSums (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ HasDistinctSubsetSums A ∧ ∀ x ∈ A, x ≤ 2 ^ (n - 1) := by
  classical
  have hpow : Function.Injective (fun i : ℕ => 2 ^ i) := Nat.pow_right_injective (le_refl 2)
  refine ⟨(Finset.range n).image (fun i => 2 ^ i), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hpow, Finset.card_range]
  · intro B hB C hC hBC
    obtain ⟨S, _hS, rfl⟩ := Finset.subset_image_iff.mp hB
    obtain ⟨T, _hT, rfl⟩ := Finset.subset_image_iff.mp hC
    rw [Finset.sum_image (fun a _ b _ hab => hpow hab),
        Finset.sum_image (fun a _ b _ hab => hpow hab)] at hBC
    rw [Finset.geomSum_injective (le_refl 2) hBC]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

end DistinctSubsetSums
