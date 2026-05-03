/-
# Weighted Packing Bounds

This file is the overlap-aware analogue of `PackingBound.lean`.

The main theorem is a denominator-cleared fractional packing certificate.  Think
of every forbidden edge `edge i` as having rational weight `weight i / C`.
If every vertex has total incident weight at most `1`, equivalently cleared load
at most `C`, and every forbidden edge is not contained in `A`, then `A` must
omit at least the total edge weight:

  C * |A| + Σᵢ weight i ≤ C * |U|.

This supports finite and parametric LP-style certificates where forbidden
unit-fraction identities overlap.
-/
import Mathlib

namespace WeightedPacking

open scoped BigOperators

/-- A denominator-cleared weighted forbidden-edge packing bound.

`U` is the ambient finite universe, `A ⊆ U` is the candidate avoiding set, `I`
indexes forbidden edges, `weight i` is the integer numerator of the edge weight,
and `C` is the common denominator/capacity.  If no forbidden edge is contained in
`A`, every edge lies in `U`, and every vertex has load at most `C`, then the
weighted total of forbidden edges is a certified omission count. -/
theorem weighted_forbidden_edge_bound {ι : Type*} (U A : Finset ℕ) (I : Finset ι)
    (edge : ι → Finset ℕ) (weight : ι → ℕ) (C : ℕ)
    (hA : A ⊆ U)
    (hedgeU : ∀ i ∈ I, edge i ⊆ U)
    (hforbid : ∀ i ∈ I, ¬ edge i ⊆ A)
    (hload : ∀ x ∈ U, (∑ i ∈ I, if x ∈ edge i then weight i else 0) ≤ C) :
    C * A.card + (∑ i ∈ I, weight i) ≤ C * U.card := by
  classical
  set M := U \ A with hM
  have h_weight_le_omitted :
      (∑ i ∈ I, weight i) ≤
        ∑ i ∈ I, ∑ x ∈ M, if x ∈ edge i then weight i else 0 := by
    refine Finset.sum_le_sum ?_
    intro i hi
    obtain ⟨x, hxedge, hxA⟩ := Finset.not_subset.mp (hforbid i hi)
    have hxU : x ∈ U := hedgeU i hi hxedge
    have hxM : x ∈ M := by
      simp [hM, hxU, hxA]
    calc
      weight i = (if x ∈ edge i then weight i else 0) := by simp [hxedge]
      _ ≤ ∑ y ∈ M, if y ∈ edge i then weight i else 0 := by
        exact Finset.single_le_sum (s := M)
          (f := fun y => if y ∈ edge i then weight i else 0)
          (fun y _ => by
            by_cases hy : y ∈ edge i
            · simp [hy]
            · simp [hy]) hxM
  have h_omitted_le_capacity :
      (∑ i ∈ I, ∑ x ∈ M, if x ∈ edge i then weight i else 0) ≤ C * M.card := by
    calc
      (∑ i ∈ I, ∑ x ∈ M, if x ∈ edge i then weight i else 0)
          = ∑ x ∈ M, ∑ i ∈ I, if x ∈ edge i then weight i else 0 := by
            rw [Finset.sum_comm]
      _ ≤ ∑ _x ∈ M, C := by
        refine Finset.sum_le_sum ?_
        intro x hxM
        have hxU : x ∈ U := by
          simpa [hM] using (Finset.mem_sdiff.mp hxM).1
        exact hload x hxU
      _ = M.card * C := Finset.sum_const_nat fun _ _ => rfl
      _ = C * M.card := by ring
  have htotal : (∑ i ∈ I, weight i) ≤ C * M.card :=
    le_trans h_weight_le_omitted h_omitted_le_capacity
  have hMcard : M.card + A.card = U.card := by
    simpa [hM] using Finset.card_sdiff_add_card_eq_card hA
  have hsplit : C * U.card = C * M.card + C * A.card := by
    rw [← hMcard]
    ring
  omega

/-- Weighted forbidden-edge packing for a disjoint family of local certificates.

For every parameter `d ∈ D`, the local edges `edge d i` lie in a gadget
`gadget d`, no local edge is contained in `A`, and every point of that gadget
has local load at most `C`. If the gadgets are pairwise disjoint and lie in
the ambient universe `U`, the local certificates add without overlap:

`C * |A| + |D| * Σᵢ weightᵢ ≤ C * |U|`.
-/
theorem weighted_forbidden_disjoint_family_bound {ι : Type*}
    (U A D : Finset ℕ) (I : Finset ι)
    (gadget : ℕ → Finset ℕ) (edge : ℕ → ι → Finset ℕ)
    (weight : ι → ℕ) (C : ℕ)
    (hA : A ⊆ U)
    (hpwd : (↑D : Set ℕ).PairwiseDisjoint gadget)
    (hgadgetU : ∀ d ∈ D, gadget d ⊆ U)
    (hedgeG : ∀ d ∈ D, ∀ i ∈ I, edge d i ⊆ gadget d)
    (hforbid : ∀ d ∈ D, ∀ i ∈ I, ¬ edge d i ⊆ A)
    (hload : ∀ d ∈ D, ∀ x ∈ gadget d,
      (∑ i ∈ I, if x ∈ edge d i then weight i else 0) ≤ C) :
    C * A.card + D.card * (∑ i ∈ I, weight i) ≤ C * U.card := by
  classical
  let J : Finset (ℕ × ι) := D.product I
  let edge' : ℕ × ι → Finset ℕ := fun p => edge p.1 p.2
  let weight' : ℕ × ι → ℕ := fun p => weight p.2
  have hedgeU : ∀ p ∈ J, edge' p ⊆ U := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hd, hi⟩
    exact (hedgeG p.1 hd p.2 hi).trans (hgadgetU p.1 hd)
  have hforbid' : ∀ p ∈ J, ¬ edge' p ⊆ A := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hd, hi⟩
    exact hforbid p.1 hd p.2 hi
  have hload' : ∀ x ∈ U,
      (∑ p ∈ J, if x ∈ edge' p then weight' p else 0) ≤ C := by
    intro x hxU
    change (∑ p ∈ D.product I, if x ∈ edge' p then weight' p else 0) ≤ C
    rw [Finset.product_eq_sprod]
    rw [Finset.sum_product]
    simp only [edge', weight']
    by_cases hxDG : ∃ d ∈ D, x ∈ gadget d
    · obtain ⟨d₀, hd₀, hxd₀⟩ := hxDG
      have hsum_eq :
          (∑ d ∈ D, ∑ i ∈ I, if x ∈ edge d i then weight i else 0) =
            ∑ i ∈ I, if x ∈ edge d₀ i then weight i else 0 := by
        refine Finset.sum_eq_single d₀ ?_ ?_
        · intro d hd hne
          apply Finset.sum_eq_zero
          intro i hi
          have hxnot : x ∉ edge d i := by
            intro hxe
            have hxd : x ∈ gadget d := hedgeG d hd i hi hxe
            have hdisj : Disjoint (gadget d) (gadget d₀) := hpwd hd hd₀ hne
            rw [Finset.disjoint_left] at hdisj
            exact hdisj hxd hxd₀
          simp [hxnot]
        · intro hd₀_not
          exact False.elim (hd₀_not hd₀)
      rw [hsum_eq]
      exact hload d₀ hd₀ x hxd₀
    · have hzero :
          (∑ d ∈ D, ∑ i ∈ I, if x ∈ edge d i then weight i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro i hi
        have hxnot : x ∉ edge d i := by
          intro hxe
          exact hxDG ⟨d, hd, hedgeG d hd i hi hxe⟩
        simp [hxnot]
      rw [hzero]
      omega
  have hweight_sum :
      (∑ p ∈ J, weight' p) = D.card * (∑ i ∈ I, weight i) := by
    change (∑ p ∈ D.product I, weight' p) = D.card * (∑ i ∈ I, weight i)
    rw [Finset.product_eq_sprod]
    rw [Finset.sum_product]
    simp only [weight']
    exact Finset.sum_const_nat (fun _ _ => rfl)
  have h := weighted_forbidden_edge_bound U A J edge' weight' C hA hedgeU hforbid' hload'
  simpa [hweight_sum] using h

end WeightedPacking
