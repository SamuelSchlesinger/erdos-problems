/-
# Weighted Sum-Free Packing Certificates

This file specializes `Erdos.Common.WeightedPacking` to Problem #301.

The theorem `weighted_sum_free_certificate_bound` is the bridge from an LP-style
certificate to a genuine upper bound: a finite weighted list of reciprocal
identities, with per-integer load at most a common capacity `C`, certifies a
denominator-cleared size bound for every sum-free set.
-/
import Erdos.UnitFractionSets.Statement
import Erdos.Common.WeightedPacking

namespace UnitFractionSets

open scoped BigOperators

/-- A denominator-cleared weighted certificate theorem for Problem #301.

For each `i ∈ I`, `target i` and `rhs i` describe a forbidden identity

`1 / target i = ∑ b ∈ rhs i, 1 / b`.

If the edge `{target i} ∪ rhs i` lies in `[1,N]`, `rhs i` is nonempty and does
not contain the target, and every integer in `[1,N]` has total incident
certificate weight at most `C`, then every sum-free `A ⊆ [1,N]` satisfies

`C * A.card + Σᵢ weight i ≤ C * N`.

This is the Lean-side verifier shape for overlapping LP certificates. -/
theorem weighted_sum_free_certificate_bound (N C : ℕ) (A I : Finset ℕ)
    (target : ℕ → ℕ) (rhs : ℕ → Finset ℕ) (weight : ℕ → ℕ)
    (hA : SumFree A) (hAN : A ⊆ Finset.Icc 1 N)
    (hedgeN : ∀ i ∈ I, insert (target i) (rhs i) ⊆ Finset.Icc 1 N)
    (hrhs_nonempty : ∀ i ∈ I, (rhs i).Nonempty)
    (htarget_not_rhs : ∀ i ∈ I, target i ∉ rhs i)
    (hidentity : ∀ i ∈ I,
      (1 / (target i : ℕ) : ℚ) = ∑ b ∈ rhs i, (1 / b : ℚ))
    (hload : ∀ x ∈ Finset.Icc 1 N,
      (∑ i ∈ I, if x ∈ insert (target i) (rhs i) then weight i else 0) ≤ C) :
    C * A.card + (∑ i ∈ I, weight i) ≤ C * N := by
  classical
  have hforbid : ∀ i ∈ I, ¬ insert (target i) (rhs i) ⊆ A := by
    intro i hi hedgeA
    have htA : target i ∈ A := hedgeA (Finset.mem_insert_self _ _)
    have hrhs_sub : rhs i ⊆ A.erase (target i) := by
      intro b hb
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hbt
        exact htarget_not_rhs i hi (by simpa [hbt] using hb)
      · exact hedgeA (Finset.mem_insert_of_mem hb)
    exact hA (target i) htA (rhs i) hrhs_sub (hrhs_nonempty i hi) (hidentity i hi)
  have h := WeightedPacking.weighted_forbidden_edge_bound (Finset.Icc 1 N) A I
    (fun i => insert (target i) (rhs i)) weight C hAN hedgeN hforbid hload
  simpa using h

/-- A parametric weighted template theorem for Problem #301.

The finite template `I` consists of multiplier identities

`1 / target i = Σ_{m ∈ rhs i} 1 / m`

with integer weights. For each parameter `a ∈ D`, the identity scales to

`1 / (target i * a) = Σ_{m ∈ rhs i} 1 / (m * a)`.

If the scaled template edges lie in pairwise-disjoint gadgets inside `[1,N]`
and have local load at most `C` on each gadget, then all copies contribute to a
global denominator-cleared bound. This is the Lean bridge from a finite
multiplier-template LP certificate to an asymptotic packing theorem. -/
theorem weighted_scaled_sum_free_family_bound (N C : ℕ) (A D I : Finset ℕ)
    (gadget : ℕ → Finset ℕ) (target : ℕ → ℕ) (rhs : ℕ → Finset ℕ)
    (weight : ℕ → ℕ)
    (hA : SumFree A) (hAN : A ⊆ Finset.Icc 1 N)
    (hDpos : ∀ a ∈ D, 0 < a)
    (hpwd : (↑D : Set ℕ).PairwiseDisjoint gadget)
    (hgadgetN : ∀ a ∈ D, gadget a ⊆ Finset.Icc 1 N)
    (hedgeG : ∀ a ∈ D, ∀ i ∈ I,
      insert (target i * a) ((rhs i).image fun m => m * a) ⊆ gadget a)
    (hrhs_nonempty : ∀ i ∈ I, (rhs i).Nonempty)
    (htarget_not_rhs : ∀ i ∈ I, target i ∉ rhs i)
    (hidentity : ∀ i ∈ I,
      (1 / (target i : ℕ) : ℚ) = ∑ m ∈ rhs i, (1 / m : ℚ))
    (hload : ∀ a ∈ D, ∀ x ∈ gadget a,
      (∑ i ∈ I,
        if x ∈ insert (target i * a) ((rhs i).image fun m => m * a)
        then weight i else 0) ≤ C) :
    C * A.card + D.card * (∑ i ∈ I, weight i) ≤ C * N := by
  classical
  let edge : ℕ → ℕ → Finset ℕ := fun a i =>
    insert (target i * a) ((rhs i).image fun m => m * a)
  have hforbid : ∀ a ∈ D, ∀ i ∈ I, ¬ edge a i ⊆ A := by
    intro a ha i hi hedgeA
    have ha_pos : 0 < a := hDpos a ha
    have htarget_edge : target i * a ∈ edge a i := Finset.mem_insert_self _ _
    have htarget_Icc : target i * a ∈ Finset.Icc 1 N :=
      hgadgetN a ha (hedgeG a ha i hi htarget_edge)
    have htarget_pos : 0 < target i := by
      by_cases ht0 : target i = 0
      · simp [ht0] at htarget_Icc
      · exact Nat.pos_of_ne_zero ht0
    have htA : target i * a ∈ A := hedgeA htarget_edge
    let Rscaled : Finset ℕ := (rhs i).image fun m => m * a
    have hRscaled_sub : Rscaled ⊆ A.erase (target i * a) := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨m, hm, rfl⟩
      rw [Finset.mem_erase]
      refine ⟨?_, hedgeA (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, hm, rfl⟩))⟩
      intro hEq
      have hm_eq : m = target i := Nat.eq_of_mul_eq_mul_right ha_pos hEq
      exact htarget_not_rhs i hi (by simpa [hm_eq] using hm)
    have hRscaled_nonempty : Rscaled.Nonempty := by
      obtain ⟨m, hm⟩ := hrhs_nonempty i hi
      exact ⟨m * a, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
    have hsum_image :
        (∑ b ∈ Rscaled, (1 / b : ℚ)) =
          ∑ m ∈ rhs i, (1 / (m * a : ℕ) : ℚ) := by
      dsimp [Rscaled]
      rw [Finset.sum_image]
      intro m hm n hn hmn
      exact Nat.eq_of_mul_eq_mul_right ha_pos hmn
    have hscaled :
        (1 / (target i * a : ℕ) : ℚ) =
          ∑ m ∈ rhs i, (1 / (m * a : ℕ) : ℚ) := by
      have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have htQ : (target i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have htarget_scale :
          (1 / (target i * a : ℕ) : ℚ) =
            (1 / (a : ℚ)) * (1 / (target i : ℚ)) := by
        push_cast
        field_simp [haQ, htQ]
      calc
        (1 / (target i * a : ℕ) : ℚ)
            = (1 / (a : ℚ)) * (1 / (target i : ℚ)) := htarget_scale
        _ = (1 / (a : ℚ)) * (∑ m ∈ rhs i, (1 / (m : ℚ))) := by
          rw [hidentity i hi]
        _ = ∑ m ∈ rhs i, (1 / (a : ℚ)) * (1 / (m : ℚ)) := by
          rw [Finset.mul_sum]
        _ = ∑ m ∈ rhs i, (1 / (m * a : ℕ) : ℚ) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hm_edge : m * a ∈ edge a i :=
            Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
          have hm_Icc : m * a ∈ Finset.Icc 1 N :=
            hgadgetN a ha (hedgeG a ha i hi hm_edge)
          have hm_pos : 0 < m := by
            by_cases hm0 : m = 0
            · simp [hm0] at hm_Icc
            · exact Nat.pos_of_ne_zero hm0
          have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          symm
          push_cast
          field_simp [haQ, hmQ]
    exact hA (target i * a) htA Rscaled hRscaled_sub hRscaled_nonempty
      (hscaled.trans hsum_image.symm)
  have h := WeightedPacking.weighted_forbidden_disjoint_family_bound (Finset.Icc 1 N)
    A D I gadget edge weight C hAN hpwd hgadgetN hedgeG hforbid hload
  simpa using h

end UnitFractionSets
