import Erdos.PermutationMonotoneAP.Statement

/-!
# Density reduction for Erdős #197 (Erdős–Graham partition)

We set up natural upper/lower density and formalize the LeSaulnier–Vijay
reduction: if every 3-free set `S` has `upperDensity S ≤ uA` and
`lowerDensity S ≤ uB` with `uA + uB < 1`, then `ℕ` cannot be partitioned into
two 3-free sets (so Erdős #197 has a negative answer).

This pins down exactly what a resolution of #197 requires: density UPPER bounds
on 3-free sets. The conjecture is `α(3) = 1/2`, `β(3) = 1/4` (sum `3/4 < 1`),
but no nontrivial upper bound is currently known — that gap is the open content.

Reference: LeSaulnier, Vijay, *On permutations avoiding arithmetic progressions*,
arXiv:1004.1740.
-/

namespace PermutationMonotoneAP

open Filter

/-- The number of elements of `S` in `{0, 1, …, n-1}`. -/
noncomputable def countMem (S : Set ℕ) (n : ℕ) : ℕ := (S ∩ Set.Iio n).ncard

/-- The density ratio `|S ∩ [0,n)| / n`. -/
noncomputable def densityRatio (S : Set ℕ) (n : ℕ) : ℝ := (countMem S n : ℝ) / n

/-- Upper natural density of `S ⊆ ℕ`. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ := limsup (densityRatio S) atTop

/-- Lower natural density of `S ⊆ ℕ`. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ := liminf (densityRatio S) atTop

/-- A set and its complement partition the counts: `|A ∩ [0,n)| + |Aᶜ ∩ [0,n)| = n`. -/
theorem countMem_add_countMem_compl (A : Set ℕ) (n : ℕ) :
    countMem A n + countMem Aᶜ n = n := by
  have hf1 : (A ∩ Set.Iio n).Finite := (Set.finite_Iio n).subset Set.inter_subset_right
  have hf2 : (Aᶜ ∩ Set.Iio n).Finite := (Set.finite_Iio n).subset Set.inter_subset_right
  have hdisj : Disjoint (A ∩ Set.Iio n) (Aᶜ ∩ Set.Iio n) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨hxA, _⟩ ⟨hxAc, _⟩
    exact hxAc hxA
  have hunion : (A ∩ Set.Iio n) ∪ (Aᶜ ∩ Set.Iio n) = Set.Iio n := by
    rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
  rw [countMem, countMem, ← Set.ncard_union_eq hdisj hf1 hf2, hunion, Set.ncard_Iio_nat]

/-- For `n ≥ 1`, the complementary density ratio is `1 - densityRatio A n`. -/
theorem densityRatio_compl {A : Set ℕ} {n : ℕ} (hn : n ≠ 0) :
    densityRatio Aᶜ n = 1 - densityRatio A n := by
  have hsum : (countMem A n : ℝ) + (countMem Aᶜ n : ℝ) = n := by
    exact_mod_cast countMem_add_countMem_compl A n
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [densityRatio, densityRatio]
  field_simp
  linarith [hsum]

/-- The density ratio is bounded above by `1`. -/
theorem densityRatio_le_one (S : Set ℕ) (n : ℕ) : densityRatio S n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [densityRatio, h]
  · rw [densityRatio, div_le_one (by exact_mod_cast h)]
    have hle : countMem S n ≤ n := by
      rw [countMem]
      have h2 : (S ∩ Set.Iio n).ncard ≤ (Set.Iio n).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Iio n)
      rwa [Set.ncard_Iio_nat] at h2
    exact_mod_cast hle

/-- The density ratio is nonnegative. -/
theorem densityRatio_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ densityRatio S n :=
  div_nonneg (by positivity) (by positivity)

theorem isBoundedUnder_le_densityRatio (S : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (densityRatio S) :=
  ⟨1, eventually_map.mpr (Eventually.of_forall fun n => densityRatio_le_one S n)⟩

theorem isBoundedUnder_ge_densityRatio (S : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (densityRatio S) :=
  ⟨0, eventually_map.mpr (Eventually.of_forall fun n => densityRatio_nonneg S n)⟩

theorem isCoboundedUnder_le_densityRatio (S : Set ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop (densityRatio S) :=
  (isBoundedUnder_ge_densityRatio S).isCoboundedUnder_le

/-- **Key density identity.** For any `A ⊆ ℕ`,
`upperDensity A + lowerDensity Aᶜ = 1`. -/
theorem upperDensity_add_lowerDensity_compl (A : Set ℕ) :
    upperDensity A + lowerDensity Aᶜ = 1 := by
  have hcongr : lowerDensity Aᶜ = liminf (fun n => 1 - densityRatio A n) atTop := by
    unfold lowerDensity
    exact liminf_congr
      (by filter_upwards [eventually_ne_atTop 0] with n hn using densityRatio_compl hn)
  rw [hcongr, liminf_const_sub atTop (densityRatio A) 1
      (isBoundedUnder_le_densityRatio A) (isCoboundedUnder_le_densityRatio A)]
  unfold upperDensity
  ring

/-- **LeSaulnier–Vijay reduction.** If there are constants `uA, uB` bounding the
upper density and lower density (respectively) of every 3-free set, with
`uA + uB < 1`, then `ℕ` cannot be partitioned into two 3-free sets — i.e.
Erdős problem #197 has a negative answer. This is exactly the open target:
prove such density upper bounds (conjecturally `uA = 1/2`, `uB = 1/4`). -/
theorem not_erdos197_of_density_bounds {uA uB : ℝ} (hsum : uA + uB < 1)
    (hupper : ∀ S : Set ℕ, IsFree S 3 → upperDensity S ≤ uA)
    (hlower : ∀ S : Set ℕ, IsFree S 3 → lowerDensity S ≤ uB) :
    ¬ Erdos197 := by
  rintro ⟨A, B, hpart, hA, hB⟩
  have hBeq : B = Aᶜ := by
    ext n
    have := hpart n
    simp only [Set.mem_compl_iff]
    tauto
  have hBfree : IsFree Aᶜ 3 := hBeq ▸ hB
  have key : upperDensity A + lowerDensity Aᶜ = 1 := upperDensity_add_lowerDensity_compl A
  have h1 : upperDensity A ≤ uA := hupper A hA
  have h2 : lowerDensity Aᶜ ≤ uB := hlower Aᶜ hBfree
  linarith

/-- **Conditional resolution of Erdős #197.** Under the LeSaulnier–Vijay density
conjecture `α(3) = 1/2`, `β(3) = 1/4` (here stated as the upper bounds
`upperDensity S ≤ 1/2` and `lowerDensity S ≤ 1/4` for every 3-free set `S`),
the Erdős–Graham partition problem has a negative answer: `ℕ` cannot be
partitioned into two 3-free sets. -/
theorem not_erdos197_of_conjecture
    (hupper : ∀ S : Set ℕ, IsFree S 3 → upperDensity S ≤ 1 / 2)
    (hlower : ∀ S : Set ℕ, IsFree S 3 → lowerDensity S ≤ 1 / 4) :
    ¬ Erdos197 :=
  not_erdos197_of_density_bounds (by norm_num) hupper hlower

end PermutationMonotoneAP
