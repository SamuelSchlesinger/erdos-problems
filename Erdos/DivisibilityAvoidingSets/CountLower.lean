import Erdos.DivisibilityAvoidingSets.GoodCore

/-!
# Counting lower bounds from certified blocks

The block template proves that certain arithmetic-progression blocks are
avoiding and glue together safely.  This file records the elementary counting
step: a whole block contained in `A ∩ {1, ..., N}` contributes its full length
to `countUpTo A N`.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- If an AP block lies inside `A` and below `N`, its finset model lies in the
finset used by `countUpTo A N`. -/
theorem apBlockFinset_subset_countUpToFilter {A : Set ℕ} {r M T L N : ℕ}
    [DecidablePred fun n : ℕ => n ∈ A]
    (hsub : apBlock r M T L ⊆ A)
    (hmin : 1 ≤ apMin r M T)
    (hmax : apMax r M T L ≤ N) :
    apBlockFinset r M T L ⊆ (Finset.Icc 1 N).filter fun n => n ∈ A := by
  intro n hn
  have hblock : n ∈ apBlock r M T L := by
    simpa using hn
  have hn_min : 1 ≤ n := hmin.trans (apMin_le_of_mem_apBlock hblock)
  have hn_max : n ≤ N := (le_apMax_of_mem_apBlock hblock).trans hmax
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn_min, hn_max⟩, hsub hblock⟩

/-- A contained AP block gives a natural-number lower bound for the counting
function. -/
theorem apBlock_length_le_countUpTo {A : Set ℕ} {r M T L N : ℕ}
    (hM : 0 < M)
    (hsub : apBlock r M T L ⊆ A)
    (hmin : 1 ≤ apMin r M T)
    (hmax : apMax r M T L ≤ N) :
    L ≤ countUpTo A N := by
  classical
  unfold countUpTo
  rw [← apBlockFinset_card (r := r) (M := M) (T := T) (L := L) hM]
  exact Finset.card_le_card (apBlockFinset_subset_countUpToFilter hsub hmin hmax)

/-- The same lower bound as a real inequality. -/
theorem apBlock_length_le_countUpTo_real {A : Set ℕ} {r M T L N : ℕ}
    (hM : 0 < M)
    (hsub : apBlock r M T L ⊆ A)
    (hmin : 1 ≤ apMin r M T)
    (hmax : apMax r M T L ≤ N) :
    (L : ℝ) ≤ (countUpTo A N : ℝ) := by
  exact_mod_cast apBlock_length_le_countUpTo (A := A) (r := r) (M := M)
    (T := T) (L := L) (N := N) hM hsub hmin hmax

/-- If `N ≤ L ^ 2`, then the real square root of `N` is at most `L`. -/
theorem sqrt_nat_le_of_le_sq {N L : ℕ} (hNL : N ≤ L ^ 2) :
    Real.sqrt (N : ℝ) ≤ (L : ℝ) := by
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  exact_mod_cast hNL

/-- A block of length at least `sqrt N`, contained in `A ∩ {1, ..., N}`, gives
the desired square-root counting lower bound. -/
theorem sqrt_le_countUpTo_of_block {A : Set ℕ} {r M T L N : ℕ}
    (hM : 0 < M)
    (hsub : apBlock r M T L ⊆ A)
    (hmin : 1 ≤ apMin r M T)
    (hmax : apMax r M T L ≤ N)
    (hNL : N ≤ L ^ 2) :
    Real.sqrt (N : ℝ) ≤ (countUpTo A N : ℝ) :=
  (sqrt_nat_le_of_le_sq hNL).trans
    (apBlock_length_le_countUpTo_real hM hsub hmin hmax)

/-- An abstract block-cover criterion for positive square-root lower density.
For every large `N`, it is enough to find one certified block inside `A`,
below `N`, whose length has square at least `N`. -/
theorem hasPositiveSqrtLiminf_of_eventual_block_cover {A : Set ℕ}
    (hcover :
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ ⦃N : ℕ⦄, N₀ ≤ N →
        ∃ r M T L : ℕ,
          0 < M ∧
          apBlock r M T L ⊆ A ∧
          1 ≤ apMin r M T ∧
          apMax r M T L ≤ N ∧
          N ≤ L ^ 2) :
    HasPositiveSqrtLiminf A := by
  rcases hcover with ⟨N₀, hN₀one, hN₀⟩
  refine ⟨1, by norm_num, N₀, hN₀one, ?_⟩
  intro N hN
  obtain ⟨r, M, T, L, hM, hsub, hmin, hmax, hNL⟩ := hN₀ hN
  have hNpos : 0 < N := by omega
  have hsqrt_count : Real.sqrt (N : ℝ) ≤ (countUpTo A N : ℝ) :=
    sqrt_le_countUpTo_of_block hM hsub hmin hmax hNL
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  rw [le_div_iff₀ hsqrt_pos]
  simpa using hsqrt_count

/-- A positive avoiding set satisfying the block-cover criterion answers the
first density question affirmatively. -/
theorem erdos12_positiveSqrtDensity_of_eventual_block_cover {A : Set ℕ}
    (hAinf : A.Infinite) (hApos : PositiveSet A) (hAavoid : AvoidingSet A)
    (hcover :
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ ⦃N : ℕ⦄, N₀ ≤ N →
        ∃ r M T L : ℕ,
          0 < M ∧
          apBlock r M T L ⊆ A ∧
          1 ≤ apMin r M T ∧
          apMax r M T L ≤ N ∧
          N ≤ L ^ 2) :
    Erdos12PositiveSqrtDensityQuestion :=
  ⟨A, hAinf, hApos, hAavoid, hasPositiveSqrtLiminf_of_eventual_block_cover hcover⟩

end DivisibilityAvoidingSets
