import Erdos.DivisibilityAvoidingSets.BlockTemplate

/-!
# Dense core consequences for Erdős problem #12

The live status of problem #12 says that the square-root density question has a
positive answer and the power-saving question has a negative answer.  Both
follow from a single stronger construction: an avoiding set whose counting
function is eventually at least `N^(1 - ε)` for every `ε > 0`.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- A set has eventual subpower lower density if for every positive exponent
saving `ε`, its count is eventually at least `N^(1 - ε)`. -/
def HasEventuallySubpowerLowerDensity (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ ⦃N : ℕ⦄, N₀ ≤ N →
      (N : ℝ) ^ (1 - ε) ≤ (countUpTo A N : ℝ)

/-- A single fixed-exponent eventual lower bound, used as a flexible
counterexample package for the power-saving question. -/
def HasEventuallyPowerLowerDensity (A : Set ℕ) (c : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ ⦃N : ℕ⦄, N₀ ≤ N →
    (N : ℝ) ^ (1 - c) ≤ (countUpTo A N : ℝ)

/-- Eventual subpower lower density implies the square-root liminf package in
the statement of problem #12. -/
theorem HasEventuallySubpowerLowerDensity.hasPositiveSqrtLiminf {A : Set ℕ}
    (hA : HasEventuallySubpowerLowerDensity A) :
    HasPositiveSqrtLiminf A := by
  obtain ⟨N₀, hN₀⟩ := hA (1 / 2) (by norm_num)
  refine ⟨1, by norm_num, max 1 N₀, by omega, ?_⟩
  intro N hN
  have hN₀le : N₀ ≤ N := le_trans (Nat.le_max_right _ _) hN
  have hNpos : 0 < N := by omega
  have hcount : Real.sqrt (N : ℝ) ≤ (countUpTo A N : ℝ) := by
    have h := hN₀ hN₀le
    have hhalf : (1 : ℝ) - 2⁻¹ = (2⁻¹ : ℝ) := by norm_num
    simpa [Real.sqrt_eq_rpow, one_div, hhalf] using h
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  rw [le_div_iff₀ hsqrt_pos]
  simpa using hcount

/-- A positive avoiding set with eventual subpower lower density answers the
first density question affirmatively. -/
theorem erdos12_positiveSqrtDensity_of_subpower_dense {A : Set ℕ}
    (hAinf : A.Infinite) (hApos : PositiveSet A) (hAavoid : AvoidingSet A)
    (hdense : HasEventuallySubpowerLowerDensity A) :
    Erdos12PositiveSqrtDensityQuestion :=
  ⟨A, hAinf, hApos, hAavoid, hdense.hasPositiveSqrtLiminf⟩

/-- A positive avoiding set with eventual subpower lower density disproves the
uniform power-saving question. -/
theorem not_erdos12PowerSaving_of_subpower_dense {A : Set ℕ}
    (hAinf : A.Infinite) (hApos : PositiveSet A) (hAavoid : AvoidingSet A)
    (hdense : HasEventuallySubpowerLowerDensity A) :
    ¬ Erdos12PowerSavingQuestion := by
  rintro ⟨c, hcpos, hforall⟩
  obtain ⟨N₀, hN₀⟩ := hdense c hcpos
  have hbad_finite :
      {N : ℕ | (countUpTo A N : ℝ) < (N : ℝ) ^ (1 - c)}.Finite := by
    refine (Set.finite_lt_nat N₀).subset ?_
    intro N hNbad
    by_contra hnot
    have hle : N₀ ≤ N := Nat.le_of_not_gt hnot
    exact not_lt_of_ge (hN₀ hle) hNbad
  exact (hforall A hAinf hApos hAavoid) hbad_finite

/-- To refute the uniform power-saving question, it is enough to construct,
for every positive saving `c`, one positive avoiding set with an eventual
`N^(1-c)` lower bound. -/
theorem not_erdos12PowerSaving_of_counterexamples
    (hcounter :
      ∀ c : ℝ, 0 < c →
        ∃ A : Set ℕ, A.Infinite ∧ PositiveSet A ∧ AvoidingSet A ∧
          HasEventuallyPowerLowerDensity A c) :
    ¬ Erdos12PowerSavingQuestion := by
  rintro ⟨c, hcpos, hforall⟩
  obtain ⟨A, hAinf, hApos, hAavoid, N₀, hN₀⟩ := hcounter c hcpos
  have hbad_finite :
      {N : ℕ | (countUpTo A N : ℝ) < (N : ℝ) ^ (1 - c)}.Finite := by
    refine (Set.finite_lt_nat N₀).subset ?_
    intro N hNbad
    by_contra hnot
    have hle : N₀ ≤ N := Nat.le_of_not_gt hnot
    exact not_lt_of_ge (hN₀ hle) hNbad
  exact (hforall A hAinf hApos hAavoid) hbad_finite

end DivisibilityAvoidingSets
