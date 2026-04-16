/- 
# Erdős Problem 864: Almost-Sidon Sets with One Exceptional Sum

Erdős and Freud asked for the largest possible size of a set
`A ⊆ {1, ..., N}` such that there is at most one integer with more than one
representation as `a + b` with `a ≤ b` and `a, b ∈ A`.

Reference: https://www.erdosproblems.com/864
-/
import Erdos.SidonSumsets.Statement

namespace AlmostSidonSets

open SidonSumsets

/-- The finite interval `{1, ..., N}`. -/
def ground (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- A finite Sidon set, via coercion to a set. -/
def IsSidonFinset (A : Finset ℕ) : Prop :=
  IsSidon (A : Set ℕ)

/-- `n` has two distinct sorted representations as a sum of elements of `A`. -/
def HasTwoSumReprs (A : Finset ℕ) (n : ℕ) : Prop :=
  ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ A, ∃ b₂ ∈ A,
    a₁ ≤ a₂ ∧
    b₁ ≤ b₂ ∧
    a₁ + a₂ = n ∧
    b₁ + b₂ = n ∧
    (a₁ ≠ b₁ ∨ a₂ ≠ b₂)

/-- A finite set is *almost Sidon* if there is at most one integer with two
distinct sorted two-term sum representations. -/
def AlmostSidonFinset (A : Finset ℕ) : Prop :=
  ∀ m n : ℕ, HasTwoSumReprs A m → HasTwoSumReprs A n → m = n

/-- An almost-Sidon set contained in `{1, ..., N}`. -/
def AlmostSidonInInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  AlmostSidonFinset A ∧ ∀ a ∈ A, a ∈ ground N

/-- Asymptotic packaging of Erdős and Freud's upper-bound question. -/
def OptimalUpperBoundConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ ⦃N : ℕ⦄, N₀ ≤ N →
    ∀ A : Finset ℕ, AlmostSidonInInterval A N →
      (A.card : ℝ) ≤ (((2 : ℝ) / Real.sqrt 3) + ε) * Real.sqrt N

@[simp] theorem mem_ground {N x : ℕ} :
    x ∈ ground N ↔ 1 ≤ x ∧ x ≤ N := by
  simp [ground]

end AlmostSidonSets
