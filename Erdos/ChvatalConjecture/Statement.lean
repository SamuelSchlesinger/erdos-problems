/-
# Erdős Problem 701: Chvátal's Conjecture

Let `𝒜` be a family of finite sets closed under taking subsets. Erdős asked
whether there is some element `x` such that every intersecting subfamily of `𝒜`
has size at most the `x`-star `{s ∈ 𝒜 | x ∈ s}`.

We package the problem on finite ground sets `Fin (n + 1)` so that a candidate
element `x` is always available.

Reference: https://www.erdosproblems.com/701
-/
import Mathlib

namespace ChvatalConjecture

/-- A finite set family is down-closed if it is closed under passing to
subsets. -/
def DownClosed {α : Type*} (𝒜 : Finset (Finset α)) : Prop :=
  IsLowerSet (𝒜 : Set (Finset α))

/-- The `x`-star of a finite set family consists of all members that contain
`x`. -/
def star {α : Type*} [DecidableEq α] (x : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter fun s => x ∈ s

/-- The `x`-star maximizes intersecting subfamilies if every intersecting
subfamily of `𝒜` has cardinality at most that star. -/
def StarMaximizesIntersecting {α : Type*} [DecidableEq α]
    (x : α) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ℱ : Finset (Finset α),
    (ℱ : Set (Finset α)).Intersecting →
    ℱ ⊆ 𝒜 →
    ℱ.card ≤ (star x 𝒜).card

/-- Finite-set formulation of Erdős problem `#701`. -/
def Erdos701Conjecture : Prop :=
  ∀ n : ℕ, ∀ 𝒜 : Finset (Finset (Fin (n + 1))),
    DownClosed 𝒜 →
    ∃ x : Fin (n + 1), StarMaximizesIntersecting x 𝒜

end ChvatalConjecture
