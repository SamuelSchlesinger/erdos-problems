/-
# Erdős Problem 152: Isolated Sums in Sidon Sumsets

Erdős, Sárközy, and Sós studied isolated elements of `A + A` when `A` is a
finite Sidon set. This directory begins a formal attack on an infinite variant:
must every infinite Sidon set have infinitely many isolated sums?

Reference: https://www.erdosproblems.com/152
-/
import Mathlib

namespace SidonSumsets

/-- A set of naturals is Sidon if ordered sum representations are unique after
sorting the summands. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂ : ℕ⦄,
    a₁ ∈ A →
    a₂ ∈ A →
    b₁ ∈ A →
    b₂ ∈ A →
    a₁ ≤ a₂ →
    b₁ ≤ b₂ →
    a₁ + a₂ = b₁ + b₂ →
    a₁ = b₁ ∧ a₂ = b₂

/-- The sumset `A + A`, written as a set of naturals. -/
def sumset (A : Set ℕ) : Set ℕ :=
  {s : ℕ | ∃ a ∈ A, ∃ b ∈ A, a + b = s}

/-- `s` is isolated in `S` if both immediate neighbors are absent. -/
def Isolated (S : Set ℕ) (s : ℕ) : Prop :=
  s ∈ S ∧ s - 1 ∉ S ∧ s + 1 ∉ S

/-- Value truncation of a set of naturals. -/
def truncateByValue (A : Set ℕ) (N : ℕ) : Set ℕ :=
  {a : ℕ | a ∈ A ∧ a ≤ N}

/-- Isolated sums detected strictly below the truncation threshold. -/
def lowerIsolated (A : Set ℕ) (N : ℕ) : Set ℕ :=
  {s : ℕ | s < N ∧ Isolated (sumset (truncateByValue A N)) s}

/-- Infinite Sidon analogue of Erdős problem #152. -/
def infiniteConjecture : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsSidon A → {s : ℕ | Isolated (sumset A) s}.Infinite

@[simp] theorem mem_sumset {A : Set ℕ} {s : ℕ} :
    s ∈ sumset A ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = s :=
  Iff.rfl

@[simp] theorem mem_truncateByValue {A : Set ℕ} {N a : ℕ} :
    a ∈ truncateByValue A N ↔ a ∈ A ∧ a ≤ N :=
  Iff.rfl

@[simp] theorem mem_lowerIsolated {A : Set ℕ} {N s : ℕ} :
    s ∈ lowerIsolated A N ↔ s < N ∧ Isolated (sumset (truncateByValue A N)) s :=
  Iff.rfl

end SidonSumsets
