import Mathlib

/-!
# Erdős Problem 431: The Inverse Goldbach Problem

Are there infinite sets `A, B ⊆ ℕ` such that the sumset `A + B` agrees with the
set of prime numbers up to finitely many exceptions?

Reference: https://www.erdosproblems.com/431
-/

open Set

namespace InverseGoldbach

/-- The pairwise sumset `A + B` inside `ℕ`. -/
def pairSumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, a + b = n}

@[simp] theorem mem_pairSumset {A B : Set ℕ} {n : ℕ} :
    n ∈ pairSumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = n :=
  Iff.rfl

/-- `AgreesWithPrimesEventually S` means that `S` differs from the prime numbers
only on a finite initial segment. -/
def AgreesWithPrimesEventually (S : Set ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, n ∈ S ↔ Nat.Prime n

/-- Erdős problem `#431`: can an additive sumset of two infinite subsets of `ℕ`
eventually coincide with the prime numbers? -/
def InverseGoldbachProblem : Prop :=
  ∃ A B : Set ℕ,
    A.Infinite ∧ B.Infinite ∧ AgreesWithPrimesEventually (pairSumset A B)

/-- The even elements of a subset of `ℕ`. -/
def evenPart (A : Set ℕ) : Set ℕ :=
  {n | n ∈ A ∧ Even n}

/-- The odd elements of a subset of `ℕ`. -/
def oddPart (A : Set ℕ) : Set ℕ :=
  {n | n ∈ A ∧ Odd n}

@[simp] theorem mem_evenPart {A : Set ℕ} {n : ℕ} :
    n ∈ evenPart A ↔ n ∈ A ∧ Even n :=
  Iff.rfl

@[simp] theorem mem_oddPart {A : Set ℕ} {n : ℕ} :
    n ∈ oddPart A ↔ n ∈ A ∧ Odd n :=
  Iff.rfl

end InverseGoldbach
