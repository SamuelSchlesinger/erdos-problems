/-
# Erdős Problem 25: Residue-Class Avoidance and Logarithmic Density

Let `1 ≤ n₁ < n₂ < ⋯` be an arbitrary sequence of integers, each with an
associated residue class `aᵢ mod nᵢ`. Let `A` be the set of integers `n` such
that for every `i`, either `n < nᵢ` or `n` is not congruent to `aᵢ` modulo
`nᵢ`. Problem `#25` asks whether the logarithmic density of `A` must exist.

We model the ambient set for logarithmic density as the positive natural
numbers; the value at `0` is harmless because the finite logarithmic sums below
start at `1`.

Reference: https://www.erdosproblems.com/25
-/
import Mathlib

namespace ResidueAvoidingDensity

/-- A residue-class avoidance system consists of a strictly increasing sequence
of positive moduli and one residue attached to each modulus.

The sequence is indexed by `ℕ`, so the first modulus is `modulus 0`; this is
the Lean version of the mathematical sequence `n₁, n₂, ...`. -/
structure ResidueSystem where
  modulus : ℕ → ℕ
  residue : ℕ → ℕ
  modulus_pos : ∀ i, 0 < modulus i
  strictMono_modulus : StrictMono modulus

namespace ResidueSystem

/-- The `i`-th avoidance condition for an integer `n`: before the modulus
appears the condition is vacuous, and afterward `n` must avoid the prescribed
residue class modulo `modulus i`. -/
def SatisfiesConstraint (S : ResidueSystem) (i n : ℕ) : Prop :=
  n < S.modulus i ∨ ¬ n ≡ S.residue i [MOD S.modulus i]

/-- `n` satisfies all constraints whose indices lie in `I`. This is useful for
finite or partial collections of constraints. -/
def AvoidsOn (S : ResidueSystem) (I : Set ℕ) (n : ℕ) : Prop :=
  ∀ i, i ∈ I → S.SatisfiesConstraint i n

/-- The set of integers satisfying all constraints with indices in `I`. -/
def avoidedSetOn (S : ResidueSystem) (I : Set ℕ) : Set ℕ :=
  {n | S.AvoidsOn I n}

/-- `n` satisfies the first `k` constraints. For `k = 0` this imposes no
restriction. -/
def AvoidsUpTo (S : ResidueSystem) (k n : ℕ) : Prop :=
  ∀ i, i < k → S.SatisfiesConstraint i n

/-- The integers satisfying the first `k` residue-class avoidance constraints. -/
def avoidedSetUpTo (S : ResidueSystem) (k : ℕ) : Set ℕ :=
  {n | S.AvoidsUpTo k n}

/-- The full avoided set from Erdős problem `#25`. -/
def avoidedSet (S : ResidueSystem) : Set ℕ :=
  {n | ∀ i, S.SatisfiesConstraint i n}

/-- The logarithmic contribution of `n` to a set `A`. It is noncomputable only
because membership in an arbitrary set is classically decidable. -/
noncomputable def finiteLogWeight (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then (n : ℝ)⁻¹ else 0

/-- The finite logarithmic numerator `∑_{1 ≤ n ≤ N, n ∈ A} 1 / n`. -/
noncomputable def finiteLogSum (A : Set ℕ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 N) fun n => finiteLogWeight A n

/-- The harmonic normalizing denominator `∑_{1 ≤ n ≤ N} 1 / n`. -/
noncomputable def harmonicLogSum (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 N) fun n => (n : ℝ)⁻¹

/-- The finite logarithmic density ratio for a set `A` up to height `N`. -/
noncomputable def finiteLogDensity (A : Set ℕ) (N : ℕ) : ℝ :=
  finiteLogSum A N / harmonicLogSum N

/-- A set has logarithmic density `d` if its finite logarithmic densities tend
to `d` along the natural numbers. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => finiteLogDensity A N) Filter.atTop (nhds d)

/-- The logarithmic density of `A` exists. -/
def LogDensityExists (A : Set ℕ) : Prop :=
  ∃ d : ℝ, HasLogDensity A d

/-- Erdős problem `#25`: every residue-class avoidance system has an avoided
set with logarithmic density. -/
def Erdos25Conjecture : Prop :=
  ∀ S : ResidueSystem, LogDensityExists S.avoidedSet

end ResidueSystem

end ResidueAvoidingDensity
