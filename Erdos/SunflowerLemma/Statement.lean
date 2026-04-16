/-
# Erdős Problem 20: The Sunflower Lemma

Let `f(n,k)` be minimal such that every `n`-uniform family of at least
`f(n,k)` sets contains a `k`-sunflower. Erdős asked whether `f(n,k) < c_k^n`
for some constant `c_k > 0`.

We package finite set families as `Finset (Finset ℕ)`.

Reference: https://www.erdosproblems.com/20
-/
import Mathlib

namespace SunflowerLemma

/-- An `n`-uniform family is a finite family whose members all have size `n`. -/
def Uniform (n : ℕ) (𝒜 : Finset (Finset ℕ)) : Prop :=
  ∀ s ∈ 𝒜, s.card = n

/-- A finite family is a sunflower with core `core` if every member contains
the core and any two distinct members intersect exactly in the core. -/
def IsSunflower (core : Finset ℕ) (𝒜 : Finset (Finset ℕ)) : Prop :=
  ∀ s ∈ 𝒜, core ⊆ s ∧ ∀ t ∈ 𝒜, s ≠ t → s ∩ t = core

/-- A family contains a `k`-sunflower if it has a `k`-element subfamily which is
a sunflower with some core. -/
def ContainsSunflower (k : ℕ) (𝒜 : Finset (Finset ℕ)) : Prop :=
  ∃ 𝒮 ⊆ 𝒜, 𝒮.card = k ∧ ∃ core, IsSunflower core 𝒮

/-- `SunflowerBound n k m` means that every `n`-uniform family of cardinality at
least `m` contains a `k`-sunflower. -/
def SunflowerBound (n k m : ℕ) : Prop :=
  ∀ 𝒜 : Finset (Finset ℕ),
    Uniform n 𝒜 →
    m ≤ 𝒜.card →
    ContainsSunflower k 𝒜

/-- The extremal quantity from Erdős problem `#20`. -/
noncomputable def sunflowerNumber (n k : ℕ) : ℕ :=
  sInf {m : ℕ | SunflowerBound n k m}

end SunflowerLemma
