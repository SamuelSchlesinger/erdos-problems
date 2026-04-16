/-
# Erdős Problem 901: Property B Bounds for Uniform Hypergraphs

Let `m(n)` be minimal such that there is an `n`-uniform hypergraph with `m(n)`
edges which is `3`-chromatic, equivalently does not have Property B. Estimate
`m(n)`.

We model a finite hypergraph as a finite family of finite edges on a finite
vertex type. A Property B witness is a set of vertices that contains no edge
and whose complement also contains no edge, i.e. a `2`-coloring with no
monochromatic edge.

Reference: https://www.erdosproblems.com/901
-/
import Mathlib

namespace PropertyBBounds

/-- An `n`-uniform hypergraph is a finite family of finite edges, each of size
`n`. -/
def Uniform {α : Type*} (n : ℕ) (H : Finset (Finset α)) : Prop :=
  ∀ e ∈ H, e.card = n

/-- A Property B witness is a set of vertices whose two color classes both meet
every edge. Equivalently, neither color class contains a monochromatic edge. -/
def PropertyBWitness {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) (S : Finset α) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ S ∧ ¬ e ⊆ Sᶜ

/-- A finite hypergraph has Property B if it admits a witness set meeting every
edge while containing none. -/
def HasPropertyB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) : Prop :=
  ∃ S : Finset α, PropertyBWitness H S

/-- `BadUniformHypergraph n m` means that some finite `n`-uniform hypergraph
with exactly `m` edges fails Property B. -/
def BadUniformHypergraph (n m : ℕ) : Prop :=
  ∃ α : Type, ∃ _ : Fintype α, ∃ _ : DecidableEq α, ∃ H : Finset (Finset α),
    Uniform n H ∧ ¬ HasPropertyB H ∧ H.card = m

/-- The extremal edge count from problem `#901`. If no bad `n`-uniform
hypergraph existed, this would default to `0`, but the elementary file below
constructs such examples for every `n ≥ 1`. -/
noncomputable def mValue (n : ℕ) : ℕ :=
  sInf {m : ℕ | BadUniformHypergraph n m}

/-- Erdős and Lovász speculated that `m(n)` should have order of magnitude
`n 2^n`. -/
def Erdos901Conjecture : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      c * (n : ℝ) * (2 : ℝ) ^ n ≤ (mValue n : ℝ) ∧
      (mValue n : ℝ) ≤ C * (n : ℝ) * (2 : ℝ) ^ n

end PropertyBBounds
