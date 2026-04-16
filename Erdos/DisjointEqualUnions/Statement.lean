/- 
# Erdős Problem 643: Hypergraphs with No Disjoint Equal-Unions

Let `f(n;t)` be minimal such that every `t`-uniform hypergraph on `n` vertices
with at least `f(n;t)` edges contains four distinct edges `A, B, C, D` with

* `A ∩ B = ∅`
* `C ∩ D = ∅`
* `A ∪ B = C ∪ D`.

Erdős asked for the size of `f(n;t)`, in particular whether for fixed
`t ≥ 3` one has `f(n;t) = (1 + o(1)) * choose(n, t - 1)`.

Reference: https://www.erdosproblems.com/643
-/
import Mathlib

namespace DisjointEqualUnions

/-- A `t`-uniform hypergraph on `Fin n`. -/
def Uniform {n t : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = t

/-- The forbidden configuration from Erdős problem `#643`. -/
def HasForbiddenQuad {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ A ∈ H, ∃ B ∈ H, ∃ C ∈ H, ∃ D ∈ H,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    Disjoint A B ∧ Disjoint C D ∧ A ∪ B = C ∪ D

/-- `ForceBound n t m` means that every `t`-uniform hypergraph on `Fin n` with
at least `m` edges contains a forbidden quadruple. -/
def ForceBound (n t m : ℕ) : Prop :=
  ∀ H : Finset (Finset (Fin n)), Uniform (t := t) H → m ≤ H.card → HasForbiddenQuad H

/-- The extremal threshold in problem `#643`. -/
noncomputable def fValue (n t : ℕ) : ℕ :=
  sInf {m : ℕ | ForceBound n t m}

end DisjointEqualUnions
