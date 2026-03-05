/-
# Erdos-Moser Equation

Find positive integer solutions to

  1^k + 2^k + ... + (m - 1)^k = m^k.

The Erdos-Moser conjecture says the unique positive solution is `(m, k) = (3, 1)`.

Reference: https://en.wikipedia.org/wiki/Erdos-Moser_equation
-/
import Mathlib

namespace ErdosMoser

open scoped BigOperators

/-- `powerSum m k` computes `∑_{i=0}^{m-1} i^k`.
    For positive `k` this equals `1^k + ... + (m-1)^k` since `0^k = 0`. -/
def powerSum (m k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, i ^ k

/-- `(m, k)` solves the Erdos-Moser equation. -/
def IsSolution (m k : ℕ) : Prop :=
  0 < m ∧ 0 < k ∧ powerSum m k = m ^ k

instance instDecidableIsSolution (m k : ℕ) : Decidable (IsSolution m k) := by
  unfold IsSolution
  infer_instance

/-- The Erdos-Moser conjecture: `(3, 1)` is the unique positive solution. -/
def Conjecture : Prop :=
  ∀ m k : ℕ, IsSolution m k → m = 3 ∧ k = 1

/-- A witness object for a concrete solution pair `(m, k)`. -/
structure Witness where
  m : ℕ
  k : ℕ
  hsol : IsSolution m k

/-- Reformulation of `Conjecture` in terms of witness objects. -/
theorem conjecture_iff_unique_witness :
    Conjecture ↔ ∀ w : Witness, w.m = 3 ∧ w.k = 1 := by
  constructor
  · intro h w
    exact h w.m w.k w.hsol
  · intro h m k hsol
    exact h ⟨m, k, hsol⟩

/-- The classical solution `(m, k) = (3, 1)` from `1 + 2 = 3`. -/
theorem solution_three_one : IsSolution 3 1 := by
  refine ⟨by decide, by decide, ?_⟩
  change (∑ x ∈ Finset.range 3, x) = 3
  decide

/-- There is no positive-exponent solution with `m = 1`. -/
theorem no_solution_one (k : ℕ) : ¬IsSolution 1 k := by
  intro h
  rcases h with ⟨_, hk, hEq⟩
  have hFalse : False := by
    have hEq' := hEq
    simp [powerSum, hk.ne'] at hEq'
  exact hFalse.elim

/-- A concrete witness exists, namely `(3, 1)`. -/
theorem witness_exists : Nonempty Witness := by
  exact ⟨⟨3, 1, solution_three_one⟩⟩

end ErdosMoser
