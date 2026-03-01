/-
# Connections Between Unit Fraction Problems

Problem 301 (SumFree) generalizes Problem 302 (TripleFree): a set
with no 1/a = Σ 1/bᵢ certainly has no 1/a = 1/b + 1/c. This file
formalizes this implication and related structural connections.
-/
import Erdos.UnitFractionSets.Statement
import Erdos.UnitFractionTriples.Statement

namespace UnitFractionConnections

open UnitFractionSets UnitFractionTriples

/-- **SumFree implies TripleFree.**

    If A contains no representation 1/a = Σ_{b ∈ S} 1/b for any
    nonempty S ⊆ A \ {a}, then in particular it contains no
    1/a = 1/b + 1/c with distinct a, b, c ∈ A.

    This witnesses that Problem 301 is a strict generalization of Problem 302:
    any upper bound on the SumFree function immediately gives an upper bound
    on the TripleFree function, and any TripleFree construction that fails
    to be SumFree shows a gap between the two problems. -/
theorem sumFree_implies_tripleFree {A : Finset ℕ} (hA : SumFree A) :
    TripleFree A := by
  intro a ha b hb c hc hab hac hbc htrip
  obtain ⟨_, _, _, hq⟩ := htrip
  -- Build S = {b, c} ⊆ A.erase a
  have hbA : b ∈ A.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hcA : c ∈ A.erase a := Finset.mem_erase.mpr ⟨hac.symm, hc⟩
  have hbne : b ∉ ({c} : Finset ℕ) := by
    rw [Finset.mem_singleton]; exact hbc
  let S : Finset ℕ := {b, c}
  have hSsub : S ⊆ A.erase a := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hbA
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact hcA
  have hSne : S.Nonempty := ⟨b, Finset.mem_insert_self b {c}⟩
  -- ∑_{x ∈ S} 1/x = 1/b + 1/c = 1/a
  have hsum : ∑ x ∈ S, (1 / x : ℚ) = 1 / b + 1 / c := by
    rw [show S = insert b {c} from rfl, Finset.sum_insert hbne, Finset.sum_singleton]
  exact hA a ha S hSsub hSne (hq ▸ hsum.symm)

end UnitFractionConnections
