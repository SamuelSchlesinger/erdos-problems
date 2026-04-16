import Erdos.CliqueFreeIndependence.Statement

/- 
# Elementary Facts About Clique-Free Independence Bounds

This file records the first formal infrastructure for problem `#802`. We prove
basic facts about the average degree, identify the empty graph as having
average degree `0` and independence number `n`, and settle the exact `r = 2`
base case: a `K₂`-free graph has no edges, hence is itself an independent set.
-/
namespace CliqueFreeIndependence

open SimpleGraph

theorem averageDegree_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) :
    0 ≤ averageDegree G := by
  classical
  unfold averageDegree
  positivity

@[simp] theorem averageDegree_bot {n : ℕ} :
    averageDegree (⊥ : SimpleGraph (Fin n)) = 0 := by
  classical
  simp [averageDegree]

@[simp] theorem indepNum_bot {n : ℕ} :
    (⊥ : SimpleGraph (Fin n)).indepNum = n := by
  classical
  let s : Finset (Fin n) := Finset.univ
  have hsmax : (⊥ : SimpleGraph (Fin n)).IsMaximumIndepSet s := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp
    · intro t ht
      exact Finset.card_le_univ t
  simpa [s] using
    (maximumIndepSet_card_eq_indepNum (G := (⊥ : SimpleGraph (Fin n))) s hsmax).symm

/-- A `K₂`-free graph has no edges, so it is the empty graph. -/
theorem cliqueFree_two_eq_bot {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 2) :
    G = ⊥ := by
  classical
  ext a b
  constructor
  · intro hab
    exfalso
    have hclique : G.IsClique ({a, b} : Set (Fin n)) := by
      rw [SimpleGraph.isClique_pair]
      intro _
      exact hab
    have hpair : G.IsNClique 2 ({a, b} : Finset (Fin n)) := by
      rw [SimpleGraph.isNClique_iff]
      exact ⟨by simpa using hclique, by simp [hab.ne]⟩
    exact hG _ hpair
  · intro h
    simp at h

/-- Consequently, the exact `r = 2` case has full independence number. -/
theorem cliqueFree_two_indepNum_eq_card {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 2) :
    G.indepNum = n := by
  rw [cliqueFree_two_eq_bot hG, indepNum_bot]

end CliqueFreeIndependence
