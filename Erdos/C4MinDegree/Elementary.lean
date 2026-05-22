import Erdos.C4MinDegree.Statement

/- 
# Elementary Facts About Minimum Degree Forcing a Four-Cycle

This file records the first formal facts about the definitions for Erdős
problem `#85`. A `C4Witness` exposes the four distinct vertices and four cycle
edges by construction, the empty graph has no such witness, and the forcing
predicate is monotone in the degree threshold.
-/
namespace C4MinDegree

open SimpleGraph

/-- The vertex data in a `C₄` witness are pairwise distinct. -/
theorem C4Witness.distinct_vertices {n : ℕ} {G : SimpleGraph (Fin n)}
    (W : C4Witness G) :
    W.v0 ≠ W.v1 ∧ W.v0 ≠ W.v2 ∧ W.v0 ≠ W.v3 ∧
      W.v1 ≠ W.v2 ∧ W.v1 ≠ W.v3 ∧ W.v2 ≠ W.v3 :=
  W.distinct

/-- The edge data in a `C₄` witness are exactly the four cyclic adjacencies. -/
theorem C4Witness.cycle_edges {n : ℕ} {G : SimpleGraph (Fin n)}
    (W : C4Witness G) :
    G.Adj W.v0 W.v1 ∧ G.Adj W.v1 W.v2 ∧
      G.Adj W.v2 W.v3 ∧ G.Adj W.v3 W.v0 :=
  ⟨W.edge01, W.edge12, W.edge23, W.edge30⟩

/-- A concrete witness immediately gives the existential `HasC4` predicate. -/
theorem C4Witness.hasC4 {n : ℕ} {G : SimpleGraph (Fin n)}
    (W : C4Witness G) :
    HasC4 G :=
  ⟨W⟩

/-- The empty graph has no `C₄`: the first required cycle edge already
contradicts emptiness. -/
@[simp] theorem not_hasC4_bot {n : ℕ} :
    ¬ HasC4 (⊥ : SimpleGraph (Fin n)) := by
  rintro ⟨W⟩
  simpa [SimpleGraph.bot_adj] using W.edge01

/-- Lowering the requested minimum degree preserves the
`MinDegreeAtLeast` predicate. -/
theorem MinDegreeAtLeast.mono {n d e : ℕ} {G : SimpleGraph (Fin n)}
    (hde : d ≤ e) (hG : MinDegreeAtLeast G e) :
    MinDegreeAtLeast G d := by
  intro v
  exact hde.trans (hG v)

/-- If threshold `d` forces a `C₄`, then every larger threshold also forces a
`C₄`, since it is a stronger minimum-degree hypothesis. -/
theorem ForceC4.mono {n d e : ℕ} (hde : d ≤ e)
    (hforce : ForceC4 n d) :
    ForceC4 n e := by
  intro G hG
  exact hforce G (MinDegreeAtLeast.mono hde hG)

end C4MinDegree
