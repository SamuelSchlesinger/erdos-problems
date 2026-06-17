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

/-- A `C₄` witness in a graph `G` transports along the subgraph order: every
adjacency of `G` is an adjacency of any larger graph `H`, so the same four
vertices and cycle edges witness a `C₄` in `H` (Erdős problem `#85`).

This is the natural monotonicity statement for the four-cycle predicate: adding
edges can only create, never destroy, copies of `C₄`. -/
def C4Witness.mono {n : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G ≤ H)
    (W : C4Witness G) :
    C4Witness H where
  v0 := W.v0
  v1 := W.v1
  v2 := W.v2
  v3 := W.v3
  distinct := W.distinct
  edge01 := SimpleGraph.le_iff_adj.mp hGH _ _ W.edge01
  edge12 := SimpleGraph.le_iff_adj.mp hGH _ _ W.edge12
  edge23 := SimpleGraph.le_iff_adj.mp hGH _ _ W.edge23
  edge30 := SimpleGraph.le_iff_adj.mp hGH _ _ W.edge30

/-- `HasC4` is monotone under the subgraph order: if `G ≤ H` and `G` contains a
`C₄`, then so does `H`. Together with `not_hasC4_bot`, this records that having a
four-cycle is an upward-closed property of graphs (Erdős problem `#85`). -/
theorem HasC4.mono {n : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G ≤ H)
    (hG : HasC4 G) :
    HasC4 H := by
  obtain ⟨W⟩ := hG
  exact ⟨W.mono hGH⟩

/-- The complete graph on four vertices contains a `C₄`: the cyclic ordering
`0, 1, 2, 3` of the four distinct vertices of `Fin 4` is a four-cycle, since in
the complete graph every pair of distinct vertices is adjacent (Erdős problem
`#85`). This grounds `HasC4` with an explicit positive instance. -/
theorem hasC4_top_four : HasC4 (⊤ : SimpleGraph (Fin 4)) :=
  ⟨{ v0 := 0
     v1 := 1
     v2 := 2
     v3 := 3
     distinct := by decide
     edge01 := by rw [SimpleGraph.top_adj]; decide
     edge12 := by rw [SimpleGraph.top_adj]; decide
     edge23 := by rw [SimpleGraph.top_adj]; decide
     edge30 := by rw [SimpleGraph.top_adj]; decide }⟩

end C4MinDegree
