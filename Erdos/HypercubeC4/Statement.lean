/-
# Erdos Problem 86: C4-free subgraphs of the hypercube

Let `Q n` be the `n`-dimensional hypercube graph: its vertices are binary
strings of length `n`, and two vertices are adjacent exactly when they differ in
one coordinate. Problem `#86` asks whether every subgraph with asymptotically at
least half the edges of `Q n` must contain a copy of `C4`.

We formalize the vertex set as `Fin n -> Bool`, define adjacency through
Hamming distance one, package subgraphs as edge-subgraphs of the hypercube, and
state the usual `1/2 + o(1)` bound in its epsilon form.

Reference: https://www.erdosproblems.com/86
-/
import Mathlib

namespace HypercubeC4

/-- The vertex set of the `n`-dimensional hypercube: binary strings indexed by
`Fin n`. -/
abbrev Vertex (n : ℕ) := Fin n → Bool

/-- Two hypercube vertices differ at coordinate `i` if their Boolean values
there are unequal. -/
def DiffersAt {n : ℕ} (x y : Vertex n) (i : Fin n) : Prop :=
  x i ≠ y i

/-- The Hamming distance between two vertices, counted as the number of
coordinates on which they differ. -/
noncomputable def hammingDistance {n : ℕ} (x y : Vertex n) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter fun i => DiffersAt x y i).card

/-- Hamming distance is symmetric because inequality of Boolean coordinate
values is symmetric. -/
theorem hammingDistance_comm {n : ℕ} (x y : Vertex n) :
    hammingDistance x y = hammingDistance y x := by
  classical
  unfold hammingDistance
  congr 1
  ext i
  simp [DiffersAt, ne_comm]

/-- A vertex differs from itself in no coordinate, so its Hamming distance to
itself is zero. -/
theorem hammingDistance_self {n : ℕ} (x : Vertex n) :
    hammingDistance x x = 0 := by
  classical
  simp [hammingDistance, DiffersAt]

/-- Hypercube adjacency: two vertices are adjacent exactly when their Hamming
distance is one. -/
def Adjacent {n : ℕ} (x y : Vertex n) : Prop :=
  hammingDistance x y = 1

/-- Hypercube adjacency is symmetric, inherited from symmetry of Hamming
distance. -/
theorem adjacent_symm {n : ℕ} {x y : Vertex n} (h : Adjacent x y) :
    Adjacent y x := by
  simpa [Adjacent, hammingDistance_comm y x] using h

/-- Hypercube adjacency is irreflexive: a vertex has Hamming distance zero from
itself, not one. -/
theorem adjacent_irrefl {n : ℕ} (x : Vertex n) :
    ¬ Adjacent x x := by
  simp [Adjacent, hammingDistance_self]

/-- Flip a single coordinate of a hypercube vertex. -/
def flip {n : ℕ} (x : Vertex n) (i : Fin n) : Vertex n :=
  Function.update x i (!x i)

/-- The `n`-dimensional hypercube graph `Q_n`. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj := Adjacent
  symm := by
    intro x y hxy
    exact adjacent_symm hxy
  loopless := by
    intro x
    exact adjacent_irrefl x

/-- A subgraph of the hypercube, represented by a simple graph whose edges are
all hypercube edges. -/
structure HypercubeSubgraph (n : ℕ) where
  graph : SimpleGraph (Vertex n)
  edge_subset : graph ≤ hypercubeGraph n

/-- The number of edges in a finite hypercube subgraph. -/
noncomputable def HypercubeSubgraph.edgeCount {n : ℕ}
    (H : HypercubeSubgraph n) : ℕ := by
  classical
  exact H.graph.edgeFinset.card

/-- A concrete witness for a copy of `C4` in a graph: four distinct vertices
with the four cyclic edges present. We do not require inducedness. -/
structure C4Witness {n : ℕ} (G : SimpleGraph (Vertex n)) where
  v0 : Vertex n
  v1 : Vertex n
  v2 : Vertex n
  v3 : Vertex n
  edge01 : G.Adj v0 v1
  edge12 : G.Adj v1 v2
  edge23 : G.Adj v2 v3
  edge30 : G.Adj v3 v0
  v0_ne_v1 : v0 ≠ v1
  v0_ne_v2 : v0 ≠ v2
  v0_ne_v3 : v0 ≠ v3
  v1_ne_v2 : v1 ≠ v2
  v1_ne_v3 : v1 ≠ v3
  v2_ne_v3 : v2 ≠ v3

/-- A graph contains a not-necessarily-induced four-cycle. -/
def GraphContainsC4 {n : ℕ} (G : SimpleGraph (Vertex n)) : Prop :=
  Nonempty (C4Witness G)

/-- A hypercube subgraph contains a four-cycle when its underlying graph does. -/
def HypercubeSubgraph.ContainsC4 {n : ℕ}
    (H : HypercubeSubgraph n) : Prop :=
  GraphContainsC4 H.graph

/-- The edge scale in problem `#86`: `(1/2 + delta) n 2^(n-1)`. The hypercube
has `n * 2^(n-1)` edges for `n > 0`, so this is the finite-threshold form of
the `1/2 + o(1)` question. -/
noncomputable def erdos86Threshold (delta : ℝ) (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2 + delta) * (n : ℝ) * (2 : ℝ) ^ (n - 1)

/-- Epsilon-form statement of Erdős problem `#86`: for every fixed
`delta > 0`, all sufficiently high-dimensional hypercube subgraphs with more
than `(1/2 + delta) n 2^(n-1)` edges contain a `C4`. The strict inequality is
the standard way to express the extremal upper bound
`ex(Q_n, C₄) ≤ (1/2 + o(1)) n 2^(n-1)` without accidental integer-rounding
strengthening at exact thresholds. -/
def Erdos86Conjecture : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : HypercubeSubgraph n,
        erdos86Threshold delta n < (H.edgeCount : ℝ) → H.ContainsC4

end HypercubeC4
