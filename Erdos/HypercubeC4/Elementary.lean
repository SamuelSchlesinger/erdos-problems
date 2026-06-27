import Erdos.HypercubeC4.Statement

/-
# Elementary facts for Erdos Problem 86

This file records basic, reviewer-readable facts about the hypercube model used
in `Statement.lean`: the vertex count, the empty zeroth-dimensional cube, and
the effect of flipping one coordinate.
-/
namespace HypercubeC4

/-- The hypercube `Q_n` has `2^n` vertices, since a vertex is a function
`Fin n -> Bool`. -/
@[simp] theorem vertex_card (n : ℕ) :
    Fintype.card (Vertex n) = 2 ^ n := by
  simp [Vertex]

/-- Adjacency can be used in either order. -/
theorem adjacent_comm {n : ℕ} {x y : Vertex n} :
    Adjacent x y ↔ Adjacent y x := by
  exact ⟨adjacent_symm, adjacent_symm⟩

/-- No vertex is adjacent to itself in the hypercube. -/
@[simp] theorem not_adjacent_self {n : ℕ} (x : Vertex n) :
    ¬ Adjacent x x :=
  adjacent_irrefl x

/-- In dimension zero, all Hamming distances are zero because there are no
coordinates at which two vertices can differ. -/
@[simp] theorem hammingDistance_zero (x y : Vertex 0) :
    hammingDistance x y = 0 := by
  classical
  simp [hammingDistance]

/-- The graph `Q_0` has no adjacent pair of vertices. -/
@[simp] theorem no_adjacent_zero (x y : Vertex 0) :
    ¬ Adjacent x y := by
  simp [Adjacent]

/-- Equivalently, the zeroth-dimensional hypercube is the empty simple graph. -/
@[simp] theorem hypercubeGraph_zero_eq_bot :
    hypercubeGraph 0 = ⊥ := by
  ext x y
  constructor
  · intro h
    exact (no_adjacent_zero x y) h
  · intro h
    simp at h

/-- Consequently, `Q_0` has edge count zero. -/
@[simp] theorem hypercubeGraph_zero_edgeFinset_card :
    (hypercubeGraph 0).edgeFinset.card = 0 := by
  classical
  simp [hypercubeGraph_zero_eq_bot]

/-- At the coordinate that is flipped, the new Boolean value is the negation of
the old one. -/
@[simp] theorem flip_apply_same {n : ℕ} (x : Vertex n) (i : Fin n) :
    flip x i i = !x i := by
  simp [flip]

/-- Away from the flipped coordinate, the vertex is unchanged. -/
@[simp] theorem flip_apply_of_ne {n : ℕ} (x : Vertex n) {i j : Fin n}
    (h : j ≠ i) :
    flip x i j = x j := by
  simp [flip, h]

/-- Flipping coordinate `i` changes exactly coordinate `i`. -/
theorem differsAt_flip_iff {n : ℕ} (x : Vertex n) (i j : Fin n) :
    DiffersAt x (flip x i) j ↔ j = i := by
  by_cases h : j = i
  · subst h
    simp [DiffersAt, flip]
  · simp [DiffersAt, flip, h]

/-- The Hamming distance from a vertex to the result of flipping one coordinate
is exactly one. -/
@[simp] theorem hammingDistance_flip {n : ℕ} (x : Vertex n) (i : Fin n) :
    hammingDistance x (flip x i) = 1 := by
  classical
  unfold hammingDistance
  have hset :
      ((Finset.univ : Finset (Fin n)).filter fun j =>
        DiffersAt x (flip x i) j) = {i} := by
    ext j
    simp [differsAt_flip_iff]
  rw [hset]
  simp

/-- Flipping one coordinate of a vertex gives an adjacent vertex in `Q_n`. -/
theorem adjacent_flip {n : ℕ} (x : Vertex n) (i : Fin n) :
    Adjacent x (flip x i) := by
  simp [Adjacent]

/-- The same one-coordinate flip is an edge of the bundled hypercube graph. -/
theorem hypercubeGraph_adj_flip {n : ℕ} (x : Vertex n) (i : Fin n) :
    (hypercubeGraph n).Adj x (flip x i) := adjacent_flip x i

end HypercubeC4
