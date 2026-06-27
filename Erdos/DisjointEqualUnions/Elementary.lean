import Erdos.DisjointEqualUnions.Statement

/- 
# Elementary Facts About Disjoint Equal-Unions

This file formalizes the standard pairwise-intersecting obstruction for Erdős
problem `#643`. If no two edges of a family are disjoint, then the forbidden
equal-union disjoint quadruple cannot occur. In particular, this applies to a
star family, where every edge contains a fixed vertex `v`.

Taking all `t`-sets through one vertex therefore gives a `t`-uniform family of
size `choose(n - 1, t - 1)` with no forbidden quadruple, yielding the lower
bound construction behind Füredi's theorem.
-/
namespace DisjointEqualUnions

/-- A hypergraph is pairwise non-disjoint if any two distinct edges meet. -/
def PairwiseNonDisjoint {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  (↑H : Set (Finset (Fin n))).Pairwise (fun A B => ¬ Disjoint A B)

/-- Pairwise non-disjoint families avoid the forbidden configuration in
Erdős problem `#643`: the first disjoint pair required by such a configuration
already contradicts pairwise non-disjointness. -/
theorem not_hasForbiddenQuad_of_pairwiseNonDisjoint {n : ℕ}
    {H : Finset (Finset (Fin n))} (hH : PairwiseNonDisjoint H) :
    ¬ HasForbiddenQuad H := by
  rintro ⟨A, hA, B, hB, C, hC, D, hD, hAB, -, -, -, -, -, hdisAB, -, -⟩
  exact hH hA hB hAB hdisAB

/-- The family of all `t`-sets containing a fixed vertex `v`. -/
def starFamily {n : ℕ} (v : Fin n) (t : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ.erase v).powersetCard (t - 1)).image (insert v)

theorem mem_starFamily_vertex {n t : ℕ} {v : Fin n} {e : Finset (Fin n)}
    (he : e ∈ starFamily v t) :
    v ∈ e := by
  rcases Finset.mem_image.mp he with ⟨s, hs, rfl⟩
  simp

theorem starFamily_uniform {n t : ℕ} (v : Fin n) (ht : 1 ≤ t) :
    Uniform (t := t) (starFamily v t) := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨s, hs, rfl⟩
  have hsSub : s ⊆ Finset.univ.erase v := (Finset.mem_powersetCard.mp hs).1
  have hvnot : v ∉ s := by
    intro hv
    simpa using hsSub hv
  have hsCard : s.card = t - 1 := (Finset.mem_powersetCard.mp hs).2
  rw [Finset.card_insert_of_notMem hvnot, hsCard]
  omega

theorem starFamily_card {n t : ℕ} (v : Fin n) :
    (starFamily v t).card = Nat.choose (n - 1) (t - 1) := by
  unfold starFamily
  rw [Finset.card_image_of_injOn]
  · simp
  · intro s hs u hu hEq
    have hs' : s ∈ (Finset.univ.erase v).powersetCard (t - 1) := by simpa using hs
    have hu' : u ∈ (Finset.univ.erase v).powersetCard (t - 1) := by simpa using hu
    have hsSub : s ⊆ Finset.univ.erase v := (Finset.mem_powersetCard.mp hs').1
    have huSub : u ⊆ Finset.univ.erase v := (Finset.mem_powersetCard.mp hu').1
    have hsv : v ∉ s := by
      intro hv
      simpa using hsSub hv
    have huv : v ∉ u := by
      intro hv
      simpa using huSub hv
    have hErase := congrArg (fun w : Finset (Fin n) => w.erase v) hEq
    simpa [Finset.erase_insert hsv, Finset.erase_insert huv] using hErase

/-- A star family is pairwise non-disjoint because every edge contains its
center vertex. -/
theorem starFamily_pairwiseNonDisjoint {n t : ℕ} (v : Fin n) :
    PairwiseNonDisjoint (starFamily v t) := by
  intro A hA B hB _ hdis
  have hAv : v ∈ A := mem_starFamily_vertex (by simpa using hA)
  have hBv : v ∈ B := mem_starFamily_vertex (by simpa using hB)
  exact (Finset.disjoint_left.mp hdis hAv) hBv

theorem not_hasForbiddenQuad_starFamily {n t : ℕ} (v : Fin n) :
    ¬ HasForbiddenQuad (starFamily v t) := not_hasForbiddenQuad_of_pairwiseNonDisjoint
    (starFamily_pairwiseNonDisjoint (t := t) v)

/-- The star family witnesses that the forcing threshold must exceed
`choose(n - 1, t - 1)` whenever `n > 0` and `t > 0`. -/
theorem not_forceBound_starFamily {n t : ℕ} (hn : 0 < n) (ht : 1 ≤ t) :
    ¬ ForceBound n t (Nat.choose (n - 1) (t - 1)) := by
  let v : Fin n := ⟨0, hn⟩
  intro h
  have huni : Uniform (t := t) (starFamily v t) := starFamily_uniform v ht
  have hcard : Nat.choose (n - 1) (t - 1) ≤ (starFamily v t).card := by
    simp [starFamily_card]
  exact not_hasForbiddenQuad_starFamily v (h (starFamily v t) huni hcard)

end DisjointEqualUnions
