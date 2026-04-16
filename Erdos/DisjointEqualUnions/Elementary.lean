import Erdos.DisjointEqualUnions.Statement

/- 
# Elementary Facts About Disjoint Equal-Unions

This file formalizes the standard star-family obstruction for Erdős problem
`#643`. If every edge contains a fixed vertex `v`, then no two edges are
disjoint, so the forbidden equal-union disjoint quadruple cannot occur.

Taking all `t`-sets through one vertex therefore gives a `t`-uniform family of
size `choose(n - 1, t - 1)` with no forbidden quadruple, yielding the lower
bound construction behind Füredi's theorem.
-/
namespace DisjointEqualUnions

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

theorem not_hasForbiddenQuad_starFamily {n t : ℕ} (v : Fin n) :
    ¬ HasForbiddenQuad (starFamily v t) := by
  rintro ⟨A, hA, B, hB, C, hC, D, hD, -, -, -, -, -, -, hdisAB, -, -⟩
  have hAv : v ∈ A := mem_starFamily_vertex hA
  have hBv : v ∈ B := mem_starFamily_vertex hB
  exact (Finset.disjoint_left.mp hdisAB hAv) hBv

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
