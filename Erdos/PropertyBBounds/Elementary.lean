import Erdos.PropertyBBounds.Statement

/-
# Elementary Facts About Property B Bounds

This file formalizes the classical middle-layer construction behind Erdős
problem `#901`. On a vertex set of size `2n - 1`, the family of all `n`-sets
is `n`-uniform and has no Property B witness. Consequently

`m(n) ≤ choose (2n - 1) n`

for every `n ≥ 1`.

We also record the elementary lower-bound sanity check: the empty hypergraph
has Property B, so a bad uniform hypergraph must have at least one edge. In
the one-uniform case this combines with the middle-layer construction to give
`m(1) = 1`.
-/
namespace PropertyBBounds

/-- The complete `n`-uniform hypergraph on `2n - 1` vertices, realized as the
middle layer of the Boolean lattice. -/
def middleLayer (n : ℕ) : Finset (Finset (Fin (2 * n - 1))) :=
  (Finset.univ : Finset (Fin (2 * n - 1))).powersetCard n

theorem middleLayer_uniform (n : ℕ) :
    Uniform n (middleLayer n) := by
  intro e he
  exact (Finset.mem_powersetCard.mp he).2

theorem middleLayer_card (n : ℕ) :
    (middleLayer n).card = Nat.choose (2 * n - 1) n := by
  simp [middleLayer]

/-- The middle layer on `2n - 1` vertices is not two-colorable: if neither
color class contains an `n`-set, then both classes have size `< n`, impossible
because their sizes add to `2n - 1`. -/
theorem not_hasPropertyB_middleLayer {n : ℕ} (hn : 1 ≤ n) :
    ¬ HasPropertyB (middleLayer n) := by
  intro hB
  rcases hB with ⟨S, hS⟩
  have hlt : S.card < n := by
    by_contra hnot
    have hle : n ≤ S.card := le_of_not_gt hnot
    rcases (Finset.powersetCard_nonempty.2 hle) with ⟨e, he⟩
    have heS : e ⊆ S := (Finset.mem_powersetCard.mp he).1
    have heH : e ∈ middleLayer n := by
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp he).2⟩
    exact (hS e heH).1 heS
  have hclt : Sᶜ.card < n := by
    by_contra hnot
    have hle : n ≤ Sᶜ.card := le_of_not_gt hnot
    rcases (Finset.powersetCard_nonempty.2 hle) with ⟨e, he⟩
    have heSc : e ⊆ Sᶜ := (Finset.mem_powersetCard.mp he).1
    have heH : e ∈ middleLayer n := by
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp he).2⟩
    exact (hS e heH).2 heSc
  have hsum : S.card + Sᶜ.card = 2 * n - 1 := by
    simp
  have hle1 : S.card + 1 ≤ n := Nat.lt_iff_add_one_le.mp hlt
  have hle2 : Sᶜ.card + 1 ≤ n := Nat.lt_iff_add_one_le.mp hclt
  omega

/-- Hence the middle layer supplies a bad `n`-uniform hypergraph with
`choose (2n - 1) n` edges. -/
theorem badUniformHypergraph_middleLayer {n : ℕ} (hn : 1 ≤ n) :
    BadUniformHypergraph n (Nat.choose (2 * n - 1) n) := by
  refine ⟨Fin (2 * n - 1), inferInstance, inferInstance, middleLayer n, ?_, ?_, ?_⟩
  · exact middleLayer_uniform n
  · exact not_hasPropertyB_middleLayer hn
  · exact middleLayer_card n

/-- The empty hypergraph has Property B: any choice of color class vacuously
avoids monochromatic edges. -/
theorem hasPropertyB_empty (α : Type*) [Fintype α] [DecidableEq α] :
    HasPropertyB (∅ : Finset (Finset α)) := by
  refine ⟨∅, ?_⟩
  intro e he
  simp at he

/-- Consequently, no `n`-uniform hypergraph with zero edges can fail
Property B. -/
theorem not_badUniformHypergraph_zero_edges (n : ℕ) :
    ¬ BadUniformHypergraph n 0 := by
  rintro ⟨α, hα, hαdec, H, _hUniform, hnotB, hcard⟩
  letI := hα
  letI := hαdec
  have hH : H = ∅ := Finset.card_eq_zero.mp hcard
  exact hnotB (by simpa [hH] using hasPropertyB_empty α)

/-- Any explicit bad witness bounds `m(n)` from above by minimality. -/
theorem mValue_le_of_badUniformHypergraph {n m : ℕ}
    (h : BadUniformHypergraph n m) :
    mValue n ≤ m := Nat.sInf_le h

/-- Once a bad `n`-uniform hypergraph exists, the minimum bad edge count is at
least one. -/
theorem one_le_mValue_of_exists_bad {n m : ℕ}
    (hbad : BadUniformHypergraph n m) :
    1 ≤ mValue n := by
  have hne : ({m : ℕ | BadUniformHypergraph n m} : Set ℕ).Nonempty := ⟨m, hbad⟩
  have hmem : BadUniformHypergraph n (mValue n) := Nat.sInf_mem hne
  by_contra hnot
  have hzero : mValue n = 0 := by
    omega
  exact not_badUniformHypergraph_zero_edges n (by simpa [hzero] using hmem)

/-- The classical Erdős-Lovász middle-layer construction gives the elementary
upper bound `m(n) ≤ choose (2n - 1) n`. -/
theorem mValue_le_middleLayer {n : ℕ} (hn : 1 ≤ n) :
    mValue n ≤ Nat.choose (2 * n - 1) n := by
  exact mValue_le_of_badUniformHypergraph (badUniformHypergraph_middleLayer hn)

/-- In particular, the problem's exact small case `m(2) = 3` is consistent
with the general middle-layer upper bound. -/
theorem mValue_two_le_three :
    mValue 2 ≤ 3 := by
  simpa using mValue_le_middleLayer (n := 2) (by omega)

/-- The exact one-uniform case: one singleton edge is already non-Property-B,
and zero edges never suffice. -/
theorem mValue_one :
    mValue 1 = 1 := by
  refine le_antisymm ?_ ?_
  · simpa using mValue_le_middleLayer (n := 1) (by omega)
  · exact one_le_mValue_of_exists_bad
      (badUniformHypergraph_middleLayer (n := 1) (by omega))

end PropertyBBounds
