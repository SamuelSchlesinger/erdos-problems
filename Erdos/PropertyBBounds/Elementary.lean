import Erdos.PropertyBBounds.Statement

/-
# Elementary Facts About Property B Bounds

This file formalizes the classical middle-layer construction behind Erdős
problem `#901`. On a vertex set of size `2n - 1`, the family of all `n`-sets
is `n`-uniform and has no Property B witness. Consequently

`m(n) ≤ choose (2n - 1) n`

for every `n ≥ 1`.
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

/-- Any explicit bad witness bounds `m(n)` from above by minimality. -/
theorem mValue_le_of_badUniformHypergraph {n m : ℕ}
    (h : BadUniformHypergraph n m) :
    mValue n ≤ m := by
  exact Nat.sInf_le h

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

end PropertyBBounds
