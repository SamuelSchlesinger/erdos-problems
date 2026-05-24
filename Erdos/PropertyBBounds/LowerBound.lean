import Erdos.PropertyBBounds.Statement
import Erdos.PropertyBBounds.Elementary

set_option linter.style.header false

/-!
# Erdős' classical `2^(n-1)` lower bound for Property B

Erdős (1963) proved that every `n`-uniform hypergraph with fewer than `2^(n-1)`
edges admits Property B (a proper 2-coloring with no monochromatic edge). This
file gives a self-contained, double-counting formalization, which yields

  `mValue n ≥ 2^(n-1)` for every `n ≥ 1`.

## Mathematical content

Fix a finite vertex type `α` of size `v` and an `n`-uniform hypergraph `H` on
`α`. For each 2-coloring `S : Finset α` (viewed as the "red" class), let

  `monoEdges H S = { e ∈ H : e ⊆ S ∨ e ⊆ Sᶜ }`.

Summing over **all** `S ⊆ α` and swapping the order of summation:

  `∑_{S ⊆ α} #(monoEdges H S) = ∑_{e ∈ H} #{S : e ⊆ S ∨ e ⊆ Sᶜ}`

For an edge `e` of size `n` with `n ≥ 1`, the inner count is `2 · 2^{v-n}`
(monochromatically red or blue; these are disjoint because some vertex of `e`
would have to be in both `S` and `Sᶜ`). Hence the total equals
`|H| · 2 · 2^{v-n}`. The number of colorings is `2^v`. If
`|H| < 2^{n-1}` then the total is `< 2^v`, so by pigeonhole some `S` has
`monoEdges H S = ∅` -- i.e. `S` is a Property B witness.

This is the textbook form of Erdős's original probabilistic proof.
-/

namespace PropertyBBounds

open Finset

/-- Edges of `H` that are monochromatic under the 2-coloring `S`. -/
def monoEdges {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  H.filter (fun e => e ⊆ S ∨ e ⊆ Sᶜ)

/-- Property B witnesses are exactly the colorings with zero monochromatic
edges. -/
lemma propertyBWitness_iff_monoEdges_empty {α : Type*} [Fintype α] [DecidableEq α]
    {H : Finset (Finset α)} {S : Finset α} :
    PropertyBWitness H S ↔ monoEdges H S = ∅ := by
  simp [PropertyBWitness, monoEdges, Finset.filter_eq_empty_iff, not_or]

/-- The set of 2-colorings (subsets of the vertex universe). -/
abbrev colorings (α : Type*) [Fintype α] [DecidableEq α] :
    Finset (Finset α) := (Finset.univ : Finset α).powerset

lemma card_colorings (α : Type*) [Fintype α] [DecidableEq α] :
    (colorings α).card = 2 ^ (Fintype.card α) := by
  simp [colorings, Finset.card_powerset]

/-! ### Counting subsets containing a given subset -/

/-- The number of `S ⊆ univ` containing a given `e` equals `2^{|α| - |e|}`. The
map `S ↦ S \ e` is a bijection between `{S : e ⊆ S}` and `Powerset eᶜ`. -/
lemma card_filter_superset {α : Type*} [Fintype α] [DecidableEq α]
    (e : Finset α) :
    ((colorings α).filter (fun S => e ⊆ S)).card =
      2 ^ (Fintype.card α - e.card) := by
  classical
  set f : Finset α → Finset α := fun S => S \ e with hf_def
  have hinj : Set.InjOn f ↑((colorings α).filter (fun S => e ⊆ S)) := by
    intro S₁ hS₁ S₂ hS₂ hfeq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hS₁ hS₂
    have eq1 : S₁ = S₁ \ e ∪ e := (Finset.sdiff_union_of_subset hS₁.2).symm
    have eq2 : S₂ = S₂ \ e ∪ e := (Finset.sdiff_union_of_subset hS₂.2).symm
    rw [eq1, eq2]; simp only [hf_def] at hfeq; rw [hfeq]
  have himage : ((colorings α).filter (fun S => e ⊆ S)).image f = eᶜ.powerset := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset,
      colorings, Finset.subset_univ, true_and, hf_def]
    refine ⟨?_, fun hT => ⟨T ∪ e, Finset.subset_union_right, ?_⟩⟩
    · rintro ⟨S, _, rfl⟩ x hx
      simp only [Finset.mem_sdiff, Finset.mem_compl] at hx ⊢
      exact hx.2
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      refine ⟨fun ⟨hxor, hxe⟩ => hxor.resolve_right (fun h => hxe h), fun hxT => ?_⟩
      have hxe : x ∉ e := fun h => (Finset.mem_compl.mp (hT hxT)) h
      exact ⟨Or.inl hxT, hxe⟩
  rw [← Finset.card_image_of_injOn hinj, himage, Finset.card_powerset, Finset.card_compl]

/-- The number of `S ⊆ univ` with `e ⊆ Sᶜ` equals `2^{|α| - |e|}`. Direct
calculation: `e ⊆ Sᶜ ↔ S ⊆ eᶜ`, and the subsets of `eᶜ` form its powerset. -/
lemma card_filter_subset_compl {α : Type*} [Fintype α] [DecidableEq α]
    (e : Finset α) :
    ((colorings α).filter (fun S => e ⊆ Sᶜ)).card =
      2 ^ (Fintype.card α - e.card) := by
  classical
  have h_eq : (colorings α).filter (fun S => e ⊆ Sᶜ) = eᶜ.powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, colorings, Finset.subset_univ,
      true_and, Finset.subset_compl_comm]
  rw [h_eq, Finset.card_powerset, Finset.card_compl]

/-- For an `n`-uniform edge `e` with `n ≥ 1`, the number of 2-colorings making
`e` monochromatic equals `2 · 2^{v-n}` where `v = |α|`. -/
lemma card_monochromatic_for_edge {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 ≤ n) (e : Finset α) (he : e.card = n) :
    ((colorings α).filter (fun S => e ⊆ S ∨ e ⊆ Sᶜ)).card =
      2 * 2 ^ (Fintype.card α - n) := by
  classical
  rcases Finset.card_pos.mp (by omega : 0 < e.card) with ⟨x, hx⟩
  have hdisj : Disjoint ((colorings α).filter (fun S => e ⊆ S))
                        ((colorings α).filter (fun S => e ⊆ Sᶜ)) := by
    rw [Finset.disjoint_filter]
    intro S _ hSsub hSsubc
    exact absurd (hSsub hx) (by simpa using hSsubc hx)
  rw [Finset.filter_or, Finset.card_union_of_disjoint hdisj,
      card_filter_superset e, card_filter_subset_compl e, he, two_mul]

/-! ### Double counting -/

/-- The key identity: summing the monochromatic count across all colorings
swaps with summing per-edge counts. -/
lemma sum_monoEdges_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 ≤ n) {H : Finset (Finset α)} (hH : Uniform n H) :
    ∑ S ∈ colorings α, (monoEdges H S).card =
      H.card * (2 * 2 ^ (Fintype.card α - n)) := by
  classical
  simp_rw [monoEdges, Finset.card_filter]
  rw [Finset.sum_comm]
  have h2 : ∀ e ∈ H,
      ∑ S ∈ colorings α, (if (e ⊆ S ∨ e ⊆ Sᶜ) then (1 : ℕ) else 0) =
        2 * 2 ^ (Fintype.card α - n) := by
    intro e he
    rw [← card_monochromatic_for_edge (α := α) hn e (hH e he), ← Finset.card_filter]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]

/-! ### The lower-bound theorem -/

/-- If `H` is `n`-uniform with `n ≥ 1`, on a vertex universe of size at least
`n`, and `2 · |H| < 2^n`, then some 2-coloring has zero monochromatic edges. -/
theorem exists_propertyBWitness_of_few_edges
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 ≤ n) (hvn : n ≤ Fintype.card α)
    {H : Finset (Finset α)} (hH : Uniform n H)
    (hsmall : 2 * H.card < 2 ^ n) :
    HasPropertyB H := by
  classical
  -- Suppose otherwise: every coloring has ≥ 1 monochromatic edge.
  by_contra hcontra
  unfold HasPropertyB at hcontra; push_neg at hcontra
  have hge : ∀ S ∈ colorings α, 1 ≤ (monoEdges H S).card := fun S _ =>
    Nat.one_le_iff_ne_zero.mpr fun h =>
      hcontra S ((propertyBWitness_iff_monoEdges_empty).mpr (Finset.card_eq_zero.mp h))
  have hsum_ge : (colorings α).card ≤ ∑ S ∈ colorings α, (monoEdges H S).card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum hge
  rw [sum_monoEdges_card_eq hn hH, card_colorings] at hsum_ge
  -- Now: 2^v ≤ |H| * 2 * 2^(v - n), with v - n ≥ 0.
  -- I.e. 2^v ≤ 2 * |H| * 2^(v - n) < 2^n * 2^(v - n) = 2^v, contradiction.
  set v := Fintype.card α
  have hpow : 2 ^ v = 2 ^ n * 2 ^ (v - n) := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (v - n) := pow_pos (by norm_num) _
  have hineq : H.card * (2 * 2 ^ (v - n)) < 2 ^ n * 2 ^ (v - n) := by
    calc H.card * (2 * 2 ^ (v - n))
        = (2 * H.card) * 2 ^ (v - n) := by ring
      _ < 2 ^ n * 2 ^ (v - n) := Nat.mul_lt_mul_of_pos_right hsmall hpos
  rw [hpow] at hsum_ge
  exact absurd (lt_of_le_of_lt hsum_ge hineq) (lt_irrefl _)

/-- **Erdős's `2^(n-1)` lower bound (1963).** Every `n`-uniform hypergraph
with fewer than `2^(n-1)` edges has Property B. -/
theorem hasPropertyB_of_card_lt {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 ≤ n) (hvn : n ≤ Fintype.card α)
    {H : Finset (Finset α)} (hH : Uniform n H)
    (hsmall : H.card < 2 ^ (n - 1)) :
    HasPropertyB H := by
  refine exists_propertyBWitness_of_few_edges hn hvn hH ?_
  have : 2 * 2 ^ (n - 1) = 2 ^ n := by
    have : 2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
    rw [this, pow_succ]; ring
  omega

/-! ### Consequences for `mValue` -/

/-- A bad `n`-uniform hypergraph (one failing Property B) must have at least
`2^(n-1)` edges, regardless of the vertex universe used to realize it. -/
theorem badUniformHypergraph_card_ge
    {n m : ℕ} (hn : 1 ≤ n) (h : BadUniformHypergraph n m) :
    2 ^ (n - 1) ≤ m := by
  classical
  rcases h with ⟨α, hα, hαdec, H, hUniform, hnotB, hcard⟩
  letI := hα
  letI := hαdec
  -- The vertex universe must contain at least one edge of size n, so |α| ≥ n
  -- — except in the degenerate case `H = ∅`, which we handle separately.
  by_contra hlt
  push_neg at hlt
  -- We need n ≤ |α| to apply the lower-bound theorem. Either H is empty
  -- (impossible: empty hypergraph has Property B by hasPropertyB_empty) or H
  -- has an edge e of size n contained in α.
  by_cases hHe : H.Nonempty
  · rcases hHe with ⟨e, he⟩
    have hen : e.card = n := hUniform e he
    have hvn : n ≤ Fintype.card α := by
      rw [← hen]
      have := Finset.card_le_univ e
      simpa using this
    have hwit : HasPropertyB H := by
      apply hasPropertyB_of_card_lt hn hvn hUniform
      omega
    exact hnotB hwit
  · have hHempty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHe
    have : HasPropertyB H := by
      rw [hHempty]; exact hasPropertyB_empty α
    exact hnotB this

/-- **`m(n) ≥ 2^(n-1)`** for every `n ≥ 1` — once we know a bad hypergraph
exists (which it does, by the middle-layer construction in
`PropertyBBounds.Elementary`). -/
theorem mValue_ge_pow {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ mValue n := by
  -- The middle-layer construction gives a bad n-uniform hypergraph, so the
  -- inf is attained.
  have hbad := badUniformHypergraph_middleLayer (n := n) hn
  have hne : ({m : ℕ | BadUniformHypergraph n m} : Set ℕ).Nonempty :=
    ⟨_, hbad⟩
  have hmem : BadUniformHypergraph n (mValue n) := Nat.sInf_mem hne
  exact badUniformHypergraph_card_ge hn hmem

/-- A concrete tightening of `mValue_one`: combining with the upper bound, the
case `n = 1` agrees: `m(1) = 1 = 2^0`. -/
example : 2 ^ (1 - 1) ≤ mValue 1 := mValue_ge_pow (by omega)

/-- For `n = 2`, our bound gives `m(2) ≥ 2`. The known value is `m(2) = 3`,
which would require a separate argument. -/
example : 2 ^ (2 - 1) ≤ mValue 2 := mValue_ge_pow (by omega)

end PropertyBBounds
