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
  unfold PropertyBWitness monoEdges
  constructor
  · intro hS
    rw [Finset.filter_eq_empty_iff]
    intro e he hor
    rcases hor with h1 | h2
    · exact (hS e he).1 h1
    · exact (hS e he).2 h2
  · intro hempty e he
    refine ⟨?_, ?_⟩ <;> intro hcontra
    · have : e ∈ H.filter (fun e => e ⊆ S ∨ e ⊆ Sᶜ) :=
        Finset.mem_filter.mpr ⟨he, Or.inl hcontra⟩
      rw [hempty] at this; exact Finset.notMem_empty _ this
    · have : e ∈ H.filter (fun e => e ⊆ S ∨ e ⊆ Sᶜ) :=
        Finset.mem_filter.mpr ⟨he, Or.inr hcontra⟩
      rw [hempty] at this; exact Finset.notMem_empty _ this

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
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_powerset,
      Set.mem_setOf_eq, colorings] at hS₁ hS₂
    have h1 : e ⊆ S₁ := hS₁.2
    have h2 : e ⊆ S₂ := hS₂.2
    have eq1 : S₁ = S₁ \ e ∪ e := (Finset.sdiff_union_of_subset h1).symm
    have eq2 : S₂ = S₂ \ e ∪ e := (Finset.sdiff_union_of_subset h2).symm
    rw [eq1, eq2]; simp only [hf_def] at hfeq; rw [hfeq]
  have himage : ((colorings α).filter (fun S => e ⊆ S)).image f = eᶜ.powerset := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset,
      colorings, Finset.subset_univ, true_and, hf_def]
    constructor
    · rintro ⟨S, heS, rfl⟩
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_compl] at hx ⊢
      exact hx.2
    · intro hT
      refine ⟨T ∪ e, Finset.subset_union_right, ?_⟩
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxor, hxe⟩
        rcases hxor with hxT | hxe'
        · exact hxT
        · exact (hxe hxe').elim
      · intro hxT
        have hxe : x ∉ e := by
          have := hT hxT
          simp only [Finset.mem_compl] at this
          exact this
        exact ⟨Or.inl hxT, hxe⟩
  have hcard : ((colorings α).filter (fun S => e ⊆ S)).card =
      (((colorings α).filter (fun S => e ⊆ S)).image f).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [hcard, himage, Finset.card_powerset, Finset.card_compl]

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
      true_and]
    constructor
    · intro hSub x hxS
      by_contra hxnec
      simp only [Finset.mem_compl, not_not] at hxnec
      have hxSc : x ∈ Sᶜ := hSub hxnec
      simp only [Finset.mem_compl] at hxSc
      exact hxSc hxS
    · intro hScompl x hxe
      simp only [Finset.mem_compl]
      intro hxS
      have : x ∈ eᶜ := hScompl hxS
      simp only [Finset.mem_compl] at this
      exact this hxe
  rw [h_eq, Finset.card_powerset, Finset.card_compl]

/-- For an `n`-uniform edge `e` with `n ≥ 1`, the number of 2-colorings making
`e` monochromatic equals `2 · 2^{v-n}` where `v = |α|`. -/
lemma card_monochromatic_for_edge {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 ≤ n) (e : Finset α) (he : e.card = n) :
    ((colorings α).filter (fun S => e ⊆ S ∨ e ⊆ Sᶜ)).card =
      2 * 2 ^ (Fintype.card α - n) := by
  classical
  have hdisj : Disjoint ((colorings α).filter (fun S => e ⊆ S))
                        ((colorings α).filter (fun S => e ⊆ Sᶜ)) := by
    rw [Finset.disjoint_filter]
    intro S _ hSsub hSsubc
    have hne : e.Nonempty := by
      rw [← Finset.card_pos]; omega
    rcases hne with ⟨x, hx⟩
    have hxS : x ∈ S := hSsub hx
    have hxSc : x ∈ Sᶜ := hSsubc hx
    simp only [Finset.mem_compl] at hxSc
    exact hxSc hxS
  have hunion : (colorings α).filter (fun S => e ⊆ S ∨ e ⊆ Sᶜ) =
      (colorings α).filter (fun S => e ⊆ S) ∪
        (colorings α).filter (fun S => e ⊆ Sᶜ) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hunion, Finset.card_union_of_disjoint hdisj,
      card_filter_superset e, card_filter_subset_compl e, he, two_mul]

/-! ### Double counting -/

/-- The key identity: summing the monochromatic count across all colorings
swaps with summing per-edge counts. -/
lemma sum_monoEdges_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 1 ≤ n) {H : Finset (Finset α)} (hH : Uniform n H) :
    ∑ S ∈ colorings α, (monoEdges H S).card =
      H.card * (2 * 2 ^ (Fintype.card α - n)) := by
  classical
  -- Rewrite (filter (mono S) H).card as ∑ e ∈ H, indicator.
  have h1 : ∀ S ∈ colorings α, (monoEdges H S).card =
      ∑ e ∈ H, if (e ⊆ S ∨ e ⊆ Sᶜ) then (1 : ℕ) else 0 := by
    intro S _
    unfold monoEdges
    exact Finset.card_filter (fun e => e ⊆ S ∨ e ⊆ Sᶜ) H
  rw [Finset.sum_congr rfl h1]
  -- Swap summation order.
  rw [Finset.sum_comm]
  -- For each e ∈ H, the inner sum equals (count of S making e mono).
  have h2 : ∀ e ∈ H,
      ∑ S ∈ colorings α, (if (e ⊆ S ∨ e ⊆ Sᶜ) then (1 : ℕ) else 0) =
        2 * 2 ^ (Fintype.card α - n) := by
    intro e he
    have hcard : e.card = n := hH e he
    have := card_monochromatic_for_edge (α := α) hn e hcard
    rw [← this]
    unfold colorings
    exact (Finset.card_filter (fun S => e ⊆ S ∨ e ⊆ Sᶜ)
            ((Finset.univ : Finset α).powerset)).symm
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
  have hge : ∀ S ∈ colorings α, 1 ≤ (monoEdges H S).card := by
    intro S _
    have hnotwit := hcontra S
    rw [propertyBWitness_iff_monoEdges_empty] at hnotwit
    by_contra hlt
    push_neg at hlt
    have : (monoEdges H S).card = 0 := by omega
    exact hnotwit (Finset.card_eq_zero.mp this)
  have hsum_ge : (colorings α).card ≤ ∑ S ∈ colorings α, (monoEdges H S).card := by
    have := Finset.card_eq_sum_ones (colorings α)
    rw [this]
    exact Finset.sum_le_sum hge
  rw [sum_monoEdges_card_eq hn hH, card_colorings] at hsum_ge
  -- Now: 2^v ≤ |H| * 2 * 2^(v - n), with v - n ≥ 0.
  -- I.e. 2^v ≤ 2 * |H| * 2^(v - n) < 2^n * 2^(v - n) = 2^v, contradiction.
  set v := Fintype.card α
  have hpow : 2 ^ v = 2 ^ n * 2 ^ (v - n) := by
    rw [← pow_add]; congr 1; omega
  have hineq : H.card * (2 * 2 ^ (v - n)) < 2 ^ n * 2 ^ (v - n) := by
    have hpos : 0 < 2 ^ (v - n) := pow_pos (by norm_num) _
    have := hsmall
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
