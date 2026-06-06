import Erdos.DivisibilityAvoidingSets.BlockCoverage

/-!
# Tagged arithmetic-progression block criterion

This file packages the work needed to turn a tagged AP block construction into
the positive square-root density statement for Erdős problem #12.  The remaining
construction work is arithmetical: choose residues, tags, and scales satisfying
the hypotheses below.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- If every AP block starts at a positive value, their ordered union is a
positive set. -/
theorem positiveSet_iUnion_apBlock {r M T L : ℕ → ℕ}
    (hmin : ∀ i, 0 < apMin (r i) (M i) (T i)) :
    PositiveSet (⋃ i, apBlock (r i) (M i) (T i) (L i)) := by
  intro n hn
  rcases Set.mem_iUnion.mp hn with ⟨i, hi⟩
  exact (hmin i).trans_le (apMin_le_of_mem_apBlock hi)

/-- If every ordered AP block is nonempty and all later blocks sit above all
earlier blocks, their union is infinite. -/
theorem infinite_iUnion_apBlock_of_order {r M T L : ℕ → ℕ}
    (hLpos : ∀ i, 0 < L i)
    (horder :
      ∀ ⦃i j x y : ℕ⦄, i < j →
        x ∈ apBlock (r i) (M i) (T i) (L i) →
        y ∈ apBlock (r j) (M j) (T j) (L j) →
        x < y) :
    (⋃ i, apBlock (r i) (M i) (T i) (L i)).Infinite := by
  let f : ℕ → ℕ := fun i => apMin (r i) (M i) (T i)
  have hf_mem_block : ∀ i, f i ∈ apBlock (r i) (M i) (T i) (L i) := by
    intro i
    refine ⟨0, hLpos i, ?_⟩
    simp [f, apMin]
  have hf_mem_union :
      Set.range f ⊆ ⋃ i, apBlock (r i) (M i) (T i) (L i) := by
    rintro n ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, hf_mem_block i⟩
  have hf_strict : StrictMono f := by
    intro i j hij
    exact horder hij (hf_mem_block i) (hf_mem_block j)
  exact (Set.infinite_range_of_injective hf_strict.injective).mono hf_mem_union

/-- Tagged, narrow, ordered AP blocks form an avoiding union. -/
theorem avoidingSet_iUnion_apBlock_of_tagged {r M T L q : ℕ → ℕ}
    (horder :
      ∀ ⦃i j x y : ℕ⦄, i < j →
        x ∈ apBlock (r i) (M i) (T i) (L i) →
        y ∈ apBlock (r j) (M j) (T j) (L j) →
        x < y)
    (hmin : ∀ i, 0 < apMin (r i) (M i) (T i))
    (hnarrow :
      ∀ i, 2 * apMax (r i) (M i) (T i) (L i) <
        3 * apMin (r i) (M i) (T i))
    (htag_zero :
      ∀ ⦃i x : ℕ⦄,
        x ∈ apBlock (r i) (M i) (T i) (L i) → q i ∣ x)
    (htag_one :
      ∀ ⦃i j x : ℕ⦄, i < j →
        x ∈ apBlock (r j) (M j) (T j) (L j) → x ≡ 1 [MOD q i])
    (hq_not_dvd_one : ∀ i, ¬ q i ∣ 1)
    (hq_not_dvd_two : ∀ i, ¬ q i ∣ 2) :
    AvoidingSet (⋃ i, apBlock (r i) (M i) (T i) (L i)) := by
  exact avoidingSet_iUnion_of_tagged_blocks
    (B := fun i => apBlock (r i) (M i) (T i) (L i)) (q := q)
    horder
    (fun i => avoidingSet_apBlock_of_narrow (hmin i) (hnarrow i))
    htag_zero htag_one hq_not_dvd_one hq_not_dvd_two

/-- A complete square-root-density criterion for tagged AP block
constructions.  It combines:

* ordered nonempty blocks for infinitude,
* tag congruences and narrowness for avoidance,
* endpoint coverage for the square-root lower bound.
-/
theorem erdos12_positiveSqrtDensity_of_tagged_ap_blocks
    {r M T L E q : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c)
    (hE : StrictMono E)
    (hM : ∀ i, 0 < M i)
    (hLpos : ∀ i, 0 < L i)
    (hmin : ∀ i, 1 ≤ apMin (r i) (M i) (T i))
    (hmax : ∀ i, apMax (r i) (M i) (T i) (L i) ≤ E i)
    (hcover : ∀ i, c * Real.sqrt (E (i + 1) : ℝ) ≤ (L i : ℝ))
    (horder :
      ∀ ⦃i j x y : ℕ⦄, i < j →
        x ∈ apBlock (r i) (M i) (T i) (L i) →
        y ∈ apBlock (r j) (M j) (T j) (L j) →
        x < y)
    (hnarrow :
      ∀ i, 2 * apMax (r i) (M i) (T i) (L i) <
        3 * apMin (r i) (M i) (T i))
    (htag_zero :
      ∀ ⦃i x : ℕ⦄,
        x ∈ apBlock (r i) (M i) (T i) (L i) → q i ∣ x)
    (htag_one :
      ∀ ⦃i j x : ℕ⦄, i < j →
        x ∈ apBlock (r j) (M j) (T j) (L j) → x ≡ 1 [MOD q i])
    (hq_not_dvd_one : ∀ i, ¬ q i ∣ 1)
    (hq_not_dvd_two : ∀ i, ¬ q i ∣ 2) :
    Erdos12PositiveSqrtDensityQuestion := by
  let A : Set ℕ := ⋃ i, apBlock (r i) (M i) (T i) (L i)
  have hAinf : A.Infinite :=
    infinite_iUnion_apBlock_of_order hLpos horder
  have hApos : PositiveSet A :=
    positiveSet_iUnion_apBlock
      (fun i => lt_of_lt_of_le Nat.zero_lt_one (hmin i))
  have hAavoid : AvoidingSet A :=
    avoidingSet_iUnion_apBlock_of_tagged horder
      (fun i => lt_of_lt_of_le Nat.zero_lt_one (hmin i))
      hnarrow htag_zero htag_one hq_not_dvd_one hq_not_dvd_two
  refine erdos12_positiveSqrtDensity_of_ap_blocks
    (A := A) (r := r) (M := M) (T := T) (L := L) (E := E) (c := c)
    hAinf hApos hAavoid hc hE hM ?_ hmin hmax hcover
  intro i n hn
  exact Set.mem_iUnion.mpr ⟨i, hn⟩

end DivisibilityAvoidingSets
