/-
# Generic Gap Counts for Subsets of `ℤ`

Reusable counting infrastructure for the "shape" of a finite set of integers
via gap and isolation statistics.

For a set `X ⊆ ℤ`:
- `gapCount X k` is the number of `x ∈ X` with `x + k ∈ X`,
- `numInterior X` is the number of `x ∈ X` with both `x - 1, x + 1 ∈ X`,
- `numIsolated X` is the number of `x ∈ X` with neither `x - 1` nor `x + 1` in `X`,
- `skipOver X` is the set of `x ∈ X` with `x + 1 ∉ X` but `x + 2 ∈ X`.

These are the elementary primitives underlying the Erdős–Sárközy–Sós
isolated-sums bound for finite Sidon sets (Erdős problem `#152`) and related
extremal arguments. This file collects only the *generic* structural identities
that hold for arbitrary subsets of `ℤ`; the Sidon-specific quadruple-counting
argument that bounds `numIsolated (A + A)` from below is downstream.

Reference (technique): the proof structure of `erdos_152.lean` in
`google-deepmind/alphaproof-nexus-results` (Apache 2.0).
-/
import Mathlib

set_option linter.style.header false

namespace GapCounts

variable (X : Set ℤ)

/-- The gap-`k` count: number of `x ∈ X` such that `x + k ∈ X`. -/
noncomputable def gapCount (k : ℤ) : ℕ := {x ∈ X | x + k ∈ X}.ncard

/-- Interior points of `X`: elements with both immediate neighbors in `X`. -/
noncomputable def numInterior : ℕ := {x ∈ X | x - 1 ∈ X ∧ x + 1 ∈ X}.ncard

/-- Isolated points of `X`: elements with neither immediate neighbor in `X`. -/
noncomputable def numIsolated : ℕ := {x ∈ X | x - 1 ∉ X ∧ x + 1 ∉ X}.ncard

/-- Skip-over points of `X`: `x ∈ X` with `x + 1 ∉ X` but `x + 2 ∈ X`. -/
def skipOver : Set ℤ := {x ∈ X | x + 1 ∉ X ∧ x + 2 ∈ X}

/-! ### Basic membership and finiteness -/

theorem subset_of_gapCount_set {k : ℤ} : {x ∈ X | x + k ∈ X} ⊆ X := fun _ hx => hx.1

theorem subset_of_interior_set : {x ∈ X | x - 1 ∈ X ∧ x + 1 ∈ X} ⊆ X := fun _ hx => hx.1

theorem subset_of_isolated_set : {x ∈ X | x - 1 ∉ X ∧ x + 1 ∉ X} ⊆ X := fun _ hx => hx.1

theorem skipOver_subset : skipOver X ⊆ X := fun _ hx => hx.1

theorem gapCount_le_ncard (hX : X.Finite) (k : ℤ) : gapCount X k ≤ X.ncard :=
  Set.ncard_le_ncard (subset_of_gapCount_set X) hX

theorem numInterior_le_ncard (hX : X.Finite) : numInterior X ≤ X.ncard :=
  Set.ncard_le_ncard (subset_of_interior_set X) hX

theorem numIsolated_le_ncard (hX : X.Finite) : numIsolated X ≤ X.ncard :=
  Set.ncard_le_ncard (subset_of_isolated_set X) hX

/-! ### Pointwise four-window indicator inequality

The core algebraic kernel of the argument bounding `numIsolated (A + A)` for
Sidon sets `A`. Writing the indicators of `x, x+1, x+2, x+3` as `a, b, c, d`,
this pointwise inequality between Boolean-valued polynomials is the seed that,
when summed over all `x`, yields `4 · gapCount X 1 + gapCount X 3 ≤
3 · X.ncard + 2 · gapCount X 2`. -/

/-- Pointwise indicator inequality on a four-element window `{x, x+1, x+2, x+3}`. -/
theorem four_window_indicator_ineq (a b c d : ℤ)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) :
    a * b + 2 * b * c + c * d + a * d ≤ a + b + c + a * c + b * d := by
  rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;>
        rcases hd with rfl | rfl <;> omega

/-! ### Shift symmetry of `gapCount`

The set `{x ∈ X | x + k ∈ X}` is in bijection with `{y ∈ X | y - k ∈ X}` via
`x ↦ x + k`, so the count is invariant under reflecting the gap direction. -/

theorem ncard_setOf_sub_eq_gapCount (k : ℤ) :
    {x ∈ X | x - k ∈ X}.ncard = gapCount X k := by
  classical
  have hbij : {x ∈ X | x - k ∈ X} = (fun y => y + k) '' {y ∈ X | y + k ∈ X} := by
    ext z
    constructor
    · rintro ⟨hz, hzk⟩
      refine ⟨z - k, ⟨hzk, ?_⟩, by ring⟩
      simpa using hz
    · rintro ⟨y, ⟨hy, hyk⟩, rfl⟩
      refine ⟨hyk, ?_⟩
      simpa using hy
  rw [hbij, Set.ncard_image_of_injective _ (add_left_injective k)]
  rfl

/-! ### Partition identity

`numIsolated X + 2 · gapCount X 1 = X.ncard + numInterior X`.

Proof sketch: partition `X` into the four cells determined by whether each of
`x - 1, x + 1` lies in `X`. With cells
`I, L, R, C` (isolated, left-only, right-only, interior) we have
`|X| = |I| + |L| + |R| + |C|`, while
`gapCount X 1 = |R| + |C|` (counting `x ∈ X` with `x + 1 ∈ X`) and
`gapCount X 1 = |L| + |C|` (counting `x ∈ X` with `x - 1 ∈ X`, equal by shift).
Hence `2 · gapCount X 1 = |L| + |R| + 2 |C|`, and rearranging gives the claim. -/

theorem numIsolated_add_two_mul_gapCount_one (hX : X.Finite) :
    numIsolated X + 2 * gapCount X 1 = X.ncard + numInterior X := by
  classical
  -- Four cells.
  set I : Set ℤ := {x ∈ X | x - 1 ∉ X ∧ x + 1 ∉ X} with hI_def
  set L : Set ℤ := {x ∈ X | x - 1 ∈ X ∧ x + 1 ∉ X} with hL_def
  set R : Set ℤ := {x ∈ X | x - 1 ∉ X ∧ x + 1 ∈ X} with hR_def
  set C : Set ℤ := {x ∈ X | x - 1 ∈ X ∧ x + 1 ∈ X} with hC_def
  have hI_fin : I.Finite := hX.subset (fun _ hx => hx.1)
  have hL_fin : L.Finite := hX.subset (fun _ hx => hx.1)
  have hR_fin : R.Finite := hX.subset (fun _ hx => hx.1)
  have hC_fin : C.Finite := hX.subset (fun _ hx => hx.1)
  -- Cell cardinalities in terms of named counts.
  have hI_card : I.ncard = numIsolated X := rfl
  have hC_card : C.ncard = numInterior X := rfl
  -- (1) `R ∪ C = {x ∈ X | x + 1 ∈ X}`, disjoint, total = `gapCount X 1`.
  have h_union_right : R ∪ C = {x ∈ X | x + 1 ∈ X} := by
    ext x
    constructor
    · rintro (⟨hx, _, h1⟩ | ⟨hx, _, h1⟩) <;> exact ⟨hx, h1⟩
    · rintro ⟨hx, h1⟩
      by_cases hm1 : x - 1 ∈ X
      · right; exact ⟨hx, hm1, h1⟩
      · left; exact ⟨hx, hm1, h1⟩
  have h_disj_right : Disjoint R C := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hm1, _⟩ ⟨_, hm1', _⟩
    exact hm1 hm1'
  have h_R_add_C : R.ncard + C.ncard = gapCount X 1 := by
    rw [← Set.ncard_union_eq h_disj_right hR_fin hC_fin, h_union_right]
    rfl
  -- (2) `L ∪ C = {x ∈ X | x - 1 ∈ X}`, disjoint, total = `gapCount X 1` (via shift).
  have h_union_left : L ∪ C = {x ∈ X | x - 1 ∈ X} := by
    ext x
    constructor
    · rintro (⟨hx, hm1, _⟩ | ⟨hx, hm1, _⟩) <;> exact ⟨hx, hm1⟩
    · rintro ⟨hx, hm1⟩
      by_cases hp1 : x + 1 ∈ X
      · right; exact ⟨hx, hm1, hp1⟩
      · left; exact ⟨hx, hm1, hp1⟩
  have h_disj_left : Disjoint L C := by
    rw [Set.disjoint_left]
    rintro x ⟨_, _, h1⟩ ⟨_, _, h1'⟩
    exact h1 h1'
  have h_L_add_C : L.ncard + C.ncard = gapCount X 1 := by
    have := ncard_setOf_sub_eq_gapCount X 1
    rw [← Set.ncard_union_eq h_disj_left hL_fin hC_fin, h_union_left, this]
  -- (3) Partition `X = I ∪ L ∪ R ∪ C` with all four cells disjoint.
  have h_partition : X = I ∪ L ∪ R ∪ C := by
    ext x
    simp only [Set.mem_union, hI_def, hL_def, hR_def, hC_def, Set.mem_setOf_eq]
    constructor
    · intro hx
      by_cases hm1 : x - 1 ∈ X <;> by_cases hp1 : x + 1 ∈ X
      · -- hm1=T, hp1=T → C (interior).
        right; exact ⟨hx, hm1, hp1⟩
      · -- hm1=T, hp1=F → L (left-only).
        left; left; right; exact ⟨hx, hm1, hp1⟩
      · -- hm1=F, hp1=T → R (right-only).
        left; right; exact ⟨hx, hm1, hp1⟩
      · -- hm1=F, hp1=F → I (isolated).
        left; left; left; exact ⟨hx, hm1, hp1⟩
    · rintro (((⟨hx, _, _⟩ | ⟨hx, _, _⟩) | ⟨hx, _, _⟩) | ⟨hx, _, _⟩) <;> exact hx
  -- Disjointness of all four cells.
  have h_disj_IL : Disjoint I L := by
    rw [Set.disjoint_left]; rintro x ⟨_, h1, _⟩ ⟨_, h1', _⟩; exact h1 h1'
  have h_disj_IR : Disjoint I R := by
    rw [Set.disjoint_left]; rintro x ⟨_, _, h1⟩ ⟨_, _, h1'⟩; exact h1 h1'
  have h_disj_IC : Disjoint I C := by
    rw [Set.disjoint_left]; rintro x ⟨_, h1, _⟩ ⟨_, h1', _⟩; exact h1 h1'
  have h_disj_LR : Disjoint L R := by
    rw [Set.disjoint_left]; rintro x ⟨_, h1, _⟩ ⟨_, h1', _⟩; exact h1' h1
  have h_disj_IuL_R : Disjoint (I ∪ L) R := by
    rw [Set.disjoint_union_left]; exact ⟨h_disj_IR, h_disj_LR⟩
  have h_disj_IuLuR_C : Disjoint ((I ∪ L) ∪ R) C := by
    rw [Set.disjoint_union_left, Set.disjoint_union_left]
    exact ⟨⟨h_disj_IC, h_disj_left⟩, h_disj_right⟩
  -- Compute |X| as the sum of the four cell cardinalities.
  have h_X_card : X.ncard = I.ncard + L.ncard + R.ncard + C.ncard := by
    rw [h_partition,
        Set.ncard_union_eq h_disj_IuLuR_C ((hI_fin.union hL_fin).union hR_fin) hC_fin,
        Set.ncard_union_eq h_disj_IuL_R (hI_fin.union hL_fin) hR_fin,
        Set.ncard_union_eq h_disj_IL hI_fin hL_fin]
  -- Combine: `|I| + 2 · gap = |I| + (|L| + |C|) + (|R| + |C|) = |X| + |C|`.
  rw [← hI_card, ← hC_card]
  omega

end GapCounts
