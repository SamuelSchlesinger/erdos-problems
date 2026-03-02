/-
# Generic Packing Bound

Reusable counting argument for density upper bounds.

Given a "forbidden" set A ⊆ {1,…,N} and pairwise disjoint gadgets of
constant size s, each of which allows at most r elements in A (r ≤ s),
the deficit (s − r) per gadget forces:

  A.card + (s − r) * |D| ≤ N

The two-family version handles S + T families with cross-disjointness:

  A.card + (s₁ − r₁) * |D₁| + (s₂ − r₂) * |D₂| ≤ N

This abstracts the capstone pattern from UnitFractionPairs/VanDoorn.lean,
UnitFractionTriples/VanDoorn.lean, and StarNeighborhood.lean.
-/
import Mathlib

namespace PackingBound

/-! ### Helper lemmas -/

/-- |⋃ S_d| = s * |D| when all |S_d| = s and the gadgets are pairwise disjoint. -/
theorem card_biUnion_const (D : Finset ℕ) (gadget : ℕ → Finset ℕ) (s : ℕ)
    (hpwd : (↑D : Set ℕ).PairwiseDisjoint gadget)
    (hcard : ∀ d ∈ D, (gadget d).card = s) :
    (D.biUnion gadget).card = s * D.card := by
  rw [Finset.card_biUnion hpwd, Finset.sum_const_nat hcard]
  ring

/-- |(⋃ S_d) ∩ A| ≤ r * |D| when each |S_d ∩ A| ≤ r and gadgets are pairwise disjoint. -/
theorem card_inter_biUnion_le (D : Finset ℕ) (gadget : ℕ → Finset ℕ)
    (A : Finset ℕ) (r : ℕ)
    (hpwd : (↑D : Set ℕ).PairwiseDisjoint gadget)
    (hinter : ∀ d ∈ D, (gadget d ∩ A).card ≤ r) :
    (D.biUnion gadget ∩ A).card ≤ r * D.card := by
  rw [Finset.biUnion_inter]
  have hpwd' : (↑D : Set ℕ).PairwiseDisjoint (fun d => gadget d ∩ A) := by
    intro a₁ ha₁ a₂ ha₂ hne
    exact (hpwd ha₁ ha₂ hne).mono Finset.inter_subset_left Finset.inter_subset_left
  calc (D.biUnion (fun d => gadget d ∩ A)).card
      = ∑ d ∈ D, (gadget d ∩ A).card := Finset.card_biUnion hpwd'
    _ ≤ ∑ d ∈ D, r := Finset.sum_le_sum hinter
    _ = D.card * r := Finset.sum_const_nat (fun _ _ => rfl)
    _ = r * D.card := by ring

/-! ### Single-family packing bound -/

/-- Standard packing bound: A ⊆ [1,N] with pairwise disjoint gadgets of size s,
    each allowing ≤ r elements in A (r ≤ s), implies A.card + (s-r)*|D| ≤ N. -/
theorem single_family_bound (N : ℕ) (A D : Finset ℕ) (gadget : ℕ → Finset ℕ)
    (s r : ℕ) (hle : r ≤ s)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hpwd : (↑D : Set ℕ).PairwiseDisjoint gadget)
    (hcard : ∀ d ∈ D, (gadget d).card = s)
    (hinter : ∀ d ∈ D, (gadget d ∩ A).card ≤ r)
    (hsub : D.biUnion gadget ⊆ Finset.Icc 1 N) :
    A.card + (s - r) * D.card ≤ N := by
  set U := D.biUnion gadget
  -- |U| = s * |D|
  have hUcard : U.card = s * D.card := card_biUnion_const D gadget s hpwd hcard
  -- |U ∩ A| ≤ r * |D|
  have hUA : (U ∩ A).card ≤ r * D.card := card_inter_biUnion_le D gadget A r hpwd hinter
  -- A ⊆ (U ∩ A) ∪ (Icc \ U)
  have hAle : A.card ≤ (U ∩ A).card + (Finset.Icc 1 N \ U).card :=
    calc A.card
        ≤ (U ∩ A ∪ (Finset.Icc 1 N \ U)).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ U
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  -- |Icc \ U| + |U| = N
  have hsdiff : (Finset.Icc 1 N \ U).card + U.card = (Finset.Icc 1 N).card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  -- Help omega with ℕ subtraction: (s-r)*|D| + r*|D| = s*|D|
  have hsub_mul : (s - r) * D.card + r * D.card = s * D.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle]
  omega

/-! ### Two-family packing bound -/

/-- Two-family packing bound with cross-disjointness.
    Two independent gadget families with pairwise disjoint gadgets of sizes s₁, s₂,
    each allowing ≤ r₁, r₂ elements in A, and families cross-disjoint, implies
    A.card + (s₁-r₁)*|D₁| + (s₂-r₂)*|D₂| ≤ N. -/
theorem two_family_bound (N : ℕ) (A D₁ D₂ : Finset ℕ)
    (gadget₁ gadget₂ : ℕ → Finset ℕ) (s₁ r₁ s₂ r₂ : ℕ)
    (hle₁ : r₁ ≤ s₁) (hle₂ : r₂ ≤ s₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    -- Family 1
    (hpwd₁ : (↑D₁ : Set ℕ).PairwiseDisjoint gadget₁)
    (hcard₁ : ∀ d ∈ D₁, (gadget₁ d).card = s₁)
    (hinter₁ : ∀ d ∈ D₁, (gadget₁ d ∩ A).card ≤ r₁)
    (hsub₁ : D₁.biUnion gadget₁ ⊆ Finset.Icc 1 N)
    -- Family 2
    (hpwd₂ : (↑D₂ : Set ℕ).PairwiseDisjoint gadget₂)
    (hcard₂ : ∀ d ∈ D₂, (gadget₂ d).card = s₂)
    (hinter₂ : ∀ d ∈ D₂, (gadget₂ d ∩ A).card ≤ r₂)
    (hsub₂ : D₂.biUnion gadget₂ ⊆ Finset.Icc 1 N)
    -- Cross-disjointness
    (hcross : Disjoint (D₁.biUnion gadget₁) (D₂.biUnion gadget₂)) :
    A.card + (s₁ - r₁) * D₁.card + (s₂ - r₂) * D₂.card ≤ N := by
  set U₁ := D₁.biUnion gadget₁
  set U₂ := D₂.biUnion gadget₂
  -- Cardinalities
  have hU₁card : U₁.card = s₁ * D₁.card := card_biUnion_const D₁ gadget₁ s₁ hpwd₁ hcard₁
  have hU₂card : U₂.card = s₂ * D₂.card := card_biUnion_const D₂ gadget₂ s₂ hpwd₂ hcard₂
  -- Intersection bounds
  have hU₁A : (U₁ ∩ A).card ≤ r₁ * D₁.card := card_inter_biUnion_le D₁ gadget₁ A r₁ hpwd₁ hinter₁
  have hU₂A : (U₂ ∩ A).card ≤ r₂ * D₂.card := card_inter_biUnion_le D₂ gadget₂ A r₂ hpwd₂ hinter₂
  -- Union
  have hU_card : (U₁ ∪ U₂).card = U₁.card + U₂.card :=
    Finset.card_union_of_disjoint hcross
  have hUsub : U₁ ∪ U₂ ⊆ Finset.Icc 1 N :=
    Finset.union_subset hsub₁ hsub₂
  -- Combined intersection: |(U₁ ∪ U₂) ∩ A| ≤ r₁*|D₁| + r₂*|D₂|
  have hUA : ((U₁ ∪ U₂) ∩ A).card ≤ r₁ * D₁.card + r₂ * D₂.card :=
    calc ((U₁ ∪ U₂) ∩ A).card
        ≤ (U₁ ∩ A).card + (U₂ ∩ A).card := by
          rw [Finset.union_inter_distrib_right]
          exact Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add hU₁A hU₂A
  -- A ⊆ (U ∩ A) ∪ (Icc \ U)
  have hAle : A.card ≤ ((U₁ ∪ U₂) ∩ A).card + (Finset.Icc 1 N \ (U₁ ∪ U₂)).card :=
    calc A.card
        ≤ ((U₁ ∪ U₂) ∩ A ∪ (Finset.Icc 1 N \ (U₁ ∪ U₂))).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ U₁ ∪ U₂
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  -- |Icc \ U| + |U| = N
  have hsdiff : (Finset.Icc 1 N \ (U₁ ∪ U₂)).card + (U₁ ∪ U₂).card =
      (Finset.Icc 1 N).card := Finset.card_sdiff_add_card_eq_card hUsub
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  -- Help omega with ℕ subtraction
  have hsub_mul₁ : (s₁ - r₁) * D₁.card + r₁ * D₁.card = s₁ * D₁.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle₁]
  have hsub_mul₂ : (s₂ - r₂) * D₂.card + r₂ * D₂.card = s₂ * D₂.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle₂]
  omega

/-! ### Three-family packing bound -/

/-- Three-family packing bound with pairwise cross-disjointness.
    Three independent gadget families with pairwise disjoint gadgets of sizes
    s₁, s₂, s₃, each allowing ≤ r₁, r₂, r₃ elements in A, and families
    pairwise cross-disjoint, implies
    A.card + (s₁-r₁)*|D₁| + (s₂-r₂)*|D₂| + (s₃-r₃)*|D₃| ≤ N. -/
theorem three_family_bound (N : ℕ) (A D₁ D₂ D₃ : Finset ℕ)
    (gadget₁ gadget₂ gadget₃ : ℕ → Finset ℕ) (s₁ r₁ s₂ r₂ s₃ r₃ : ℕ)
    (hle₁ : r₁ ≤ s₁) (hle₂ : r₂ ≤ s₂) (hle₃ : r₃ ≤ s₃)
    (hAN : A ⊆ Finset.Icc 1 N)
    -- Family 1
    (hpwd₁ : (↑D₁ : Set ℕ).PairwiseDisjoint gadget₁)
    (hcard₁ : ∀ d ∈ D₁, (gadget₁ d).card = s₁)
    (hinter₁ : ∀ d ∈ D₁, (gadget₁ d ∩ A).card ≤ r₁)
    (hsub₁ : D₁.biUnion gadget₁ ⊆ Finset.Icc 1 N)
    -- Family 2
    (hpwd₂ : (↑D₂ : Set ℕ).PairwiseDisjoint gadget₂)
    (hcard₂ : ∀ d ∈ D₂, (gadget₂ d).card = s₂)
    (hinter₂ : ∀ d ∈ D₂, (gadget₂ d ∩ A).card ≤ r₂)
    (hsub₂ : D₂.biUnion gadget₂ ⊆ Finset.Icc 1 N)
    -- Family 3
    (hpwd₃ : (↑D₃ : Set ℕ).PairwiseDisjoint gadget₃)
    (hcard₃ : ∀ d ∈ D₃, (gadget₃ d).card = s₃)
    (hinter₃ : ∀ d ∈ D₃, (gadget₃ d ∩ A).card ≤ r₃)
    (hsub₃ : D₃.biUnion gadget₃ ⊆ Finset.Icc 1 N)
    -- Pairwise cross-disjointness
    (hcross₁₂ : Disjoint (D₁.biUnion gadget₁) (D₂.biUnion gadget₂))
    (hcross₁₃ : Disjoint (D₁.biUnion gadget₁) (D₃.biUnion gadget₃))
    (hcross₂₃ : Disjoint (D₂.biUnion gadget₂) (D₃.biUnion gadget₃)) :
    A.card + (s₁ - r₁) * D₁.card + (s₂ - r₂) * D₂.card +
      (s₃ - r₃) * D₃.card ≤ N := by
  set U₁ := D₁.biUnion gadget₁
  set U₂ := D₂.biUnion gadget₂
  set U₃ := D₃.biUnion gadget₃
  -- Cardinalities
  have hU₁card : U₁.card = s₁ * D₁.card := card_biUnion_const D₁ gadget₁ s₁ hpwd₁ hcard₁
  have hU₂card : U₂.card = s₂ * D₂.card := card_biUnion_const D₂ gadget₂ s₂ hpwd₂ hcard₂
  have hU₃card : U₃.card = s₃ * D₃.card := card_biUnion_const D₃ gadget₃ s₃ hpwd₃ hcard₃
  -- Intersection bounds
  have hU₁A : (U₁ ∩ A).card ≤ r₁ * D₁.card :=
    card_inter_biUnion_le D₁ gadget₁ A r₁ hpwd₁ hinter₁
  have hU₂A : (U₂ ∩ A).card ≤ r₂ * D₂.card :=
    card_inter_biUnion_le D₂ gadget₂ A r₂ hpwd₂ hinter₂
  have hU₃A : (U₃ ∩ A).card ≤ r₃ * D₃.card :=
    card_inter_biUnion_le D₃ gadget₃ A r₃ hpwd₃ hinter₃
  -- U₁ ∪ U₂ and U₃ are disjoint
  have hU₁₂_U₃ : Disjoint (U₁ ∪ U₂) U₃ :=
    Finset.disjoint_union_left.mpr ⟨hcross₁₃, hcross₂₃⟩
  -- Three-way union
  set U := U₁ ∪ U₂ ∪ U₃
  have hU_card : U.card = U₁.card + U₂.card + U₃.card := by
    rw [show U = (U₁ ∪ U₂) ∪ U₃ from rfl,
        Finset.card_union_of_disjoint hU₁₂_U₃,
        Finset.card_union_of_disjoint hcross₁₂]
  have hUsub : U ⊆ Finset.Icc 1 N :=
    Finset.union_subset (Finset.union_subset hsub₁ hsub₂) hsub₃
  -- Combined intersection bound
  have hUA : (U ∩ A).card ≤ r₁ * D₁.card + r₂ * D₂.card + r₃ * D₃.card := by
    have h12 : ((U₁ ∪ U₂) ∩ A).card ≤ (U₁ ∩ A).card + (U₂ ∩ A).card := by
      rw [Finset.union_inter_distrib_right]; exact Finset.card_union_le _ _
    have h123 : (U ∩ A).card ≤ ((U₁ ∪ U₂) ∩ A).card + (U₃ ∩ A).card := by
      change ((U₁ ∪ U₂ ∪ U₃) ∩ A).card ≤ _
      rw [Finset.union_inter_distrib_right]; exact Finset.card_union_le _ _
    omega
  -- A ⊆ (U ∩ A) ∪ (Icc \ U)
  have hAle : A.card ≤ (U ∩ A).card + (Finset.Icc 1 N \ U).card :=
    calc A.card
        ≤ (U ∩ A ∪ (Finset.Icc 1 N \ U)).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ U
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  -- |Icc \ U| + |U| = N
  have hsdiff : (Finset.Icc 1 N \ U).card + U.card = (Finset.Icc 1 N).card :=
    Finset.card_sdiff_add_card_eq_card hUsub
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  -- Help omega with ℕ subtraction
  have hsub_mul₁ : (s₁ - r₁) * D₁.card + r₁ * D₁.card = s₁ * D₁.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle₁]
  have hsub_mul₂ : (s₂ - r₂) * D₂.card + r₂ * D₂.card = s₂ * D₂.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle₂]
  have hsub_mul₃ : (s₃ - r₃) * D₃.card + r₃ * D₃.card = s₃ * D₃.card := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle₃]
  omega

end PackingBound
