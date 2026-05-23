/-
# Elementary Cubic Bound for Obstruction-Covered Sidon Sets

If a Sidon set `A ⊆ {1, ..., N}` has the property that every outside point is
captured by one of the elementary obstruction families

- midpoint candidates `(a + b) / 2`, or
- sum-difference candidates `a + b - c`,

then the interval `{1, ..., N}` is covered by `A` together with at most
`|A|^2 + |A|^3` further candidates. This gives the coarse bound

`N ≤ |A| + |A|^2 + |A|^3`.

This is the standard easy counting heuristic behind the lower bound
`|A| ≫ N^{1/3}` for maximal Sidon sets.

We also derive a sharper cubic bound `N ≤ |A|^3 + |A|^2 - |A|` by stripping
away the redundant obstructions coming from diagonal pairs `(a, a)` (whose
midpoint is `a ∈ A`) and from triples `(a, a, a)` (whose sum-difference is
`a ∈ A`). After these explicit cancellations the obstruction count drops below
`|A|^3 + |A|^2`, comfortably under the crude `3|A|^3` bound and approaching the
expected leading constant `1`.
-/
import Erdos.MaximalSidonSets.Statement

namespace MaximalSidonSets

/-- There are at most `|A|^2` midpoint candidates. -/
theorem card_midpointCandidates_le (A : Finset ℕ) :
    (midpointCandidates A).card ≤ A.card ^ 2 := by
  calc
    (midpointCandidates A).card ≤ (A.product A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product _ _
    _ = A.card ^ 2 := by rw [pow_two]

/-- There are at most `|A|^3` sum-difference candidates. -/
theorem card_sumDiffCandidates_le (A : Finset ℕ) :
    (sumDiffCandidates A).card ≤ A.card ^ 3 := by
  calc
    (sumDiffCandidates A).card ≤ ((A.product A).product A).card := Finset.card_image_le
    _ = (A.product A).card * A.card := Finset.card_product _ _
    _ = (A.card * A.card) * A.card := by simp [Finset.card_product]
    _ = A.card ^ 3 := by
      rw [pow_succ, pow_two]

/-! ### Refined obstruction counts

We now strip off the trivially redundant midpoint and sum-difference
obstructions and prove a strictly sharper cubic bound. -/

/-- Midpoint candidates coming from genuinely distinct pairs `a ≠ b`. -/
def midpointOffDiagCandidates (A : Finset ℕ) : Finset ℕ :=
  A.offDiag.image fun ab => (ab.1 + ab.2) / 2

/-- Sum-difference candidates coming from triples not all equal. -/
def sumDiffNontrivialCandidates (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (((A ×ˢ A) ×ˢ A).filter
      (fun abc => ¬ (abc.1.1 = abc.1.2 ∧ abc.1.2 = abc.2))).image
    (fun abc => abc.1.1 + abc.1.2 - abc.2)

/-- Off-diagonal midpoint candidates form an obvious subset of all midpoint
candidates. -/
theorem midpointOffDiagCandidates_subset (A : Finset ℕ) :
    midpointOffDiagCandidates A ⊆ midpointCandidates A := by
  intro x hx
  simp only [midpointOffDiagCandidates, Finset.mem_image, Finset.mem_offDiag] at hx
  rcases hx with ⟨⟨a, b⟩, ⟨ha, hb, _⟩, hx⟩
  refine Finset.mem_image.mpr ⟨(a, b), ?_, hx⟩
  exact Finset.mem_product.mpr ⟨ha, hb⟩

/-- Every diagonal midpoint is already in `A`, so dropping it from the
candidate family does not enlarge the obstruction. -/
theorem midpointCandidates_subset_union (A : Finset ℕ) :
    midpointCandidates A ⊆ A ∪ midpointOffDiagCandidates A := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨⟨a, b⟩, hab, hx⟩
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  by_cases hab_eq : a = b
  · subst hab_eq
    have hx' : x = a := by
      have h : (a + a) / 2 = a := by omega
      simpa [h] using hx.symm
    exact Finset.mem_union.mpr (Or.inl (hx' ▸ ha))
  · refine Finset.mem_union.mpr (Or.inr ?_)
    refine Finset.mem_image.mpr ⟨(a, b), ?_, hx⟩
    simp [Finset.mem_offDiag, ha, hb, hab_eq]

/-- Sub-diagonal sum-difference candidates form an obvious subset of all
sum-difference candidates. -/
theorem sumDiffNontrivialCandidates_subset (A : Finset ℕ) :
    sumDiffNontrivialCandidates A ⊆ sumDiffCandidates A := by
  classical
  intro x hx
  simp only [sumDiffNontrivialCandidates, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product] at hx
  rcases hx with ⟨⟨⟨a, b⟩, c⟩, ⟨⟨⟨ha, hb⟩, hc⟩, _⟩, hx⟩
  refine Finset.mem_image.mpr ⟨((a, b), c), ?_, hx⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩

/-- Every fully-diagonal triple gives a sum-difference equal to a member of
`A`, so dropping such triples does not enlarge the obstruction. -/
theorem sumDiffCandidates_subset_union (A : Finset ℕ) :
    sumDiffCandidates A ⊆ A ∪ sumDiffNontrivialCandidates A := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨⟨⟨a, b⟩, c⟩, habc, hx⟩
  rcases Finset.mem_product.mp habc with ⟨hab, hc⟩
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  by_cases hall : a = b ∧ b = c
  · obtain ⟨hab_eq, hbc_eq⟩ := hall
    subst hab_eq
    subst hbc_eq
    have hx' : x = a := by
      have h : a + a - a = a := by omega
      simpa [h] using hx.symm
    exact Finset.mem_union.mpr (Or.inl (hx' ▸ ha))
  · refine Finset.mem_union.mpr (Or.inr ?_)
    refine Finset.mem_image.mpr ⟨((a, b), c), ?_, hx⟩
    refine Finset.mem_filter.mpr ⟨?_, hall⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩

/-- **Midpoint obstruction count bound.** Counting only midpoints from genuinely
distinct pairs `a ≠ b`, there are at most `|A|^2 - |A|` such midpoints, half of
which are forced to coincide by symmetry but which we do not need here. -/
theorem card_midpointOffDiagCandidates_le (A : Finset ℕ) :
    (midpointOffDiagCandidates A).card ≤ A.card ^ 2 - A.card := by
  calc
    (midpointOffDiagCandidates A).card
        ≤ A.offDiag.card := Finset.card_image_le
    _ = A.card * A.card - A.card := Finset.offDiag_card A
    _ = A.card ^ 2 - A.card := by rw [pow_two]

/-- **Sum-difference obstruction count bound.** Counting only sum-differences
from triples `(a, b, c)` not all equal, there are at most `|A|^3 - |A|` such
candidates. -/
theorem card_sumDiffNontrivialCandidates_le (A : Finset ℕ) :
    (sumDiffNontrivialCandidates A).card ≤ A.card ^ 3 - A.card := by
  classical
  -- Cardinality of the filtered triple set is `|A|^3 - |A|`.
  have hdom :
      (((A ×ˢ A) ×ˢ A).filter
          (fun abc : (ℕ × ℕ) × ℕ => ¬ (abc.1.1 = abc.1.2 ∧ abc.1.2 = abc.2))).card
        = A.card ^ 3 - A.card := by
    -- The complement (the "all-equal" diagonal) is in bijection with `A` via
    -- `a ↦ ((a, a), a)`, so it has cardinality `|A|`.
    have hdiag :
        (((A ×ˢ A) ×ˢ A).filter
            (fun abc : (ℕ × ℕ) × ℕ => (abc.1.1 = abc.1.2 ∧ abc.1.2 = abc.2))).card
          = A.card := by
      let f : ℕ → (ℕ × ℕ) × ℕ := fun a => ((a, a), a)
      have hf : Function.Injective f := by
        intro a b h
        have := congrArg (·.2) h
        simpa [f] using this
      have himage :
          A.image f =
            ((A ×ˢ A) ×ˢ A).filter
              (fun abc : (ℕ × ℕ) × ℕ => abc.1.1 = abc.1.2 ∧ abc.1.2 = abc.2) := by
        ext ⟨⟨a, b⟩, c⟩
        constructor
        · intro h
          rcases Finset.mem_image.mp h with ⟨t, htA, ht⟩
          have ht1 : t = a := by simpa [f] using congrArg (·.1.1) ht
          have ht2 : t = b := by simpa [f] using congrArg (·.1.2) ht
          have ht3 : t = c := by simpa [f] using congrArg (·.2) ht
          have hab : a = b := ht1.symm.trans ht2
          have hbc : b = c := ht2.symm.trans ht3
          refine Finset.mem_filter.mpr ⟨?_, hab, hbc⟩
          refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
          · exact ht1 ▸ htA
          · exact ht2 ▸ htA
          · exact ht3 ▸ htA
        · intro h
          rcases Finset.mem_filter.mp h with ⟨hmem, h12, h23⟩
          rcases Finset.mem_product.mp hmem with ⟨hab_mem, hc_mem⟩
          rcases Finset.mem_product.mp hab_mem with ⟨ha_mem, _⟩
          refine Finset.mem_image.mpr ⟨a, ha_mem, ?_⟩
          -- After `a = b` and `b = c`, the triple `((a, b), c) = ((a, a), a) = f a`.
          have hab_eq : a = b := h12
          have hac_eq : a = c := h12.trans h23
          subst hab_eq
          subst hac_eq
          rfl
      have hcard := Finset.card_image_of_injective A hf
      rw [himage] at hcard
      exact hcard
    have htotal : ((A ×ˢ A) ×ˢ A).card = A.card ^ 3 := by
      simp [Finset.card_product, pow_succ, Nat.mul_comm]
    -- `filter (¬ P) = univ \ filter P` lets us subtract.
    have hfilter_compl :
        (((A ×ˢ A) ×ˢ A).filter
            (fun abc : (ℕ × ℕ) × ℕ => ¬ (abc.1.1 = abc.1.2 ∧ abc.1.2 = abc.2))).card
          = ((A ×ˢ A) ×ˢ A).card -
              (((A ×ˢ A) ×ˢ A).filter
                (fun abc : (ℕ × ℕ) × ℕ => abc.1.1 = abc.1.2 ∧ abc.1.2 = abc.2)).card := by
      rw [Finset.filter_not]
      exact Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
    rw [hfilter_compl, htotal, hdiag]
  calc
    (sumDiffNontrivialCandidates A).card
        ≤ (((A ×ˢ A) ×ˢ A).filter
            (fun abc : (ℕ × ℕ) × ℕ => ¬ (abc.1.1 = abc.1.2 ∧ abc.1.2 = abc.2))).card := by
          unfold sumDiffNontrivialCandidates
          exact Finset.card_image_le
    _ = A.card ^ 3 - A.card := hdom

/-- The obstruction-cover hypothesis places every point of `{1, ..., N}` into
the union of `A` with the elementary candidate sets. -/
theorem ground_subset_allCandidates {A : Finset ℕ} {N : ℕ}
    (hcover : ObstructionCoveredInInterval A N) :
    ground N ⊆ allCandidates A := by
  intro x hx
  by_cases hxa : x ∈ A
  · exact (mem_allCandidates).mpr <| Or.inl hxa
  · exact (mem_allCandidates).mpr <| Or.inr <| Finset.mem_union.mp (hcover.2 hx hxa)

/-- Coarse cardinality bound for the combined candidate family. -/
theorem card_allCandidates_le (A : Finset ℕ) :
    (allCandidates A).card ≤
      A.card + (midpointCandidates A).card + (sumDiffCandidates A).card := by
  calc
    (allCandidates A).card
      ≤ (A ∪ midpointCandidates A).card + (sumDiffCandidates A).card := by
          simpa [allCandidates] using
            Finset.card_union_le (A ∪ midpointCandidates A) (sumDiffCandidates A)
    _ ≤ (A.card + (midpointCandidates A).card) + (sumDiffCandidates A).card := by
          gcongr
          exact Finset.card_union_le A (midpointCandidates A)
    _ = A.card + (midpointCandidates A).card + (sumDiffCandidates A).card := by omega

/-- The easy cubic counting inequality behind the lower bound
`|A| ≫ N^{1/3}`. -/
theorem cubic_counting_bound_of_obstructionCover {A : Finset ℕ} {N : ℕ}
    (hcover : ObstructionCoveredInInterval A N) :
    N ≤ A.card + A.card ^ 2 + A.card ^ 3 := by
  have hground :
      (ground N).card ≤ (allCandidates A).card :=
    Finset.card_le_card (ground_subset_allCandidates hcover)
  have hmid : (midpointCandidates A).card ≤ A.card ^ 2 :=
    card_midpointCandidates_le A
  have hsum : (sumDiffCandidates A).card ≤ A.card ^ 3 :=
    card_sumDiffCandidates_le A
  calc
    N = (ground N).card := by simp [ground]
    _ ≤ (allCandidates A).card := hground
    _ ≤ A.card + (midpointCandidates A).card + (sumDiffCandidates A).card :=
      card_allCandidates_le A
    _ ≤ A.card + A.card ^ 2 + A.card ^ 3 := by omega

/-! ### Sharper sub-`3|A|^3` bound

We combine the refined obstruction counts above with the standard subset
manipulation to drop the obstruction total below `|A|^3 + |A|^2`. The point is
that the diagonal contributions to both midpoint and sum-difference families
land inside `A` itself and can therefore be absorbed for free. -/

/-- After absorbing diagonal contributions, the candidate family is contained
in `A` together with the refined off-diagonal and nontrivial subfamilies. -/
theorem allCandidates_subset_refined (A : Finset ℕ) :
    allCandidates A ⊆ A ∪ midpointOffDiagCandidates A ∪ sumDiffNontrivialCandidates A := by
  intro x hx
  rcases (mem_allCandidates).mp hx with hA | hmid | hsum
  · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hA
  · have hmid' := midpointCandidates_subset_union A hmid
    rcases Finset.mem_union.mp hmid' with hA | hoff
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hA
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr hoff
  · have hsum' := sumDiffCandidates_subset_union A hsum
    rcases Finset.mem_union.mp hsum' with hA | hntr
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hA
    · exact Finset.mem_union.mpr <| Or.inr hntr

/-- Cardinality bound for the refined candidate family. -/
theorem card_refined_candidates_le (A : Finset ℕ) :
    (A ∪ midpointOffDiagCandidates A ∪ sumDiffNontrivialCandidates A).card ≤
      A.card + (A.card ^ 2 - A.card) + (A.card ^ 3 - A.card) := by
  classical
  calc
    (A ∪ midpointOffDiagCandidates A ∪ sumDiffNontrivialCandidates A).card
        ≤ (A ∪ midpointOffDiagCandidates A).card +
            (sumDiffNontrivialCandidates A).card :=
          Finset.card_union_le _ _
    _ ≤ (A.card + (midpointOffDiagCandidates A).card) +
            (sumDiffNontrivialCandidates A).card := by
          gcongr
          exact Finset.card_union_le A (midpointOffDiagCandidates A)
    _ ≤ (A.card + (A.card ^ 2 - A.card)) + (A.card ^ 3 - A.card) := by
          gcongr
          · exact card_midpointOffDiagCandidates_le A
          · exact card_sumDiffNontrivialCandidates_le A
    _ = A.card + (A.card ^ 2 - A.card) + (A.card ^ 3 - A.card) := rfl

/-- **Obstruction cover implies sharper bound.** Under the obstruction-cover
hypothesis, the interval `{1, ..., N}` is contained in the refined candidate
family, yielding the sharper cubic bound

`N ≤ |A| + (|A|^2 - |A|) + (|A|^3 - |A|)`,

which in particular bounds `N` by `|A|^3 + |A|^2 - |A|` when `|A| ≥ 1`. -/
theorem sharper_cubic_counting_bound_of_obstructionCover {A : Finset ℕ} {N : ℕ}
    (hcover : ObstructionCoveredInInterval A N) :
    N ≤ A.card + (A.card ^ 2 - A.card) + (A.card ^ 3 - A.card) := by
  have hsubset : ground N ⊆
      A ∪ midpointOffDiagCandidates A ∪ sumDiffNontrivialCandidates A :=
    (ground_subset_allCandidates hcover).trans (allCandidates_subset_refined A)
  calc
    N = (ground N).card := by simp [ground]
    _ ≤ (A ∪ midpointOffDiagCandidates A ∪ sumDiffNontrivialCandidates A).card :=
        Finset.card_le_card hsubset
    _ ≤ A.card + (A.card ^ 2 - A.card) + (A.card ^ 3 - A.card) :=
        card_refined_candidates_le A

/-- Compressed sharper bound: `N ≤ |A|^3 + |A|^2 - |A|`. This is strictly
sharper than the crude `|A| + |A|^2 + |A|^3` whenever `|A| ≥ 1`, and is well
below the simple `3|A|^3` bound. -/
theorem sharper_cube_bound_of_obstructionCover {A : Finset ℕ} {N : ℕ}
    (hcover : ObstructionCoveredInInterval A N) :
    N ≤ A.card ^ 3 + A.card ^ 2 - A.card := by
  have h := sharper_cubic_counting_bound_of_obstructionCover hcover
  -- Two cases: `|A| = 0` (then `ground N` is empty, so `N = 0`) or `|A| ≥ 1`.
  by_cases hA : A.card = 0
  · have hAEmpty : A = ∅ := Finset.card_eq_zero.mp hA
    have hN : N = 0 := by
      by_contra hN0
      have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
      have h1ground : (1 : ℕ) ∈ ground N := by simp [ground, hN1]
      have h1notA : (1 : ℕ) ∉ A := by simp [hAEmpty]
      have hmem := hcover.2 h1ground h1notA
      -- Both candidate sets are empty when `A = ∅`.
      have hmid_empty : midpointCandidates A = ∅ := by
        simp [midpointCandidates, hAEmpty]
      have hsum_empty : sumDiffCandidates A = ∅ := by
        simp [sumDiffCandidates, hAEmpty]
      simp [hmid_empty, hsum_empty] at hmem
    simp [hN]
  · have hA1 : 1 ≤ A.card := Nat.one_le_iff_ne_zero.mpr hA
    -- `|A| ≤ |A|^2 ≤ |A|^3`
    have hk2 : A.card ≤ A.card ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul_left A.card hA1
    have hk3 : A.card ^ 2 ≤ A.card ^ 3 := by
      have hk3' : A.card ^ 2 ≤ A.card * (A.card ^ 2) := by
        simpa using Nat.mul_le_mul_right (A.card ^ 2) hA1
      simpa [pow_succ, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using hk3'
    omega

end MaximalSidonSets
