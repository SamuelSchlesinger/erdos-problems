import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Erdos.DivisibilityAvoidingSets.TailResidues
import Erdos.DivisibilityAvoidingSets.BlockTemplate

/-!
# Reciprocal-sum criteria for Erdős problem #12

The still-open part of problem #12 asks whether every positive avoiding set has
convergent reciprocal sum.  This file records reusable analytic reductions:
translate the subtype sum in the statement into an ordinary indicator function
on `ℕ`, compare that indicator to a nonnegative summable majorant, and bound
finite-window reciprocal sums by `cardinality / minimum`.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- The reciprocal function restricted to `A`, as an ordinary function on
natural numbers. -/
noncomputable def reciprocalIndicator (A : Set ℕ) : ℕ → ℝ :=
  A.indicator fun n : ℕ => (1 : ℝ) / (n : ℝ)

/-- The subtype formulation in the statement is equivalent to summability of
the ordinary indicator on `ℕ`. -/
theorem reciprocalSummable_iff_indicator (A : Set ℕ) :
    ReciprocalSummable A ↔ Summable (reciprocalIndicator A) := by
  unfold ReciprocalSummable reciprocalIndicator
  simpa [Function.comp_def] using
    (summable_subtype_iff_indicator
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) (s := A))

theorem reciprocalIndicator_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ reciprocalIndicator A n := by
  unfold reciprocalIndicator
  by_cases hn : n ∈ A
  · simp [Set.indicator_of_mem hn]
  · simp [Set.indicator_of_notMem hn]

theorem reciprocalIndicator_mono {A B : Set ℕ} (hBA : B ⊆ A) (n : ℕ) :
    reciprocalIndicator B n ≤ reciprocalIndicator A n := by
  unfold reciprocalIndicator
  by_cases hnB : n ∈ B
  · have hnA : n ∈ A := hBA hnB
    simp [Set.indicator_of_mem hnB, Set.indicator_of_mem hnA]
  · by_cases hnA : n ∈ A
    · simp [Set.indicator_of_notMem hnB, Set.indicator_of_mem hnA]
    · simp [Set.indicator_of_notMem hnB, Set.indicator_of_notMem hnA]

/-- Reciprocal summability passes to subsets. -/
theorem ReciprocalSummable.mono {A B : Set ℕ}
    (hA : ReciprocalSummable A) (hBA : B ⊆ A) :
    ReciprocalSummable B := by
  rw [reciprocalSummable_iff_indicator] at hA ⊢
  exact Summable.of_nonneg_of_le
    (reciprocalIndicator_nonneg B)
    (reciprocalIndicator_mono hBA)
    hA

/-- Every finite reciprocal sub-sum of a reciprocally summable set is bounded
by the full reciprocal-indicator tsum. -/
theorem finset_sum_reciprocal_le_tsum_indicator_of_subset
    {A : Set ℕ} (hA : ReciprocalSummable A) {F : Finset ℕ}
    (hF : ∀ n ∈ F, n ∈ A) :
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) ≤
      ∑' n : ℕ, reciprocalIndicator A n := by
  have hsumm : Summable (reciprocalIndicator A) :=
    (reciprocalSummable_iff_indicator A).mp hA
  calc
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) =
        ∑ n ∈ F, reciprocalIndicator A n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      simp [reciprocalIndicator, Set.indicator_of_mem (hF n hn)]
    _ ≤ ∑' n : ℕ, reciprocalIndicator A n := by
      exact Summable.sum_le_tsum
        (f := reciprocalIndicator A) F
        (fun n _hn => reciprocalIndicator_nonneg A n) hsumm

/-- The empty set has convergent reciprocal sum. -/
theorem reciprocalSummable_empty : ReciprocalSummable (∅ : Set ℕ) := by
  rw [reciprocalSummable_iff_indicator]
  simp [reciprocalIndicator]

/-- Every finite set has convergent reciprocal sum. -/
theorem reciprocalSummable_of_finite {A : Set ℕ} (hA : A.Finite) :
    ReciprocalSummable A := by
  unfold ReciprocalSummable
  haveI : Fintype A := hA.fintype
  exact (hasSum_fintype fun n : A => (1 : ℝ) / (n : ℕ)).summable

/-- A nonsummable set is necessarily infinite. -/
theorem infinite_of_not_reciprocalSummable {A : Set ℕ}
    (hnot : ¬ ReciprocalSummable A) :
    A.Infinite := by
  intro hfin
  exact hnot (reciprocalSummable_of_finite hfin)

/-- Any set bounded above in `ℕ` has convergent reciprocal sum. -/
theorem reciprocalSummable_of_subset_Iio {A : Set ℕ} {N : ℕ}
    (hA : A ⊆ Set.Iio N) :
    ReciprocalSummable A :=
  reciprocalSummable_of_finite (Set.finite_Iio N |>.subset hA)

/-- Reciprocal summability is stable under finite unions. -/
theorem ReciprocalSummable.union {A B : Set ℕ}
    (hA : ReciprocalSummable A) (hB : ReciprocalSummable B) :
    ReciprocalSummable (A ∪ B) := by
  rw [reciprocalSummable_iff_indicator] at hA hB ⊢
  refine Summable.of_nonneg_of_le
    (reciprocalIndicator_nonneg (A ∪ B)) ?_ (hA.add hB)
  intro n
  have hrec_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  unfold reciprocalIndicator
  by_cases hnA : n ∈ A
  · by_cases hnB : n ∈ B
    · have hnU : n ∈ A ∪ B := Or.inl hnA
      simp [Set.indicator_of_mem hnA, Set.indicator_of_mem hnB,
        Set.indicator_of_mem hnU]
    · have hnU : n ∈ A ∪ B := Or.inl hnA
      simp [Set.indicator_of_mem hnA, Set.indicator_of_notMem hnB,
        Set.indicator_of_mem hnU]
  · by_cases hnB : n ∈ B
    · have hnU : n ∈ A ∪ B := Or.inr hnB
      simp [Set.indicator_of_notMem hnA, Set.indicator_of_mem hnB,
        Set.indicator_of_mem hnU]
    · have hnU : n ∉ A ∪ B := by
        intro hn
        exact hn.elim hnA hnB
      simp [Set.indicator_of_notMem hnA, Set.indicator_of_notMem hnB,
        Set.indicator_of_notMem hnU]

/-- Removing a finite set from a nonsummable set leaves a nonsummable set. -/
theorem not_reciprocalSummable_diff_of_finite {A B : Set ℕ}
    (hnot : ¬ ReciprocalSummable A) (hB : B.Finite) :
    ¬ ReciprocalSummable (A \ B) := by
  intro hdiff
  have hBsum : ReciprocalSummable B := reciprocalSummable_of_finite hB
  have hunion : ReciprocalSummable ((A \ B) ∪ B) := hdiff.union hBsum
  have hAsub : A ⊆ (A \ B) ∪ B := by
    intro n hnA
    by_cases hnB : n ∈ B
    · exact Or.inr hnB
    · exact Or.inl ⟨hnA, hnB⟩
  exact hnot (hunion.mono hAsub)

/-- Removing a reciprocally summable set from a nonsummable set leaves a
nonsummable set. -/
theorem not_reciprocalSummable_diff_of_reciprocalSummable {A B : Set ℕ}
    (hnot : ¬ ReciprocalSummable A) (hB : ReciprocalSummable B) :
    ¬ ReciprocalSummable (A \ B) := by
  intro hdiff
  have hunion : ReciprocalSummable ((A \ B) ∪ B) := hdiff.union hB
  have hAsub : A ⊆ (A \ B) ∪ B := by
    intro n hnA
    by_cases hnB : n ∈ B
    · exact Or.inr hnB
    · exact Or.inl ⟨hnA, hnB⟩
  exact hnot (hunion.mono hAsub)

/-- Removing a finite finset from a nonsummable set leaves a nonsummable set. -/
theorem not_reciprocalSummable_diff_finset {A : Set ℕ} {F : Finset ℕ}
    (hnot : ¬ ReciprocalSummable A) :
    ¬ ReciprocalSummable (A \ (F : Set ℕ)) :=
  not_reciprocalSummable_diff_of_finite hnot F.finite_toSet

/-- Every tail of a nonsummable set is nonsummable. -/
theorem not_reciprocalSummable_inter_Ici {A : Set ℕ} (hnot : ¬ ReciprocalSummable A)
    (N : ℕ) :
    ¬ ReciprocalSummable (A ∩ Set.Ici N) := by
  intro htail
  have hsmall : ReciprocalSummable (A ∩ Set.Iio N) :=
    reciprocalSummable_of_subset_Iio fun n hn => hn.2
  have hunion : ReciprocalSummable ((A ∩ Set.Ici N) ∪ (A ∩ Set.Iio N)) :=
    htail.union hsmall
  have hAsub : A ⊆ (A ∩ Set.Ici N) ∪ (A ∩ Set.Iio N) := by
    intro n hnA
    by_cases hN : N ≤ n
    · exact Or.inl ⟨hnA, hN⟩
    · exact Or.inr ⟨hnA, Nat.lt_of_not_ge hN⟩
  exact hnot (hunion.mono hAsub)

/-- A reciprocally nonsummable set has elements arbitrarily far out. -/
theorem exists_mem_ge_of_not_reciprocalSummable {A : Set ℕ}
    (hnot : ¬ ReciprocalSummable A) (N : ℕ) :
    ∃ n, n ∈ A ∧ N ≤ n := by
  by_contra hnone
  have hsub : A ⊆ Set.Iio N := by
    intro n hn
    by_contra hnlt
    exact hnone ⟨n, hn, Nat.le_of_not_gt hnlt⟩
  exact hnot (reciprocalSummable_of_subset_Iio hsub)

/-- Reciprocal summability is stable under unions indexed by a finset. -/
theorem ReciprocalSummable.biUnion_finset {ι : Type*} {I : Finset ι}
    {B : ι → Set ℕ} (hB : ∀ i ∈ I, ReciprocalSummable (B i)) :
    ReciprocalSummable (⋃ i ∈ I, B i) := by
  classical
  induction I using Finset.induction with
  | empty =>
      simpa using reciprocalSummable_empty
  | insert i I hi ih =>
      have hiB : ReciprocalSummable (B i) :=
        hB i (Finset.mem_insert_self i I)
      have hIB : ReciprocalSummable (⋃ j ∈ I, B j) :=
        ih fun j hj => hB j (Finset.mem_insert_of_mem hj)
      simpa [Set.biUnion_insert] using hiB.union hIB

/-- Finite-cover pigeonhole for nonsummability: if a nonsummable set is covered
by finitely many pieces, then one intersection with a covering piece is still
nonsummable. -/
theorem exists_not_reciprocalSummable_inter_of_finite_cover
    {ι : Type*} {I : Finset ι} {A : Set ℕ} {B : ι → Set ℕ}
    (hnot : ¬ ReciprocalSummable A)
    (hcover : A ⊆ ⋃ i ∈ I, B i) :
    ∃ i ∈ I, ¬ ReciprocalSummable (A ∩ B i) := by
  by_contra hnone
  have hpieces : ∀ i ∈ I, ReciprocalSummable (A ∩ B i) := by
    intro i hi
    by_contra hbad
    exact hnone ⟨i, hi, hbad⟩
  have hunion : ReciprocalSummable (⋃ i ∈ I, A ∩ B i) :=
    ReciprocalSummable.biUnion_finset hpieces
  have hAsub : A ⊆ ⋃ i ∈ I, A ∩ B i := by
    intro n hnA
    have hnCover : n ∈ ⋃ i ∈ I, B i := hcover hnA
    simp only [Set.mem_iUnion, Set.mem_inter_iff] at hnCover ⊢
    rcases hnCover with ⟨i, hiI, hnBi⟩
    exact ⟨i, hiI, hnA, hnBi⟩
  exact hnot (hunion.mono hAsub)

/-- Weighted finite-cover inequality.  If every element of a finite set `F`
lies in at least one of finitely many pieces `B i`, then the total weight of
`F` is at most the sum of the weights of its intersections with those pieces.
This is the finite-shell pigeonhole input for the common-factor branch. -/
theorem finset_sum_le_sum_filter_of_cover {α ι : Type*}
    {F : Finset α} {I : Finset ι} {B : ι → Set α} {w : α → ℝ}
    [∀ i, DecidablePred fun x => x ∈ B i]
    (hw : ∀ x, 0 ≤ w x)
    (hcover : ∀ x ∈ F, ∃ i ∈ I, x ∈ B i) :
    (∑ x ∈ F, w x) ≤
      ∑ i ∈ I, ∑ x ∈ F.filter (fun x => x ∈ B i), w x := by
  classical
  calc
    (∑ x ∈ F, w x) ≤
        ∑ x ∈ F, ∑ i ∈ I, if x ∈ B i then w x else 0 := by
      refine Finset.sum_le_sum fun x hxF => ?_
      rcases hcover x hxF with ⟨i, hiI, hxi⟩
      have hrest_nonneg :
          0 ≤ ∑ j ∈ I.erase i, if x ∈ B j then w x else 0 := by
        exact Finset.sum_nonneg fun j _hj => by
          by_cases hxj : x ∈ B j
          · simp [hxj, hw x]
          · simp [hxj]
      calc
        w x = (if x ∈ B i then w x else 0) := by simp [hxi]
        _ ≤ (if x ∈ B i then w x else 0) +
            ∑ j ∈ I.erase i, if x ∈ B j then w x else 0 := by
          linarith
        _ = ∑ j ∈ I, if x ∈ B j then w x else 0 := by
          simpa using
            (Finset.add_sum_erase I (fun j => if x ∈ B j then w x else 0) hiI)
    _ = ∑ i ∈ I, ∑ x ∈ F, if x ∈ B i then w x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ∑ x ∈ F.filter (fun x => x ∈ B i), w x := by
      refine Finset.sum_congr rfl fun i _hi => ?_
      simp [Finset.sum_filter]

/-- Quantitative pigeonhole form of `finset_sum_le_sum_filter_of_cover`: if
the total weight of `F` is larger than `|I| * c`, then one covering piece has
weight larger than `c`. -/
theorem exists_lt_sum_filter_of_card_mul_lt_sum_of_cover {α ι : Type*}
    {F : Finset α} {I : Finset ι} {B : ι → Set α} {w : α → ℝ}
    [∀ i, DecidablePred fun x => x ∈ B i]
    (hw : ∀ x, 0 ≤ w x)
    (hcover : ∀ x ∈ F, ∃ i ∈ I, x ∈ B i)
    {c : ℝ} (hbig : (I.card : ℝ) * c < ∑ x ∈ F, w x) :
    ∃ i ∈ I, c < ∑ x ∈ F.filter (fun x => x ∈ B i), w x := by
  classical
  by_contra hnone
  have hpiece_le :
      ∀ i ∈ I, (∑ x ∈ F.filter (fun x => x ∈ B i), w x) ≤ c := by
    intro i hi
    exact not_lt.mp fun hlt => hnone ⟨i, hi, hlt⟩
  have hsum_piece_le :
      (∑ i ∈ I, ∑ x ∈ F.filter (fun x => x ∈ B i), w x) ≤
        ∑ i ∈ I, c :=
    Finset.sum_le_sum fun i hi => hpiece_le i hi
  have hcover_le :
      (∑ x ∈ F, w x) ≤
        ∑ i ∈ I, ∑ x ∈ F.filter (fun x => x ∈ B i), w x :=
    finset_sum_le_sum_filter_of_cover hw hcover
  have hconst : (∑ _i ∈ I, c) = (I.card : ℝ) * c := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Reciprocal-weight specialization of the finite-cover pigeonhole lemma. -/
theorem exists_lt_sum_reciprocal_filter_of_card_mul_lt_sum_of_cover
    {ι : Type*} {F : Finset ℕ} {I : Finset ι} {B : ι → Set ℕ}
    [∀ i, DecidablePred fun x => x ∈ B i]
    (hcover : ∀ x ∈ F, ∃ i ∈ I, x ∈ B i)
    {c : ℝ} (hbig : (I.card : ℝ) * c < ∑ x ∈ F, (1 : ℝ) / (x : ℝ)) :
    ∃ i ∈ I, c < ∑ x ∈ F.filter (fun x => x ∈ B i), (1 : ℝ) / (x : ℝ) :=
  exists_lt_sum_filter_of_card_mul_lt_sum_of_cover
    (w := fun x : ℕ => (1 : ℝ) / (x : ℝ))
    (fun x => one_div_nonneg.mpr (Nat.cast_nonneg x)) hcover hbig

/-- If a nonnegative sequence is eventually bounded by a summable sequence,
then it is summable.  This is the analytic bookkeeping behind the heavy-shell
extraction used in the global charging argument. -/
theorem summable_of_nonneg_of_eventually_le_summable
    {f u : ℕ → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n)
    (hu : Summable u) {N : ℕ} (hbound : ∀ n, N ≤ n → f n ≤ u n) :
    Summable f := by
  let g : ℕ → ℝ := fun n => if n < N then f n else u n
  have hg : Summable g := by
    refine hu.congr_atTop ?_
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    simp [g, not_lt.mpr hn]
  refine Summable.of_nonneg_of_le hf_nonneg ?_ hg
  intro n
  by_cases hn : n < N
  · simp [g, hn]
  · have hN : N ≤ n := not_lt.mp hn
    simp [g, hn, hbound n hN]

/-- A nonnegative nonsummable sequence beats every summable threshold
arbitrarily far out. -/
theorem exists_ge_lt_of_not_summable_of_summable
    {f u : ℕ → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n)
    (hnot : ¬ Summable f) (hu : Summable u) (N : ℕ) :
    ∃ n, N ≤ n ∧ u n < f n := by
  by_contra hnone
  have hbound : ∀ n, N ≤ n → f n ≤ u n := by
    intro n hn
    by_contra hlt
    exact hnone ⟨n, hn, lt_of_not_ge hlt⟩
  exact hnot (summable_of_nonneg_of_eventually_le_summable hf_nonneg hu hbound)

/-- A nonnegative nonsummable sequence has arbitrarily large mass on finite
tail intervals.  This is the cumulative analogue of the heavy-shell extraction:
even if no individual term is large, enough tail terms eventually beat any
fixed nonnegative threshold. -/
theorem exists_lt_sum_Ico_of_not_summable_nonneg
    {f : ℕ → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n)
    (hnot : ¬ Summable f) {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    ∃ n, N < n ∧ C < ∑ i ∈ Finset.Ico N n, f i := by
  have hTendsto :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf_nonneg).mp hnot
  let S₀ : ℝ := ∑ i ∈ Finset.range N, f i
  rcases Filter.exists_lt_of_tendsto_atTop hTendsto 0 (C + S₀) with
    ⟨n, _hn0, hnlarge⟩
  have hNn : N < n := by
    by_contra hnotlt
    have hnN : n ≤ N := not_lt.mp hnotlt
    have hsum_le :
        (∑ i ∈ Finset.range n, f i) ≤ S₀ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hnN) ?_
      intro i _hiN _hin
      exact hf_nonneg i
    linarith
  have hsplit :
      S₀ + ∑ i ∈ Finset.Ico N n, f i =
        ∑ i ∈ Finset.range n, f i := by
    exact Finset.sum_range_add_sum_Ico f hNn.le
  refine ⟨n, hNn, ?_⟩
  linarith

/-- A summable pointwise majorant for the reciprocal indicator proves
`ReciprocalSummable`. -/
theorem reciprocalSummable_of_indicator_le {A : Set ℕ} {f : ℕ → ℝ}
    (hf : Summable f)
    (hbound : ∀ n, reciprocalIndicator A n ≤ f n) :
    ReciprocalSummable A := by
  rw [reciprocalSummable_iff_indicator]
  exact Summable.of_nonneg_of_le (reciprocalIndicator_nonneg A) hbound hf

/-- A convenient on-`A` version of the majorant criterion. -/
theorem reciprocalSummable_of_pointwise_bound {A : Set ℕ} {f : ℕ → ℝ}
    (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f)
    (hbound : ∀ ⦃n : ℕ⦄, n ∈ A → (1 : ℝ) / (n : ℝ) ≤ f n) :
    ReciprocalSummable A := by
  exact reciprocalSummable_of_indicator_le hf fun n => by
    unfold reciprocalIndicator
    by_cases hn : n ∈ A
    · simpa [Set.indicator_of_mem hn] using hbound hn
    · simpa [Set.indicator_of_notMem hn] using hf_nonneg n

/-- If every element of a finite set is at least `m`, then its reciprocal mass
is at most `|F| / m`. -/
theorem finset_sum_reciprocal_le_card_div_min {F : Finset ℕ} {m : ℕ}
    (hm : 0 < m) (hmin : ∀ n, n ∈ F → m ≤ n) :
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) ≤ (F.card : ℝ) / (m : ℝ) := by
  calc
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) ≤ ∑ n ∈ F, (1 : ℝ) / (m : ℝ) := by
      exact Finset.sum_le_sum fun n hn =>
        one_div_le_one_div_of_le (Nat.cast_pos.mpr hm)
          (by exact_mod_cast hmin n hn)
    _ = (F.card : ℝ) / (m : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_num
      ring

/-- Arithmetic-progression block specialization: the reciprocal mass of a
finite AP block is bounded by `length / first element`. -/
theorem apBlockFinset_sum_reciprocal_le_length_div_min {r M T L : ℕ}
    (hM : 0 < M) (hmin : 0 < apMin r M T) :
    (∑ n ∈ apBlockFinset r M T L, (1 : ℝ) / (n : ℝ)) ≤
      (L : ℝ) / (apMin r M T : ℝ) := by
  have h := finset_sum_reciprocal_le_card_div_min
    (F := apBlockFinset r M T L) (m := apMin r M T) hmin
    (fun n hn => apMin_le_of_mem_apBlock (by simpa using hn))
  rwa [apBlockFinset_card hM] at h

end DivisibilityAvoidingSets
