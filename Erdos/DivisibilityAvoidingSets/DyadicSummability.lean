import Erdos.DivisibilityAvoidingSets.ReciprocalCriteria

/-!
# Dyadic reciprocal-summability criteria

This file gives a convenient target for the still-open reciprocal-sum part of
Erdős problem #12.  If the dyadic shell counts of a positive set satisfy

`∑ k, |A ∩ [2^k, 2^(k+1))| / 2^k < ∞`,

then the reciprocal sum over `A` converges.  Thus an eventual proof of the open
part can aim at dyadic shell bounds rather than directly manipulating the
subtype sum in the statement.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- The `k`th dyadic shell `[2^k, 2^(k+1))`. -/
def dyadicShell (k : ℕ) : Set ℕ :=
  Set.Ico (2 ^ k) (2 ^ (k + 1))

/-- The `k`th dyadic shell as a subset of a subtype `A`. -/
def dyadicShellInSubtype (A : Set ℕ) (k : ℕ) : Set A :=
  {a : A | (a : ℕ) ∈ dyadicShell k}

theorem dyadicShell_finite (k : ℕ) :
    (dyadicShell k).Finite := by
  unfold dyadicShell
  exact Set.finite_Ico _ _

theorem dyadicShellInSubtype_finite (A : Set ℕ) (k : ℕ) :
    (dyadicShellInSubtype A k).Finite := by
  unfold dyadicShellInSubtype
  exact Set.Finite.preimage_embedding
    (Function.Embedding.subtype fun n : ℕ => n ∈ A)
    (dyadicShell_finite k)

/-- Every positive element of `A` lies in exactly one dyadic shell. -/
theorem existsUnique_mem_dyadicShellInSubtype {A : Set ℕ}
    (hApos : PositiveSet A) (a : A) :
    ∃! k : ℕ, a ∈ dyadicShellInSubtype A k := by
  refine ⟨Nat.log 2 ((a : A) : ℕ), ?_, ?_⟩
  · unfold dyadicShellInSubtype dyadicShell
    exact ⟨Nat.pow_log_le_self 2 (hApos a.property).ne',
      Nat.lt_pow_succ_log_self Nat.one_lt_two ((a : A) : ℕ)⟩
  · intro k hk
    unfold dyadicShellInSubtype dyadicShell at hk
    have hlog : Nat.log 2 ((a : A) : ℕ) = k :=
      Nat.log_eq_of_pow_le_of_lt_pow hk.1 hk.2
    exact hlog.symm

/-- The reciprocal mass of one dyadic shell is at most its cardinality divided
by the shell's lower endpoint. -/
theorem dyadicShellInSubtype_reciprocal_tsum_le (A : Set ℕ) (k : ℕ) :
    (∑' a : dyadicShellInSubtype A k, (1 : ℝ) / ((a : A) : ℕ)) ≤
      ((dyadicShellInSubtype A k).ncard : ℝ) / ((2 : ℝ) ^ k) := by
  classical
  let S : Set A := dyadicShellInSubtype A k
  have hSfin : S.Finite := dyadicShellInSubtype_finite A k
  haveI : Fintype S := hSfin.fintype
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
  calc
    (∑' a : S, (1 : ℝ) / ((a : A) : ℕ)) =
        ∑ a : S, (1 : ℝ) / (((a : A) : ℕ) : ℝ) := by
      rw [tsum_fintype]
    _ ≤ ∑ _a : S, (1 : ℝ) / ((2 : ℝ) ^ k) := Finset.sum_le_sum fun a _ha => by
        have ha_lower_nat : 2 ^ k ≤ ((a : A) : ℕ) := a.property.1
        have ha_lower : (2 : ℝ) ^ k ≤ (((a : A) : ℕ) : ℝ) := by
          exact_mod_cast ha_lower_nat
        exact one_div_le_one_div_of_le hpow_pos ha_lower
    _ = ((dyadicShellInSubtype A k).ncard : ℝ) / ((2 : ℝ) ^ k) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : Fintype.card S = S.ncard := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      simp [S, hcard, div_eq_mul_inv]

/-- Subtype dyadic criterion for reciprocal summability. -/
theorem reciprocalSummable_of_dyadicShellSubtype_summable {A : Set ℕ}
    (hApos : PositiveSet A)
    (hshell : Summable fun k : ℕ =>
      ((dyadicShellInSubtype A k).ncard : ℝ) / ((2 : ℝ) ^ k)) :
    ReciprocalSummable A := by
  unfold ReciprocalSummable
  have hf_nonneg :
      (0 : A → ℝ) ≤ fun a : A => (1 : ℝ) / (((a : A) : ℕ) : ℝ) := by
    intro a
    exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  rw [summable_partition hf_nonneg (existsUnique_mem_dyadicShellInSubtype hApos)]
  constructor
  · intro k
    exact (dyadicShellInSubtype_finite A k).summable
      (fun a : A => (1 : ℝ) / (((a : A) : ℕ) : ℝ))
  · exact Summable.of_nonneg_of_le
      (fun _ => tsum_nonneg fun a => one_div_nonneg.mpr (Nat.cast_nonneg _))
      (fun k => dyadicShellInSubtype_reciprocal_tsum_le A k)
      hshell

/-- Exact dyadic decomposition of the reciprocal sum.  For a positive set,
reciprocal summability is equivalent to summability of the actual reciprocal
mass in each dyadic shell. -/
theorem reciprocalSummable_iff_dyadicShellSubtype_reciprocal_summable
    {A : Set ℕ} (hApos : PositiveSet A) :
    ReciprocalSummable A ↔
      Summable fun k : ℕ =>
        ∑' a : dyadicShellInSubtype A k,
          (1 : ℝ) / (((a : A) : ℕ) : ℝ) := by
  unfold ReciprocalSummable
  have hf_nonneg :
      (0 : A → ℝ) ≤ fun a : A => (1 : ℝ) / (((a : A) : ℕ) : ℝ) := by
    intro a
    exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  rw [summable_partition hf_nonneg (existsUnique_mem_dyadicShellInSubtype hApos)]
  constructor
  · exact fun h => h.2
  · intro hshell
    constructor
    · intro k
      exact (dyadicShellInSubtype_finite A k).summable
        (fun a : A => (1 : ℝ) / (((a : A) : ℕ) : ℝ))
    · exact hshell

/-- Contrapositive of the exact dyadic decomposition: a positive nonsummable
set has nonsummable actual reciprocal shell masses. -/
theorem not_summable_dyadicShellSubtype_reciprocal_of_not_reciprocalSummable
    {A : Set ℕ} (hApos : PositiveSet A) (hnot : ¬ ReciprocalSummable A) :
    ¬ Summable fun k : ℕ =>
      ∑' a : dyadicShellInSubtype A k,
        (1 : ℝ) / (((a : A) : ℕ) : ℝ) := by
  intro hshell
  exact hnot
    ((reciprocalSummable_iff_dyadicShellSubtype_reciprocal_summable hApos).2 hshell)

/-- The subtype shell cardinality is the ordinary set shell cardinality. -/
theorem dyadicShellInSubtype_ncard_eq (A : Set ℕ) (k : ℕ) :
    (dyadicShellInSubtype A k).ncard = (A ∩ dyadicShell k).ncard := by
  unfold dyadicShellInSubtype
  rw [Set.ncard_subtype]
  congr 1
  ext n
  simp [Set.inter_comm]

/-- Ordinary set-count dyadic criterion for reciprocal summability. -/
theorem reciprocalSummable_of_dyadicShell_summable {A : Set ℕ}
    (hApos : PositiveSet A)
    (hshell : Summable fun k : ℕ =>
      ((A ∩ dyadicShell k).ncard : ℝ) / ((2 : ℝ) ^ k)) :
    ReciprocalSummable A := by
  apply reciprocalSummable_of_dyadicShellSubtype_summable hApos
  convert hshell using 1
  ext k
  rw [dyadicShellInSubtype_ncard_eq]

/-- A comparison-test version of the dyadic criterion. -/
theorem reciprocalSummable_of_dyadicShell_bound {A : Set ℕ} {u : ℕ → ℝ}
    (hApos : PositiveSet A) (hu : Summable u)
    (hbound : ∀ k,
      ((A ∩ dyadicShell k).ncard : ℝ) / ((2 : ℝ) ^ k) ≤ u k) :
    ReciprocalSummable A :=
  reciprocalSummable_of_dyadicShell_summable hApos
    (Summable.of_nonneg_of_le
      (fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)) hbound hu)

/-- Eventual comparison version of the dyadic criterion.  Finitely many
initial shells do not matter, so it is enough to dominate the dyadic shell
masses from some scale onward. -/
theorem reciprocalSummable_of_eventually_dyadicShell_bound
    {A : Set ℕ} {u : ℕ → ℝ}
    (hApos : PositiveSet A) (hu : Summable u) {N : ℕ}
    (hbound : ∀ k, N ≤ k →
      ((A ∩ dyadicShell k).ncard : ℝ) / ((2 : ℝ) ^ k) ≤ u k) :
    ReciprocalSummable A :=
  reciprocalSummable_of_dyadicShell_summable hApos
    (summable_of_nonneg_of_eventually_le_summable
      (fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)) hu hbound)

end DivisibilityAvoidingSets
