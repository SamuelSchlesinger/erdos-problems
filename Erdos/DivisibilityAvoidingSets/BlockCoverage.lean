import Erdos.DivisibilityAvoidingSets.CountLower

/-!
# Endpoint coverage for block constructions

This file keeps the density argument independent of the divisibility tags.
Once a construction supplies finite blocks `F i` below endpoints `E i`, with
each block large compared to the next endpoint, the counting function has a
positive square-root lower density.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- A strictly increasing sequence of natural-number endpoints partitions every
`N ≥ E 0` into an interval `[E i, E (i + 1))`. -/
theorem StrictMono.exists_le_lt_succ_nat {E : ℕ → ℕ} (hE : StrictMono E)
    {N : ℕ} (hN : E 0 ≤ N) :
    ∃ i, E i ≤ N ∧ N < E (i + 1) := by
  have hgrowth : ∀ n : ℕ, E 0 + n ≤ E n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep : E n + 1 ≤ E (n + 1) :=
          Nat.succ_le_of_lt (hE (Nat.lt_succ_self n))
        omega
  have hex : ∃ k : ℕ, N < E k := by
    refine ⟨N + 1, ?_⟩
    have hle : E 0 + (N + 1) ≤ E (N + 1) := hgrowth (N + 1)
    omega
  let k := Nat.find hex
  have hk : N < E k := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    have : N < E 0 := by
      simpa [k, hk0] using hk
    omega
  refine ⟨k - 1, ?_, ?_⟩
  · have hnot : ¬ N < E (k - 1) := Nat.find_min hex (Nat.pred_lt (Nat.ne_of_gt hkpos))
    omega
  · have hk_eq : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hkpos
    simpa [hk_eq] using hk

/-- A finite block contained in `A ∩ {1, ..., N}` gives a cardinality lower
bound for `countUpTo A N`. -/
theorem finset_card_le_countUpTo {A : Set ℕ} {F : Finset ℕ} {N : ℕ}
    (hFsub : (F : Set ℕ) ⊆ A)
    (hFone : ∀ x, x ∈ F → 1 ≤ x)
    (hFle : ∀ x, x ∈ F → x ≤ N) :
    F.card ≤ countUpTo A N := by
  classical
  unfold countUpTo
  refine Finset.card_le_card ?_
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hFone x hx, hFle x hx⟩, hFsub hx⟩

/-- Generic endpoint coverage criterion for positive square-root lower
density.  The block `F i` only needs to lie below `E i`, while its size is
compared with the following endpoint `E (i + 1)`, so the proof covers all
intermediate cutoffs `N`. -/
theorem hasPositiveSqrtLiminf_of_finset_blocks {A : Set ℕ}
    {F : ℕ → Finset ℕ} {E L : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c)
    (hE : StrictMono E)
    (hFsub : ∀ i, (F i : Set ℕ) ⊆ A)
    (hFone : ∀ i x, x ∈ F i → 1 ≤ x)
    (hFle : ∀ i x, x ∈ F i → x ≤ E i)
    (hcard : ∀ i, (F i).card = L i)
    (hcover : ∀ i, c * Real.sqrt (E (i + 1) : ℝ) ≤ (L i : ℝ)) :
    HasPositiveSqrtLiminf A := by
  refine ⟨c, hc, max 1 (E 0), by omega, ?_⟩
  intro N hN
  have hE0N : E 0 ≤ N := (Nat.le_max_right 1 (E 0)).trans hN
  obtain ⟨i, hEiN, hNlt⟩ := StrictMono.exists_le_lt_succ_nat hE hE0N
  have hcount_nat : L i ≤ countUpTo A N := by
    rw [← hcard i]
    exact finset_card_le_countUpTo (hFsub i) (hFone i)
      (fun x hx => (hFle i x hx).trans hEiN)
  have hcount_real : (L i : ℝ) ≤ (countUpTo A N : ℝ) := by
    exact_mod_cast hcount_nat
  have hNpos : 0 < N := by
    have : 1 ≤ N := (Nat.le_max_left 1 (E 0)).trans hN
    omega
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  rw [le_div_iff₀ hsqrt_pos]
  have hNEsucc : (N : ℝ) ≤ (E (i + 1) : ℝ) := by
    exact_mod_cast hNlt.le
  have hsqrt_le : Real.sqrt (N : ℝ) ≤ Real.sqrt (E (i + 1) : ℝ) :=
    Real.sqrt_le_sqrt hNEsucc
  have hmul_le :
      c * Real.sqrt (N : ℝ) ≤ c * Real.sqrt (E (i + 1) : ℝ) :=
    mul_le_mul_of_nonneg_left hsqrt_le hc.le
  exact hmul_le.trans ((hcover i).trans hcount_real)

/-- Arithmetic-progression specialization of
`hasPositiveSqrtLiminf_of_finset_blocks`. -/
theorem hasPositiveSqrtLiminf_of_ap_blocks {A : Set ℕ}
    {r M T L E : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c)
    (hE : StrictMono E)
    (hM : ∀ i, 0 < M i)
    (hsub : ∀ i, apBlock (r i) (M i) (T i) (L i) ⊆ A)
    (hmin : ∀ i, 1 ≤ apMin (r i) (M i) (T i))
    (hmax : ∀ i, apMax (r i) (M i) (T i) (L i) ≤ E i)
    (hcover : ∀ i, c * Real.sqrt (E (i + 1) : ℝ) ≤ (L i : ℝ)) :
    HasPositiveSqrtLiminf A := by
  refine hasPositiveSqrtLiminf_of_finset_blocks (A := A)
    (F := fun i => apBlockFinset (r i) (M i) (T i) (L i))
    (E := E) (L := L) (c := c) hc hE ?_ ?_ ?_ ?_ hcover
  · intro i x hx
    exact hsub i (by simpa using hx)
  · intro i x hx
    have hblock : x ∈ apBlock (r i) (M i) (T i) (L i) := by
      simpa using hx
    exact (hmin i).trans (apMin_le_of_mem_apBlock hblock)
  · intro i x hx
    have hblock : x ∈ apBlock (r i) (M i) (T i) (L i) := by
      simpa using hx
    exact (le_apMax_of_mem_apBlock hblock).trans (hmax i)
  · intro i
    exact apBlockFinset_card (hM i)

/-- A positive avoiding set satisfying the AP endpoint-coverage criterion
answers the first density question affirmatively. -/
theorem erdos12_positiveSqrtDensity_of_ap_blocks {A : Set ℕ}
    {r M T L E : ℕ → ℕ} {c : ℝ}
    (hAinf : A.Infinite) (hApos : PositiveSet A) (hAavoid : AvoidingSet A)
    (hc : 0 < c)
    (hE : StrictMono E)
    (hM : ∀ i, 0 < M i)
    (hsub : ∀ i, apBlock (r i) (M i) (T i) (L i) ⊆ A)
    (hmin : ∀ i, 1 ≤ apMin (r i) (M i) (T i))
    (hmax : ∀ i, apMax (r i) (M i) (T i) (L i) ≤ E i)
    (hcover : ∀ i, c * Real.sqrt (E (i + 1) : ℝ) ≤ (L i : ℝ)) :
    Erdos12PositiveSqrtDensityQuestion :=
  ⟨A, hAinf, hApos, hAavoid,
    hasPositiveSqrtLiminf_of_ap_blocks hc hE hM hsub hmin hmax hcover⟩

end DivisibilityAvoidingSets
