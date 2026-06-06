import Erdos.DivisibilityAvoidingSets.DyadicSummability
import Erdos.DivisibilityAvoidingSets.ResiduePacking

/-!
# Dyadic packing consequences of the residue bounds

This file bridges the local LCM-window packing theorem to the dyadic
summability criterion.  Once a finite set of earlier moduli lies below the
start of a dyadic shell, every shell element is in every selected tail, so the
shell can be covered by consecutive LCM windows and bounded by the product of
the local half-modulus losses.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- The finite set `A ∩ [2^k, 2^(k+1))`. -/
noncomputable def dyadicShellFinset (A : Set ℕ) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter fun n => n ∈ A

/-- Reciprocal mass of the finite dyadic shell `A ∩ [2^k, 2^(k+1))`. -/
noncomputable def dyadicShellReciprocalMass (A : Set ℕ) (k : ℕ) : ℝ :=
  ∑ n ∈ dyadicShellFinset A k, (1 : ℝ) / (n : ℝ)

/-- Reciprocal contribution of the elements of a finite core `J` which happen
to lie in a dyadic shell. -/
noncomputable def dyadicShellCoreMass (A : Set ℕ) (k : ℕ) (J : Finset ℕ) : ℝ :=
  ∑ n ∈ (dyadicShellFinset A k).filter (fun n => n ∈ J), (1 : ℝ) / (n : ℝ)

/-- Reciprocal contribution in a shell from elements outside `J` which are
not coprime to a fixed core element `a`. -/
noncomputable def dyadicShellNoncoreNoncoprimeMass
    (A : Set ℕ) (k : ℕ) (J : Finset ℕ) (a : ℕ) : ℝ :=
  ∑ n ∈ ((dyadicShellFinset A k).filter (fun n => n ∉ J)).filter
      (fun n => ¬ Nat.Coprime n a),
    (1 : ℝ) / (n : ℝ)

theorem dyadicShellReciprocalMass_nonneg (A : Set ℕ) (k : ℕ) :
    0 ≤ dyadicShellReciprocalMass A k := by
  unfold dyadicShellReciprocalMass
  exact Finset.sum_nonneg fun n _ => one_div_nonneg.mpr (Nat.cast_nonneg n)

theorem dyadicShellCoreMass_nonneg (A : Set ℕ) (k : ℕ) (J : Finset ℕ) :
    0 ≤ dyadicShellCoreMass A k J := by
  unfold dyadicShellCoreMass
  exact Finset.sum_nonneg fun n _ => one_div_nonneg.mpr (Nat.cast_nonneg n)

theorem mem_dyadicShellFinset {A : Set ℕ} {k n : ℕ} :
    n ∈ dyadicShellFinset A k ↔ n ∈ A ∧ n ∈ dyadicShell k := by
  classical
  unfold dyadicShellFinset dyadicShell
  simp [Set.mem_Ico, and_comm]

/-- Every positive element of `A` above `2 ^ N` lies in a dyadic shell whose
index is at least `N`. -/
theorem exists_ge_mem_dyadicShellFinset_of_mem_Ici_pow
    {A : Set ℕ} (hApos : PositiveSet A) {N x : ℕ}
    (hxA : x ∈ A) (hxN : 2 ^ N ≤ x) :
    ∃ k, N ≤ k ∧ x ∈ dyadicShellFinset A k := by
  let k := Nat.log 2 x
  have hxpos : 0 < x := hApos hxA
  have hlower : 2 ^ k ≤ x := Nat.pow_log_le_self 2 hxpos.ne'
  have hupper : x < 2 ^ (k + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two x
  have hNk : N ≤ k := by
    by_contra hnot
    have hklt : k < N := Nat.lt_of_not_ge hnot
    have hksucc : k + 1 ≤ N := Nat.succ_le_of_lt hklt
    have hpowle : 2 ^ (k + 1) ≤ 2 ^ N :=
      Nat.pow_le_pow_right (by norm_num) hksucc
    have hxlt : x < x := hupper.trans_le (hpowle.trans hxN)
    exact (lt_irrefl x hxlt).elim
  exact ⟨k, hNk, mem_dyadicShellFinset.mpr ⟨hxA, hlower, hupper⟩⟩

theorem dyadicShellFinset_card_eq_ncard (A : Set ℕ) (k : ℕ) :
    (dyadicShellFinset A k).card = (A ∩ dyadicShell k).ncard := by
  classical
  have hfin : (A ∩ dyadicShell k).Finite := by
    exact (dyadicShell_finite k).subset fun _ hn => hn.2
  rw [Set.ncard_eq_toFinset_card (A ∩ dyadicShell k) hfin]
  congr 1
  ext n
  simp [dyadicShellFinset, dyadicShell, Set.mem_Ico, and_comm]

/-- The subtype shell reciprocal mass agrees with the explicit finite shell
sum. -/
theorem dyadicShellInSubtype_reciprocal_tsum_eq_finset_sum (A : Set ℕ) (k : ℕ) :
    (∑' a : dyadicShellInSubtype A k,
        (1 : ℝ) / (((a : A) : ℕ) : ℝ)) =
      ∑ n ∈ dyadicShellFinset A k, (1 : ℝ) / (n : ℝ) := by
  classical
  let e : dyadicShellInSubtype A k ≃ {n : ℕ // n ∈ dyadicShellFinset A k} :=
    { toFun := fun a => ⟨((a : A) : ℕ), by
        exact mem_dyadicShellFinset.mpr ⟨(a : A).property, a.property⟩⟩
      invFun := fun n => ⟨⟨n, (mem_dyadicShellFinset.mp n.property).1⟩,
        (mem_dyadicShellFinset.mp n.property).2⟩
      left_inv := fun a => by
        ext
        rfl
      right_inv := fun n => by
        ext
        rfl }
  have hfinite := dyadicShellInSubtype_finite A k
  haveI : Fintype (dyadicShellInSubtype A k) := hfinite.fintype
  calc
    (∑' a : dyadicShellInSubtype A k,
        (1 : ℝ) / (((a : A) : ℕ) : ℝ)) =
        ∑ a : dyadicShellInSubtype A k,
          (1 : ℝ) / (((a : A) : ℕ) : ℝ) := by
      rw [tsum_fintype]
    _ = ∑ n : {n : ℕ // n ∈ dyadicShellFinset A k},
          (1 : ℝ) / (n : ℝ) := by
      exact Fintype.sum_equiv e
        (fun a : dyadicShellInSubtype A k =>
          (1 : ℝ) / (((a : A) : ℕ) : ℝ))
        (fun n : {n : ℕ // n ∈ dyadicShellFinset A k} =>
          (1 : ℝ) / (n : ℝ))
        (by intro a; rfl)
    _ = ∑ n ∈ dyadicShellFinset A k, (1 : ℝ) / (n : ℝ) := by
      symm
      exact Finset.sum_subtype (s := dyadicShellFinset A k)
        (p := fun n : ℕ => n ∈ dyadicShellFinset A k)
        (fun n => by simp) (fun n => (1 : ℝ) / (n : ℝ))

/-- Exact dyadic decomposition in the explicit finite-shell language used by
the packing lemmas. -/
theorem reciprocalSummable_iff_dyadicShellFinset_reciprocal_summable
    {A : Set ℕ} (hApos : PositiveSet A) :
    ReciprocalSummable A ↔
      Summable fun k : ℕ =>
        ∑ n ∈ dyadicShellFinset A k, (1 : ℝ) / (n : ℝ) := by
  rw [reciprocalSummable_iff_dyadicShellSubtype_reciprocal_summable hApos]
  simp only [dyadicShellInSubtype_reciprocal_tsum_eq_finset_sum]

/-- Exact dyadic decomposition in the named shell-mass notation. -/
theorem reciprocalSummable_iff_dyadicShellReciprocalMass_summable
    {A : Set ℕ} (hApos : PositiveSet A) :
    ReciprocalSummable A ↔ Summable (dyadicShellReciprocalMass A) := by
  rw [reciprocalSummable_iff_dyadicShellFinset_reciprocal_summable hApos]
  rfl

theorem dyadicShellCoreMass_le_core_shell_mass
    (A : Set ℕ) (k : ℕ) (J : Finset ℕ) :
    dyadicShellCoreMass A k J ≤ dyadicShellReciprocalMass (J : Set ℕ) k := by
  unfold dyadicShellCoreMass dyadicShellReciprocalMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
  · intro x hx
    have hxFilter := Finset.mem_filter.mp hx
    have hxShellA := mem_dyadicShellFinset.mp hxFilter.1
    exact mem_dyadicShellFinset.mpr ⟨hxFilter.2, hxShellA.2⟩
  · intro x _hxTarget _hxNotSource
    exact one_div_nonneg.mpr (Nat.cast_nonneg x)

/-- A fixed positive finite core contributes summably many reciprocal weights
across all dyadic shells. -/
theorem summable_dyadicShellCoreMass_of_core_positive
    (A : Set ℕ) {J : Finset ℕ} (hJpos : ∀ a ∈ J, 0 < a) :
    Summable fun k => dyadicShellCoreMass A k J := by
  have hpos : PositiveSet (J : Set ℕ) := by
    intro n hn
    exact hJpos n hn
  have hrec : ReciprocalSummable (J : Set ℕ) :=
    reciprocalSummable_of_finite J.finite_toSet
  have hshell : Summable (dyadicShellReciprocalMass (J : Set ℕ)) :=
    (reciprocalSummable_iff_dyadicShellReciprocalMass_summable hpos).1 hrec
  exact Summable.of_nonneg_of_le
    (fun k => dyadicShellCoreMass_nonneg A k J)
    (fun k => dyadicShellCoreMass_le_core_shell_mass A k J)
    hshell

/-- A positive nonsummable set has nonsummable finite-shell reciprocal
masses. -/
theorem not_summable_dyadicShellFinset_reciprocal_of_not_reciprocalSummable
    {A : Set ℕ} (hApos : PositiveSet A) (hnot : ¬ ReciprocalSummable A) :
    ¬ Summable fun k : ℕ =>
      ∑ n ∈ dyadicShellFinset A k, (1 : ℝ) / (n : ℝ) := by
  intro hshell
  exact hnot
    ((reciprocalSummable_iff_dyadicShellFinset_reciprocal_summable hApos).2 hshell)

/-- A positive nonsummable set has nonsummable named shell masses. -/
theorem not_summable_dyadicShellReciprocalMass_of_not_reciprocalSummable
    {A : Set ℕ} (hApos : PositiveSet A) (hnot : ¬ ReciprocalSummable A) :
    ¬ Summable (dyadicShellReciprocalMass A) := by
  intro hshell
  exact hnot
    ((reciprocalSummable_iff_dyadicShellReciprocalMass_summable hApos).2 hshell)

/-- Heavy-shell extraction: if `A` is positive and nonsummable, its dyadic
reciprocal shell mass beats every summable threshold arbitrarily far out. -/
theorem exists_ge_lt_dyadicShellReciprocalMass_of_not_reciprocalSummable
    {A : Set ℕ} (hApos : PositiveSet A) (hnot : ¬ ReciprocalSummable A)
    {u : ℕ → ℝ} (hu : Summable u) (N : ℕ) :
    ∃ k, N ≤ k ∧ u k < dyadicShellReciprocalMass A k :=
  exists_ge_lt_of_not_summable_of_summable
    (dyadicShellReciprocalMass_nonneg A)
    (not_summable_dyadicShellReciprocalMass_of_not_reciprocalSummable hApos hnot)
    hu N

/-- If a positive set receives nonsummably much reciprocal mass in its dyadic
shells, then its reciprocal sum diverges.  This is the fixed-layer trigger for
the common-factor descent branch. -/
theorem not_reciprocalSummable_of_not_summable_shell_lower_bound
    {B : Set ℕ} (hBpos : PositiveSet B)
    {c : ℕ → ℝ} (hc_nonneg : ∀ k, 0 ≤ c k) (hcnot : ¬ Summable c)
    (hlower : ∀ k, c k ≤ dyadicShellReciprocalMass B k) :
    ¬ ReciprocalSummable B := by
  intro hBsum
  have hshell : Summable (dyadicShellReciprocalMass B) :=
    (reciprocalSummable_iff_dyadicShellReciprocalMass_summable hBpos).1 hBsum
  have hc : Summable c :=
    Summable.of_nonneg_of_le hc_nonneg hlower hshell
  exact hcnot hc

/-- Dyadic-shell packing bound from any finite family of earlier selected
moduli.  The future global combinatorial theorem should choose `J` so that the
right-hand side has summable mass after division by `2^k`. -/
theorem AvoidingSet.dyadicShellFinset_card_le_lcmPacking
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A)
    {J : Finset ι} {m : ι → ℕ} {k : ℕ}
    (hmA : ∀ i ∈ J, m i ∈ A)
    (hmpos : ∀ i ∈ J, 0 < m i)
    (hmlt : ∀ i ∈ J, m i < 2 ^ k) :
    (dyadicShellFinset A k).card ≤
      (∏ i ∈ J, (m i / 2 + 1)) * ((2 ^ k) / J.lcm m + 1) := by
  classical
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [pow_succ, Nat.mul_comm, two_mul]
  refine hA.finset_card_le_multi_tail_moduli_of_subset_Ico_lcm_cover
    (J := J) (m := m) (F := dyadicShellFinset A k) (X := 2 ^ k) (H := 2 ^ k)
    hmA hmpos ?_ ?_
  · intro i hi n hn
    have hnmem := mem_dyadicShellFinset.mp hn
    exact ⟨hnmem.1, by
      have hn_lower : 2 ^ k ≤ n := hnmem.2.1
      exact (hmlt i hi).trans_le hn_lower⟩
  · intro n hn
    have hnmem := mem_dyadicShellFinset.mp hn
    simpa [dyadicShell, hpow] using hnmem.2

/-- The same dyadic-shell packing bound in the `ncard` form used by the
summability criterion. -/
theorem AvoidingSet.dyadicShell_ncard_le_lcmPacking
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A)
    {J : Finset ι} {m : ι → ℕ} {k : ℕ}
    (hmA : ∀ i ∈ J, m i ∈ A)
    (hmpos : ∀ i ∈ J, 0 < m i)
    (hmlt : ∀ i ∈ J, m i < 2 ^ k) :
    (A ∩ dyadicShell k).ncard ≤
      (∏ i ∈ J, (m i / 2 + 1)) * ((2 ^ k) / J.lcm m + 1) := by
  rw [← dyadicShellFinset_card_eq_ncard]
  exact hA.dyadicShellFinset_card_le_lcmPacking hmA hmpos hmlt

/-- Real-valued shell-mass version of the LCM-packing bound. -/
theorem AvoidingSet.dyadicShell_mass_le_lcmPacking
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A)
    {J : Finset ι} {m : ι → ℕ} {k : ℕ}
    (hmA : ∀ i ∈ J, m i ∈ A)
    (hmpos : ∀ i ∈ J, 0 < m i)
    (hmlt : ∀ i ∈ J, m i < 2 ^ k) :
    ((A ∩ dyadicShell k).ncard : ℝ) / ((2 : ℝ) ^ k) ≤
      (((∏ i ∈ J, (m i / 2 + 1)) * ((2 ^ k) / J.lcm m + 1) : ℕ) : ℝ) /
        ((2 : ℝ) ^ k) := by
  have hcard := hA.dyadicShell_ncard_le_lcmPacking hmA hmpos hmlt
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- A selection theorem with summable LCM-packing majorants proves the
remaining reciprocal-summability conjecture for `A`.  This is the formal target
for the global combinatorial work: choose, at every scale, earlier moduli whose
LCM-packing majorant is summable. -/
theorem AvoidingSet.reciprocalSummable_of_lcmPacking_selection
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A)
    (hpos : PositiveSet A) {J : ℕ → Finset ι} {m : ℕ → ι → ℕ}
    {u : ℕ → ℝ}
    (hu : Summable u)
    (hmA : ∀ k i, i ∈ J k → m k i ∈ A)
    (hmpos : ∀ k i, i ∈ J k → 0 < m k i)
    (hmlt : ∀ k i, i ∈ J k → m k i < 2 ^ k)
    (hbound : ∀ k,
      ((((∏ i ∈ J k, (m k i / 2 + 1)) *
            ((2 ^ k) / (J k).lcm (m k) + 1) : ℕ) : ℝ) /
          ((2 : ℝ) ^ k)) ≤ u k) :
    ReciprocalSummable A := by
  refine reciprocalSummable_of_dyadicShell_bound hpos hu ?_
  intro k
  exact (hA.dyadicShell_mass_le_lcmPacking
    (J := J k) (m := m k) (hmA k) (hmpos k) (hmlt k)).trans (hbound k)

end DivisibilityAvoidingSets
