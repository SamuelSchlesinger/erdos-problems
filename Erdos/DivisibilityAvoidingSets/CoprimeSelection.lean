import Erdos.DivisibilityAvoidingSets.DyadicPacking

/-!
# Coprime-selection sufficient criteria

This file isolates the cleanest positive branch of the LCM-packing strategy.
If, at a dyadic scale, we can select many earlier elements of the avoiding set
whose moduli are pairwise coprime and whose LCM still fits inside the shell
length, then each selected modulus contributes a uniform loss.  For moduli at
least `4`, that loss is at most `3 / 4`.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

theorem nat_cast_div_le_div (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (Nat.cast_pos.mpr hb)]
  exact_mod_cast Nat.div_mul_le_self a b

theorem lcmPackingMajorant_le_gain_plus_error {P X L : ℕ}
    (hX : 0 < X) (hL : 0 < L) :
    (((P * (X / L + 1) : ℕ) : ℝ) / (X : ℝ)) ≤
      (P : ℝ) / (L : ℝ) + (P : ℝ) / (X : ℝ) := by
  have hdiv : ((X / L : ℕ) : ℝ) ≤ (X : ℝ) / (L : ℝ) :=
    nat_cast_div_le_div X L hL
  have hsum : ((X / L : ℕ) : ℝ) + 1 ≤ (X : ℝ) / (L : ℝ) + 1 := by
    linarith
  have hmul :
      (P : ℝ) * (((X / L : ℕ) : ℝ) + 1) ≤
        (P : ℝ) * ((X : ℝ) / (L : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg P)
  calc
    (((P * (X / L + 1) : ℕ) : ℝ) / (X : ℝ)) =
        (P : ℝ) * (((X / L : ℕ) : ℝ) + 1) / (X : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_add]
    _ ≤ (P : ℝ) * ((X : ℝ) / (L : ℝ) + 1) / (X : ℝ) := by
      exact div_le_div_of_nonneg_right hmul (le_of_lt (Nat.cast_pos.mpr hX))
    _ = (P : ℝ) / (L : ℝ) + (P : ℝ) / (X : ℝ) := by
      field_simp [Nat.cast_pos.mpr hX, Nat.cast_pos.mpr hL]

theorem lcmPackingMajorant_le_two_mul_gain {P X L : ℕ}
    (hX : 0 < X) (hL : 0 < L) (hLX : L ≤ X) :
    (((P * (X / L + 1) : ℕ) : ℝ) / (X : ℝ)) ≤
      2 * ((P : ℝ) / (L : ℝ)) := by
  have hsplit := lcmPackingMajorant_le_gain_plus_error (P := P) (X := X) (L := L) hX hL
  have hLXreal : (L : ℝ) ≤ (X : ℝ) := by exact_mod_cast hLX
  have herror : (P : ℝ) / (X : ℝ) ≤ (P : ℝ) / (L : ℝ) := by
    have hinv : (1 : ℝ) / (X : ℝ) ≤ 1 / (L : ℝ) :=
      one_div_le_one_div_of_le (Nat.cast_pos.mpr hL) hLXreal
    calc
      (P : ℝ) / (X : ℝ) = (P : ℝ) * (1 / (X : ℝ)) := by ring
      _ ≤ (P : ℝ) * (1 / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg P)
      _ = (P : ℝ) / (L : ℝ) := by ring
  linarith

theorem half_plus_one_le_three_quarters_mul {a : ℕ} (ha : 4 ≤ a) :
    (((a / 2 + 1 : ℕ) : ℝ)) ≤ (3 / 4 : ℝ) * (a : ℝ) := by
  have hdiv : ((a / 2 : ℕ) : ℝ) ≤ (a : ℝ) / 2 :=
    nat_cast_div_le_div a 2 (by norm_num)
  have ha_real : (4 : ℝ) ≤ a := by exact_mod_cast ha
  calc
    (((a / 2 + 1 : ℕ) : ℝ)) = ((a / 2 : ℕ) : ℝ) + 1 := by
      norm_num
    _ ≤ (a : ℝ) / 2 + 1 := by linarith
    _ ≤ (3 / 4 : ℝ) * (a : ℝ) := by nlinarith

theorem pow_le_pow_of_nonneg_le_one_of_le {a : ℝ}
    (h0 : 0 ≤ a) (h1 : a ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  exact mul_le_of_le_one_right (pow_nonneg h0 m) (pow_le_one₀ h0 h1)

/-- Pairwise coprime selected moduli of size at least `4` have LCM gain at
most `(3 / 4) ^ |J|`. -/
theorem lcmGain_le_geometric_of_pairwise_coprime
    {ι : Type*} {J : Finset ι} {m : ι → ℕ}
    (hcop : (J : Set ι).Pairwise (Function.onFun Nat.Coprime m))
    (hlarge : ∀ i ∈ J, 4 ≤ m i) :
    ((∏ i ∈ J, (m i / 2 + 1) : ℕ) : ℝ) / ((J.lcm m : ℕ) : ℝ) ≤
      (3 / 4 : ℝ) ^ J.card := by
  classical
  have hprod :
      ((∏ i ∈ J, (m i / 2 + 1) : ℕ) : ℝ) ≤
        (3 / 4 : ℝ) ^ J.card * ((∏ i ∈ J, m i : ℕ) : ℝ) := by
    calc
      ((∏ i ∈ J, (m i / 2 + 1) : ℕ) : ℝ) =
          ∏ i ∈ J, (((m i / 2 + 1 : ℕ) : ℝ)) := by
        simp
      _ ≤ ∏ i ∈ J, ((3 / 4 : ℝ) * (m i : ℝ)) := by
        exact Finset.prod_le_prod
          (fun i hi => by positivity)
          fun i hi =>
          half_plus_one_le_three_quarters_mul (hlarge i hi)
      _ = (3 / 4 : ℝ) ^ J.card * ((∏ i ∈ J, m i : ℕ) : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp
  have hlcm_eq : J.lcm m = ∏ i ∈ J, m i := Finset.lcm_eq_prod hcop
  have hprod_pos : (0 : ℝ) < ((∏ i ∈ J, m i : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun i hi => by
      have hlarge_i := hlarge i hi
      omega
  calc
    ((∏ i ∈ J, (m i / 2 + 1) : ℕ) : ℝ) / ((J.lcm m : ℕ) : ℝ) =
        ((∏ i ∈ J, (m i / 2 + 1) : ℕ) : ℝ) /
          ((∏ i ∈ J, m i : ℕ) : ℝ) := by
      rw [hlcm_eq]
    _ ≤ ((3 / 4 : ℝ) ^ J.card * ((∏ i ∈ J, m i : ℕ) : ℝ)) /
        ((∏ i ∈ J, m i : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hprod (le_of_lt hprod_pos)
    _ = (3 / 4 : ℝ) ^ J.card := by
      field_simp [hprod_pos.ne']

/-- Coprime selected moduli whose LCM fits in the dyadic length give geometric
shell decay. -/
theorem AvoidingSet.dyadicShell_mass_le_two_mul_geometric_of_coprime
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A)
    {J : Finset ι} {m : ι → ℕ} {k : ℕ}
    (hmA : ∀ i ∈ J, m i ∈ A)
    (hmpos : ∀ i ∈ J, 0 < m i)
    (hmlt : ∀ i ∈ J, m i < 2 ^ k)
    (hLle : J.lcm m ≤ 2 ^ k)
    (hcop : (J : Set ι).Pairwise (Function.onFun Nat.Coprime m))
    (hlarge : ∀ i ∈ J, 4 ≤ m i) :
    ((A ∩ dyadicShell k).ncard : ℝ) / ((2 : ℝ) ^ k) ≤
      2 * ((3 / 4 : ℝ) ^ J.card) := by
  have hmass := hA.dyadicShell_mass_le_lcmPacking hmA hmpos hmlt
  have hLpos : 0 < J.lcm m := finset_lcm_pos_of_forall_pos hmpos
  have hpacking :=
    lcmPackingMajorant_le_two_mul_gain
      (P := ∏ i ∈ J, (m i / 2 + 1)) (X := 2 ^ k) (L := J.lcm m)
      (by positivity) hLpos hLle
  have hgain := lcmGain_le_geometric_of_pairwise_coprime hcop hlarge
  have hgeom := hpacking.trans
    (mul_le_mul_of_nonneg_left hgain (by norm_num))
  exact hmass.trans (by
    simpa [Nat.cast_pow] using hgeom)

/-- A scale-by-scale coprime selection proves reciprocal summability as soon as
the resulting geometric shell majorants are summable.  This is the realistic
form of the independent-prime-content branch: logarithmic growth of `|J k|`
with a sufficiently large constant would be one way to prove the summability
hypothesis. -/
theorem AvoidingSet.reciprocalSummable_of_coprime_lcm_selection_summable_card
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {J : ℕ → Finset ι} {m : ℕ → ι → ℕ}
    (hcardSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ (J k).card))
    (hmA : ∀ k i, i ∈ J k → m k i ∈ A)
    (hmpos : ∀ k i, i ∈ J k → 0 < m k i)
    (hmlt : ∀ k i, i ∈ J k → m k i < 2 ^ k)
    (hLle : ∀ k, (J k).lcm (m k) ≤ 2 ^ k)
    (hcop : ∀ k, (J k : Set ι).Pairwise (Function.onFun Nat.Coprime (m k)))
    (hlarge : ∀ k i, i ∈ J k → 4 ≤ m k i) :
    ReciprocalSummable A := by
  refine reciprocalSummable_of_dyadicShell_bound
    (u := fun k => 2 * ((3 / 4 : ℝ) ^ (J k).card)) hpos hcardSummable ?_
  intro k
  exact hA.dyadicShell_mass_le_two_mul_geometric_of_coprime
    (J := J k) (m := m k) (hmA k) (hmpos k) (hmlt k)
    (hLle k) (hcop k) (hlarge k)

/-- A lower bound `f k ≤ |J k|` is enough when the coarser geometric majorant
`2 * (3 / 4) ^ f k` is summable. -/
theorem AvoidingSet.reciprocalSummable_of_coprime_lcm_selection_card_lower
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {J : ℕ → Finset ι} {m : ℕ → ι → ℕ} {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (hmA : ∀ k i, i ∈ J k → m k i ∈ A)
    (hmpos : ∀ k i, i ∈ J k → 0 < m k i)
    (hmlt : ∀ k i, i ∈ J k → m k i < 2 ^ k)
    (hLle : ∀ k, (J k).lcm (m k) ≤ 2 ^ k)
    (hcop : ∀ k, (J k : Set ι).Pairwise (Function.onFun Nat.Coprime (m k)))
    (hlarge : ∀ k i, i ∈ J k → 4 ≤ m k i)
    (hcard : ∀ k, f k ≤ (J k).card) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_coprime_lcm_selection_summable_card hpos ?_
    hmA hmpos hmlt hLle hcop hlarge
  exact Summable.of_nonneg_of_le
    (fun k => by positivity)
    (fun k => by
      have hpow :
          (3 / 4 : ℝ) ^ (J k).card ≤ (3 / 4 : ℝ) ^ f k :=
        pow_le_pow_of_nonneg_le_one_of_le
          (by norm_num : 0 ≤ (3 / 4 : ℝ))
          (by norm_num : (3 / 4 : ℝ) ≤ 1)
          (hcard k)
      exact mul_le_mul_of_nonneg_left hpow (by norm_num))
    hfSummable

/-- A scale-by-scale coprime selection with at least `k` selected moduli at
dyadic scale `k` proves reciprocal summability.  This is the clean independent
prime-content branch of the positive strategy. -/
theorem AvoidingSet.reciprocalSummable_of_coprime_lcm_selection
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {J : ℕ → Finset ι} {m : ℕ → ι → ℕ}
    (hmA : ∀ k i, i ∈ J k → m k i ∈ A)
    (hmpos : ∀ k i, i ∈ J k → 0 < m k i)
    (hmlt : ∀ k i, i ∈ J k → m k i < 2 ^ k)
    (hLle : ∀ k, (J k).lcm (m k) ≤ 2 ^ k)
    (hcop : ∀ k, (J k : Set ι).Pairwise (Function.onFun Nat.Coprime (m k)))
    (hlarge : ∀ k i, i ∈ J k → 4 ≤ m k i)
    (hcard : ∀ k, k ≤ (J k).card) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_coprime_lcm_selection_card_lower
    (f := fun k => k) hpos ?_ hmA hmpos hmlt hLle hcop hlarge hcard
  exact (summable_geometric_of_lt_one
      (by norm_num : 0 ≤ (3 / 4 : ℝ))
      (by norm_num : (3 / 4 : ℝ) < 1)).mul_left 2

/-- A concrete selection package at scale `k`: a finite set of actual earlier
members of `A`, large enough for the requested rank, pairwise coprime, and with
LCM still inside the dyadic length. -/
def CoprimeLCMSelection (A : Set ℕ) (k r : ℕ) (J : Finset ℕ) : Prop :=
  (∀ a ∈ J, a ∈ A) ∧
    (∀ a ∈ J, a < 2 ^ k) ∧
    J.lcm (fun a : ℕ => a) ≤ 2 ^ k ∧
    (J : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun a : ℕ => a) ∧
    (∀ a ∈ J, 4 ≤ a) ∧
    r ≤ J.card

/-- The finite set of elements of `A` below `2 ^ k` which are large enough to
be selected, are not already in the core `J`, and still fit in the remaining
LCM budget after adjoining them to `J`. -/
noncomputable def lcmRoomFinset (A : Set ℕ) (k : ℕ) (J : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 4 (2 ^ k)).filter fun x =>
    x ∈ A ∧ x ∉ J ∧ J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k

theorem mem_lcmRoomFinset {A : Set ℕ} {k x : ℕ} {J : Finset ℕ} :
    x ∈ lcmRoomFinset A k J ↔
      4 ≤ x ∧ x < 2 ^ k ∧ x ∈ A ∧ x ∉ J ∧
        J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k := by
  classical
  unfold lcmRoomFinset
  simp [and_assoc]

theorem CoprimeLCMSelection.rank_mono {A : Set ℕ} {k r s : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) (hsr : s ≤ r) :
    CoprimeLCMSelection A k s J :=
  ⟨hJ.1, hJ.2.1, hJ.2.2.1, hJ.2.2.2.1, hJ.2.2.2.2.1,
    hsr.trans hJ.2.2.2.2.2⟩

/-- A selected core remains valid at every later dyadic scale: the inequalities
`a < 2 ^ k` and `lcm(J) ≤ 2 ^ k` only become easier as `k` increases. -/
theorem CoprimeLCMSelection.scale_mono {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) (hkK : k ≤ K) :
    CoprimeLCMSelection A K r J := by
  have hpow : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hkK
  exact ⟨hJ.1, (fun a ha => (hJ.2.1 a ha).trans_le hpow),
    hJ.2.2.1.trans hpow, hJ.2.2.2.1, hJ.2.2.2.2.1,
    hJ.2.2.2.2.2⟩

/-- Rank `r` has an eventual coprime-LCM selection threshold `T` if every
scale at least `T` admits a rank-`r` selection. -/
def CoprimeLCMSelectionThreshold (A : Set ℕ) (r T : ℕ) : Prop :=
  ∀ K, T ≤ K → ∃ J : Finset ℕ, CoprimeLCMSelection A K r J

/-- A concrete selection at scale `k` gives the eventual threshold `k`, because
the same core remains valid at every later scale. -/
theorem CoprimeLCMSelection.threshold {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) :
    CoprimeLCMSelectionThreshold A r k := by
  intro K hkK
  exact ⟨J, hJ.scale_mono hkK⟩

/-- Raising an eventual threshold preserves eventual selection. -/
theorem CoprimeLCMSelectionThreshold.mono {A : Set ℕ} {r T U : ℕ}
    (hT : CoprimeLCMSelectionThreshold A r T) (hTU : T ≤ U) :
    CoprimeLCMSelectionThreshold A r U := by
  intro K hUK
  exact hT K (hTU.trans hUK)

/-- A threshold bounded by `k` gives an actual selection at scale `k`. -/
theorem CoprimeLCMSelectionThreshold.exists_selection_at
    {A : Set ℕ} {r T k : ℕ}
    (hT : CoprimeLCMSelectionThreshold A r T) (hTk : T ≤ k) :
    ∃ J : Finset ℕ, CoprimeLCMSelection A k r J :=
  hT k hTk

/-- If rank `f k` has a self-bounded eventual threshold for every large `k`,
then the scale-by-scale selections required by the summability criterion are
available on the same tail. -/
theorem exists_coprime_lcm_selection_of_self_bounded_threshold
    {A : Set ℕ} {f : ℕ → ℕ} {N : ℕ}
    (hthreshold : ∀ k, N ≤ k → ∃ T, T ≤ k ∧
      CoprimeLCMSelectionThreshold A (f k) T) :
    ∀ k, N ≤ k → ∃ J : Finset ℕ, CoprimeLCMSelection A k (f k) J := by
  intro k hk
  rcases hthreshold k hk with ⟨T, hTk, hT⟩
  exact hT.exists_selection_at hTk

/-- The least eventual selection threshold, packaged with an explicit
existence proof. -/
noncomputable def CoprimeLCMSelection.minThreshold
    (A : Set ℕ) (r : ℕ)
    (h : ∃ T, CoprimeLCMSelectionThreshold A r T) : ℕ :=
  by
    classical
    exact Nat.find h

/-- The least threshold is itself a valid eventual selection threshold. -/
theorem CoprimeLCMSelection.minThreshold_spec
    (A : Set ℕ) (r : ℕ)
    (h : ∃ T, CoprimeLCMSelectionThreshold A r T) :
    CoprimeLCMSelectionThreshold A r
      (CoprimeLCMSelection.minThreshold A r h) :=
  by
    classical
    exact Nat.find_spec h

/-- Minimality of the least eventual selection threshold. -/
theorem CoprimeLCMSelection.minThreshold_le
    {A : Set ℕ} {r T : ℕ}
    (h : ∃ U, CoprimeLCMSelectionThreshold A r U)
    (hT : CoprimeLCMSelectionThreshold A r T) :
    CoprimeLCMSelection.minThreshold A r h ≤ T :=
  by
    classical
    exact Nat.find_le hT

/-- A self-bound on the least threshold converts directly into an actual
selection at that scale. -/
theorem CoprimeLCMSelection.exists_selection_at_of_minThreshold_le
    {A : Set ℕ} {r k : ℕ}
    {h : ∃ T, CoprimeLCMSelectionThreshold A r T}
    (hle : CoprimeLCMSelection.minThreshold A r h ≤ k) :
    ∃ J : Finset ℕ, CoprimeLCMSelection A k r J :=
  (CoprimeLCMSelection.minThreshold_spec A r h).exists_selection_at hle

/-- The empty core is always a valid rank-zero selection. -/
theorem CoprimeLCMSelection.empty (A : Set ℕ) (k : ℕ) :
    CoprimeLCMSelection A k 0 (∅ : Finset ℕ) := by
  refine ⟨by simp, by simp, ?_, by simp, by simp, by simp⟩
  simpa using Nat.one_le_pow k 2 (by norm_num)

/-- A selection below `2 ^ k` has at most `2 ^ k` elements. -/
theorem CoprimeLCMSelection.card_le_pow {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) :
    J.card ≤ 2 ^ k := by
  have hsub : J ⊆ Finset.range (2 ^ k) := by
    intro a ha
    simpa using hJ.2.1 a ha
  simpa using Finset.card_le_card hsub

/-- Consequently the requested rank of a selection is at most `2 ^ k`. -/
theorem CoprimeLCMSelection.rank_le_pow {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) :
    r ≤ 2 ^ k :=
  hJ.2.2.2.2.2.trans hJ.card_le_pow

/-- A new element extends a coprime LCM selection whenever it is admissible,
coprime to the old core, and the enlarged LCM still fits inside the dyadic
budget. -/
theorem CoprimeLCMSelection.insert {A : Set ℕ} {k r x : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J)
    (hxA : x ∈ A) (hxlt : x < 2 ^ k) (hxlarge : 4 ≤ x)
    (hxnot : x ∉ J)
    (hxcop : ∀ a ∈ J, Nat.Coprime x a)
    (hxlcm : J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k) :
    CoprimeLCMSelection A k (r + 1) (Insert.insert x J : Finset ℕ) := by
  classical
  have hcop_symm :
      Symmetric (Function.onFun Nat.Coprime fun a : ℕ => a) := by
    intro a b hab
    exact hab.symm
  have hcop_insert :
      ((Insert.insert x J : Finset ℕ) : Set ℕ).Pairwise
        (Function.onFun Nat.Coprime fun a : ℕ => a) := by
    rw [Finset.coe_insert]
    exact hJ.2.2.2.1.insert_of_symmetric hcop_symm
      fun a ha _hxa => hxcop a ha
  have hlcm_insert :
      (Insert.insert x J : Finset ℕ).lcm (fun a : ℕ => a) =
        J.lcm (fun a : ℕ => a) * x := by
    calc
      (Insert.insert x J : Finset ℕ).lcm (fun a : ℕ => a) =
          ∏ a ∈ (Insert.insert x J : Finset ℕ), a := by
        exact Finset.lcm_eq_prod hcop_insert
      _ = x * ∏ a ∈ J, a := by
        rw [Finset.prod_insert hxnot]
      _ = x * J.lcm (fun a : ℕ => a) := by
        rw [Finset.lcm_eq_prod hJ.2.2.2.1]
      _ = J.lcm (fun a : ℕ => a) * x := by
        rw [Nat.mul_comm]
  refine ⟨?_, ?_, ?_, hcop_insert, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haJ
    · exact hxA
    · exact hJ.1 a haJ
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haJ
    · exact hxlt
    · exact hJ.2.1 a haJ
  · rwa [hlcm_insert]
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haJ
    · exact hxlarge
    · exact hJ.2.2.2.2.1 a haJ
  · rw [Finset.card_insert_of_notMem hxnot]
    exact Nat.succ_le_succ hJ.2.2.2.2.2

/-- Failure of the coprime LCM package at scale `k` and requested rank `r`. -/
def CoprimeLCMSelectionFailure (A : Set ℕ) (k r : ℕ) : Prop :=
  ∀ J : Finset ℕ, ¬ CoprimeLCMSelection A k r J

theorem CoprimeLCMSelectionFailure.mono_rank {A : Set ℕ} {k r s : ℕ}
    (hfail : CoprimeLCMSelectionFailure A k s) (hsr : s ≤ r) :
    CoprimeLCMSelectionFailure A k r := by
  intro J hJ
  exact hfail J (hJ.rank_mono hsr)

/-- If rank `r` fails at scale `k`, then `k` lies before every eventual
threshold from which rank `r` succeeds at all later scales. -/
theorem CoprimeLCMSelectionFailure.lt_eventual_selection_threshold
    {A : Set ℕ} {k r T : ℕ}
    (hfail : CoprimeLCMSelectionFailure A k r)
    (hT : ∀ K, T ≤ K → ∃ J, CoprimeLCMSelection A K r J) :
    k < T := by
  by_contra hnot
  have hTk : T ≤ k := not_lt.mp hnot
  rcases hT k hTk with ⟨J, hJ⟩
  exact hfail J hJ

/-- A failure at scale `k` rules out every eventual threshold at or before
`k`. -/
theorem CoprimeLCMSelectionFailure.not_threshold_at_or_before
    {A : Set ℕ} {k r T : ℕ}
    (hfail : CoprimeLCMSelectionFailure A k r) (hTk : T ≤ k) :
    ¬ CoprimeLCMSelectionThreshold A r T := by
  intro hT
  rcases hT.exists_selection_at hTk with ⟨J, hJ⟩
  exact hfail J hJ

/-- Threshold-predicate form of `lt_eventual_selection_threshold`. -/
theorem CoprimeLCMSelectionFailure.lt_selection_threshold
    {A : Set ℕ} {k r T : ℕ}
    (hfail : CoprimeLCMSelectionFailure A k r)
    (hT : CoprimeLCMSelectionThreshold A r T) :
    k < T :=
  hfail.lt_eventual_selection_threshold hT

/-- Rank `2 ^ k + 1` selections are impossible at scale `k`. -/
theorem CoprimeLCMSelectionFailure.pow_succ (A : Set ℕ) (k : ℕ) :
    CoprimeLCMSelectionFailure A k (2 ^ k + 1) := by
  intro J hJ
  have h := hJ.rank_le_pow
  omega

/-- At each scale there is a maximal coprime LCM core: it realizes some rank
`r`, and rank `r + 1` fails.  This is the canonical finite obstruction package
used by the common-factor branch. -/
theorem exists_maximal_coprime_lcm_selection (A : Set ℕ) (k : ℕ) :
    ∃ r J, CoprimeLCMSelection A k r J ∧
      CoprimeLCMSelectionFailure A k (r + 1) := by
  classical
  let P : ℕ → Prop := fun r => ∃ J : Finset ℕ, CoprimeLCMSelection A k r J
  have hP0 : P 0 := ⟨∅, CoprimeLCMSelection.empty A k⟩
  let r := Nat.findGreatest P (2 ^ k)
  have hPr : P r := by
    exact Nat.findGreatest_spec (P := P) (m := 0) (n := 2 ^ k) (Nat.zero_le _) hP0
  rcases hPr with ⟨J, hJ⟩
  refine ⟨r, J, hJ, ?_⟩
  intro K hK
  have hbound : r + 1 ≤ 2 ^ k := hK.rank_le_pow
  have hnot : ¬ P (r + 1) := by
    exact Nat.findGreatest_is_greatest (P := P) (n := 2 ^ k)
      (k := r + 1) (Nat.lt_succ_self r) hbound
  exact hnot ⟨K, hK⟩

/-- If rank `r + 1` selections fail but a rank `r` core exists, then any
admissible element coprime to that core must exceed the remaining LCM budget.
This is the finite obstruction that the common-factor branch has to exploit. -/
theorem CoprimeLCMSelectionFailure.lcm_budget_obstruction
    {A : Set ℕ} {k r x : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A k (r + 1))
    (hJ : CoprimeLCMSelection A k r J)
    (hxA : x ∈ A) (hxlt : x < 2 ^ k) (hxlarge : 4 ≤ x)
    (hxnot : x ∉ J)
    (hxcop : ∀ a ∈ J, Nat.Coprime x a) :
    2 ^ k < J.lcm (fun a : ℕ => a) * x := by
  by_contra hnot_lt
  have hxlcm : J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k := not_lt.mp hnot_lt
  exact hfail (Insert.insert x J : Finset ℕ)
    (hJ.insert hxA hxlt hxlarge hxnot hxcop hxlcm)

/-- Dichotomy forced by failure of the next coprime selection rank: every
admissible unselected element either shares a factor with the current core or
is too large for the remaining LCM budget. -/
theorem CoprimeLCMSelectionFailure.common_factor_or_lcm_budget_obstruction
    {A : Set ℕ} {k r x : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A k (r + 1))
    (hJ : CoprimeLCMSelection A k r J)
    (hxA : x ∈ A) (hxlt : x < 2 ^ k) (hxlarge : 4 ≤ x)
    (hxnot : x ∉ J) :
    (∃ a ∈ J, ¬ Nat.Coprime x a) ∨
      2 ^ k < J.lcm (fun a : ℕ => a) * x := by
  classical
  by_cases hxcop : ∀ a ∈ J, Nat.Coprime x a
  · exact Or.inr
      (hfail.lcm_budget_obstruction hJ hxA hxlt hxlarge hxnot hxcop)
  · left
    push Not at hxcop
    exact hxcop

/-- In the remaining-budget range, failure of the next coprime selection rank
forces an actual common factor with the current core. -/
theorem CoprimeLCMSelectionFailure.common_factor_of_lcm_room
    {A : Set ℕ} {k r x : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A k (r + 1))
    (hJ : CoprimeLCMSelection A k r J)
    (hxA : x ∈ A) (hxlt : x < 2 ^ k) (hxlarge : 4 ≤ x)
    (hxnot : x ∉ J)
    (hroom : J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k) :
    ∃ a ∈ J, ¬ Nat.Coprime x a := by
  rcases hfail.common_factor_or_lcm_budget_obstruction
      hJ hxA hxlt hxlarge hxnot with hcommon | hbudget
  · exact hcommon
  · exact False.elim ((not_lt_of_ge hroom) hbudget)

/-- Any family of admissible elements with enough LCM room is covered by the
non-coprime alternatives coming from the current finite core, provided the next
selection rank fails. -/
theorem CoprimeLCMSelectionFailure.noncoprime_core_cover_of_lcm_room
    {A S : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A k (r + 1))
    (hJ : CoprimeLCMSelection A k r J)
    (hS : ∀ ⦃x : ℕ⦄, x ∈ S →
      x ∈ A ∧ x < 2 ^ k ∧ 4 ≤ x ∧ x ∉ J ∧
        J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k) :
    S ⊆ ⋃ a ∈ J, {x | ¬ Nat.Coprime x a} := by
  intro x hx
  rcases hS hx with ⟨hxA, hxlt, hxlarge, hxnot, hroom⟩
  rcases hfail.common_factor_of_lcm_room hJ hxA hxlt hxlarge hxnot hroom with
    ⟨a, haJ, hxacop⟩
  simp only [Set.mem_iUnion]
  exact ⟨a, haJ, hxacop⟩

/-- Finite-shell quantitative form of the previous cover.  If the elements
still inside the remaining LCM budget have reciprocal mass exceeding
`|J| * c`, then one element of the finite core captures mass exceeding `c`
through the non-coprime alternative. -/
theorem CoprimeLCMSelectionFailure.exists_core_large_reciprocal_mass_of_lcm_room
    {A : Set ℕ} {k r : ℕ} {J F : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A k (r + 1))
    (hJ : CoprimeLCMSelection A k r J)
    (hF : ∀ ⦃x : ℕ⦄, x ∈ F →
      x ∈ A ∧ x < 2 ^ k ∧ 4 ≤ x ∧ x ∉ J ∧
        J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k)
    {c : ℝ} (hbig : (J.card : ℝ) * c <
      ∑ x ∈ F, (1 : ℝ) / (x : ℝ)) :
    ∃ a ∈ J, c <
      ∑ x ∈ F.filter (fun x => ¬ Nat.Coprime x a),
        (1 : ℝ) / (x : ℝ) := by
  classical
  let B : ℕ → Set ℕ := fun a => {x | ¬ Nat.Coprime x a}
  have hcoverSet : (F : Set ℕ) ⊆ ⋃ a ∈ J, B a :=
    hfail.noncoprime_core_cover_of_lcm_room (S := (F : Set ℕ)) hJ hF
  have hcover : ∀ x ∈ F, ∃ a ∈ J, x ∈ B a := by
    intro x hxF
    have hxcover := hcoverSet hxF
    simpa [B] using hxcover
  simpa [B] using
    (exists_lt_sum_reciprocal_filter_of_card_mul_lt_sum_of_cover
      (F := F) (I := J) (B := B) hcover hbig)

/-- Standard `lcmRoomFinset` specialization of the finite-shell concentration
lemma. -/
theorem CoprimeLCMSelectionFailure.exists_core_large_reciprocal_mass_of_lcmRoomFinset
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A k (r + 1))
    (hJ : CoprimeLCMSelection A k r J)
    {c : ℝ} (hbig : (J.card : ℝ) * c <
      ∑ x ∈ lcmRoomFinset A k J, (1 : ℝ) / (x : ℝ)) :
    ∃ a ∈ J, c <
      ∑ x ∈ (lcmRoomFinset A k J).filter (fun x => ¬ Nat.Coprime x a),
        (1 : ℝ) / (x : ℝ) := by
  refine hfail.exists_core_large_reciprocal_mass_of_lcm_room hJ ?_ hbig
  intro x hx
  rcases mem_lcmRoomFinset.mp hx with ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨hxA, hxlt, hxlarge, hxnot, hxroom⟩

/-- Delayed-scale inclusion: if a later core `J` has enough LCM budget to
cover the whole earlier dyadic shell, then every earlier-shell element not
already in `J` lies in the later LCM-room finset.  The hypothesis `2 ≤ k`
discards the two tiny initial shells, ensuring shell elements are at least
`4`. -/
theorem mem_lcmRoomFinset_of_mem_dyadicShellFinset
    {A : Set ℕ} {k K r x : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hx : x ∈ dyadicShellFinset A k)
    (hxnot : x ∉ J)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K) :
    x ∈ lcmRoomFinset A K J := by
  have hxmem := mem_dyadicShellFinset.mp hx
  have hxA : x ∈ A := hxmem.1
  have hxlower : 2 ^ k ≤ x := hxmem.2.1
  have hxupper : x < 2 ^ (k + 1) := hxmem.2.2
  have hxlarge : 4 ≤ x := by
    have hpow : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    norm_num at hpow
    exact hpow.trans hxlower
  have hLpos : 0 < J.lcm (fun a : ℕ => a) := by
    exact finset_lcm_pos_of_forall_pos fun a ha =>
      Nat.lt_of_lt_of_le (by norm_num : 0 < 4) (hJ.2.2.2.2.1 a ha)
  have hupper_le_delay :
      2 ^ (k + 1) ≤ J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) := by
    exact Nat.le_mul_of_pos_left _ hLpos
  have hxltK : x < 2 ^ K :=
    hxupper.trans_le (hupper_le_delay.trans hdelay)
  have hxroom : J.lcm (fun a : ℕ => a) * x ≤ 2 ^ K := by
    exact (Nat.mul_le_mul_left _ (Nat.le_of_lt hxupper)).trans hdelay
  exact mem_lcmRoomFinset.mpr ⟨hxlarge, hxltK, hxA, hxnot, hxroom⟩

/-- A failed later-scale extension covers an earlier dyadic shell, after
removing the finitely many elements already present in the later core, whenever
the later LCM budget covers the shell. -/
theorem CoprimeLCMSelectionFailure.noncoprime_core_cover_of_delayed_shell
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A K (r + 1))
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K) :
    ((dyadicShellFinset A k).filter (fun x => x ∉ J) : Set ℕ) ⊆
      ⋃ a ∈ J, {x | ¬ Nat.Coprime x a} := by
  refine hfail.noncoprime_core_cover_of_lcm_room hJ ?_
  intro x hx
  have hxShell : x ∈ dyadicShellFinset A k := (Finset.mem_filter.mp hx).1
  have hxnot : x ∉ J := (Finset.mem_filter.mp hx).2
  have hxRoom :=
    mem_lcmRoomFinset_of_mem_dyadicShellFinset hJ hk hxShell hxnot hdelay
  rcases mem_lcmRoomFinset.mp hxRoom with ⟨hxlarge, hxlt, hxA, hxnotJ, hxroom⟩
  exact ⟨hxA, hxlt, hxlarge, hxnotJ, hxroom⟩

/-- Delayed-shell quantitative concentration.  If a later maximality failure
has enough budget to see an earlier shell and the shell-minus-core reciprocal
mass exceeds `|J| * c`, then one later core element captures more than `c`
of that earlier shell through the non-coprime alternative. -/
theorem CoprimeLCMSelectionFailure.exists_core_large_reciprocal_mass_of_delayed_shell
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A K (r + 1))
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K)
    {c : ℝ} (hbig : (J.card : ℝ) * c <
      ∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∉ J),
        (1 : ℝ) / (x : ℝ)) :
    ∃ a ∈ J, c <
      ∑ x ∈ ((dyadicShellFinset A k).filter (fun x => x ∉ J)).filter
          (fun x => ¬ Nat.Coprime x a),
        (1 : ℝ) / (x : ℝ) := by
  refine hfail.exists_core_large_reciprocal_mass_of_lcm_room hJ ?_ hbig
  intro x hx
  have hxShell : x ∈ dyadicShellFinset A k := (Finset.mem_filter.mp hx).1
  have hxnot : x ∉ J := (Finset.mem_filter.mp hx).2
  have hxRoom :=
    mem_lcmRoomFinset_of_mem_dyadicShellFinset hJ hk hxShell hxnot hdelay
  rcases mem_lcmRoomFinset.mp hxRoom with ⟨hxlarge, hxlt, hxA, hxnotJ, hxroom⟩
  exact ⟨hxA, hxlt, hxlarge, hxnotJ, hxroom⟩

/-- Full-shell version of delayed-shell concentration.  The hypothesis says
that, after paying for the finitely many elements of the later core which
already lie in the earlier shell, enough reciprocal mass remains to force a
large non-coprime contribution from one core element. -/
theorem CoprimeLCMSelectionFailure.exists_core_large_reciprocal_mass_of_delayed_shell'
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A K (r + 1))
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K)
    {c : ℝ} (hbig : (J.card : ℝ) * c +
      (∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∈ J),
        (1 : ℝ) / (x : ℝ)) <
      ∑ x ∈ dyadicShellFinset A k, (1 : ℝ) / (x : ℝ)) :
    ∃ a ∈ J, c <
      ∑ x ∈ ((dyadicShellFinset A k).filter (fun x => x ∉ J)).filter
          (fun x => ¬ Nat.Coprime x a),
        (1 : ℝ) / (x : ℝ) := by
  have hsplit :
      (∑ x ∈ dyadicShellFinset A k, (1 : ℝ) / (x : ℝ)) =
        (∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∈ J),
          (1 : ℝ) / (x : ℝ)) +
        (∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∉ J),
          (1 : ℝ) / (x : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (dyadicShellFinset A k)
      (fun x => x ∈ J)]
  have hminus : (J.card : ℝ) * c <
      ∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∉ J),
        (1 : ℝ) / (x : ℝ) := by
    rw [hsplit] at hbig
    linarith
  exact hfail.exists_core_large_reciprocal_mass_of_delayed_shell
    hJ hk hdelay hminus

/-- Canonical maximal-core package at scale `k`: a maximal core exists and
its remaining LCM-room set is covered by the non-coprime alternatives from the
core. -/
theorem exists_maximal_coprime_lcm_selection_with_lcmRoom_cover (A : Set ℕ) (k : ℕ) :
    ∃ r J, CoprimeLCMSelection A k r J ∧
      CoprimeLCMSelectionFailure A k (r + 1) ∧
      (lcmRoomFinset A k J : Set ℕ) ⊆ ⋃ a ∈ J, {x | ¬ Nat.Coprime x a} := by
  rcases exists_maximal_coprime_lcm_selection A k with ⟨r, J, hJ, hfail⟩
  refine ⟨r, J, hJ, hfail, ?_⟩
  refine hfail.noncoprime_core_cover_of_lcm_room hJ ?_
  intro x hx
  rcases mem_lcmRoomFinset.mp hx with ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨hxA, hxlt, hxlarge, hxnot, hxroom⟩

/-- Quantitative maximal-core package: for the canonical room set of a
maximal core, any reciprocal-mass surplus over `|J| * c` is carried by one
non-coprime layer from the core. -/
theorem exists_maximal_coprime_lcm_selection_with_lcmRoom_concentration
    (A : Set ℕ) (k : ℕ) :
    ∃ r J, CoprimeLCMSelection A k r J ∧
      CoprimeLCMSelectionFailure A k (r + 1) ∧
      ∀ {c : ℝ}, (J.card : ℝ) * c <
        ∑ x ∈ lcmRoomFinset A k J, (1 : ℝ) / (x : ℝ) →
        ∃ a ∈ J, c <
          ∑ x ∈ (lcmRoomFinset A k J).filter (fun x => ¬ Nat.Coprime x a),
            (1 : ℝ) / (x : ℝ) := by
  rcases exists_maximal_coprime_lcm_selection A k with ⟨r, J, hJ, hfail⟩
  refine ⟨r, J, hJ, hfail, ?_⟩
  intro c hbig
  exact hfail.exists_core_large_reciprocal_mass_of_lcmRoomFinset hJ hbig

/-- Maximal-core delayed-shell concentration package.  Once the maximal later
core has enough budget to see an earlier shell, the previous concentration
lemma applies to that shell. -/
theorem exists_maximal_coprime_lcm_selection_with_delayed_shell_concentration
    (A : Set ℕ) {k K : ℕ} (hk : 2 ≤ k) :
    ∃ r J, CoprimeLCMSelection A K r J ∧
      CoprimeLCMSelectionFailure A K (r + 1) ∧
      (J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K →
        ∀ {c : ℝ}, (J.card : ℝ) * c <
          ∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∉ J),
            (1 : ℝ) / (x : ℝ) →
          ∃ a ∈ J, c <
            ∑ x ∈ ((dyadicShellFinset A k).filter (fun x => x ∉ J)).filter
                (fun x => ¬ Nat.Coprime x a),
              (1 : ℝ) / (x : ℝ)) := by
  rcases exists_maximal_coprime_lcm_selection A K with ⟨r, J, hJ, hfail⟩
  refine ⟨r, J, hJ, hfail, ?_⟩
  intro hdelay c hbig
  exact hfail.exists_core_large_reciprocal_mass_of_delayed_shell hJ hk hdelay hbig

/-- Full-shell maximal-core delayed concentration package, with the finite
core contribution explicitly paid for in the hypothesis. -/
theorem exists_maximal_coprime_lcm_selection_with_delayed_shell_concentration'
    (A : Set ℕ) {k K : ℕ} (hk : 2 ≤ k) :
    ∃ r J, CoprimeLCMSelection A K r J ∧
      CoprimeLCMSelectionFailure A K (r + 1) ∧
      (J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K →
        ∀ {c : ℝ}, (J.card : ℝ) * c +
          (∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∈ J),
            (1 : ℝ) / (x : ℝ)) <
          ∑ x ∈ dyadicShellFinset A k, (1 : ℝ) / (x : ℝ) →
          ∃ a ∈ J, c <
            ∑ x ∈ ((dyadicShellFinset A k).filter (fun x => x ∉ J)).filter
                (fun x => ¬ Nat.Coprime x a),
              (1 : ℝ) / (x : ℝ)) := by
  rcases exists_maximal_coprime_lcm_selection A K with ⟨r, J, hJ, hfail⟩
  refine ⟨r, J, hJ, hfail, ?_⟩
  intro hdelay c hbig
  exact hfail.exists_core_large_reciprocal_mass_of_delayed_shell'
    hJ hk hdelay hbig

/-- Scheduled delayed charging step.  Suppose a later core `J k` is chosen for
each earlier shell `k`, its next extension fails, and its LCM budget sees shell
`k` for all `k ≥ 2`.  If the proposed thresholds

`|J k| * c k + (core contribution in shell k)`

are summable, then some arbitrarily late shell forces one core element to carry
more than `c k` reciprocal mass through the non-coprime alternative. -/
theorem exists_delayed_shell_concentration_of_summable_threshold
    {A : Set ℕ} (hApos : PositiveSet A) (hnot : ¬ ReciprocalSummable A)
    {K r : ℕ → ℕ} {J : ℕ → Finset ℕ} {c : ℕ → ℝ}
    (hthreshold : Summable fun k =>
      ((J k).card : ℝ) * c k + dyadicShellCoreMass A k (J k))
    (hJ : ∀ k, CoprimeLCMSelection A (K k) (r k) (J k))
    (hfail : ∀ k, CoprimeLCMSelectionFailure A (K k) (r k + 1))
    (hdelay : ∀ k, 2 ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (N : ℕ) :
    ∃ k, N ≤ k ∧ 2 ≤ k ∧
      ∃ a ∈ J k, c k < dyadicShellNoncoreNoncoprimeMass A k (J k) a := by
  rcases exists_ge_lt_dyadicShellReciprocalMass_of_not_reciprocalSummable
      hApos hnot hthreshold (max N 2) with ⟨k, hkge, hheavy⟩
  have hNk : N ≤ k := (le_max_left N 2).trans hkge
  have hk2 : 2 ≤ k := (le_max_right N 2).trans hkge
  have hbig : ((J k).card : ℝ) * c k +
      (∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∈ J k),
        (1 : ℝ) / (x : ℝ)) <
      ∑ x ∈ dyadicShellFinset A k, (1 : ℝ) / (x : ℝ) := by
    simpa [dyadicShellReciprocalMass, dyadicShellCoreMass] using hheavy
  rcases (hfail k).exists_core_large_reciprocal_mass_of_delayed_shell'
      (hJ k) hk2 (hdelay k hk2) hbig with ⟨a, haJ, haMass⟩
  refine ⟨k, hNk, hk2, a, haJ, ?_⟩
  simpa [dyadicShellNoncoreNoncoprimeMass] using haMass

/-- Existence of summably many scale-wise coprime selections is enough to close
the reciprocal-summability problem for `A`.  This is the theorem-shaped hard
step: all remaining combinatorics can aim to produce these `J`s, or explain why
failure of this package forces a separate structured case. -/
theorem AvoidingSet.reciprocalSummable_of_exists_coprime_lcm_selection
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (hsel : ∀ k, ∃ J : Finset ℕ, CoprimeLCMSelection A k (f k) J) :
    ReciprocalSummable A := by
  classical
  let J : ℕ → Finset ℕ := fun k => Classical.choose (hsel k)
  have hJ : ∀ k, CoprimeLCMSelection A k (f k) (J k) :=
    fun k => Classical.choose_spec (hsel k)
  refine hA.reciprocalSummable_of_coprime_lcm_selection_card_lower
    (J := J) (m := fun _ a => a) (f := f) hpos hfSummable ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k i hi
    exact (hJ k).1 i hi
  · intro k i hi
    have hlarge_i := (hJ k).2.2.2.2.1 i hi
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4) hlarge_i
  · intro k i hi
    exact (hJ k).2.1 i hi
  · intro k
    exact (hJ k).2.2.1
  · intro k
    exact (hJ k).2.2.2.1
  · intro k i hi
    exact (hJ k).2.2.2.2.1 i hi
  · intro k
    exact (hJ k).2.2.2.2.2

/-- Eventual version of the coprime-selection criterion.  To prove reciprocal
summability it is enough to produce a summably strong rank schedule after
discarding finitely many initial dyadic scales. -/
theorem AvoidingSet.reciprocalSummable_of_eventually_exists_coprime_lcm_selection
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ} (hsel : ∀ k, N ≤ k → ∃ J : Finset ℕ,
      CoprimeLCMSelection A k (f k) J) :
    ReciprocalSummable A := by
  refine reciprocalSummable_of_eventually_dyadicShell_bound
    (u := fun k => 2 * ((3 / 4 : ℝ) ^ f k)) hpos hfSummable
    (N := N) ?_
  intro k hk
  rcases hsel k hk with ⟨J, hJ⟩
  have hbound :=
    hA.dyadicShell_mass_le_two_mul_geometric_of_coprime
      (J := J) (m := fun a : ℕ => a) (k := k)
      hJ.1
      (fun a ha => Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
        (hJ.2.2.2.2.1 a ha))
      hJ.2.1 hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2.1
  have hpow :
      (3 / 4 : ℝ) ^ J.card ≤ (3 / 4 : ℝ) ^ f k :=
    pow_le_pow_of_nonneg_le_one_of_le
      (by norm_num : 0 ≤ (3 / 4 : ℝ))
      (by norm_num : (3 / 4 : ℝ) ≤ 1)
      hJ.2.2.2.2.2
  exact hbound.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

/-- Contrapositive bookkeeping: any nonsummable avoiding set must fail every
summably strong coprime-selection scheme at some dyadic scale. -/
theorem AvoidingSet.exists_coprime_lcm_selection_failure_of_not_reciprocalSummable
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    (hnot : ¬ ReciprocalSummable A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) :
    ∃ k, CoprimeLCMSelectionFailure A k (f k) := by
  by_contra hnone
  have hsel : ∀ k, ∃ J : Finset ℕ, CoprimeLCMSelection A k (f k) J := by
    intro k
    by_contra hk
    exact hnone ⟨k, fun J hJ => hk ⟨J, hJ⟩⟩
  exact hnot (hA.reciprocalSummable_of_exists_coprime_lcm_selection hpos hfSummable hsel)

/-- Strong contrapositive: in a nonsummable avoiding set, every summably strong
rank schedule fails at arbitrarily late dyadic scales.  This is the precise
rate obstruction left after the irreducible branch gives eventual success for
each fixed rank. -/
theorem AvoidingSet.exists_ge_coprime_lcm_selection_failure_of_not_reciprocalSummable
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    (hnot : ¬ ReciprocalSummable A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k, N ≤ k ∧ CoprimeLCMSelectionFailure A k (f k) := by
  by_contra hnone
  have hsel : ∀ k, N ≤ k → ∃ J : Finset ℕ, CoprimeLCMSelection A k (f k) J := by
    intro k hk
    by_contra hkfail
    exact hnone ⟨k, hk, fun J hJ => hkfail ⟨J, hJ⟩⟩
  exact hnot
    (hA.reciprocalSummable_of_eventually_exists_coprime_lcm_selection
      hpos hfSummable hsel)

end DivisibilityAvoidingSets
