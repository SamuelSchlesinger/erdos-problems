import Erdos.DivisibilityAvoidingSets.CommonFactorDescent

/-!
# Threshold strategy for the coprime-selection branch

The remaining positive-side obstruction is quantitative: for a summably strong
rank schedule `f`, can one prove that rank `f k` already succeeds by dyadic
scale `k` for all sufficiently large `k`?

This file isolates a fixed-scale bounded greedy target.  If every partial
coprime-LCM core below the desired rank has a legal extension inside the same
dyadic scale, then the full desired rank exists at that scale.  Thus closing
the slow-rank obstruction is reduced to proving this local extension property
for a logarithmic rank schedule.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- At scale `k`, every valid partial core of rank below `r` has a legal
one-step extension which still fits inside the same LCM budget. -/
def CoprimeLCMExtensionProperty (A : Set ℕ) (k r : ℕ) : Prop :=
  ∀ s J, s < r → CoprimeLCMSelection A k s J →
    ∃ x : ℕ, x ∈ A ∧ x < 2 ^ k ∧ 4 ≤ x ∧ x ∉ J ∧
      (∀ a ∈ J, Nat.Coprime x a) ∧
      J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k

/-- Bounded greedy selection at one scale.  If every partial core below rank
`r` can be extended without leaving the dyadic budget, then a rank-`r`
coprime-LCM selection exists at that scale. -/
theorem exists_coprime_lcm_selection_of_extension_property
    {A : Set ℕ} {k r : ℕ}
    (hExt : CoprimeLCMExtensionProperty A k r) :
    ∃ J, CoprimeLCMSelection A k r J := by
  induction r with
  | zero =>
      exact ⟨∅, CoprimeLCMSelection.empty A k⟩
  | succ r ih =>
      have hExt_r : CoprimeLCMExtensionProperty A k r := by
        intro s J hs hJ
        exact hExt s J (Nat.lt_trans hs (Nat.lt_succ_self r)) hJ
      rcases ih hExt_r with ⟨J, hJ⟩
      rcases hExt r J (Nat.lt_succ_self r) hJ with
        ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩
      exact ⟨Insert.insert x J, hJ.insert hxA hxlt hxlarge hxnot hxcop hxroom⟩

/-- The assertion that `L` is the LCM of some rank-`r` selection at scale
`k`.  This lets us minimize the LCM value without choosing from a finite list
of candidate cores. -/
def CoprimeLCMSelection.LCMValue (A : Set ℕ) (k r L : ℕ) : Prop :=
  ∃ J : Finset ℕ, CoprimeLCMSelection A k r J ∧
    J.lcm (fun a : ℕ => a) = L

/-- Every existing selection has some LCM value. -/
theorem CoprimeLCMSelection.exists_lcmValue_of_exists_selection
    {A : Set ℕ} {k r : ℕ}
    (hsel : ∃ J : Finset ℕ, CoprimeLCMSelection A k r J) :
    ∃ L : ℕ, CoprimeLCMSelection.LCMValue A k r L := by
  rcases hsel with ⟨J, hJ⟩
  exact ⟨J.lcm (fun a : ℕ => a), J, hJ, rfl⟩

/-- The least LCM value among rank-`r` selections at scale `k`, assuming at
least one such selection exists. -/
noncomputable def CoprimeLCMSelection.minLCM
    (A : Set ℕ) (k r : ℕ)
    (hsel : ∃ J : Finset ℕ, CoprimeLCMSelection A k r J) : ℕ :=
  by
    classical
    exact Nat.find
      (CoprimeLCMSelection.exists_lcmValue_of_exists_selection hsel)

/-- The least LCM value is realized by an actual rank-`r` selection. -/
theorem CoprimeLCMSelection.minLCM_spec
    {A : Set ℕ} {k r : ℕ}
    (hsel : ∃ J : Finset ℕ, CoprimeLCMSelection A k r J) :
    CoprimeLCMSelection.LCMValue A k r
      (CoprimeLCMSelection.minLCM A k r hsel) :=
  by
    classical
    exact Nat.find_spec
      (CoprimeLCMSelection.exists_lcmValue_of_exists_selection hsel)

/-- Minimality of the least LCM value. -/
theorem CoprimeLCMSelection.minLCM_le_lcm
    {A : Set ℕ} {k r : ℕ}
    (hsel : ∃ J : Finset ℕ, CoprimeLCMSelection A k r J)
    {J : Finset ℕ} (hJ : CoprimeLCMSelection A k r J) :
    CoprimeLCMSelection.minLCM A k r hsel ≤
      J.lcm (fun a : ℕ => a) :=
  by
    classical
    exact Nat.find_le ⟨J, hJ, rfl⟩

/-- A rank-`r` selection whose LCM is minimal among all rank-`r` selections at
the same scale. -/
def CoprimeLCMSelection.LCMMinimal
    (A : Set ℕ) (k r : ℕ) (J : Finset ℕ) : Prop :=
  CoprimeLCMSelection A k r J ∧
    ∀ J' : Finset ℕ, CoprimeLCMSelection A k r J' →
      J.lcm (fun a : ℕ => a) ≤ J'.lcm (fun a : ℕ => a)

/-- Removing a selected element from a coprime-LCM core strictly lowers the
LCM.  Pairwise coprimality makes the LCM a product, and every selected element
is at least `4`. -/
theorem CoprimeLCMSelection.lcm_erase_lt
    {A : Set ℕ} {k r a : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) (haJ : a ∈ J) :
    (J.erase a).lcm (fun x : ℕ => x) < J.lcm (fun x : ℕ => x) := by
  classical
  have hsub : (J.erase a : Set ℕ) ⊆ (J : Set ℕ) := by
    intro x hx
    exact Finset.erase_subset a J hx
  have hcop_erase : ((J.erase a : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun x : ℕ => x) :=
    hJ.2.2.2.1.mono hsub
  have hprod_pos : 0 < ∏ x ∈ J.erase a, x := by
    exact Finset.prod_pos fun x hx => by
      have hxlarge : 4 ≤ x := hJ.2.2.2.2.1 x
        (Finset.erase_subset a J hx)
      omega
  have ha_gt : 1 < a := by
    have halarge : 4 ≤ a := hJ.2.2.2.2.1 a haJ
    omega
  have hprod_lt : (∏ x ∈ J.erase a, x) <
      (∏ x ∈ J.erase a, x) * a := by
    nlinarith [Nat.mul_lt_mul_of_pos_left ha_gt hprod_pos]
  calc
    (J.erase a).lcm (fun x : ℕ => x) = ∏ x ∈ J.erase a, x := Finset.lcm_eq_prod hcop_erase
    _ < (∏ x ∈ J.erase a, x) * a := hprod_lt
    _ = ∏ x ∈ J, x := Finset.prod_erase_mul J (fun x : ℕ => x) haJ
    _ = J.lcm (fun x : ℕ => x) := by
      rw [Finset.lcm_eq_prod hJ.2.2.2.1]

/-- Whenever a rank is selectable, some selected core realizes the smallest
possible LCM for that rank. -/
theorem CoprimeLCMSelection.exists_lcmMinimal_of_exists_selection
    {A : Set ℕ} {k r : ℕ}
    (hsel : ∃ J : Finset ℕ, CoprimeLCMSelection A k r J) :
    ∃ J : Finset ℕ, CoprimeLCMSelection.LCMMinimal A k r J := by
  rcases CoprimeLCMSelection.minLCM_spec hsel with ⟨J, hJ, hJL⟩
  refine ⟨J, hJ, ?_⟩
  intro J' hJ'
  rw [hJL]
  exact CoprimeLCMSelection.minLCM_le_lcm hsel hJ'

/-- An LCM-minimal rank-`r` selection has exactly `r` elements.  Any extra
element could be erased, preserving rank `r` while strictly lowering the LCM. -/
theorem CoprimeLCMSelection.LCMMinimal.card_eq
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A k r J) :
    J.card = r := by
  refine le_antisymm ?_ hJ.1.2.2.2.2.2
  by_contra hnot
  have hgt : r < J.card := not_le.mp hnot
  have hpos : 0 < J.card := by omega
  rcases Finset.card_pos.mp hpos with ⟨a, haJ⟩
  have hsub : (J.erase a : Set ℕ) ⊆ (J : Set ℕ) := by
    intro x hx
    exact Finset.erase_subset a J hx
  have hcop_erase : ((J.erase a : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun x : ℕ => x) :=
    hJ.1.2.2.2.1.mono hsub
  have hJerase : CoprimeLCMSelection A k r (J.erase a) := by
    refine ⟨?_, ?_, ?_, hcop_erase, ?_, ?_⟩
    · intro x hx
      exact hJ.1.1 x (Finset.erase_subset a J hx)
    · intro x hx
      exact hJ.1.2.1 x (Finset.erase_subset a J hx)
    · exact (hJ.1.lcm_erase_lt haJ).le.trans hJ.1.2.2.1
    · intro x hx
      exact hJ.1.2.2.2.2.1 x (Finset.erase_subset a J hx)
    · rw [Finset.card_erase_of_mem haJ]
      omega
  have hmin := hJ.2 (J.erase a) hJerase
  have hlt := hJ.1.lcm_erase_lt haJ
  exact (not_lt_of_ge hmin) hlt

/-- Same-rank replacement lower bound for an LCM-minimal core.  If replacing
`a ∈ J` by a new admissible `x` preserves pairwise coprimality with the
remaining core and still fits in the LCM budget, then minimality forces
`a ≤ x`; otherwise the replacement would be a valid rank-`r` selection with
strictly smaller LCM. -/
theorem CoprimeLCMSelection.LCMMinimal.le_of_replacement
    {A : Set ℕ} {K r a x : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hxA : x ∈ A) (hxlt : x < 2 ^ K) (hxlarge : 4 ≤ x)
    (hxnotJ : x ∉ J)
    (hxcop : ∀ b ∈ J.erase a, Nat.Coprime x b)
    (hxlcm : (J.erase a).lcm (fun y : ℕ => y) * x ≤ 2 ^ K) :
    a ≤ x := by
  classical
  let J' : Finset ℕ := Insert.insert x (J.erase a)
  have hsub_erase : (J.erase a : Set ℕ) ⊆ (J : Set ℕ) := by
    intro y hy
    exact Finset.erase_subset a J hy
  have hcop_erase : ((J.erase a : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun y : ℕ => y) :=
    hJ.1.2.2.2.1.mono hsub_erase
  have hxnotErase : x ∉ J.erase a := by
    intro hx
    exact hxnotJ (Finset.erase_subset a J hx)
  have hcop_symm :
      Symmetric (Function.onFun Nat.Coprime fun y : ℕ => y) := by
    intro y z hyz
    exact hyz.symm
  have hcop_insert : ((J' : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun y : ℕ => y) := by
    dsimp [J']
    rw [Finset.coe_insert]
    exact hcop_erase.insert_of_symmetric hcop_symm
      fun b hb _hxb => hxcop b hb
  have hlcm_insert :
      J'.lcm (fun y : ℕ => y) =
        (J.erase a).lcm (fun y : ℕ => y) * x := by
    calc
      J'.lcm (fun y : ℕ => y) = ∏ y ∈ J', y := Finset.lcm_eq_prod hcop_insert
      _ = x * ∏ y ∈ J.erase a, y := by
        dsimp [J']
        rw [Finset.prod_insert hxnotErase]
      _ = x * (J.erase a).lcm (fun y : ℕ => y) := by
        rw [Finset.lcm_eq_prod hcop_erase]
      _ = (J.erase a).lcm (fun y : ℕ => y) * x := by
        rw [Nat.mul_comm]
  have hcardJ' : J'.card = J.card := by
    dsimp [J']
    rw [Finset.card_insert_of_notMem hxnotErase]
    rw [Finset.card_erase_of_mem haJ]
    have hcard_pos : 0 < J.card := Finset.card_pos.mpr ⟨a, haJ⟩
    omega
  have hJ' : CoprimeLCMSelection A K r J' := by
    refine ⟨?_, ?_, ?_, hcop_insert, ?_, ?_⟩
    · intro y hy
      dsimp [J'] at hy
      rcases Finset.mem_insert.mp hy with rfl | hyErase
      · exact hxA
      · exact hJ.1.1 y (Finset.erase_subset a J hyErase)
    · intro y hy
      dsimp [J'] at hy
      rcases Finset.mem_insert.mp hy with rfl | hyErase
      · exact hxlt
      · exact hJ.1.2.1 y (Finset.erase_subset a J hyErase)
    · rwa [hlcm_insert]
    · intro y hy
      dsimp [J'] at hy
      rcases Finset.mem_insert.mp hy with rfl | hyErase
      · exact hxlarge
      · exact hJ.1.2.2.2.2.1 y (Finset.erase_subset a J hyErase)
    · rw [hcardJ']
      exact hJ.1.2.2.2.2.2
  have hmin : J.lcm (fun y : ℕ => y) ≤ J'.lcm (fun y : ℕ => y) :=
    hJ.2 J' hJ'
  have hLorig :
      J.lcm (fun y : ℕ => y) =
        (J.erase a).lcm (fun y : ℕ => y) * a := by
    calc
      J.lcm (fun y : ℕ => y) = ∏ y ∈ J, y := Finset.lcm_eq_prod hJ.1.2.2.2.1
      _ = (∏ y ∈ J.erase a, y) * a := (Finset.prod_erase_mul J (fun y : ℕ => y) haJ).symm
      _ = (J.erase a).lcm (fun y : ℕ => y) * a := by
        rw [Finset.lcm_eq_prod hcop_erase]
  have hmul :
      (J.erase a).lcm (fun y : ℕ => y) * a ≤
        (J.erase a).lcm (fun y : ℕ => y) * x := by
    simpa [hLorig, hlcm_insert] using hmin
  have hLerase_pos : 0 < (J.erase a).lcm (fun y : ℕ => y) :=
    finset_lcm_pos_of_forall_pos fun y hy => by
      have hylarge : 4 ≤ y :=
        hJ.1.2.2.2.2.1 y (Finset.erase_subset a J hy)
      omega
  exact Nat.le_of_mul_le_mul_left hmul hLerase_pos

/-- Room-element form of the replacement lower bound.  Any candidate already
inside the current LCM-room that is coprime to the core after erasing `a` is a
legal same-rank replacement for `a`, so an LCM-minimal core forces `a ≤ x`. -/
theorem CoprimeLCMSelection.LCMMinimal.le_of_room_replacement
    {A : Set ℕ} {K r a x : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hxRoom : x ∈ lcmRoomFinset A K J)
    (hxcop : ∀ b ∈ J.erase a, Nat.Coprime x b) :
    a ≤ x := by
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnotJ, hxroom⟩
  have hxlcm : (J.erase a).lcm (fun y : ℕ => y) * x ≤ 2 ^ K :=
    (Nat.mul_le_mul_right x (hJ.1.lcm_erase_lt haJ).le).trans hxroom
  exact hJ.le_of_replacement haJ hxA hxlt hxlarge hxnotJ hxcop hxlcm

/-- Quotient-lift form of the room replacement bound.  A lifted quotient
candidate `p * q` that is coprime to the erased core cannot replace `a` by a
smaller value in an LCM-minimal core. -/
theorem CoprimeLCMSelection.LCMMinimal.le_mul_of_room_quotient_replacement
    {A : Set ℕ} {K r a p q : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hxRoom : p * q ∈ lcmRoomFinset A K J)
    (hxcop : ∀ b ∈ J.erase a, Nat.Coprime (p * q) b) :
    a ≤ p * q :=
  hJ.le_of_room_replacement haJ hxRoom hxcop

/-- If rank `r` was already realized by some core `J₀` at an earlier scale,
then any LCM-minimal rank-`r` core at a later scale has LCM at most that earlier
witness's LCM. -/
theorem CoprimeLCMSelection.LCMMinimal.lcm_le_of_prior_selection
    {A : Set ℕ} {T K r : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K) :
    J.lcm (fun a : ℕ => a) ≤ J₀.lcm (fun a : ℕ => a) := hJ.2 J₀ (hJ₀.scale_mono hTK)

/-- Prior selection witness turned into delayed-prefix headroom for an
LCM-minimal later core. -/
theorem CoprimeLCMSelection.LCMMinimal.delay_of_prior_selection
    {A : Set ℕ} {T K r m : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K) :
    J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K := by
  exact (Nat.mul_le_mul_right _ (hJ.lcm_le_of_prior_selection hJ₀ hTK)).trans
    hdelay₀

/-- A selected core element forces the ambient dyadic scale to be positive. -/
theorem CoprimeLCMSelection.scale_pos_of_mem
    {A : Set ℕ} {K r a : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J) (haJ : a ∈ J) :
    0 < K := by
  by_contra hnot
  have hK0 : K = 0 := Nat.eq_zero_of_not_pos hnot
  have ha_lt : a < 2 ^ K := hJ.2.1 a haJ
  have ha_large : 4 ≤ a := hJ.2.2.2.2.1 a haJ
  rw [hK0] at ha_lt
  norm_num at ha_lt
  omega

/-- The finite set of primes dividing at least one element of a core. -/
noncomputable def corePrimeSupport (J : Finset ℕ) : Finset ℕ := by
  classical
  exact J.biUnion fun a => Nat.primeFactors a

/-- Erasing a core element can only remove support primes. -/
theorem corePrimeSupport_erase_subset (J : Finset ℕ) (a : ℕ) :
    corePrimeSupport (J.erase a) ⊆ corePrimeSupport J := by
  classical
  intro p hp
  unfold corePrimeSupport at hp ⊢
  rw [Finset.mem_biUnion] at hp ⊢
  rcases hp with ⟨b, hbErase, hpb⟩
  exact ⟨b, Finset.erase_subset a J hbErase, hpb⟩

/-- The reciprocal mass of the LCM-room associated to a core. -/
noncomputable def lcmRoomReciprocalMass (A : Set ℕ) (k : ℕ)
    (J : Finset ℕ) : ℝ :=
  ∑ x ∈ lcmRoomFinset A k J, (1 : ℝ) / (x : ℝ)

/-- Reciprocal mass of an earlier dyadic shell after removing the elements
already present in a later core. -/
noncomputable def dyadicShellNoncoreReciprocalMass
    (A : Set ℕ) (k : ℕ) (J : Finset ℕ) : ℝ :=
  ∑ x ∈ (dyadicShellFinset A k).filter (fun x => x ∉ J),
    (1 : ℝ) / (x : ℝ)

/-- The finite dyadic prefix `A ∩ [2^N, 2^(m+1))`.  This is a block of
consecutive dyadic shells, and is the natural object when a later LCM room has
enough headroom to see many earlier shells at once. -/
noncomputable def dyadicPrefixFinset (A : Set ℕ) (N m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (2 ^ N) (2 ^ (m + 1))).filter fun x => x ∈ A

/-- Reciprocal mass of `A ∩ [2^N, 2^(m+1))`. -/
noncomputable def dyadicPrefixReciprocalMass
    (A : Set ℕ) (N m : ℕ) : ℝ :=
  ∑ x ∈ dyadicPrefixFinset A N m, (1 : ℝ) / (x : ℝ)

/-- Reciprocal mass in a dyadic prefix contributed by a finite core. -/
noncomputable def dyadicPrefixCoreMass
    (A : Set ℕ) (N m : ℕ) (J : Finset ℕ) : ℝ :=
  ∑ x ∈ (dyadicPrefixFinset A N m).filter (fun x => x ∈ J),
    (1 : ℝ) / (x : ℝ)

/-- Reciprocal mass in a dyadic prefix after removing a finite core. -/
noncomputable def dyadicPrefixNoncoreReciprocalMass
    (A : Set ℕ) (N m : ℕ) (J : Finset ℕ) : ℝ :=
  ∑ x ∈ (dyadicPrefixFinset A N m).filter (fun x => x ∉ J),
    (1 : ℝ) / (x : ℝ)

/-- Dyadic shells are disjoint as finite subsets. -/
theorem pairwiseDisjoint_dyadicShellFinset (A : Set ℕ) (I : Finset ℕ) :
    ((I : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k => dyadicShellFinset A k) := by
  intro k _hk l _hl hkl
  change Disjoint (dyadicShellFinset A k) (dyadicShellFinset A l)
  rw [Finset.disjoint_left]
  intro x hxk hxl
  have hxk' := mem_dyadicShellFinset.mp hxk
  have hxl' := mem_dyadicShellFinset.mp hxl
  have hklog : Nat.log 2 x = k :=
    Nat.log_eq_of_pow_le_of_lt_pow hxk'.2.1 hxk'.2.2
  have hllog : Nat.log 2 x = l :=
    Nat.log_eq_of_pow_le_of_lt_pow hxl'.2.1 hxl'.2.2
  exact hkl (hklog.symm.trans hllog)

/-- The reciprocal mass of a finite interval of dyadic shells is contained in
the corresponding dyadic prefix. -/
theorem sum_Ico_dyadicShellReciprocalMass_le_dyadicPrefixReciprocalMass
    (A : Set ℕ) {N n : ℕ} (hNn : N < n) :
    (∑ k ∈ Finset.Ico N n, dyadicShellReciprocalMass A k) ≤
      dyadicPrefixReciprocalMass A N (n - 1) := by
  classical
  let I := Finset.Ico N n
  let U := I.biUnion fun k => dyadicShellFinset A k
  have hdisj :
      ((I : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun k => dyadicShellFinset A k) :=
    pairwiseDisjoint_dyadicShellFinset A I
  have hsumU :
      (∑ x ∈ U, (1 : ℝ) / (x : ℝ)) =
        ∑ k ∈ I, dyadicShellReciprocalMass A k := by
    simpa [U, I, dyadicShellReciprocalMass] using
      (Finset.sum_biUnion
        (s := I) (t := fun k => dyadicShellFinset A k)
        (f := fun x : ℕ => (1 : ℝ) / (x : ℝ)) hdisj)
  have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le N) hNn
  have hpred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hnpos
  have hUsub : U ⊆ dyadicPrefixFinset A N (n - 1) := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨k, hkI, hxShell⟩
    rcases Finset.mem_Ico.mp hkI with ⟨hNk, hkn⟩
    rcases mem_dyadicShellFinset.mp hxShell with ⟨hxA, hxlower, hxupper⟩
    have hprefixLower : 2 ^ N ≤ x :=
      (Nat.pow_le_pow_right (by norm_num) hNk).trans hxlower
    have hksucc : k + 1 ≤ n := Nat.succ_le_of_lt hkn
    have hprefixUpper : x < 2 ^ (n - 1 + 1) := by
      rw [hpred]
      exact hxupper.trans_le (Nat.pow_le_pow_right (by norm_num) hksucc)
    rw [dyadicPrefixFinset]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hprefixLower, hprefixUpper⟩, hxA⟩
  calc
    (∑ k ∈ Finset.Ico N n, dyadicShellReciprocalMass A k) =
        ∑ x ∈ U, (1 : ℝ) / (x : ℝ) := hsumU.symm
    _ ≤ ∑ x ∈ dyadicPrefixFinset A N (n - 1), (1 : ℝ) / (x : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hUsub ?_
      intro x _hxPrefix _hxMissing
      exact one_div_nonneg.mpr (Nat.cast_nonneg x)
    _ = dyadicPrefixReciprocalMass A N (n - 1) := by
      rfl

/-- Cumulative heavy-prefix extraction.  A positive nonsummable set has dyadic
prefixes with arbitrarily large reciprocal mass, even if each individual shell
is small. -/
theorem exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
    {A : Set ℕ} (hApos : PositiveSet A) (hnot : ¬ ReciprocalSummable A)
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    ∃ n, N < n ∧ C < dyadicPrefixReciprocalMass A N (n - 1) := by
  rcases exists_lt_sum_Ico_of_not_summable_nonneg
      (dyadicShellReciprocalMass_nonneg A)
      (not_summable_dyadicShellReciprocalMass_of_not_reciprocalSummable
        hApos hnot)
      hC N with ⟨n, hNn, hsum⟩
  exact ⟨n, hNn,
    hsum.trans_le
      (sum_Ico_dyadicShellReciprocalMass_le_dyadicPrefixReciprocalMass
        A hNn)⟩

/-- If a later LCM core has enough budget to see an earlier shell, then the
earlier shell-minus-core reciprocal mass is contained in the later LCM-room
mass.  This is the quantitative delayed-visibility bridge. -/
theorem dyadicShellNoncoreReciprocalMass_le_lcmRoomReciprocalMass_of_delay
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K) :
    dyadicShellNoncoreReciprocalMass A k J ≤
      lcmRoomReciprocalMass A K J := by
  unfold dyadicShellNoncoreReciprocalMass lcmRoomReciprocalMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
  · intro x hx
    have hxShell : x ∈ dyadicShellFinset A k := (Finset.mem_filter.mp hx).1
    have hxnot : x ∉ J := (Finset.mem_filter.mp hx).2
    exact mem_lcmRoomFinset_of_mem_dyadicShellFinset
      hJ hk hxShell hxnot hdelay
  · intro x _hxRoom _hxMissing
    exact one_div_nonneg.mpr (Nat.cast_nonneg x)

/-- A delayed visible shell is paid for by the later core elements already in
that shell, plus the reciprocal mass of the later LCM-room. -/
theorem dyadicShellReciprocalMass_le_coreMass_add_lcmRoomReciprocalMass_of_delay
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K) :
    dyadicShellReciprocalMass A k ≤
      dyadicShellCoreMass A k J + lcmRoomReciprocalMass A K J := by
  have hsplit :
      dyadicShellReciprocalMass A k =
        dyadicShellCoreMass A k J +
          dyadicShellNoncoreReciprocalMass A k J := by
    unfold dyadicShellReciprocalMass dyadicShellCoreMass
      dyadicShellNoncoreReciprocalMass
    rw [← Finset.sum_filter_add_sum_filter_not (dyadicShellFinset A k)
      (fun x => x ∈ J)]
  have hroom :=
    dyadicShellNoncoreReciprocalMass_le_lcmRoomReciprocalMass_of_delay
      hJ hk hdelay
  rw [hsplit]
  exact add_le_add_right hroom _

/-- If a later LCM core has enough budget to see a whole dyadic prefix, then
the prefix-minus-core reciprocal mass is contained in the later LCM-room mass. -/
theorem dyadicPrefixNoncoreReciprocalMass_le_lcmRoomReciprocalMass_of_delay
    {A : Set ℕ} {N m K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K) :
    dyadicPrefixNoncoreReciprocalMass A N m J ≤
      lcmRoomReciprocalMass A K J := by
  classical
  unfold dyadicPrefixNoncoreReciprocalMass lcmRoomReciprocalMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
  · intro x hx
    have hxPrefix : x ∈ dyadicPrefixFinset A N m :=
      (Finset.mem_filter.mp hx).1
    have hxnot : x ∉ J := (Finset.mem_filter.mp hx).2
    rw [dyadicPrefixFinset] at hxPrefix
    rcases Finset.mem_filter.mp hxPrefix with ⟨hxIco, hxA⟩
    rcases Finset.mem_Ico.mp hxIco with ⟨hxlower, hxupper⟩
    have hxlarge : 4 ≤ x := by
      have hpow : 2 ^ 2 ≤ 2 ^ N :=
        Nat.pow_le_pow_right (by norm_num) hN
      norm_num at hpow
      exact hpow.trans hxlower
    have hLpos : 0 < J.lcm (fun a : ℕ => a) := by
      exact finset_lcm_pos_of_forall_pos fun a ha =>
        Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
          (hJ.2.2.2.2.1 a ha)
    have hupper_le_delay :
        2 ^ (m + 1) ≤ J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) := Nat.le_mul_of_pos_left _ hLpos
    have hxltK : x < 2 ^ K :=
      hxupper.trans_le (hupper_le_delay.trans hdelay)
    have hxroom : J.lcm (fun a : ℕ => a) * x ≤ 2 ^ K :=
      (Nat.mul_le_mul_left _ (Nat.le_of_lt hxupper)).trans hdelay
    exact mem_lcmRoomFinset.mpr ⟨hxlarge, hxltK, hxA, hxnot, hxroom⟩
  · intro x _hxRoom _hxMissing
    exact one_div_nonneg.mpr (Nat.cast_nonneg x)

/-- A delayed visible dyadic prefix is paid for by the later core elements
already in that prefix, plus the reciprocal mass of the later LCM-room. -/
theorem dyadicPrefixReciprocalMass_le_coreMass_add_lcmRoomReciprocalMass_of_delay
    {A : Set ℕ} {N m K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K) :
    dyadicPrefixReciprocalMass A N m ≤
      dyadicPrefixCoreMass A N m J + lcmRoomReciprocalMass A K J := by
  have hsplit :
      dyadicPrefixReciprocalMass A N m =
        dyadicPrefixCoreMass A N m J +
          dyadicPrefixNoncoreReciprocalMass A N m J := by
    unfold dyadicPrefixReciprocalMass dyadicPrefixCoreMass
      dyadicPrefixNoncoreReciprocalMass
    rw [← Finset.sum_filter_add_sum_filter_not (dyadicPrefixFinset A N m)
      (fun x => x ∈ J)]
  have hroom :=
    dyadicPrefixNoncoreReciprocalMass_le_lcmRoomReciprocalMass_of_delay
      hJ hN hdelay
  rw [hsplit]
  exact add_le_add_right hroom _

/-- The direct contribution of a finite core to the `k`-th dyadic shell is at
most `|J| / 2^k`, since every element in that shell is at least `2^k`. -/
theorem dyadicShellCoreMass_le_card_div_pow
    (A : Set ℕ) (k : ℕ) (J : Finset ℕ) :
    dyadicShellCoreMass A k J ≤
      (J.card : ℝ) / (((2 ^ k : ℕ) : ℝ)) := by
  classical
  let F := (dyadicShellFinset A k).filter (fun x => x ∈ J)
  have hpowpos : (0 : ℝ) < (((2 ^ k : ℕ) : ℝ)) := by
    positivity
  calc
    dyadicShellCoreMass A k J =
        ∑ x ∈ F, (1 : ℝ) / (x : ℝ) := by
      rfl
    _ ≤ ∑ _x ∈ F, (1 : ℝ) / (((2 ^ k : ℕ) : ℝ)) := by
      refine Finset.sum_le_sum fun x hx => ?_
      have hxShell : x ∈ dyadicShellFinset A k :=
        (Finset.mem_filter.mp hx).1
      have hxlower : 2 ^ k ≤ x := (mem_dyadicShellFinset.mp hxShell).2.1
      have hxreal : (((2 ^ k : ℕ) : ℝ)) ≤ (x : ℝ) := by
        exact_mod_cast hxlower
      exact one_div_le_one_div_of_le hpowpos hxreal
    _ = (F.card : ℝ) / (((2 ^ k : ℕ) : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (J.card : ℝ) / (((2 ^ k : ℕ) : ℝ)) := by
      have hFsub : F ⊆ J := by
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      have hcard : (F.card : ℝ) ≤ (J.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hFsub
      exact div_le_div_of_nonneg_right hcard (le_of_lt hpowpos)

/-- The direct contribution of a finite core to a dyadic prefix starting at
`2^N` is at most `|J| / 2^N`. -/
theorem dyadicPrefixCoreMass_le_card_div_pow
    (A : Set ℕ) (N m : ℕ) (J : Finset ℕ) :
    dyadicPrefixCoreMass A N m J ≤
      (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
  classical
  let F := (dyadicPrefixFinset A N m).filter (fun x => x ∈ J)
  have hpowpos : (0 : ℝ) < (((2 ^ N : ℕ) : ℝ)) := by
    positivity
  calc
    dyadicPrefixCoreMass A N m J =
        ∑ x ∈ F, (1 : ℝ) / (x : ℝ) := by
      rfl
    _ ≤ ∑ _x ∈ F, (1 : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
      refine Finset.sum_le_sum fun x hx => ?_
      have hxPrefix : x ∈ dyadicPrefixFinset A N m :=
        (Finset.mem_filter.mp hx).1
      rw [dyadicPrefixFinset] at hxPrefix
      have hxlower : 2 ^ N ≤ x :=
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hxPrefix).1).1
      have hxreal : (((2 ^ N : ℕ) : ℝ)) ≤ (x : ℝ) := by
        exact_mod_cast hxlower
      exact one_div_le_one_div_of_le hpowpos hxreal
    _ = (F.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
      have hFsub : F ⊆ J := by
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      have hcard : (F.card : ℝ) ≤ (J.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hFsub
      exact div_le_div_of_nonneg_right hcard (le_of_lt hpowpos)

/-- A delayed visible shell is paid for by at most `|J| / 2^k` from the core
itself, plus the later LCM-room mass. -/
theorem dyadicShellReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K) :
    dyadicShellReciprocalMass A k ≤
      (J.card : ℝ) / (((2 ^ k : ℕ) : ℝ)) +
        lcmRoomReciprocalMass A K J := by
  have hshell :=
    dyadicShellReciprocalMass_le_coreMass_add_lcmRoomReciprocalMass_of_delay
      hJ hk hdelay
  have hcore := dyadicShellCoreMass_le_card_div_pow A k J
  linarith

/-- A delayed visible dyadic prefix is paid for by at most `|J| / 2^N` from
the core itself, plus the later LCM-room mass. -/
theorem dyadicPrefixReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
    {A : Set ℕ} {N m K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K) :
    dyadicPrefixReciprocalMass A N m ≤
      (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        lcmRoomReciprocalMass A K J := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_coreMass_add_lcmRoomReciprocalMass_of_delay
      hJ hN hdelay
  have hcore := dyadicPrefixCoreMass_le_card_div_pow A N m J
  linarith

/-- The reciprocal mass in the LCM-room captured by divisibility by a prime
or, more generally, by a fixed divisor `p`. -/
noncomputable def lcmRoomPrimeDivisorMass (A : Set ℕ) (k : ℕ)
    (J : Finset ℕ) (p : ℕ) : ℝ :=
  ∑ x ∈ (lcmRoomFinset A k J).filter (fun x => p ∣ x),
    (1 : ℝ) / (x : ℝ)

/-- Prime-divisor mass in an LCM-room is nonnegative. -/
theorem lcmRoomPrimeDivisorMass_nonneg (A : Set ℕ) (k : ℕ)
    (J : Finset ℕ) (p : ℕ) :
    0 ≤ lcmRoomPrimeDivisorMass A k J p := by
  unfold lcmRoomPrimeDivisorMass
  exact Finset.sum_nonneg fun x _hx =>
    one_div_nonneg.mpr (Nat.cast_nonneg x)

/-- Actual reciprocal mass below the dyadic cap `2^k` captured by multiples of
`p` inside `A`.  Unlike `multiplesBelowReciprocalMass`, this keeps membership
in `A`; unlike `lcmRoomPrimeDivisorMass`, it forgets the current core and LCM
room. -/
noncomputable def belowScalePrimeDivisorMass (A : Set ℕ) (k p : ℕ) : ℝ :=
  by
    classical
    exact ∑ x ∈ (Finset.Ico 1 (2 ^ k)).filter (fun x => x ∈ A ∧ p ∣ x),
      (1 : ℝ) / (x : ℝ)

/-- Total reciprocal mass in the LCM-room captured by the prime support of the
core.  This is the prime-support version of the non-coprime capture term. -/
noncomputable def lcmRoomPrimeSupportMass (A : Set ℕ) (k : ℕ)
    (J : Finset ℕ) : ℝ :=
  ∑ p ∈ corePrimeSupport J, lcmRoomPrimeDivisorMass A k J p

/-- Actual LCM-room mass captured by the part of the core prime support lying
inside a chosen finite prime set `P`.  These primes should be paid for by their
real contribution to `A`, not by the coarse absolute `k / p` bound. -/
noncomputable def lcmRoomPrimeSupportMassWithin
    (A : Set ℕ) (k : ℕ) (J P : Finset ℕ) : ℝ :=
  ∑ p ∈ (corePrimeSupport J).filter (fun p => p ∈ P),
    lcmRoomPrimeDivisorMass A k J p

/-- Actual LCM-room mass captured by support primes outside a chosen finite
old-prime set `P`. -/
noncomputable def lcmRoomFreshPrimeSupportMass
    (A : Set ℕ) (k : ℕ) (J P : Finset ℕ) : ℝ :=
  ∑ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P),
    lcmRoomPrimeDivisorMass A k J p

/-- Actual below-scale mass captured by a finite prime set. -/
noncomputable def belowScalePrimeSupportMass
    (A : Set ℕ) (k : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, belowScalePrimeDivisorMass A k p

/-- Absolute reciprocal mass of all positive multiples of `p` below the dyadic
cap `2 ^ k`.  This forgets the set `A` and the LCM-room restriction, so it is a
coarse but purely sieve-theoretic upper bound for any one prime-divisor layer. -/
noncomputable def multiplesBelowReciprocalMass (k p : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Ico 1 (2 ^ k)).filter (fun x => p ∣ x),
    (1 : ℝ) / (x : ℝ)

/-- The absolute dyadic multiples majorant summed over the prime support of a
core.  Proving this is strictly smaller than the actual room mass is a concrete
large-prime sparsity route to a coprime extension. -/
noncomputable def corePrimeSupportMultiplesBelowMass (k : ℕ)
    (J : Finset ℕ) : ℝ :=
  ∑ p ∈ corePrimeSupport J, multiplesBelowReciprocalMass k p

/-- Absolute multiples majorant for the part of the core prime support outside
a chosen finite prime set `P`. -/
noncomputable def corePrimeSupportOutsideMultiplesBelowMass
    (k : ℕ) (J P : Finset ℕ) : ℝ :=
  ∑ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P),
    multiplesBelowReciprocalMass k p

/-- The ordinary harmonic reciprocal mass below the dyadic cap `2 ^ k`.  A
multiple layer for a prime `p` is bounded by `(1 / p)` times this quantity. -/
noncomputable def dyadicHarmonicMass (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (1 : ℕ) (2 ^ k), (1 : ℝ) / (m : ℝ)

/-- Sum of reciprocal primes over the prime support of a core. -/
noncomputable def corePrimeSupportPrimeReciprocalMass (J : Finset ℕ) : ℝ :=
  ∑ p ∈ corePrimeSupport J, (1 : ℝ) / (p : ℝ)

/-- If the whole LCM-room is covered by prime-divisibility layers from the
core support, then the room mass is bounded by the corresponding
prime-support capture mass. -/
theorem lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ}
    (hcover : ((lcmRoomFinset A k J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    lcmRoomReciprocalMass A k J ≤ lcmRoomPrimeSupportMass A k J := by
  classical
  let F := lcmRoomFinset A k J
  let B : ℕ → Set ℕ := fun p => {x | p ∣ x}
  have hcover' : ∀ x ∈ F, ∃ p ∈ corePrimeSupport J, x ∈ B p := by
    intro x hx
    have hxcover := hcover hx
    simpa [B] using hxcover
  have hle : (∑ x ∈ F, (1 : ℝ) / (x : ℝ)) ≤
      ∑ p ∈ corePrimeSupport J, ∑ x ∈ F.filter (fun x => x ∈ B p),
        (1 : ℝ) / (x : ℝ) := by
    exact finset_sum_le_sum_filter_of_cover
      (w := fun x : ℕ => (1 : ℝ) / (x : ℝ))
      (fun x => one_div_nonneg.mpr (Nat.cast_nonneg x)) hcover'
  simpa [F, B, lcmRoomReciprocalMass, lcmRoomPrimeSupportMass,
    lcmRoomPrimeDivisorMass] using hle

/-- Under the scale-prime-support obstruction, any delayed visible shell whose
mass is not already paid by the later core forces a large reciprocal-prime
mass in the core support. -/
theorem lt_scale_primeSupportMass_of_unpaid_delayed_shell_obstruction
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      (K : ℝ) * corePrimeSupportPrimeReciprocalMass J)
    (hheavy : dyadicShellCoreMass A k J + c <
      dyadicShellReciprocalMass A k) :
    c < (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  have hshell :=
    dyadicShellReciprocalMass_le_coreMass_add_lcmRoomReciprocalMass_of_delay
      hJ hk hdelay
  linarith

/-- Numerical delayed-shell obstruction: under the scale-prime-support
obstruction, a visible earlier shell has mass bounded by the direct finite-core
payment `|J| / 2^k` plus the scale-weighted reciprocal-prime mass. -/
theorem dyadicShellReciprocalMass_le_card_div_pow_add_scale_primeSupport_of_delay_obstruction
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    dyadicShellReciprocalMass A k ≤
      (J.card : ℝ) / (((2 ^ k : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  have hshell :=
    dyadicShellReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
      hJ hk hdelay
  linarith

/-- Prefix version of the numerical delayed obstruction: under the
scale-prime-support obstruction, every visible dyadic prefix has mass bounded
by `|J| / 2^N` plus the scale-weighted reciprocal-prime mass. -/
theorem dyadicPrefixReciprocalMass_le_card_div_pow_add_scalePrimeSupport_of_delay_obstruction
    {A : Set ℕ} {N m K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    dyadicPrefixReciprocalMass A N m ≤
      (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
      hJ hN hdelay
  linarith

/-- Mixed small/large-prime delayed-prefix obstruction.  If a later LCM-room is
covered by actual capture from a chosen finite prime set `P`, plus an outside
prime budget, then every earlier dyadic prefix visible from that room is bounded
by the finite-core payment plus those two terms.

This is the quantitative bridge needed for the growing-cutoff attack: after a
heavy-prefix extraction, the excess mass must be paid either by actual small
prime capture or by the explicit large-prime budget. -/
theorem dyadicPrefixReciprocalMass_le_card_div_pow_add_mixedPrimeSupport_of_delay_obstruction
    {A : Set ℕ} {N m K r : ℕ} {J P : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J P +
        corePrimeSupportOutsideMultiplesBelowMass K J P) :
    dyadicPrefixReciprocalMass A N m ≤
      (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (lcmRoomPrimeSupportMassWithin A K J P +
          corePrimeSupportOutsideMultiplesBelowMass K J P) := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
      hJ hN hdelay
  linarith

/-- Standard cutoff version of the mixed delayed-prefix obstruction.  With
`P = M.primesBelow`, the outside-prime contribution is the explicit numerical
budget supplied by the scale split. -/
theorem dyadicPrefixReciprocalMass_le_card_div_pow_add_primesBelowBudget_of_delay
    {A : Set ℕ} {N m K r M : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
        (K : ℝ) * ((K : ℝ) / (M : ℝ))) :
    dyadicPrefixReciprocalMass A N m ≤
      (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
          (K : ℝ) * ((K : ℝ) / (M : ℝ))) := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
      hJ hN hdelay
  linarith

/-- A heavy visible prefix forces actual small-prime capture, unless the
outside prime budget already pays for the excess. -/
theorem lt_mixedPrimeSupportMass_of_heavy_delayed_prefix_obstruction
    {A : Set ℕ} {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J P +
        corePrimeSupportOutsideMultiplesBelowMass K J P)
    (hheavy : (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (corePrimeSupportOutsideMultiplesBelowMass K J P + c) <
      dyadicPrefixReciprocalMass A N m) :
    c < lcmRoomPrimeSupportMassWithin A K J P := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_mixedPrimeSupport_of_delay_obstruction
      hJ hN hdelay hobstruction
  linarith

/-- Standard cutoff form of the previous lemma.  For a very large cutoff `M`,
the term `K^2 / M` can be made negligible, so a heavy delayed prefix forces
actual capture by primes below `M`. -/
theorem lt_primesBelowSupportMass_of_heavy_delayed_prefix_obstruction
    {A : Set ℕ} {N m K r M : ℕ} {J : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
        (K : ℝ) * ((K : ℝ) / (M : ℝ)))
    (hheavy : (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        ((K : ℝ) * ((K : ℝ) / (M : ℝ)) + c) <
      dyadicPrefixReciprocalMass A N m) :
    c < lcmRoomPrimeSupportMassWithin A K J M.primesBelow := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_primesBelowBudget_of_delay
      hJ hN hdelay hobstruction
  linarith

/-- If an earlier visible shell beats the trivial finite-core payment by `c`,
then the scale-prime-support obstruction forces `c` into the reciprocal-prime
mass of the later core support. -/
theorem lt_scale_primeSupportMass_of_heavy_delayed_shell_obstruction
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      (K : ℝ) * corePrimeSupportPrimeReciprocalMass J)
    (hheavy : (J.card : ℝ) / (((2 ^ k : ℕ) : ℝ)) + c <
      dyadicShellReciprocalMass A k) :
    c < (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  have hshell :=
    dyadicShellReciprocalMass_le_card_div_pow_add_scale_primeSupport_of_delay_obstruction
      hJ hk hdelay hobstruction
  linarith

/-- If a visible dyadic prefix beats the trivial finite-core payment by `c`,
then the scale-prime-support obstruction forces `c` into the reciprocal-prime
mass of the later core support. -/
theorem lt_scale_primeSupportMass_of_heavy_delayed_prefix_obstruction
    {A : Set ℕ} {N m K r : ℕ} {J : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      (K : ℝ) * corePrimeSupportPrimeReciprocalMass J)
    (hheavy : (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) + c <
      dyadicPrefixReciprocalMass A N m) :
    c < (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_scalePrimeSupport_of_delay_obstruction
      hJ hN hdelay hobstruction
  linarith

/-- Exact LCM-minimal version of the numerical delayed-shell obstruction.  For
minimal cores the finite-core payment is exactly the rank divided by `2^k`. -/
theorem CoprimeLCMSelection.LCMMinimal.shellMass_le_rank_div_pow_add_scalePrimeSupport_of_delay
    {A : Set ℕ} {k K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hk : 2 ≤ k)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    dyadicShellReciprocalMass A k ≤
      (r : ℝ) / (((2 ^ k : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  have hshell :=
    dyadicShellReciprocalMass_le_card_div_pow_add_scale_primeSupport_of_delay_obstruction
      hJ.1 hk hdelay hobstruction
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  simpa [hcard] using hshell

/-- Exact LCM-minimal prefix version of the numerical delayed obstruction. -/
theorem CoprimeLCMSelection.LCMMinimal.prefixMass_le_rank_div_pow_add_scalePrimeSupport
    {A : Set ℕ} {N m K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    dyadicPrefixReciprocalMass A N m ≤
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_scalePrimeSupport_of_delay_obstruction
      hJ.1 hN hdelay hobstruction
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  simpa [hcard] using hprefix

/-- Prior-witness form of the exact prefix obstruction.  If rank `r` was
already realized by `J₀` at an earlier scale, then an LCM-minimal bad core of
the same rank at scale `K` inherits any prefix headroom certified by `J₀`. -/
theorem CoprimeLCMSelection.LCMMinimal.prefixMass_le_rank_div_pow_add_scalePrimeSupport_of_prior
    {A : Set ℕ} {N m T K r : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hN : 2 ≤ N)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    dyadicPrefixReciprocalMass A N m ≤
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  exact hJ.prefixMass_le_rank_div_pow_add_scalePrimeSupport hN
    (hJ.delay_of_prior_selection hJ₀ hTK hdelay₀) hobstruction

/-- Exact LCM-minimal prefix version of the mixed small/large-prime delayed
obstruction.  The finite-core payment is exactly `r / 2^N`. -/
theorem CoprimeLCMSelection.LCMMinimal.prefixMass_le_rank_div_pow_add_mixedPrimeSupport
    {A : Set ℕ} {N m K r : ℕ} {J P : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J P +
        corePrimeSupportOutsideMultiplesBelowMass K J P) :
    dyadicPrefixReciprocalMass A N m ≤
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (lcmRoomPrimeSupportMassWithin A K J P +
          corePrimeSupportOutsideMultiplesBelowMass K J P) := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_mixedPrimeSupport_of_delay_obstruction
      hJ.1 hN hdelay hobstruction
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  simpa [hcard] using hprefix

/-- Prior-witness form of the mixed prefix obstruction.  If the same rank was
already realized earlier, minimality transfers that earlier LCM headroom to the
later bad core. -/
theorem CoprimeLCMSelection.LCMMinimal.prefixMass_le_rank_div_pow_add_mixedPrimeSupport_of_prior
    {A : Set ℕ} {N m T K r : ℕ} {J J₀ P : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hN : 2 ≤ N)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J P +
        corePrimeSupportOutsideMultiplesBelowMass K J P) :
    dyadicPrefixReciprocalMass A N m ≤
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (lcmRoomPrimeSupportMassWithin A K J P +
          corePrimeSupportOutsideMultiplesBelowMass K J P) := by
  exact hJ.prefixMass_le_rank_div_pow_add_mixedPrimeSupport hN
    (hJ.delay_of_prior_selection hJ₀ hTK hdelay₀) hobstruction

/-- Exact LCM-minimal prefix version of the standard cutoff obstruction. -/
theorem CoprimeLCMSelection.LCMMinimal.prefixMass_le_rank_div_pow_add_primesBelowBudget
    {A : Set ℕ} {N m K r M : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
        (K : ℝ) * ((K : ℝ) / (M : ℝ))) :
    dyadicPrefixReciprocalMass A N m ≤
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
          (K : ℝ) * ((K : ℝ) / (M : ℝ))) := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_primesBelowBudget_of_delay
      hJ.1 hN hdelay hobstruction
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  simpa [hcard] using hprefix

/-- Prior-witness form of the standard cutoff prefix obstruction. -/
theorem CoprimeLCMSelection.LCMMinimal.prefixMass_le_rank_div_pow_add_primesBelowBudget_of_prior
    {A : Set ℕ} {N m T K r M : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hN : 2 ≤ N)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
        (K : ℝ) * ((K : ℝ) / (M : ℝ))) :
    dyadicPrefixReciprocalMass A N m ≤
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
          (K : ℝ) * ((K : ℝ) / (M : ℝ))) := by
  exact hJ.prefixMass_le_rank_div_pow_add_primesBelowBudget hN
    (hJ.delay_of_prior_selection hJ₀ hTK hdelay₀) hobstruction

/-- The non-coprime cover generated by a positive finite core is contained in
the cover generated by the primes dividing the core. -/
theorem core_noncoprime_cover_subset_primeSupport_cover
    {J : Finset ℕ} (hJpos : ∀ a ∈ J, 0 < a) :
    (⋃ a ∈ J, {x | ¬ Nat.Coprime x a}) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  classical
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨a, haJ, hxa⟩
  rcases Nat.Prime.not_coprime_iff_dvd.mp hxa with ⟨p, hp, hpx, hpa⟩
  have hpJ : p ∈ corePrimeSupport J := by
    unfold corePrimeSupport
    rw [Finset.mem_biUnion]
    exact ⟨a, haJ, Nat.mem_primeFactors.mpr
      ⟨hp, hpa, ne_of_gt (hJpos a haJ)⟩⟩
  exact ⟨p, hpJ, hpx⟩

/-- Every selected core element has a prime divisor belonging to the core prime
support. -/
theorem CoprimeLCMSelection.exists_prime_mem_corePrimeSupport_dvd_of_mem
    {A : Set ℕ} {k r x : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) (hxJ : x ∈ J) :
    ∃ p ∈ corePrimeSupport J, p ∣ x := by
  have hxlarge : 4 ≤ x := hJ.2.2.2.2.1 x hxJ
  have hxne0 : x ≠ 0 := ne_of_gt (by omega)
  have hxne1 : x ≠ 1 := by omega
  rcases Nat.exists_prime_and_dvd hxne1 with ⟨p, hp, hpx⟩
  have hpSupport : p ∈ corePrimeSupport J := by
    unfold corePrimeSupport
    rw [Finset.mem_biUnion]
    exact ⟨x, hxJ, Nat.mem_primeFactors.mpr ⟨hp, hpx, hxne0⟩⟩
  exact ⟨p, hpSupport, hpx⟩

/-- A prime in the support of a core divides at least one selected core
element. -/
theorem exists_mem_dvd_of_mem_corePrimeSupport {J : Finset ℕ} {p : ℕ}
    (hpSupport : p ∈ corePrimeSupport J) :
    ∃ a ∈ J, p ∣ a := by
  classical
  unfold corePrimeSupport at hpSupport
  rw [Finset.mem_biUnion] at hpSupport
  rcases hpSupport with ⟨a, haJ, hpfa⟩
  exact ⟨a, haJ, Nat.dvd_of_mem_primeFactors hpfa⟩

/-- Every element of `corePrimeSupport J` is prime. -/
theorem prime_of_mem_corePrimeSupport {J : Finset ℕ} {p : ℕ}
    (hp : p ∈ corePrimeSupport J) :
    Nat.Prime p := by
  unfold corePrimeSupport at hp
  rw [Finset.mem_biUnion] at hp
  rcases hp with ⟨a, _haJ, hpa⟩
  exact Nat.prime_of_mem_primeFactors hpa

/-- In a pairwise-coprime selected core, a fixed prime can divide at most one
core element. -/
theorem CoprimeLCMSelection.eq_of_prime_dvd_of_mem
    {A : Set ℕ} {k r p a b : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) (hp : Nat.Prime p)
    (haJ : a ∈ J) (hbJ : b ∈ J) (hpa : p ∣ a) (hpb : p ∣ b) :
    a = b := by
  by_contra hne
  have hcop : Nat.Coprime a b := hJ.2.2.2.1 haJ hbJ hne
  have hnotcop : ¬ Nat.Coprime a b :=
    Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpa, hpb⟩
  exact hnotcop hcop

/-- A prime dividing a selected carrier is coprime to every support prime that
only appears after erasing that carrier. -/
theorem CoprimeLCMSelection.coprime_prime_of_dvd_mem_of_erased_support
    {A : Set ℕ} {k r p a ℓ : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hℓSupport : ℓ ∈ corePrimeSupport (J.erase a)) :
    Nat.Coprime p ℓ := by
  have hℓPrime : Nat.Prime ℓ := prime_of_mem_corePrimeSupport hℓSupport
  have hp_ne_ℓ : p ≠ ℓ := by
    intro hpℓ
    rcases exists_mem_dvd_of_mem_corePrimeSupport hℓSupport with
      ⟨b, hbErase, hℓb⟩
    have hbJ : b ∈ J := Finset.erase_subset a J hbErase
    have hb_ne_a : b ≠ a := (Finset.mem_erase.mp hbErase).1
    have ha_ne_b : a ≠ b := fun hab => hb_ne_a hab.symm
    have hcop : Nat.Coprime a b := hJ.2.2.2.1 haJ hbJ ha_ne_b
    have hpb : p ∣ b := by
      simpa [hpℓ] using hℓb
    have hnotcop : ¬ Nat.Coprime a b :=
      Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpa, hpb⟩
    exact hnotcop hcop
  exact (Nat.coprime_primes hp hℓPrime).mpr hp_ne_ℓ

/-- Small quotient lifts are forced into the erased-core prime support.  If
`p` divides the core carrier `a`, and a room lift `p*q` is still smaller than
`a`, then `p*q` could not have been coprime to `J.erase a`; the obstructing
prime cannot be `p`, so it divides `q` and belongs to the prime support of the
erased core. -/
theorem CoprimeLCMSelection.LCMMinimal.exists_erased_support_prime_dvd_of_small_room_quotient_lift
    {A : Set ℕ} {K r a p q : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hxRoom : p * q ∈ lcmRoomFinset A K J)
    (hsmall : p * q < a) :
    ∃ ℓ ∈ corePrimeSupport (J.erase a), ℓ ∣ q := by
  classical
  have hnot_replacement :
      ¬ ∀ b ∈ J.erase a, Nat.Coprime (p * q) b := by
    intro hcop
    have hle := hJ.le_mul_of_room_quotient_replacement haJ hxRoom hcop
    exact not_lt_of_ge hle hsmall
  rw [not_forall] at hnot_replacement
  rcases hnot_replacement with ⟨b, hb⟩
  rw [Classical.not_imp] at hb
  rcases hb with ⟨hbErase, hbNotCop⟩
  rcases Nat.Prime.not_coprime_iff_dvd.mp hbNotCop with
    ⟨ℓ, hℓPrime, hℓpq, hℓb⟩
  have hbJ : b ∈ J := Finset.erase_subset a J hbErase
  have hbne_a : b ≠ a := (Finset.mem_erase.mp hbErase).1
  have hℓSupport : ℓ ∈ corePrimeSupport (J.erase a) := by
    unfold corePrimeSupport
    rw [Finset.mem_biUnion]
    have hbpos : b ≠ 0 := by
      have hlarge : 4 ≤ b := hJ.1.2.2.2.2.1 b hbJ
      omega
    exact ⟨b, hbErase, Nat.mem_primeFactors.mpr ⟨hℓPrime, hℓb, hbpos⟩⟩
  have hℓ_ne_p : ℓ ≠ p := by
    intro hEq
    have hpb : p ∣ b := by
      simpa [hEq] using hℓb
    have hane_b : a ≠ b := by
      intro hab
      exact hbne_a hab.symm
    have hcop_ab : Nat.Coprime a b := hJ.1.2.2.2.1 haJ hbJ hane_b
    have hnotcop_ab : ¬ Nat.Coprime a b :=
      Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpa, hpb⟩
    exact hnotcop_ab hcop_ab
  have hℓ_not_dvd_p : ¬ ℓ ∣ p := by
    intro hℓp
    exact hℓ_ne_p ((Nat.prime_dvd_prime_iff_eq hℓPrime hp).mp hℓp)
  have hℓq : ℓ ∣ q := by
    rcases (Nat.Prime.dvd_mul hℓPrime).mp hℓpq with hℓp | hℓq
    · exact False.elim (hℓ_not_dvd_p hℓp)
    · exact hℓq
  exact ⟨ℓ, hℓSupport, hℓq⟩

/-- Finite-window form of the small-lift excision: after fixing the carrier
`a` of `p`, the subwindow with `p*q < a` is covered by primes from the erased
core. -/
theorem CoprimeLCMSelection.LCMMinimal.small_room_quotient_lifts_subset_erased_support_cover
    {A : Set ℕ} {K r a p : ℕ} {J Q : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) :
    (((Q.filter fun q => p * q < a) : Finset ℕ) : Set ℕ) ⊆
      ⋃ ℓ ∈ corePrimeSupport (J.erase a), {q | ℓ ∣ q} := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqQ, hsmall⟩
  rcases hJ.exists_erased_support_prime_dvd_of_small_room_quotient_lift
      haJ hp hpa (hQroom q hqQ) hsmall with
    ⟨ℓ, hℓSupport, hℓq⟩
  simp only [Set.mem_iUnion]
  exact ⟨ℓ, hℓSupport, hℓq⟩

/-- Quantitative small-lift excision.  The reciprocal mass of the small part
of a finite quotient window is bounded by the sum of its divisor slices over
the erased core's prime support. -/
theorem CoprimeLCMSelection.LCMMinimal.small_room_quotient_mass_le_erased_support_mass
    {A : Set ℕ} {K r a p : ℕ} {J Q : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) :
    (∑ q ∈ Q.filter (fun q => p * q < a), (1 : ℝ) / (q : ℝ)) ≤
      ∑ ℓ ∈ corePrimeSupport (J.erase a),
        ∑ q ∈ (Q.filter (fun q => p * q < a)).filter (fun q => ℓ ∣ q),
          (1 : ℝ) / (q : ℝ) := by
  classical
  let F : Finset ℕ := Q.filter fun q => p * q < a
  let I : Finset ℕ := corePrimeSupport (J.erase a)
  let B : ℕ → Set ℕ := fun ℓ => {q | ℓ ∣ q}
  have hcover : ∀ q ∈ F, ∃ ℓ ∈ I, q ∈ B ℓ := by
    intro q hq
    have hsubset := hJ.small_room_quotient_lifts_subset_erased_support_cover
      haJ hp hpa hQroom
    have hmem : q ∈ ⋃ ℓ ∈ I, B ℓ := by
      simpa [F, I, B] using hsubset hq
    simp only [Set.mem_iUnion] at hmem
    rcases hmem with ⟨ℓ, hℓI, hℓq⟩
    exact ⟨ℓ, hℓI, hℓq⟩
  simpa [F, I, B] using
    (finset_sum_le_sum_filter_of_cover
      (F := F) (I := I) (B := B)
      (w := fun q : ℕ => (1 : ℝ) / (q : ℝ))
      (fun q => one_div_nonneg.mpr (Nat.cast_nonneg q)) hcover)

/-- Carrier-aware small-room cover.  In an LCM-minimal core, any room element
smaller than a selected carrier `a` must be blocked by the erased core: if it
were coprime to `J.erase a`, it could replace `a` and lower the LCM. -/
theorem CoprimeLCMSelection.LCMMinimal.small_room_subset_erased_support_cover
    {A : Set ℕ} {K r a : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J) :
    ((((lcmRoomFinset A K J).filter fun x => x < a) : Finset ℕ) : Set ℕ) ⊆
      ⋃ ℓ ∈ corePrimeSupport (J.erase a), {x | ℓ ∣ x} := by
  classical
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxRoom, hxsmall⟩
  by_contra hxnotCover
  have hxcop : ∀ b ∈ J.erase a, Nat.Coprime x b := by
    intro b hb
    by_contra hnotcop
    rcases Nat.Prime.not_coprime_iff_dvd.mp hnotcop with
      ⟨ℓ, hℓPrime, hℓx, hℓb⟩
    have hbJ : b ∈ J := Finset.erase_subset a J hb
    have hbpos : b ≠ 0 := by
      have hlarge : 4 ≤ b := hJ.1.2.2.2.2.1 b hbJ
      omega
    have hℓSupport : ℓ ∈ corePrimeSupport (J.erase a) := by
      unfold corePrimeSupport
      rw [Finset.mem_biUnion]
      exact ⟨b, hb, Nat.mem_primeFactors.mpr ⟨hℓPrime, hℓb, hbpos⟩⟩
    have hxCover : x ∈ ⋃ ℓ ∈ corePrimeSupport (J.erase a), {x | ℓ ∣ x} := by
      simp only [Set.mem_iUnion]
      exact ⟨ℓ, hℓSupport, hℓx⟩
    exact hxnotCover hxCover
  have hle : a ≤ x := hJ.le_of_room_replacement haJ hxRoom hxcop
  exact (not_lt_of_ge hle) hxsmall

/-- Carrier-aware local split for a quotient window.  Fix a carrier `a ∈ J`
and a prime `p ∣ a`.  Small lifts `p*q < a` are forced into the erased-core
prime support by LCM minimality.  The complementary large lifts `a ≤ p*q`
lie in the tail above `a`, so in every length-`a` window their lifts satisfy
the residue-packing half-modulus bound. -/
theorem CoprimeLCMSelection.LCMMinimal.carrier_quotient_window_split
    {A : Set ℕ} (hA : AvoidingSet A)
    {K r a p : ℕ} {J Q : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) :
    (((Q.filter fun q => p * q < a) : Finset ℕ) : Set ℕ) ⊆
        ⋃ ℓ ∈ corePrimeSupport (J.erase a), {q | ℓ ∣ q} ∧
      ∀ X : ℕ,
        (Q.filter fun q => a ≤ p * q ∧ p * q ∈ Set.Ico X (X + a)).card ≤
          a / 2 + 1 := by
  classical
  constructor
  · exact hJ.small_room_quotient_lifts_subset_erased_support_cover
      haJ hp hpa hQroom
  · intro X
    let Qlarge : Finset ℕ :=
      Q.filter fun q => a ≤ p * q ∧ p * q ∈ Set.Ico X (X + a)
    let F : Finset ℕ := Qlarge.image fun q => p * q
    have hcard_image : F.card = Qlarge.card := by
      dsimp [F]
      rw [Finset.card_image_of_injOn]
      intro q hq q' hq' hqq'
      exact Nat.mul_left_cancel hp.pos hqq'
    have hsub : F ⊆ tailWindowFinset A a X := by
      intro x hxF
      rcases Finset.mem_image.mp hxF with ⟨q, hqLarge, rfl⟩
      rcases Finset.mem_filter.mp hqLarge with ⟨hqQ, hq⟩
      rcases hq with ⟨hlarge, hIco⟩
      rcases mem_lcmRoomFinset.mp (hQroom q hqQ) with
        ⟨_hxlarge, _hxlt, hxA, hxnotJ, _hxroom⟩
      have hne : a ≠ p * q := by
        intro haeq
        exact hxnotJ (by simpa [haeq] using haJ)
      have htail : p * q ∈ tailAbove A a := ⟨hxA, lt_of_le_of_ne hlarge hne⟩
      exact mem_tailWindowFinset.mpr ⟨hIco, htail⟩
    have haA : a ∈ A := hJ.1.1 a haJ
    have hapos : 0 < a := by
      have hlarge : 4 ≤ a := hJ.1.2.2.2.2.1 a haJ
      omega
    calc
      Qlarge.card = F.card := hcard_image.symm
      _ ≤ (tailWindowFinset A a X).card := Finset.card_le_card hsub
      _ ≤ a / 2 + 1 := hA.tailWindow_card_le haA hapos X

/-- Scale-window version of the large-lift side of the carrier split.  For a
fixed carrier `a`, all room quotients whose lift lies above `a` are sparse
across the full dyadic room: their lifts sit in the tail above `a` and below
`2^K`, so the residue-packing window cover gives a half-modulus count in each
length-`a` window. -/
theorem CoprimeLCMSelection.LCMMinimal.carrier_large_quotient_card_le_scale_cover
    {A : Set ℕ} (hA : AvoidingSet A)
    {K r a p : ℕ} {J Q : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p)
    (hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) :
    (Q.filter fun q => a ≤ p * q).card ≤
      (a / 2 + 1) * ((2 ^ K) / a + 1) := by
  classical
  let Qlarge : Finset ℕ := Q.filter fun q => a ≤ p * q
  let F : Finset ℕ := Qlarge.image fun q => p * q
  have hcard_image : F.card = Qlarge.card := by
    dsimp [F]
    rw [Finset.card_image_of_injOn]
    intro q _hq q' _hq' hqq'
    exact Nat.mul_left_cancel hp.pos hqq'
  have haA : a ∈ A := hJ.1.1 a haJ
  have hapos : 0 < a := by
    have hlarge : 4 ≤ a := hJ.1.2.2.2.2.1 a haJ
    omega
  let I : Finset Unit := {()}
  let m : Unit → ℕ := fun _ => a
  have hmA : ∀ i ∈ I, m i ∈ A := by
    intro _i _hi
    exact haA
  have hmpos : ∀ i ∈ I, 0 < m i := by
    intro _i _hi
    exact hapos
  have hFtail : ∀ i ∈ I, ∀ n ∈ F, n ∈ tailAbove A (m i) := by
    intro _i _hi n hnF
    rcases Finset.mem_image.mp hnF with ⟨q, hqLarge, rfl⟩
    rcases Finset.mem_filter.mp hqLarge with ⟨hqQ, hlarge⟩
    rcases mem_lcmRoomFinset.mp (hQroom q hqQ) with
      ⟨_hxlarge, _hxlt, hxA, hxnotJ, _hxroom⟩
    have hne : a ≠ p * q := by
      intro haeq
      exact hxnotJ (by simpa [haeq] using haJ)
    exact ⟨hxA, lt_of_le_of_ne hlarge hne⟩
  have hFIco : ∀ n ∈ F, n ∈ Set.Ico 0 (0 + 2 ^ K) := by
    intro n hnF
    rcases Finset.mem_image.mp hnF with ⟨q, hqLarge, rfl⟩
    rcases Finset.mem_filter.mp hqLarge with ⟨hqQ, _hlarge⟩
    rcases mem_lcmRoomFinset.mp (hQroom q hqQ) with
      ⟨_hxlarge, hxlt, _hxA, _hxnotJ, _hxroom⟩
    exact ⟨Nat.zero_le _, by simpa using hxlt⟩
  have hcardF := hA.finset_card_le_multi_tail_moduli_of_subset_Ico_lcm_cover
    (J := I) (m := m) (F := F) (X := 0) (H := 2 ^ K)
    hmA hmpos hFtail hFIco
  have hcard :
      Qlarge.card ≤ (a / 2 + 1) * ((2 ^ K) / a + 1) := by
    rw [← hcard_image]
    simpa [I, m] using hcardF
  simpa [Qlarge] using hcard

/-- A pairwise-coprime selected core has at least as many support primes as core
elements: choose one prime divisor from each selected element; pairwise
coprimality makes those chosen primes distinct. -/
theorem CoprimeLCMSelection.card_le_corePrimeSupport_card
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) :
    J.card ≤ (corePrimeSupport J).card := by
  classical
  let pOf : ℕ → ℕ := fun a =>
    if ha : a ∈ J then
      Classical.choose (hJ.exists_prime_mem_corePrimeSupport_dvd_of_mem ha)
    else 0
  refine Finset.card_le_card_of_injOn pOf ?maps ?inj
  · intro a ha
    have haF : a ∈ J := by simpa using ha
    dsimp [pOf]
    rw [dif_pos haF]
    exact (Classical.choose_spec
      (hJ.exists_prime_mem_corePrimeSupport_dvd_of_mem haF)).1
  · intro a ha b hb hp_eq
    have haF : a ∈ J := by simpa using ha
    have hbF : b ∈ J := by simpa using hb
    by_contra hne
    have hcop : Nat.Coprime a b := hJ.2.2.2.1 haF hbF hne
    have hpaSupport : pOf a ∈ corePrimeSupport J := by
      dsimp [pOf]
      rw [dif_pos haF]
      exact (Classical.choose_spec
        (hJ.exists_prime_mem_corePrimeSupport_dvd_of_mem haF)).1
    have hpa_dvd_a : pOf a ∣ a := by
      dsimp [pOf]
      rw [dif_pos haF]
      exact (Classical.choose_spec
        (hJ.exists_prime_mem_corePrimeSupport_dvd_of_mem haF)).2
    have hpb_dvd_b : pOf b ∣ b := by
      dsimp [pOf]
      rw [dif_pos hbF]
      exact (Classical.choose_spec
        (hJ.exists_prime_mem_corePrimeSupport_dvd_of_mem hbF)).2
    have hpa_dvd_b : pOf a ∣ b := by
      simpa [hp_eq] using hpb_dvd_b
    have hpPrime : Nat.Prime (pOf a) := prime_of_mem_corePrimeSupport hpaSupport
    have hnotcop : ¬ Nat.Coprime a b :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨pOf a, hpPrime, hpa_dvd_a, hpa_dvd_b⟩
    exact hnotcop hcop

/-- Rank version of the support-prime lower bound.  Any rank-`r` selection uses
at least `r` distinct prime divisors across its core. -/
theorem CoprimeLCMSelection.rank_le_corePrimeSupport_card
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) :
    r ≤ (corePrimeSupport J).card :=
  hJ.2.2.2.2.2.trans hJ.card_le_corePrimeSupport_card

/-- Distinct primes in the core support are pairwise coprime. -/
theorem corePrimeSupport_pairwise_coprime (J : Finset ℕ) :
    ((corePrimeSupport J : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun p : ℕ => p) := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes
    (prime_of_mem_corePrimeSupport hp)
    (prime_of_mem_corePrimeSupport hq)).mpr hpq

/-- The same pairwise-coprimality statement in `IsRelPrime` form, which is
the form needed by Mathlib's product-divisibility lemma. -/
theorem corePrimeSupport_pairwise_isRelPrime (J : Finset ℕ) :
    ((corePrimeSupport J : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun IsRelPrime fun p : ℕ => p) := by
  intro p hp q hq hpq
  exact Nat.coprime_iff_isRelPrime.mp
    (corePrimeSupport_pairwise_coprime J hp hq hpq)

/-- Every prime in the core support divides the core LCM. -/
theorem corePrimeSupport_dvd_lcm {J : Finset ℕ} {p : ℕ}
    (hp : p ∈ corePrimeSupport J) :
    p ∣ J.lcm (fun a : ℕ => a) := by
  unfold corePrimeSupport at hp
  rw [Finset.mem_biUnion] at hp
  rcases hp with ⟨a, haJ, hpa⟩
  exact (Nat.dvd_of_mem_primeFactors hpa).trans (Finset.dvd_lcm haJ)

/-- If `p` divides a selected carrier `a` and `ℓ` belongs to the erased support,
then the composite divisor `p * ℓ` is part of the current core LCM. -/
theorem CoprimeLCMSelection.mul_erasedSupport_dvd_lcm
    {A : Set ℕ} {k r p a ℓ : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hℓSupport : ℓ ∈ corePrimeSupport (J.erase a)) :
    p * ℓ ∣ J.lcm (fun y : ℕ => y) := by
  have hp_dvd_lcm : p ∣ J.lcm (fun y : ℕ => y) :=
    hpa.trans (Finset.dvd_lcm haJ)
  have hℓ_dvd_lcm : ℓ ∣ J.lcm (fun y : ℕ => y) :=
    corePrimeSupport_dvd_lcm (corePrimeSupport_erase_subset J a hℓSupport)
  exact (hJ.coprime_prime_of_dvd_mem_of_erased_support
    haJ hp hpa hℓSupport).mul_dvd_of_dvd_of_dvd hp_dvd_lcm hℓ_dvd_lcm

/-- If a selected carrier `a` has self-headroom and `p ∣ a`, then the fresh
prime `p` must satisfy the square-size restriction `p^2 ≤ 2^K`. -/
theorem CoprimeLCMSelection.prime_sq_le_two_pow_of_carrier_headroom
    {A : Set ℕ} {K r p a : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J) (haJ : a ∈ J)
    (_hp : Nat.Prime p) (hpa : p ∣ a)
    (hheadroom : J.lcm (fun y : ℕ => y) * a ≤ 2 ^ K) :
    p * p ≤ 2 ^ K := by
  have hp_dvd_lcm : p ∣ J.lcm (fun y : ℕ => y) :=
    hpa.trans (Finset.dvd_lcm haJ)
  have hp2_dvd : p * p ∣ J.lcm (fun y : ℕ => y) * a :=
    mul_dvd_mul hp_dvd_lcm hpa
  have hprod_pos : 0 < J.lcm (fun y : ℕ => y) * a := by
    have hlcm_pos : 0 < J.lcm (fun y : ℕ => y) := by
      exact finset_lcm_pos_of_forall_pos fun y hy =>
        Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
          (hJ.2.2.2.2.1 y hy)
    have ha_pos : 0 < a := by
      have ha_large : 4 ≤ a := hJ.2.2.2.2.1 a haJ
      omega
    exact Nat.mul_pos hlcm_pos ha_pos
  exact (Nat.le_of_dvd hprod_pos hp2_dvd).trans hheadroom

/-- A localized composite-budget branch uses a composite divisor already below
the dyadic scale: if `p` divides the carrier and `ℓ` belongs to the erased
support, then `p * ℓ ≤ 2^K`. -/
theorem CoprimeLCMSelection.mul_erasedSupport_le_two_pow
    {A : Set ℕ} {K r p a ℓ : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hℓSupport : ℓ ∈ corePrimeSupport (J.erase a)) :
    p * ℓ ≤ 2 ^ K := by
  have hLpos : 0 < J.lcm (fun y : ℕ => y) := by
    exact finset_lcm_pos_of_forall_pos fun y hy =>
      Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
        (hJ.2.2.2.2.1 y hy)
  exact (Nat.le_of_dvd hLpos
    (hJ.mul_erasedSupport_dvd_lcm haJ hp hpa hℓSupport)).trans
      hJ.2.2.1

/-- If `p > 2^B` and `p^2 ≤ 2^K`, then the dyadic scale has doubled past
`B`: `B + B < K`. -/
theorem add_lt_scale_of_two_pow_lt_of_sq_le_two_pow
    {B K p : ℕ} (hp : 2 ^ B < p) (hsq : p * p ≤ 2 ^ K) :
    B + B < K := by
  have hp_pos : 0 < p := (by positivity : 0 < 2 ^ B).trans hp
  have hleft : 2 ^ B * 2 ^ B < p * 2 ^ B := by
    exact (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ B)).mpr hp
  have hright : p * 2 ^ B < p * p := (Nat.mul_lt_mul_left hp_pos).mpr hp
  have hpow : 2 ^ (B + B) < 2 ^ K := by
    rw [pow_add]
    exact (hleft.trans hright).trans_le hsq
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow

/-- If a composite divisor `p * ℓ` lies below `2^K`, `ℓ` is positive, and
`p > 2^B`, then `B < K`. -/
theorem lt_scale_of_two_pow_lt_of_mul_le_two_pow
    {B K p ℓ : ℕ} (hp : 2 ^ B < p) (hℓpos : 0 < ℓ)
    (hle : p * ℓ ≤ 2 ^ K) :
    B < K := by
  have hp_le_mul : p ≤ p * ℓ := Nat.le_mul_of_pos_right p hℓpos
  have hpow : 2 ^ B < 2 ^ K := hp.trans_le (hp_le_mul.trans hle)
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow

/-- A later LCM-minimal core with an earlier witness of the same rank can use
only primes up to the earlier witness's LCM.  This is the finite-prime universe
behind the fixed-rank induction step. -/
theorem CoprimeLCMSelection.LCMMinimal.corePrimeSupport_subset_primesBelow_lcm_of_prior_selection
    {A : Set ℕ} {T K r : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K) :
    corePrimeSupport J ⊆
      (Finset.Icc 2 (J₀.lcm fun a : ℕ => a)).filter fun p => Nat.Prime p := by
  intro p hpSupport
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  have hpDvd : p ∣ J.lcm fun a : ℕ => a :=
    corePrimeSupport_dvd_lcm hpSupport
  have hLpos : 0 < J.lcm fun a : ℕ => a := by
    exact finset_lcm_pos_of_forall_pos fun a ha =>
      Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
        (hJ.1.2.2.2.2.1 a ha)
  have hp_le_lcm : p ≤ J.lcm fun a : ℕ => a :=
    Nat.le_of_dvd hLpos hpDvd
  have hp_le_lcm₀ : p ≤ J₀.lcm fun a : ℕ => a :=
    hp_le_lcm.trans (hJ.lcm_le_of_prior_selection hJ₀ hTK)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, hp_le_lcm₀⟩, hpPrime⟩

/-- A valid scale-`k` core can only use support primes below the dyadic LCM
budget `2^k`. -/
theorem CoprimeLCMSelection.corePrimeSupport_subset_primesBelow_scale
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) :
    corePrimeSupport J ⊆
      (Finset.Icc 2 (2 ^ k)).filter fun p => Nat.Prime p := by
  intro p hpSupport
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  have hpDvd : p ∣ J.lcm fun a : ℕ => a :=
    corePrimeSupport_dvd_lcm hpSupport
  have hLpos : 0 < J.lcm fun a : ℕ => a := by
    exact finset_lcm_pos_of_forall_pos fun a ha =>
      Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
        (hJ.2.2.2.2.1 a ha)
  have hp_le_lcm : p ≤ J.lcm fun a : ℕ => a :=
    Nat.le_of_dvd hLpos hpDvd
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, hp_le_lcm.trans hJ.2.2.1⟩,
      hpPrime⟩

/-- Monotone version of the dyadic support-prime universe. -/
theorem CoprimeLCMSelection.corePrimeSupport_subset_primesBelow_scale_le
    {A : Set ℕ} {k r B : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) (hkB : k ≤ B) :
    corePrimeSupport J ⊆
      (Finset.Icc 2 (2 ^ B)).filter fun p => Nat.Prime p := by
  intro p hpSupport
  rcases Finset.mem_filter.mp
      (hJ.corePrimeSupport_subset_primesBelow_scale hpSupport) with
    ⟨hpIcc, hpPrime⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp2, hp_le_pow⟩
  have hpow : 2 ^ k ≤ 2 ^ B :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hkB
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hp2, hp_le_pow.trans hpow⟩, hpPrime⟩

/-- The product of all support primes divides the core LCM.  This records the
LCM budget spent by distinct prime divisors, regardless of multiplicity. -/
theorem corePrimeSupport_prod_dvd_lcm (J : Finset ℕ) :
    (∏ p ∈ corePrimeSupport J, p) ∣ J.lcm (fun a : ℕ => a) := by
  exact Finset.prod_dvd_of_isRelPrime
    (corePrimeSupport_pairwise_isRelPrime J)
    (fun p hp => corePrimeSupport_dvd_lcm hp)

/-- The core-prime-support product is positive. -/
theorem corePrimeSupport_prod_pos (J : Finset ℕ) :
    0 < ∏ p ∈ corePrimeSupport J, p := by
      exact Finset.prod_pos fun p hp => (prime_of_mem_corePrimeSupport hp).pos

/-- A positive LCM bounds the product of all support primes. -/
theorem corePrimeSupport_prod_le_lcm_of_lcm_pos {J : Finset ℕ}
    (hLpos : 0 < J.lcm (fun a : ℕ => a)) :
    (∏ p ∈ corePrimeSupport J, p) ≤ J.lcm (fun a : ℕ => a) :=
  Nat.le_of_dvd hLpos (corePrimeSupport_prod_dvd_lcm J)

/-- For a valid core at scale `k`, the product of its distinct prime divisors
is at most the dyadic LCM budget `2^k`. -/
theorem CoprimeLCMSelection.corePrimeSupport_prod_le_two_pow
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) :
    (∏ p ∈ corePrimeSupport J, p) ≤ 2 ^ k := by
  have hLpos : 0 < J.lcm (fun a : ℕ => a) := by
    exact finset_lcm_pos_of_forall_pos fun a ha =>
      Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
        (hJ.2.2.2.2.1 a ha)
  exact (corePrimeSupport_prod_le_lcm_of_lcm_pos hLpos).trans hJ.2.2.1

/-- Product pressure from support primes outside a finite box.  If every
outside support prime is at least `Q`, then `Q` to the number of outside
support primes is still bounded by the dyadic LCM budget. -/
theorem CoprimeLCMSelection.pow_outsideSupport_card_le_two_pow
    {A : Set ℕ} {k r Q : ℕ} {J P : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J)
    (hlarge :
      ∀ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P), Q ≤ p) :
    Q ^ ((corePrimeSupport J).filter (fun p => p ∉ P)).card ≤ 2 ^ k := by
  classical
  let S : Finset ℕ := (corePrimeSupport J).filter (fun p => p ∉ P)
  calc
    Q ^ S.card = ∏ _p ∈ S, Q := by
      rw [Finset.prod_const]
    _ ≤ ∏ p ∈ S, p := by
      exact Finset.prod_le_prod
        (fun _p _hp => Nat.zero_le Q)
        (fun p hp => hlarge p hp)
    _ ≤ ∏ p ∈ corePrimeSupport J, p := by
      exact Finset.prod_le_prod_of_subset_of_one_le'
        (Finset.filter_subset (fun p => p ∉ P) (corePrimeSupport J))
        (fun p hp _hpnot =>
          Nat.succ_le_of_lt (prime_of_mem_corePrimeSupport hp).pos)
    _ ≤ 2 ^ k := hJ.corePrimeSupport_prod_le_two_pow

/-- Since every support prime is at least `2`, the support product is at least
`2` to the number of support primes. -/
theorem two_pow_card_corePrimeSupport_le_prod (J : Finset ℕ) :
    2 ^ (corePrimeSupport J).card ≤ ∏ p ∈ corePrimeSupport J, p := by
  calc
    2 ^ (corePrimeSupport J).card =
        ∏ _p ∈ corePrimeSupport J, (2 : ℕ) := by
      rw [Finset.prod_const]
    _ ≤ ∏ p ∈ corePrimeSupport J, p := by
      exact Finset.prod_le_prod
        (fun _p _hp => by norm_num)
        (fun p hp => (prime_of_mem_corePrimeSupport hp).two_le)

/-- Any valid core at scale `k` has at most `k` distinct support primes. -/
theorem CoprimeLCMSelection.corePrimeSupport_card_le_scale
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A k r J) :
    (corePrimeSupport J).card ≤ k := by
  have hpow :
      2 ^ (corePrimeSupport J).card ≤ 2 ^ k :=
    (two_pow_card_corePrimeSupport_le_prod J).trans
      hJ.corePrimeSupport_prod_le_two_pow
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow

/-- Delayed prior headroom leaves only `K - (m+1)` dyadic exponents for the
support-prime product.  Equivalently, the support-cardinality budget plus the
visible prefix length is bounded by the later scale. -/
theorem CoprimeLCMSelection.LCMMinimal.corePrimeSupport_card_add_delay_le_scale_of_prior
    {A : Set ℕ} {T K r m : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K) :
    (corePrimeSupport J).card + (m + 1) ≤ K := by
  have hdelayJ : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K :=
    hJ.delay_of_prior_selection hJ₀ hTK hdelay₀
  have hLpos : 0 < J.lcm (fun a : ℕ => a) := by
    exact finset_lcm_pos_of_forall_pos fun a ha =>
      Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
        (hJ.1.2.2.2.2.1 a ha)
  have hprod_le_lcm :
      (∏ p ∈ corePrimeSupport J, p) ≤ J.lcm (fun a : ℕ => a) :=
    corePrimeSupport_prod_le_lcm_of_lcm_pos hLpos
  have hprod_delay :
      (∏ p ∈ corePrimeSupport J, p) * 2 ^ (m + 1) ≤ 2 ^ K :=
    (Nat.mul_le_mul_right _ hprod_le_lcm).trans hdelayJ
  have htwo_delay :
      2 ^ (corePrimeSupport J).card * 2 ^ (m + 1) ≤ 2 ^ K :=
    (Nat.mul_le_mul_right _ (two_pow_card_corePrimeSupport_le_prod J)).trans
      hprod_delay
  have hpow : 2 ^ ((corePrimeSupport J).card + (m + 1)) ≤ 2 ^ K := by
    rw [pow_add]
    exact htwo_delay
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow

/-- A prime-divisor layer inside an LCM-room is bounded by the absolute mass of
all multiples of that divisor below the same dyadic cap. -/
theorem lcmRoomPrimeDivisorMass_le_multiplesBelowReciprocalMass
    (A : Set ℕ) (k : ℕ) (J : Finset ℕ) (p : ℕ) :
    lcmRoomPrimeDivisorMass A k J p ≤ multiplesBelowReciprocalMass k p := by
  unfold lcmRoomPrimeDivisorMass multiplesBelowReciprocalMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
  · intro x hx
    have hxRoom : x ∈ lcmRoomFinset A k J := (Finset.mem_filter.mp hx).1
    have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
    rcases mem_lcmRoomFinset.mp hxRoom with ⟨hxlarge, hxlt, _hxA, _hxnot, _hxroom⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by omega, hxlt⟩, hpx⟩
  · intro x _hxTarget _hxSource
    exact one_div_nonneg.mpr (Nat.cast_nonneg x)

/-- Below-scale prime-divisor mass is nonnegative. -/
theorem belowScalePrimeDivisorMass_nonneg (A : Set ℕ) (k p : ℕ) :
    0 ≤ belowScalePrimeDivisorMass A k p := by
  classical
  unfold belowScalePrimeDivisorMass
  exact Finset.sum_nonneg fun x _hx =>
    one_div_nonneg.mpr (Nat.cast_nonneg x)

/-- An LCM-room prime-divisor layer is bounded by the actual below-scale
multiple-layer mass for that divisor. -/
theorem lcmRoomPrimeDivisorMass_le_belowScalePrimeDivisorMass
    (A : Set ℕ) (k : ℕ) (J : Finset ℕ) (p : ℕ) :
    lcmRoomPrimeDivisorMass A k J p ≤
      belowScalePrimeDivisorMass A k p := by
  classical
  unfold lcmRoomPrimeDivisorMass belowScalePrimeDivisorMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
  · intro x hx
    have hxRoom : x ∈ lcmRoomFinset A k J := (Finset.mem_filter.mp hx).1
    have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
    rcases mem_lcmRoomFinset.mp hxRoom with ⟨hxlarge, hxlt, hxA, _hxnot, _hxroom⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by omega, hxlt⟩, hxA, hpx⟩
  · intro x _hxTarget _hxSource
    exact one_div_nonneg.mpr (Nat.cast_nonneg x)

/-- The actual small-prime capture in an LCM-room is bounded by the full
below-scale mass of those primes in `A`. -/
theorem lcmRoomPrimeSupportMassWithin_le_belowScalePrimeSupportMass
    (A : Set ℕ) (k : ℕ) (J P : Finset ℕ) :
    lcmRoomPrimeSupportMassWithin A k J P ≤
      belowScalePrimeSupportMass A k P := by
  unfold lcmRoomPrimeSupportMassWithin belowScalePrimeSupportMass
  calc
    (∑ p ∈ (corePrimeSupport J).filter (fun p => p ∈ P),
        lcmRoomPrimeDivisorMass A k J p) ≤
        ∑ p ∈ (corePrimeSupport J).filter (fun p => p ∈ P),
          belowScalePrimeDivisorMass A k p := by
      exact Finset.sum_le_sum fun p _hp =>
        lcmRoomPrimeDivisorMass_le_belowScalePrimeDivisorMass A k J p
    _ ≤ ∑ p ∈ P, belowScalePrimeDivisorMass A k p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p _hpP _hpMissing
        exact belowScalePrimeDivisorMass_nonneg A k p

/-- Splitting a moving prime universe `Q` into a fixed old part `P` and the
fresh part outside `P` bounds the captured room mass by the sum of those two
pieces. -/
theorem lcmRoomPrimeSupportMassWithin_le_within_add_fresh
    (A : Set ℕ) (k : ℕ) (J P Q : Finset ℕ) :
    lcmRoomPrimeSupportMassWithin A k J Q ≤
      lcmRoomPrimeSupportMassWithin A k J P +
        lcmRoomPrimeSupportMassWithin A k J (Q.filter fun p => p ∉ P) := by
  classical
  unfold lcmRoomPrimeSupportMassWithin
  let S := corePrimeSupport J
  let w : ℕ → ℝ := fun p => lcmRoomPrimeDivisorMass A k J p
  have hsplit :
      (∑ p ∈ S.filter (fun p => p ∈ Q), w p) =
        (∑ p ∈ (S.filter (fun p => p ∈ Q)).filter (fun p => p ∈ P), w p) +
          ∑ p ∈ (S.filter (fun p => p ∈ Q)).filter (fun p => p ∉ P), w p := by
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter fun p => p ∈ Q)
      (fun p => p ∈ P) w]
  have hold :
      (∑ p ∈ (S.filter (fun p => p ∈ Q)).filter (fun p => p ∈ P), w p) ≤
        ∑ p ∈ S.filter (fun p => p ∈ P), w p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1.1, hp.2⟩
    · intro p _hpOld _hpMissing
      exact lcmRoomPrimeDivisorMass_nonneg A k J p
  have hfresh_eq :
      (∑ p ∈ (S.filter (fun p => p ∈ Q)).filter (fun p => p ∉ P), w p) =
        ∑ p ∈ S.filter (fun p => p ∈ Q.filter (fun p => p ∉ P)), w p := by
    refine Finset.sum_congr ?seteq ?same
    · ext p
      simp only [Finset.mem_filter]
      tauto
    · intro p _hp
      rfl
  calc
    (∑ p ∈ S.filter (fun p => p ∈ Q), w p)
        = (∑ p ∈ (S.filter (fun p => p ∈ Q)).filter (fun p => p ∈ P), w p) +
            ∑ p ∈ (S.filter (fun p => p ∈ Q)).filter (fun p => p ∉ P), w p := hsplit
    _ ≤ (∑ p ∈ S.filter (fun p => p ∈ P), w p) +
          ∑ p ∈ (S.filter (fun p => p ∈ Q)).filter (fun p => p ∉ P), w p := add_le_add hold le_rfl
    _ = (∑ p ∈ S.filter (fun p => p ∈ P), w p) +
          ∑ p ∈ S.filter (fun p => p ∈ Q.filter (fun p => p ∉ P)), w p := by
      rw [hfresh_eq]

/-- Exact old/fresh split for prime-support capture in an LCM-room. -/
theorem lcmRoomPrimeSupportMass_le_within_add_freshMass
    (A : Set ℕ) (k : ℕ) (J P : Finset ℕ) :
    lcmRoomPrimeSupportMass A k J ≤
      lcmRoomPrimeSupportMassWithin A k J P +
        lcmRoomFreshPrimeSupportMass A k J P := by
  classical
  unfold lcmRoomPrimeSupportMass lcmRoomPrimeSupportMassWithin
    lcmRoomFreshPrimeSupportMass
  rw [← Finset.sum_filter_add_sum_filter_not (corePrimeSupport J)
    (fun p => p ∈ P)]

/-- If the actual fresh support-prime mass in the LCM-room is larger than `c`
per available scale slot, then one fresh support prime has room-divisor mass
larger than `c`. -/
theorem exists_fresh_lt_lcmRoomPrimeDivisorMass_of_freshMass_scale
    {A : Set ℕ} {K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J)
    (hc_nonneg : 0 ≤ c)
    (hlarge : (K : ℝ) * c <
      lcmRoomFreshPrimeSupportMass A K J P) :
    ∃ p ∈ corePrimeSupport J, p ∉ P ∧
      c < lcmRoomPrimeDivisorMass A K J p := by
  classical
  let S : Finset ℕ := (corePrimeSupport J).filter (fun p => p ∉ P)
  let w : ℕ → ℝ := fun p => lcmRoomPrimeDivisorMass A K J p
  by_contra hnone
  have hpoint : ∀ p, p ∈ S → w p ≤ c := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpP⟩
    by_contra hle
    exact hnone ⟨p, hpSupport, hpP, lt_of_not_ge hle⟩
  have hsum_le_card : (∑ p ∈ S, w p) ≤ (S.card : ℝ) * c := by
    have hsum_le : (∑ p ∈ S, w p) ≤ ∑ _p ∈ S, c := Finset.sum_le_sum fun p hp => hpoint p hp
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum_le
  have hcard_nat : S.card ≤ K := by
    have hsub : S ⊆ corePrimeSupport J := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    exact (Finset.card_le_card hsub).trans hJ.corePrimeSupport_card_le_scale
  have hcard_real : (S.card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hcard_nat
  have hcard_mul : (S.card : ℝ) * c ≤ (K : ℝ) * c :=
    mul_le_mul_of_nonneg_right hcard_real hc_nonneg
  have hfresh_le : lcmRoomFreshPrimeSupportMass A K J P ≤ (K : ℝ) * c := by
    have hfresh_le_card :
        lcmRoomFreshPrimeSupportMass A K J P ≤ (S.card : ℝ) * c := by
      simpa [lcmRoomFreshPrimeSupportMass, S, w] using hsum_le_card
    linarith
  linarith

/-- If a fixed multiple layer is reciprocally summable, its actual below-scale
prime-divisor mass is bounded by the corresponding reciprocal-indicator tsum. -/
theorem belowScalePrimeDivisorMass_le_tsum_indicator_multipleLayer
    {A : Set ℕ} {k p : ℕ}
    (hLayer : ReciprocalSummable (multipleLayer p A)) :
    belowScalePrimeDivisorMass A k p ≤
      ∑' n : ℕ, reciprocalIndicator (multipleLayer p A) n := by
  classical
  unfold belowScalePrimeDivisorMass
  exact finset_sum_reciprocal_le_tsum_indicator_of_subset hLayer
    (fun x hx => by
      rcases Finset.mem_filter.mp hx with ⟨_hxIco, hxA, hpx⟩
      exact ⟨hxA, hpx⟩)

/-- Finite-set version of the previous bound. -/
theorem belowScalePrimeSupportMass_le_tsum_indicator_multipleLayers
    {A : Set ℕ} {k : ℕ} {P : Finset ℕ}
    (hLayer : ∀ p ∈ P, ReciprocalSummable (multipleLayer p A)) :
    belowScalePrimeSupportMass A k P ≤
      ∑ p ∈ P, ∑' n : ℕ, reciprocalIndicator (multipleLayer p A) n := by
  unfold belowScalePrimeSupportMass
  exact Finset.sum_le_sum fun p hp =>
    belowScalePrimeDivisorMass_le_tsum_indicator_multipleLayer
      (hLayer p hp)

/-- Dividing the `d`-multiple layer by `d` gives exactly the same quotient set
as dividing `A` by `d`: the extra divisibility condition is automatic for
elements of the form `d * q`. -/
theorem quotientSet_multipleLayer_eq (A : Set ℕ) (d : ℕ) :
    quotientSet d (multipleLayer d A) = quotientSet d A := by
  ext n
  simp [quotientSet, multipleLayer]

/-- Nested quotients compose multiplicatively. -/
theorem quotientSet_quotientSet_eq (A : Set ℕ) (d e : ℕ) :
    quotientSet e (quotientSet d A) = quotientSet (d * e) A := by
  ext n
  simp [quotientSet, Nat.mul_assoc]

/-- In a quotient-irreducible counterexample, every fixed prime multiple layer
is reciprocally summable. -/
theorem SummabilityCounterexample.reciprocalSummable_multipleLayer_prime_of_quotient_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {p : ℕ} (hp : Nat.Prime p) :
    ReciprocalSummable (multipleLayer p A) := by
  have hnon :
      ReciprocalSummable (noncoprimeLayer p A) :=
    hA.reciprocalSummable_noncoprimeLayer_of_quotient_irreducible
      hirred hp.pos
  exact hnon.mono fun n hn =>
    ⟨hn.1, Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hp, hn.2, dvd_rfl⟩⟩

/-- In a quotient-irreducible counterexample, every fixed prime quotient layer
is reciprocally summable.  Otherwise the quotient itself would be a smaller
counterexample, and the identity `quotientSet p (multipleLayer p A) =
quotientSet p A` would violate irreducibility. -/
theorem SummabilityCounterexample.reciprocalSummable_quotientSet_prime_of_quotient_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {p : ℕ} (hp : Nat.Prime p) :
    ReciprocalSummable (quotientSet p A) := by
  by_contra hnot
  have hcounter : SummabilityCounterexample (quotientSet p A) := by
    exact ⟨infinite_of_not_reciprocalSummable hnot,
      hA.2.1.quotientSet, hA.2.2.1.quotientSet hp.pos, hnot⟩
  have hcounterLayer :
      SummabilityCounterexample (quotientSet p (multipleLayer p A)) := by
    simpa [quotientSet_multipleLayer_eq] using hcounter
  exact hirred p p dvd_rfl hp.one_lt hcounterLayer

/-- In a quotient-irreducible counterexample, every nontrivial quotient layer
is reciprocally summable. -/
theorem SummabilityCounterexample.reciprocalSummable_quotientSet_of_quotient_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {d : ℕ} (hd : 1 < d) :
    ReciprocalSummable (quotientSet d A) := by
  by_contra hnot
  have hdpos : 0 < d := Nat.lt_trans Nat.zero_lt_one hd
  have hcounter : SummabilityCounterexample (quotientSet d A) := by
    exact ⟨infinite_of_not_reciprocalSummable hnot,
      hA.2.1.quotientSet, hA.2.2.1.quotientSet hdpos, hnot⟩
  have hcounterLayer :
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
    simpa [quotientSet_multipleLayer_eq] using hcounter
  exact hirred d d dvd_rfl hd hcounterLayer

/-- Fixed finite small-prime capture is uniformly bounded in a
quotient-irreducible counterexample.  The bound depends on the finite prime set
`P`, but not on the scale, core, or LCM-room. -/
theorem SummabilityCounterexample.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {k : ℕ} {J P : Finset ℕ}
    (hPprime : ∀ p ∈ P, Nat.Prime p) :
    lcmRoomPrimeSupportMassWithin A k J P ≤
      ∑ p ∈ P, ∑' n : ℕ, reciprocalIndicator (multipleLayer p A) n := by
  exact (lcmRoomPrimeSupportMassWithin_le_belowScalePrimeSupportMass
      A k J P).trans
    (belowScalePrimeSupportMass_le_tsum_indicator_multipleLayers
      (fun p hp =>
        hA.reciprocalSummable_multipleLayer_prime_of_quotient_irreducible
          hirred (hPprime p hp)))

/-- Total reciprocal budget of the `p`-multiple layer of `A`. -/
noncomputable def primeLayerBudget (A : Set ℕ) (p : ℕ) : ℝ :=
  ∑' n : ℕ, reciprocalIndicator (multipleLayer p A) n

/-- Prime-layer budgets are nonnegative. -/
theorem primeLayerBudget_nonneg (A : Set ℕ) (p : ℕ) :
    0 ≤ primeLayerBudget A p := by
  unfold primeLayerBudget
  exact tsum_nonneg fun n =>
    reciprocalIndicator_nonneg (multipleLayer p A) n

/-- Total reciprocal budget of the quotient layer obtained by dividing the
`p`-multiples of `A` by `p`. -/
noncomputable def primeQuotientBudget (A : Set ℕ) (p : ℕ) : ℝ :=
  ∑' q : ℕ, reciprocalIndicator (quotientSet p A) q

/-- Prime-quotient budgets are nonnegative. -/
theorem primeQuotientBudget_nonneg (A : Set ℕ) (p : ℕ) :
    0 ≤ primeQuotientBudget A p := by
  unfold primeQuotientBudget
  exact tsum_nonneg fun q =>
    reciprocalIndicator_nonneg (quotientSet p A) q

/-- Every finite quotient window is bounded by the full quotient budget. -/
theorem finset_sum_reciprocal_le_primeQuotientBudget
    {A : Set ℕ} {p : ℕ} (hquot : ReciprocalSummable (quotientSet p A))
    {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q ∈ quotientSet p A) :
    (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) ≤ primeQuotientBudget A p := by
  simpa [primeQuotientBudget] using
    finset_sum_reciprocal_le_tsum_indicator_of_subset hquot hQ

/-- Clear the erased-support reciprocal from a localized weighted composite
budget.  A positive erased support prime `ℓ` turns
`(p*c)/K < (1/ℓ) * budget(p*ℓ)` into an actual composite-quotient budget
lower bound at the divisor `p*ℓ`. -/
theorem compositeQuotientBudget_lt_of_weightedBudget
    {A : Set ℕ} {K p ℓ : ℕ} {c : ℝ} (hℓpos : 0 < ℓ)
    (hweighted :
      ((p : ℝ) * c) / (K : ℝ) <
        (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) :
    (((p * ℓ : ℕ) : ℝ) * c) / (K : ℝ) <
      primeQuotientBudget A (p * ℓ) := by
  have hℓposR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓpos
  have hmul := mul_lt_mul_of_pos_left hweighted hℓposR
  have hℓne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓposR
  have hleft :
      (ℓ : ℝ) * (((p : ℝ) * c) / (K : ℝ)) =
        (((p * ℓ : ℕ) : ℝ) * c) / (K : ℝ) := by
    norm_num
    ring
  have hright :
      (ℓ : ℝ) *
          ((1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) =
        primeQuotientBudget A (p * ℓ) := by
    field_simp [hℓne]
  rw [hleft, hright] at hmul
  exact hmul

/-- Normalize a composite-budget lower bound when the current scale is bounded
by `D`.  If `K ≤ D`, then a lower bound
`d * (D*C) / K < Q` forces the scale-free ratio `C < Q / d`. -/
theorem normalizedBudget_lt_of_compositeBudget_lt
    {K D d : ℕ} {C Q : ℝ}
    (hKpos : 0 < K) (hdpos : 0 < d) (hKD : K ≤ D) (hC : 0 ≤ C)
    (hlarge : (((d : ℕ) : ℝ) * ((D : ℝ) * C)) / (K : ℝ) < Q) :
    C < Q / (d : ℝ) := by
  have hdposR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hKposR : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hdiv := div_lt_div_of_pos_right hlarge hdposR
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdposR
  have hleft :
      ((((d : ℕ) : ℝ) * ((D : ℝ) * C)) / (K : ℝ)) / (d : ℝ) =
        ((D : ℝ) * C) / (K : ℝ) := by
    field_simp [hdne]
  rw [hleft] at hdiv
  have hKDreal : (K : ℝ) ≤ (D : ℝ) := by exact_mod_cast hKD
  have hmul : (K : ℝ) * C ≤ (D : ℝ) * C :=
    mul_le_mul_of_nonneg_right hKDreal hC
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKposR
  have hCeq : C = ((K : ℝ) * C) / (K : ℝ) := by
    field_simp [hKne]
  have hCle : C ≤ ((D : ℝ) * C) / (K : ℝ) := by
    calc
      C = ((K : ℝ) * C) / (K : ℝ) := hCeq
      _ ≤ ((D : ℝ) * C) / (K : ℝ) :=
        div_le_div_of_nonneg_right hmul (le_of_lt hKposR)
  exact lt_of_le_of_lt hCle hdiv

/-- Finite box of normalized composite quotient budgets up to dyadic scale
`D`.  This is the finite ceiling used to rule out the moderate-scale branch:
inside a bounded dyadic box, no single normalized quotient budget can exceed
the sum of all such budgets in the box. -/
noncomputable def normalizedCompositeQuotientBudgetBox
    (A : Set ℕ) (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (2 ^ D),
    primeQuotientBudget A d / (d : ℝ)

/-- The finite normalized composite-budget box is nonnegative. -/
theorem normalizedCompositeQuotientBudgetBox_nonneg
    (A : Set ℕ) (D : ℕ) :
    0 ≤ normalizedCompositeQuotientBudgetBox A D := by
  dsimp [normalizedCompositeQuotientBudgetBox]
  exact Finset.sum_nonneg fun d _hd =>
    div_nonneg (primeQuotientBudget_nonneg A d) (Nat.cast_nonneg d)

/-- A divisor inside the finite dyadic box has normalized quotient budget at
most the whole box budget. -/
theorem normalizedCompositeQuotientBudget_le_box
    (A : Set ℕ) {D d : ℕ} (hd1 : 1 ≤ d) (hdD : d ≤ 2 ^ D) :
    primeQuotientBudget A d / (d : ℝ) ≤
      normalizedCompositeQuotientBudgetBox A D := by
  dsimp [normalizedCompositeQuotientBudgetBox]
  refine Finset.single_le_sum
    (s := Finset.Icc 1 (2 ^ D))
    (f := fun x : ℕ => primeQuotientBudget A x / (x : ℝ)) ?_ ?_
  · intro x _hx
    exact div_nonneg (primeQuotientBudget_nonneg A x) (Nat.cast_nonneg x)
  · exact Finset.mem_Icc.mpr ⟨hd1, hdD⟩

/-- The multiple-layer budget and the quotient budget are exactly the same
mass under the reindexing `n = p * q`, up to the factor `1 / p`. -/
theorem primeLayerBudget_eq_inv_mul_primeQuotientBudget
    {A : Set ℕ} (hApos : PositiveSet A) {p : ℕ} (hp : 0 < p) :
    primeLayerBudget A p =
      (1 / (p : ℝ)) * primeQuotientBudget A p := by
  let e := quotientEquivMultipleLayer p A hp
  have hLayerSubtype :
      primeLayerBudget A p =
        ∑' n : multipleLayer p A, (1 : ℝ) / (((n : ℕ) : ℝ)) := by
    simpa [primeLayerBudget, reciprocalIndicator] using
      (tsum_subtype (multipleLayer p A)
        (fun n : ℕ => (1 : ℝ) / (n : ℝ))).symm
  have hQuotSubtype :
      primeQuotientBudget A p =
        ∑' q : quotientSet p A, (1 : ℝ) / (((q : ℕ) : ℝ)) := by
    simpa [primeQuotientBudget, reciprocalIndicator] using
      (tsum_subtype (quotientSet p A)
        (fun q : ℕ => (1 : ℝ) / (q : ℝ))).symm
  calc
    primeLayerBudget A p =
        ∑' n : multipleLayer p A, (1 : ℝ) / (((n : ℕ) : ℝ)) :=
      hLayerSubtype
    _ = ∑' q : quotientSet p A,
          (1 : ℝ) / ((((e q : multipleLayer p A) : ℕ) : ℝ)) := by
      exact (e.tsum_eq
        (fun n : multipleLayer p A => (1 : ℝ) / (((n : ℕ) : ℝ)))).symm
    _ = ∑' q : quotientSet p A,
          (1 / (p : ℝ)) * ((1 : ℝ) / (((q : ℕ) : ℝ))) := by
      refine tsum_congr fun q => ?_
      exact reciprocal_on_multipleLayer_comp_quotientEquiv hApos hp q
    _ = (1 / (p : ℝ)) *
          ∑' q : quotientSet p A, (1 : ℝ) / (((q : ℕ) : ℝ)) := by
      rw [tsum_mul_left]
    _ = (1 / (p : ℝ)) * primeQuotientBudget A p := by
      rw [hQuotSubtype]

/-- Equivalent form of the exact layer/quotient budget scaling. -/
theorem primeQuotientBudget_eq_mul_primeLayerBudget
    {A : Set ℕ} (hApos : PositiveSet A) {p : ℕ} (hp : 0 < p) :
    primeQuotientBudget A p = (p : ℝ) * primeLayerBudget A p := by
  have hscale :=
    primeLayerBudget_eq_inv_mul_primeQuotientBudget hApos hp
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  calc
    primeQuotientBudget A p =
        (p : ℝ) * ((1 / (p : ℝ)) * primeQuotientBudget A p) := by
      field_simp [hp_ne]
    _ = (p : ℝ) * primeLayerBudget A p := by
      rw [← hscale]

/-- Arbitrary finite-set version of the fixed-prime capture bound.  Only the
primes actually lying in the core support contribute, so no primality
assumption on all of `P` is needed. -/
theorem SummabilityCounterexample.lcmRoomPrimeSupportMassWithin_le_irreducible_bound_any
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {k : ℕ} {J P : Finset ℕ} :
    lcmRoomPrimeSupportMassWithin A k J P ≤
      ∑ p ∈ P, primeLayerBudget A p := by
  classical
  let S : Finset ℕ := (corePrimeSupport J).filter (fun p => p ∈ P)
  have hpoint : ∀ p ∈ S,
      lcmRoomPrimeDivisorMass A k J p ≤ primeLayerBudget A p := by
    intro p hpS
    have hpSupport : p ∈ corePrimeSupport J := (Finset.mem_filter.mp hpS).1
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    unfold primeLayerBudget
    exact (lcmRoomPrimeDivisorMass_le_belowScalePrimeDivisorMass A k J p).trans
      (belowScalePrimeDivisorMass_le_tsum_indicator_multipleLayer
        (hA.reciprocalSummable_multipleLayer_prime_of_quotient_irreducible
          hirred hpPrime))
  have hsum_point :
      (∑ p ∈ S, lcmRoomPrimeDivisorMass A k J p) ≤
        ∑ p ∈ S, primeLayerBudget A p :=
    Finset.sum_le_sum hpoint
  have hsub : S ⊆ P := by
    intro p hpS
    exact (Finset.mem_filter.mp hpS).2
  have hsum_sub :
      (∑ p ∈ S, primeLayerBudget A p) ≤
        ∑ p ∈ P, primeLayerBudget A p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p _hpP _hpMissing
    exact primeLayerBudget_nonneg A p
  simpa [lcmRoomPrimeSupportMassWithin, S] using hsum_point.trans hsum_sub

/-- Heavy delayed prefixes cannot force more actual capture from a fixed prime
set than the finite irreducible multiple-layer bound.  This is the fixed-prime
side of the growing-cutoff attack. -/
theorem SummabilityCounterexample.lt_fixedPrimeBound_of_heavy_delayed_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hJ : CoprimeLCMSelection A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J P +
        corePrimeSupportOutsideMultiplesBelowMass K J P)
    (hheavy : (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (corePrimeSupportOutsideMultiplesBelowMass K J P + c) <
      dyadicPrefixReciprocalMass A N m) :
    c < ∑ p ∈ P, ∑' n : ℕ,
      reciprocalIndicator (multipleLayer p A) n := by
  have hsmall :=
    lt_mixedPrimeSupportMass_of_heavy_delayed_prefix_obstruction
      hJ hN hdelay hobstruction hheavy
  exact lt_of_lt_of_le hsmall
    (hA.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
      hirred hPprime)

/-- LCM-minimal rank form of the fixed-prime heavy-prefix bound. -/
theorem SummabilityCounterexample.lt_fixedPrimeBound_of_heavy_lcmMinimal_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J P +
        corePrimeSupportOutsideMultiplesBelowMass K J P)
    (hheavy : (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (corePrimeSupportOutsideMultiplesBelowMass K J P + c) <
      dyadicPrefixReciprocalMass A N m) :
    c < ∑ p ∈ P, ∑' n : ℕ,
      reciprocalIndicator (multipleLayer p A) n := by
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  have hheavy' : (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
      (corePrimeSupportOutsideMultiplesBelowMass K J P + c) <
      dyadicPrefixReciprocalMass A N m := by
    simpa [hcard] using hheavy
  exact hA.lt_fixedPrimeBound_of_heavy_delayed_prefix hirred hPprime
    hJ.1 hN hdelay hobstruction hheavy'

/-- Standard `M.primesBelow` version: in an irreducible counterexample, a
heavy delayed prefix can only force bounded capture from primes below `M`; the
remaining excess must be paid by the explicit `K^2 / M` large-prime budget. -/
theorem SummabilityCounterexample.lt_primesBelowBound_of_heavy_lcmMinimal_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r M : ℕ} {J : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
        (K : ℝ) * ((K : ℝ) / (M : ℝ)))
    (hheavy : (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        ((K : ℝ) * ((K : ℝ) / (M : ℝ)) + c) <
      dyadicPrefixReciprocalMass A N m) :
    c < ∑ p ∈ M.primesBelow, ∑' n : ℕ,
      reciprocalIndicator (multipleLayer p A) n := by
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  have hheavy' : (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
      ((K : ℝ) * ((K : ℝ) / (M : ℝ)) + c) <
      dyadicPrefixReciprocalMass A N m := by
    simpa [hcard] using hheavy
  have hsmall :=
    lt_primesBelowSupportMass_of_heavy_delayed_prefix_obstruction
      hJ.1 hN hdelay hobstruction hheavy'
  have hPprime : ∀ p ∈ M.primesBelow, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow hp
  exact lt_of_lt_of_le hsmall
    (hA.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
      hirred hPprime)

/-- The irreducible delayed-prefix obstruction bound after the standard
small/large prime split.  The three terms are:
finite-core payment, explicit large-prime budget, and the actual layer sums for
primes below the cutoff. -/
noncomputable def primesBelowPrefixObstructionBound
    (A : Set ℕ) (N K r M : ℕ) : ℝ :=
  (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
    ((K : ℝ) * ((K : ℝ) / (M : ℝ)) +
      ∑ p ∈ M.primesBelow, ∑' n : ℕ,
        reciprocalIndicator (multipleLayer p A) n)

/-- A strict lower bound for a nonnegative `ℕ`-indexed tsum is already
witnessed by some finite partial sum. -/
theorem exists_lt_finset_sum_of_lt_tsum_nonneg
    {f : ℕ → ℝ} {c : ℝ}
    (hf_nonneg : ∀ n, 0 ≤ f n) (hlt : c < ∑' n : ℕ, f n) :
    ∃ F : Finset ℕ, c < ∑ n ∈ F, f n := by
  by_contra hnone
  have hle : ∀ F : Finset ℕ, ∑ n ∈ F, f n ≤ c := by
    intro F
    by_contra hnot
    exact hnone ⟨F, lt_of_not_ge hnot⟩
  have htsum_le : (∑' n : ℕ, f n) ≤ c :=
    Real.tsum_le_of_sum_le hf_nonneg hle
  linarith

/-- Fixed-prior version of the obstruction budget.  Minimality keeps every
later rank-`r` support prime below the prior LCM, so the only analytic cost is
the finite sum of those fixed prime layers. -/
noncomputable def fixedPriorPrimeLayerPrefixBound
    (A : Set ℕ) (N r : ℕ) (J₀ : Finset ℕ) : ℝ :=
  (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
    ∑ p ∈ (Finset.Icc 2 (J₀.lcm fun a : ℕ => a)).filter
        (fun p => Nat.Prime p),
      ∑' n : ℕ, reciprocalIndicator (multipleLayer p A) n

/-- Exact core-support version of the prime-layer prefix budget.  This charges
only the primes actually used by the current obstruction core. -/
noncomputable def corePrimeLayerPrefixBound
    (A : Set ℕ) (N r : ℕ) (J : Finset ℕ) : ℝ :=
  (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
    ∑ p ∈ corePrimeSupport J, primeLayerBudget A p

/-- If an exact support-prime budget is larger than a uniform allowance `c` per
support prime, then one support prime has layer budget larger than `c`. -/
theorem exists_lt_primeLayerBudget_of_corePrimeLayerPrefixBound
    {A : Set ℕ} {N r : ℕ} {J : Finset ℕ} {c : ℝ}
    (hlarge :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((corePrimeSupport J).card : ℝ) * c <
        corePrimeLayerPrefixBound A N r J) :
    ∃ p ∈ corePrimeSupport J, c < primeLayerBudget A p := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum_le : (∑ p ∈ corePrimeSupport J, primeLayerBudget A p) ≤
      ∑ _p ∈ corePrimeSupport J, c := Finset.sum_le_sum fun p hp => hnone p hp
  have hsum_le_card : (∑ p ∈ corePrimeSupport J, primeLayerBudget A p) ≤
      ((corePrimeSupport J).card : ℝ) * c := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum_le
  unfold corePrimeLayerPrefixBound at hlarge
  linarith

/-- Scale-card version of the support-prime average.  A valid scale-`K` core
has at most `K` distinct support primes, so if the exact support budget is
larger than `c` per available scale slot, one actual support prime has layer
budget larger than `c`. -/
theorem exists_lt_primeLayerBudget_of_corePrimeLayerPrefixBound_scale
    {A : Set ℕ} {N K r : ℕ} {J : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J)
    (hc_nonneg : 0 ≤ c)
    (hlarge :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) + (K : ℝ) * c <
        corePrimeLayerPrefixBound A N r J) :
    ∃ p ∈ corePrimeSupport J, c < primeLayerBudget A p := by
  have hcard_nat : (corePrimeSupport J).card ≤ K :=
    hJ.corePrimeSupport_card_le_scale
  have hcard_real : ((corePrimeSupport J).card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hcard_nat
  have hcard_mul :
      ((corePrimeSupport J).card : ℝ) * c ≤ (K : ℝ) * c :=
    mul_le_mul_of_nonneg_right hcard_real hc_nonneg
  exact exists_lt_primeLayerBudget_of_corePrimeLayerPrefixBound
    (A := A) (N := N) (r := r) (J := J) (c := c) (by linarith)

/-- Fresh finite-set version of the support-prime average.  If the exact
support budget is larger than the whole budget of an old finite set `P`, plus
`c` for each available scale slot, then some support prime outside `P` has
layer budget larger than `c`. -/
theorem exists_fresh_lt_primeLayerBudget_of_corePrimeLayerPrefixBound_scale
    {A : Set ℕ} {N K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J)
    (hc_nonneg : 0 ≤ c)
    (hlarge :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
        corePrimeLayerPrefixBound A N r J) :
    ∃ p ∈ corePrimeSupport J, p ∉ P ∧ c < primeLayerBudget A p := by
  classical
  let S : Finset ℕ := corePrimeSupport J
  let w : ℕ → ℝ := fun p => primeLayerBudget A p
  by_contra hnone
  have houtside_point :
      ∀ p, p ∈ S.filter (fun p => p ∉ P) → w p ≤ c := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hpP⟩
    by_contra hle
    exact hnone ⟨p, hpS, ⟨hpP, lt_of_not_ge hle⟩⟩
  have hsplit :
      (∑ p ∈ S, w p) =
        (∑ p ∈ S.filter (fun p => p ∈ P), w p) +
          ∑ p ∈ S.filter (fun p => p ∉ P), w p := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ∈ P) w]
  have hinside_le :
      (∑ p ∈ S.filter (fun p => p ∈ P), w p) ≤
        ∑ p ∈ P, w p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p _hpP _hpMissing
      exact primeLayerBudget_nonneg A p
  have houtside_le_card :
      (∑ p ∈ S.filter (fun p => p ∉ P), w p) ≤
        ∑ _p ∈ S.filter (fun p => p ∉ P), c := Finset.sum_le_sum fun p hp => houtside_point p hp
  have houtside_le_card_mul :
      (∑ p ∈ S.filter (fun p => p ∉ P), w p) ≤
        (((S.filter fun p => p ∉ P).card : ℕ) : ℝ) * c := by
    simpa [Finset.sum_const, nsmul_eq_mul] using houtside_le_card
  have hcard_filter_nat :
      (S.filter fun p => p ∉ P).card ≤ K := by
    have hsub : S.filter (fun p => p ∉ P) ⊆ S := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    exact (Finset.card_le_card hsub).trans
      (by simpa [S] using hJ.corePrimeSupport_card_le_scale)
  have hcard_filter_real :
      (((S.filter fun p => p ∉ P).card : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hcard_filter_nat
  have houtside_le :
      (∑ p ∈ S.filter (fun p => p ∉ P), w p) ≤ (K : ℝ) * c := by
    have hmul :
        (((S.filter fun p => p ∉ P).card : ℕ) : ℝ) * c ≤
          (K : ℝ) * c :=
      mul_le_mul_of_nonneg_right hcard_filter_real hc_nonneg
    linarith
  have hsum_le :
      (∑ p ∈ S, w p) ≤ (∑ p ∈ P, w p) + (K : ℝ) * c := by
    rw [hsplit]
    linarith
  unfold corePrimeLayerPrefixBound at hlarge
  dsimp [S, w] at hsum_le
  linarith

/-- Scale-only version of the fixed-prior budget, using every prime below the
dyadic LCM cap `2^T`.  This forgets the particular prior core. -/
noncomputable def scalePrimeLayerPrefixBound
    (A : Set ℕ) (N r T : ℕ) : ℝ :=
  (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
    ∑ p ∈ (Finset.Icc 2 (2 ^ T)).filter (fun p => Nat.Prime p),
      ∑' n : ℕ, reciprocalIndicator (multipleLayer p A) n

/-- Any prior at scale `T` has LCM at most `2^T`, so its fixed-prior budget is
bounded by the scale-only budget. -/
theorem CoprimeLCMSelection.fixedPriorPrimeLayerPrefixBound_le_scaleBound
    {A : Set ℕ} {N T r : ℕ} {J₀ : Finset ℕ}
    (hJ₀ : CoprimeLCMSelection A T r J₀) :
    fixedPriorPrimeLayerPrefixBound A N r J₀ ≤
      scalePrimeLayerPrefixBound A N r T := by
  classical
  let P₀ : Finset ℕ :=
    (Finset.Icc 2 (J₀.lcm fun a : ℕ => a)).filter fun p => Nat.Prime p
  let PT : Finset ℕ := (Finset.Icc 2 (2 ^ T)).filter fun p => Nat.Prime p
  have hsub : P₀ ⊆ PT := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp2, hple⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp2, hple.trans hJ₀.2.2.1⟩, hpPrime⟩
  have hsum : (∑ p ∈ P₀, ∑' n : ℕ,
        reciprocalIndicator (multipleLayer p A) n) ≤
      ∑ p ∈ PT, ∑' n : ℕ,
        reciprocalIndicator (multipleLayer p A) n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p _hpPT _hpnot
    exact tsum_nonneg fun n =>
      reciprocalIndicator_nonneg (multipleLayer p A) n
  have hbase :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) := le_rfl
  simpa [fixedPriorPrimeLayerPrefixBound, scalePrimeLayerPrefixBound, P₀, PT]
    using add_le_add hbase hsum

/-- Exact support-prefix bound.  If an LCM-minimal core's room is covered by
its own support primes, then every visible prefix is paid for by the finite
prime-layer budget of those actual support primes. -/
theorem SummabilityCounterexample.prefixMass_le_corePrimeLayerBound_of_room_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover : ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    dyadicPrefixReciprocalMass A N m ≤
      corePrimeLayerPrefixBound A N r J := by
  classical
  let P : Finset ℕ := corePrimeSupport J
  have hPprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact prime_of_mem_corePrimeSupport hp
  have hfilter : (corePrimeSupport J).filter (fun p => p ∈ P) =
      corePrimeSupport J := by
    apply Finset.ext
    intro p
    by_cases hp : p ∈ corePrimeSupport J
    · simp [P, hp]
    · simp [P, hp]
  have hwithin_eq :
      lcmRoomPrimeSupportMassWithin A K J P =
        lcmRoomPrimeSupportMass A K J := by
    unfold lcmRoomPrimeSupportMassWithin lcmRoomPrimeSupportMass
    rw [hfilter]
  have hroom_le_within :
      lcmRoomReciprocalMass A K J ≤
        lcmRoomPrimeSupportMassWithin A K J P := by
    rw [hwithin_eq]
    exact lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover hcover
  have hfinite :
      lcmRoomPrimeSupportMassWithin A K J P ≤
        ∑ p ∈ P, ∑' n : ℕ,
          reciprocalIndicator (multipleLayer p A) n :=
    hA.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
      hirred hPprime
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
      hJ.1 hN hdelay
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  calc
    dyadicPrefixReciprocalMass A N m ≤
        (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          lcmRoomReciprocalMass A K J :=
      hprefix
    _ = (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          lcmRoomReciprocalMass A K J := by
      rw [hcard]
    _ ≤ (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          lcmRoomPrimeSupportMassWithin A K J P := add_le_add le_rfl hroom_le_within
    _ ≤ (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ∑ p ∈ P, ∑' n : ℕ,
            reciprocalIndicator (multipleLayer p A) n := add_le_add le_rfl hfinite
    _ = corePrimeLayerPrefixBound A N r J := by
      simp [corePrimeLayerPrefixBound, primeLayerBudget, P]

/-- Heavy-prefix extraction from an exact room-cover obstruction.  If a delayed
LCM-minimal room is covered by its own support primes, and the visible prefix
beats the trivial core payment by more than `K * c`, then one support prime
has actual layer budget larger than `c`. -/
theorem SummabilityCounterexample.exists_large_primeLayerBudget_of_room_cover_heavy_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN2 : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover :
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (hc_nonneg : 0 ≤ c)
    (hheavy :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) + (K : ℝ) * c <
        dyadicPrefixReciprocalMass A N m) :
    ∃ p ∈ corePrimeSupport J, c < primeLayerBudget A p := by
  have hupper :=
    hA.prefixMass_le_corePrimeLayerBound_of_room_cover
      hirred hJ hN2 hdelay hcover
  exact exists_lt_primeLayerBudget_of_corePrimeLayerPrefixBound_scale
    hJ.1 hc_nonneg (lt_of_lt_of_le hheavy hupper)

/-- Fresh-prime heavy-prefix extraction.  After paying the whole layer budget
of an arbitrary finite old-prime set `P`, any delayed room-cover obstruction
whose visible prefix still has more than `K * c` excess must contain a support
prime outside `P` with layer budget larger than `c`. -/
theorem SummabilityCounterexample.exists_fresh_large_primeLayerBudget_of_room_cover_heavy_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN2 : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover :
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (hc_nonneg : 0 ≤ c)
    (hheavy :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
        dyadicPrefixReciprocalMass A N m) :
    ∃ p ∈ corePrimeSupport J, p ∉ P ∧ c < primeLayerBudget A p := by
  have hupper :=
    hA.prefixMass_le_corePrimeLayerBound_of_room_cover
      hirred hJ hN2 hdelay hcover
  exact exists_fresh_lt_primeLayerBudget_of_corePrimeLayerPrefixBound_scale
    hJ.1 hc_nonneg (lt_of_lt_of_le hheavy hupper)

/-- Actual-room version of fresh heavy-prefix extraction.  After paying the
whole layer budget of an old finite prime set `P`, any delayed room-cover whose
visible prefix still has more than `K * c` excess must contain a support prime
outside `P` whose current LCM-room divisor mass is larger than `c`. -/
theorem SummabilityCounterexample.exists_fresh_large_lcmRoomPrimeDivisorMass
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN2 : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover :
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (hc_nonneg : 0 ≤ c)
    (hheavy :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
        dyadicPrefixReciprocalMass A N m) :
    ∃ p ∈ corePrimeSupport J, p ∉ P ∧
      c < lcmRoomPrimeDivisorMass A K J p := by
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
      hJ.1 hN2 hdelay
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  have hroom_le_support :
      lcmRoomReciprocalMass A K J ≤ lcmRoomPrimeSupportMass A K J :=
    lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover hcover
  have hsplit :
      lcmRoomPrimeSupportMass A K J ≤
        lcmRoomPrimeSupportMassWithin A K J P +
          lcmRoomFreshPrimeSupportMass A K J P :=
    lcmRoomPrimeSupportMass_le_within_add_freshMass A K J P
  have hold :
      lcmRoomPrimeSupportMassWithin A K J P ≤
        ∑ p ∈ P, primeLayerBudget A p :=
    hA.lcmRoomPrimeSupportMassWithin_le_irreducible_bound_any hirred
  have hupper :
      dyadicPrefixReciprocalMass A N m ≤
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((∑ p ∈ P, primeLayerBudget A p) +
            lcmRoomFreshPrimeSupportMass A K J P) := by
    calc
      dyadicPrefixReciprocalMass A N m ≤
          (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            lcmRoomReciprocalMass A K J := hprefix
      _ = (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            lcmRoomReciprocalMass A K J := by rw [hcard]
      _ ≤ (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            lcmRoomPrimeSupportMass A K J := add_le_add le_rfl hroom_le_support
      _ ≤ (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            (lcmRoomPrimeSupportMassWithin A K J P +
              lcmRoomFreshPrimeSupportMass A K J P) := add_le_add le_rfl hsplit
      _ ≤ (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            ((∑ p ∈ P, primeLayerBudget A p) +
              lcmRoomFreshPrimeSupportMass A K J P) := by
          exact add_le_add le_rfl
            (by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hold
                  (lcmRoomFreshPrimeSupportMass A K J P))
  have hfresh_large :
      (K : ℝ) * c < lcmRoomFreshPrimeSupportMass A K J P := by
    linarith
  exact exists_fresh_lt_lcmRoomPrimeDivisorMass_of_freshMass_scale
    hJ.1 hc_nonneg hfresh_large

/-- Heavy prefixes force either scale escape or fresh overloaded prime layers.
Fix a finite old-prime set `P`, a rank ceiling `R`, a scale ceiling `B`, and a
per-prime layer threshold `c`.  In a quotient-irreducible counterexample,
there is a visible prefix such that any delayed bounded-rank room-cover
obstruction seeing it either has scale above `B`, or has a support prime outside
`P` whose actual multiple-layer budget is larger than `c`. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_scale_or_fresh_primeLayerBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧ c < primeLayerBudget A p := by
  let C : ℝ :=
    (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
      ((∑ p ∈ P, primeLayerBudget A p) + (B : ℝ) * c)
  have hC_nonneg : 0 ≤ C := by
    have hbase_nonneg :
        0 ≤ (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
      positivity
    have hsum_nonneg :
        0 ≤ ∑ p ∈ P, primeLayerBudget A p :=
          Finset.sum_nonneg fun p _hp => primeLayerBudget_nonneg A p
    have hBc_nonneg : 0 ≤ (B : ℝ) * c :=
      mul_nonneg (Nat.cast_nonneg B) hc_nonneg
    dsimp [C]
    linarith
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC_nonneg N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  by_cases hBK : B < K
  · exact Or.inl hBK
  · have hKB : K ≤ B := not_lt.mp hBK
    have hdelay : J.lcm (fun a : ℕ => a) * 2 ^ ((n - 1) + 1) ≤ 2 ^ K :=
      hJ.delay_of_prior_selection hJ₀ hTK hdelay₀
    have hbase_le :
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤
          (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
      have hrR_real : (r : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hrR
      exact div_le_div_of_nonneg_right hrR_real (by positivity)
    have hKc_le : (K : ℝ) * c ≤ (B : ℝ) * c := by
      have hKB_real : (K : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast hKB
      exact mul_le_mul_of_nonneg_right hKB_real hc_nonneg
    have hprefix_m :
        C < dyadicPrefixReciprocalMass A N (n - 1) := by
      simpa using hprefix
    have hheavy :
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
          dyadicPrefixReciprocalMass A N (n - 1) := by
      dsimp [C] at hprefix_m
      linarith
    exact Or.inr
      (hA.exists_fresh_large_primeLayerBudget_of_room_cover_heavy_prefix
        hirred hJ hN2 hdelay hcover hc_nonneg hheavy)

/-- Sequence-level escape form of the preceding dichotomy.  If delayed
room-cover obstructions continue forever with rank bounded by `R`, then for
every finite old-prime set `P`, every nonnegative layer threshold `c`, and
every scale ceiling `B`, some obstruction either occurs above scale `B` or has
a support prime outside `P` whose multiple-layer budget is larger than `c`. -/
theorem SummabilityCounterexample.exists_scale_or_freshLayer_of_endless_prior_room_covers_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧ c < primeLayerBudget A p) := by
  rcases hA.exists_prefix_forces_large_scale_or_fresh_primeLayerBudget
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale specialization of the escape theorem.  If delayed room-cover
obstructions continue forever while both rank and scale are bounded, then for
every finite old-prime set `P` and every nonnegative threshold `c`, some
obstruction has a support prime outside `P` whose layer budget is larger than
`c`. -/
theorem SummabilityCounterexample.exists_freshLayer_of_endless_prior_room_covers_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧ c < primeLayerBudget A p := by
  rcases hA.exists_prefix_forces_large_scale_or_fresh_primeLayerBudget
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · omega
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Bounded-scale endless fixed-prior room-cover delay is impossible in the
quotient-irreducible branch.  The fresh-layer escape theorem forces a support
prime outside every finite old set; choosing the old set to be all primes below
the fixed dyadic scale ceiling `2^B` contradicts the scale bound. -/
theorem SummabilityCounterexample.not_endless_prior_room_covers_rank_scale_le_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ¬ ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  intro hendless
  let P : Finset ℕ := (Finset.Icc 2 (2 ^ B)).filter fun p => Nat.Prime p
  rcases hA.exists_freshLayer_of_endless_prior_room_covers_rank_scale_le
      hN2 hirred hendless P (by norm_num : (0 : ℝ) ≤ 0) with
    ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover,
      p, hpSupport, hpNotP, _hpLarge⟩
  have hpP : p ∈ P :=
    hJ.1.corePrimeSupport_subset_primesBelow_scale_le hKB hpSupport
  exact hpNotP hpP

/-- Therefore, bounded-rank endless fixed-prior room-cover delay must escape
to arbitrarily large dyadic scales in the quotient-irreducible branch.  This
is the cleaned-up form of the positive-route obstruction after eliminating the
bounded-scale alternative. -/
theorem SummabilityCounterexample.exists_large_scale_of_endless_prior_room_covers_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    ∀ B, ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      B < K := by
  intro B
  by_contra hnone
  have hbounded : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
    intro m hm
    rcases hendless m hm with
      ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
    have hKB : K ≤ B := by
      by_contra hnotKB
      exact hnone ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀,
        hcover, lt_of_not_ge hnotKB⟩
    exact ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact hA.not_endless_prior_room_covers_rank_scale_le_of_irreducible
    hN2 hirred hbounded

/-- Finite bounded-box delay break.  Fix rank and scale ceilings `R` and `B`.
In the quotient-irreducible branch, there is a prefix length after which no
delayed fixed-prior room-cover obstruction with rank at most `R` and scale at
most `B` survives. -/
theorem SummabilityCounterexample.exists_prefix_breaks_prior_room_covers_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      K ≤ B →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ¬ (((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) := by
  have hnotEndless :=
    hA.not_endless_prior_room_covers_rank_scale_le_of_irreducible
      (N := N) (R := R) (B := B) hN2 hirred
  by_contra hnone
  apply hnotEndless
  intro m hm
  by_contra hnoWitness
  apply hnone
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hKB hJ hJ₀ hTK hdelay₀ hcover
  exact hnoWitness
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩

/-- In a quotient-irreducible counterexample, a delayed standard cutoff
obstruction bounds every visible prefix by the finite-core payment, the explicit
large-prime budget, and the finite sum of the actual layers for primes below
the cutoff. -/
theorem SummabilityCounterexample.prefixMass_le_rank_add_budget_add_primesBelowBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r M : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
        (K : ℝ) * ((K : ℝ) / (M : ℝ))) :
    dyadicPrefixReciprocalMass A N m ≤
      primesBelowPrefixObstructionBound A N K r M := by
  have hprefix :=
    hJ.prefixMass_le_rank_div_pow_add_primesBelowBudget
      hN hdelay hobstruction
  have hPprime : ∀ p ∈ M.primesBelow, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow hp
  have hfinite :=
    hA.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
      hirred hPprime (k := K) (J := J)
  unfold primesBelowPrefixObstructionBound
  linarith

/-- Prior-witness form of the irreducible cutoff prefix bound.  The delayed
headroom can be certified by any earlier rank-`r` witness. -/
theorem SummabilityCounterexample.prefixMass_le_rank_add_budget_add_primesBelowBound_of_prior
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m T K r M : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hN : 2 ≤ N)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
        (K : ℝ) * ((K : ℝ) / (M : ℝ))) :
    dyadicPrefixReciprocalMass A N m ≤
      primesBelowPrefixObstructionBound A N K r M := by
  have hprefix :=
    hJ.prefixMass_le_rank_div_pow_add_primesBelowBudget_of_prior
      hJ₀ hTK hN hdelay₀ hobstruction
  have hPprime : ∀ p ∈ M.primesBelow, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow hp
  have hfinite :=
    hA.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
      hirred hPprime (k := K) (J := J)
  unfold primesBelowPrefixObstructionBound
  linarith

/-- Sharper fixed-prior prefix bound.  If a later LCM-minimal rank-`r` core has
its room covered by its own prime support, and its delayed headroom is certified
by a fixed prior `J₀`, then the visible prefix is paid for by the finite prime
layers below `lcm(J₀)`. -/
theorem SummabilityCounterexample.prefixMass_le_fixedPriorPrimeLayerBound_of_room_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m T K r : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hN : 2 ≤ N)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover : ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    dyadicPrefixReciprocalMass A N m ≤
      fixedPriorPrimeLayerPrefixBound A N r J₀ := by
  classical
  let P : Finset ℕ :=
    (Finset.Icc 2 (J₀.lcm fun a : ℕ => a)).filter fun p => Nat.Prime p
  have hPprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsub : corePrimeSupport J ⊆ P :=
    hJ.corePrimeSupport_subset_primesBelow_lcm_of_prior_selection hJ₀ hTK
  have hfilter :
      (corePrimeSupport J).filter (fun p => p ∈ P) = corePrimeSupport J := by
    apply Finset.ext
    intro p
    by_cases hp : p ∈ corePrimeSupport J
    · simp [hp, hsub hp]
    · simp [hp]
  have hwithin_eq :
      lcmRoomPrimeSupportMassWithin A K J P =
        lcmRoomPrimeSupportMass A K J := by
    unfold lcmRoomPrimeSupportMassWithin lcmRoomPrimeSupportMass
    rw [hfilter]
  have hroom_le_within :
      lcmRoomReciprocalMass A K J ≤
        lcmRoomPrimeSupportMassWithin A K J P := by
    rw [hwithin_eq]
    exact lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover hcover
  have hfinite :
      lcmRoomPrimeSupportMassWithin A K J P ≤
        ∑ p ∈ P, ∑' n : ℕ,
          reciprocalIndicator (multipleLayer p A) n :=
    hA.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
      hirred hPprime
  have hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K :=
    hJ.delay_of_prior_selection hJ₀ hTK hdelay₀
  have hprefix :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
      hJ.1 hN hdelay
  have hcard : (J.card : ℝ) = (r : ℝ) := by
    exact_mod_cast hJ.card_eq
  calc
    dyadicPrefixReciprocalMass A N m ≤
        (J.card : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          lcmRoomReciprocalMass A K J :=
      hprefix
    _ = (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          lcmRoomReciprocalMass A K J := by
      rw [hcard]
    _ ≤ (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          lcmRoomPrimeSupportMassWithin A K J P := add_le_add le_rfl hroom_le_within
    _ ≤ (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ∑ p ∈ P, ∑' n : ℕ,
            reciprocalIndicator (multipleLayer p A) n := add_le_add le_rfl hfinite
    _ = fixedPriorPrimeLayerPrefixBound A N r J₀ := by
      simp [fixedPriorPrimeLayerPrefixBound, P]

/-- Heavy-prefix forcing with the sharp fixed-prior budget.  Thus a slow
fixed-prior room-cover block can survive only if the finite prime-layer budget
attached to its prior core is already large. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_fixedPriorBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      C < fixedPriorPrimeLayerPrefixBound A N r J₀ := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro T K r J J₀ hJ hJ₀ hTK hdelay₀ hcover
  have hupper :=
    hA.prefixMass_le_fixedPriorPrimeLayerBound_of_room_cover
      hirred hJ hJ₀ hTK hN2 hdelay₀ hcover
  linarith

/-- Heavy-prefix forcing form of the irreducible obstruction.  In a
quotient-irreducible counterexample, for every target `C` there is a dyadic
prefix such that any delayed LCM-minimal mixed small/large-prime obstruction
seeing that prefix must have right-hand side larger than `C`.

This packages the remaining task: to close the positive argument, one must
choose delayed obstruction cores for these heavy prefixes while keeping the
rank payment, large-prime budget, and growing small-prime layer sum bounded. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_primesBelowBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    ∃ m, N ≤ m ∧ ∀ (K r M : ℕ) (J : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J →
      J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      lcmRoomReciprocalMass A K J ≤
        lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
          (K : ℝ) * ((K : ℝ) / (M : ℝ)) →
      C < primesBelowPrefixObstructionBound A N K r M := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro K r M J hJ hdelay hobstruction
  have hupper :=
    hA.prefixMass_le_rank_add_budget_add_primesBelowBound
      hirred hJ hN2 hdelay hobstruction
  linarith

/-- Prior-witness heavy-prefix forcing form.  The delayed visibility may be
certified by an earlier rank witness `J₀`, then transferred to the later
LCM-minimal bad core by minimality. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_bound_of_prior
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    ∃ m, N ≤ m ∧ ∀ (T K r M : ℕ) (J J₀ : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      lcmRoomReciprocalMass A K J ≤
        lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
          (K : ℝ) * ((K : ℝ) / (M : ℝ)) →
      C < primesBelowPrefixObstructionBound A N K r M := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro T K r M J J₀ hJ hJ₀ hTK hdelay₀ hobstruction
  have hupper :=
    hA.prefixMass_le_rank_add_budget_add_primesBelowBound_of_prior
      hirred hJ hJ₀ hTK hN2 hdelay₀ hobstruction
  linarith

/-- Self-bounded delayed obstruction criterion.  A quotient-irreducible
counterexample cannot have a uniform ceiling `C` for the standard delayed
mixed-obstruction bound along every sufficiently long visible prefix. -/
theorem SummabilityCounterexample.false_of_uniform_delayed_primesBelowBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hbounded : ∀ m, N ≤ m →
      ∃ (K r M : ℕ) (J : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
            (K : ℝ) * ((K : ℝ) / (M : ℝ)) ∧
        primesBelowPrefixObstructionBound A N K r M ≤ C) :
    False := by
  rcases hA.exists_prefix_forces_large_primesBelowBound
      hirred hN2 hC with ⟨m, hm, hforce⟩
  rcases hbounded m hm with
    ⟨K, r, M, J, hJ, hdelay, hobstruction, hbound⟩
  exact (not_lt_of_ge hbound) (hforce K r M J hJ hdelay hobstruction)

/-- Prior-witness self-bounded criterion.  It is enough to produce, for every
heavy-prefix length, a later LCM-minimal obstruction whose delay is certified
by an earlier witness of the same rank and whose obstruction bound is uniformly
bounded. -/
theorem SummabilityCounterexample.false_of_uniform_prior_primesBelowBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hbounded : ∀ m, N ≤ m →
      ∃ (T K r M : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
            (K : ℝ) * ((K : ℝ) / (M : ℝ)) ∧
        primesBelowPrefixObstructionBound A N K r M ≤ C) :
    False := by
  rcases hA.exists_prefix_forces_large_bound_of_prior
      hirred hN2 hC with ⟨m, hm, hforce⟩
  rcases hbounded m hm with
    ⟨T, K, r, M, J, J₀, hJ, hJ₀, hTK, hdelay₀, hobstruction, hbound⟩
  exact (not_lt_of_ge hbound)
    (hforce T K r M J J₀ hJ hJ₀ hTK hdelay₀ hobstruction)

/-- If a moving prime universe captures more than the fixed irreducible bound
for `P` plus `c`, then more than `c` mass is captured by fresh primes outside
`P`. -/
theorem SummabilityCounterexample.lt_freshPrimeMass_of_large_growingCapture
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {k : ℕ} {J P Q : Finset ℕ} {c : ℝ}
    (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hlarge :
      (∑ p ∈ P, ∑' n : ℕ, reciprocalIndicator (multipleLayer p A) n) + c <
        lcmRoomPrimeSupportMassWithin A k J Q) :
    c < lcmRoomPrimeSupportMassWithin A k J (Q.filter fun p => p ∉ P) := by
  have hsplit :=
    lcmRoomPrimeSupportMassWithin_le_within_add_fresh A k J P Q
  have hfixed :=
    hA.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
      hirred hPprime (k := k) (J := J)
  linarith

/-- Fresh-prime drift theorem.  In a quotient-irreducible counterexample, if
capture by a moving finite prime universe is unbounded, then after removing any
fixed finite prime set, the remaining fresh-prime capture is still unbounded.

Thus the growing-cutoff obstruction cannot be discharged by fixed prime layers;
it must continually move to new primes. -/
theorem SummabilityCounterexample.unbounded_freshPrimeMass_of_unbounded_capture
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {K : ℕ → ℕ} {J Q : ℕ → Finset ℕ}
    (hunbounded : ∀ C : ℝ, ∃ t,
      C < lcmRoomPrimeSupportMassWithin A (K t) (J t) (Q t))
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, Nat.Prime p) :
    ∀ C : ℝ, ∃ t,
      C < lcmRoomPrimeSupportMassWithin A (K t) (J t)
        ((Q t).filter fun p => p ∉ P) := by
  intro C
  let B : ℝ :=
    ∑ p ∈ P, ∑' n : ℕ, reciprocalIndicator (multipleLayer p A) n
  rcases hunbounded (B + C) with ⟨t, ht⟩
  exact ⟨t, hA.lt_freshPrimeMass_of_large_growingCapture
    hirred hPprime (k := K t) (J := J t) (Q := Q t) ht⟩

/-- Standard cutoff version of fresh-prime drift, with the moving universe
chosen as `M t.primesBelow`. -/
theorem SummabilityCounterexample.unbounded_freshPrimesBelowMass
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {K M : ℕ → ℕ} {J : ℕ → Finset ℕ}
    (hunbounded : ∀ C : ℝ, ∃ t,
      C < lcmRoomPrimeSupportMassWithin A (K t) (J t) (M t).primesBelow)
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, Nat.Prime p) :
    ∀ C : ℝ, ∃ t,
      C < lcmRoomPrimeSupportMassWithin A (K t) (J t)
        (((M t).primesBelow).filter fun p => p ∉ P) :=
  hA.unbounded_freshPrimeMass_of_unbounded_capture
    hirred hunbounded P hPprime

/-- Summing the absolute multiples majorants over the core prime support bounds
the actual prime-support capture in the LCM-room. -/
theorem lcmRoomPrimeSupportMass_le_corePrimeSupportMultiplesBelowMass
    (A : Set ℕ) (k : ℕ) (J : Finset ℕ) :
    lcmRoomPrimeSupportMass A k J ≤
      corePrimeSupportMultiplesBelowMass k J := by
  unfold lcmRoomPrimeSupportMass corePrimeSupportMultiplesBelowMass
  exact Finset.sum_le_sum fun p _hp =>
    lcmRoomPrimeDivisorMass_le_multiplesBelowReciprocalMass A k J p

/-- Mixed small/large prime bound.  Prime-support capture in the room is
controlled by the actual capture of the support primes in a fixed finite set
`P`, plus the absolute dyadic multiples majorant for support primes outside
`P`. -/
theorem lcmRoomPrimeSupportMass_le_within_add_outsideMultiples
    (A : Set ℕ) (k : ℕ) (J P : Finset ℕ) :
    lcmRoomPrimeSupportMass A k J ≤
      lcmRoomPrimeSupportMassWithin A k J P +
        corePrimeSupportOutsideMultiplesBelowMass k J P := by
  unfold lcmRoomPrimeSupportMass lcmRoomPrimeSupportMassWithin
    corePrimeSupportOutsideMultiplesBelowMass
  have hsplit :
      (∑ p ∈ corePrimeSupport J, lcmRoomPrimeDivisorMass A k J p) =
        (∑ p ∈ (corePrimeSupport J).filter (fun p => p ∈ P),
          lcmRoomPrimeDivisorMass A k J p) +
        (∑ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P),
          lcmRoomPrimeDivisorMass A k J p) := by
    rw [← Finset.sum_filter_add_sum_filter_not (corePrimeSupport J)
      (fun p => p ∈ P)]
  rw [hsplit]
  have houtside :
      (∑ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P),
          lcmRoomPrimeDivisorMass A k J p) ≤
        ∑ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P),
          multiplesBelowReciprocalMass k p := by
    exact Finset.sum_le_sum fun p _hp =>
      lcmRoomPrimeDivisorMass_le_multiplesBelowReciprocalMass A k J p
  exact add_le_add_right houtside _

theorem dyadicHarmonicMass_nonneg (k : ℕ) : 0 ≤ dyadicHarmonicMass k := by
  unfold dyadicHarmonicMass
  exact Finset.sum_nonneg fun m _hm =>
    one_div_nonneg.mpr (Nat.cast_nonneg m)

/-- A single dyadic block contributes at most one unit of harmonic mass. -/
theorem dyadicBlockHarmonicMass_le_one (k : ℕ) :
    (∑ m ∈ Finset.Ico ((2 ^ k : ℕ)) ((2 ^ (k + 1) : ℕ)),
      (1 : ℝ) / (m : ℝ)) ≤ 1 := by
  have hpowpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  calc
    (∑ m ∈ Finset.Ico ((2 ^ k : ℕ)) ((2 ^ (k + 1) : ℕ)),
      (1 : ℝ) / (m : ℝ)) ≤
        ∑ _m ∈ Finset.Ico ((2 ^ k : ℕ)) ((2 ^ (k + 1) : ℕ)),
          (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hm_ge : 2 ^ k ≤ m := (Finset.mem_Ico.mp hm).1
      have hm_real : ((2 ^ k : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hm_ge
      exact one_div_le_one_div_of_le hpowpos hm_real
    _ = ((Finset.Ico ((2 ^ k : ℕ)) ((2 ^ (k + 1) : ℕ))).card : ℝ) /
          ((2 ^ k : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = 1 := by
      have hcard :
          (Finset.Ico ((2 ^ k : ℕ)) ((2 ^ (k + 1) : ℕ))).card = 2 ^ k := by
        rw [Nat.card_Ico]
        have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
          rw [pow_succ, Nat.mul_comm, two_mul]
        rw [hpow, Nat.add_sub_cancel_left]
      rw [hcard]
      field_simp [hpowpos.ne']

/-- The harmonic mass below `2 ^ k` is at most `k`, by splitting into dyadic
blocks. -/
theorem dyadicHarmonicMass_le (k : ℕ) :
    dyadicHarmonicMass k ≤ (k : ℝ) := by
  induction k with
  | zero =>
      simp [dyadicHarmonicMass]
  | succ k ih =>
      have hpow_le : 2 ^ k ≤ 2 ^ (k + 1) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
      have hone_le : (1 : ℕ) ≤ 2 ^ k :=
        Nat.one_le_pow k 2 (by norm_num)
      have hsplit :
          Finset.Ico (1 : ℕ) ((2 ^ (k + 1) : ℕ)) =
            Finset.Ico (1 : ℕ) ((2 ^ k : ℕ)) ∪
              Finset.Ico ((2 ^ k : ℕ)) ((2 ^ (k + 1) : ℕ)) :=
                (Finset.Ico_union_Ico_eq_Ico hone_le hpow_le).symm
      have hdisj : Disjoint (Finset.Ico (1 : ℕ) ((2 ^ k : ℕ)))
          (Finset.Ico ((2 ^ k : ℕ)) ((2 ^ (k + 1) : ℕ))) :=
        Finset.Ico_disjoint_Ico_consecutive 1 (2 ^ k) (2 ^ (k + 1))
      have ih' :
          (∑ m ∈ Finset.Ico (1 : ℕ) ((2 ^ k : ℕ)),
            (1 : ℝ) / (m : ℝ)) ≤ (k : ℝ) := by
        simpa [dyadicHarmonicMass] using ih
      have hblock := dyadicBlockHarmonicMass_le_one k
      calc
        dyadicHarmonicMass (k + 1) =
            (∑ m ∈ Finset.Ico (1 : ℕ) ((2 ^ k : ℕ)),
              (1 : ℝ) / (m : ℝ)) +
              ∑ m ∈ Finset.Ico ((2 ^ k : ℕ)) ((2 ^ (k + 1) : ℕ)),
                (1 : ℝ) / (m : ℝ) := by
          unfold dyadicHarmonicMass
          rw [hsplit, Finset.sum_union hdisj]
        _ ≤ (k : ℝ) + 1 := by
          nlinarith
        _ = (k + 1 : ℕ) := by norm_num

theorem corePrimeSupportPrimeReciprocalMass_nonneg (J : Finset ℕ) :
    0 ≤ corePrimeSupportPrimeReciprocalMass J := by
  unfold corePrimeSupportPrimeReciprocalMass
  exact Finset.sum_nonneg fun p _hp =>
    one_div_nonneg.mpr (Nat.cast_nonneg p)

/-- Reciprocal identity used to reindex a positive multiple `p * m`. -/
theorem reciprocal_nat_mul_eq_inv_mul_reciprocal {p m : ℕ}
    (hp : 0 < p) (hm : 0 < m) :
    (1 : ℝ) / ((p * m : ℕ) : ℝ) =
      (1 / (p : ℝ)) * ((1 : ℝ) / (m : ℝ)) := by
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Nat.cast_mul]
  field_simp [hp_ne, hm_ne]

/-- Finite quotient scaling for a multiple layer.  A finite reciprocal sum over
elements of `A` divisible by `d` is exactly `1/d` times the reciprocal sum of
their quotients. -/
theorem finite_multipleLayer_sum_eq_inv_mul_quotient_image_sum
    {A : Set ℕ} (hApos : PositiveSet A) {d : ℕ} (hd : 0 < d)
    {F : Finset ℕ} (hF : ∀ n ∈ F, n ∈ multipleLayer d A) :
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) =
      (1 / (d : ℝ)) *
        ∑ q ∈ F.image (fun n => n / d), (1 : ℝ) / (q : ℝ) := by
  classical
  have hinj : Set.InjOn (fun n : ℕ => n / d) (F : Set ℕ) := by
    intro x hx y hy hxy
    change x / d = y / d at hxy
    have hdx : d ∣ x := (hF x hx).2
    have hdy : d ∣ y := (hF y hy).2
    calc
      x = (x / d) * d := (Nat.div_mul_cancel hdx).symm
      _ = (y / d) * d := by rw [hxy]
      _ = y := Nat.div_mul_cancel hdy
  have hterm : ∀ n ∈ F,
      (1 : ℝ) / (n : ℝ) =
        (1 / (d : ℝ)) * ((1 : ℝ) / ((n / d : ℕ) : ℝ)) := by
    intro n hn
    have hnLayer : n ∈ multipleLayer d A := hF n hn
    have hnpos : 0 < n := hApos hnLayer.1
    have hdvd : d ∣ n := hnLayer.2
    have hd_le_n : d ≤ n := Nat.le_of_dvd hnpos hdvd
    have hqpos : 0 < n / d := Nat.div_pos hd_le_n hd
    have hmul : d * (n / d) = n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hdvd
    calc
      (1 : ℝ) / (n : ℝ) =
          (1 : ℝ) / ((d * (n / d) : ℕ) : ℝ) := by rw [hmul]
      _ = (1 / (d : ℝ)) * ((1 : ℝ) / ((n / d : ℕ) : ℝ)) :=
          reciprocal_nat_mul_eq_inv_mul_reciprocal hd hqpos
  have himage :
      (∑ q ∈ F.image (fun n => n / d), (1 : ℝ) / (q : ℝ)) =
        ∑ n ∈ F, (1 : ℝ) / ((n / d : ℕ) : ℝ) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact hinj hx hy hxy
  calc
    (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) =
        ∑ n ∈ F,
          (1 / (d : ℝ)) * ((1 : ℝ) / ((n / d : ℕ) : ℝ)) := Finset.sum_congr rfl hterm
    _ = (1 / (d : ℝ)) *
        ∑ n ∈ F, (1 : ℝ) / ((n / d : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
    _ = (1 / (d : ℝ)) *
        ∑ q ∈ F.image (fun n => n / d), (1 : ℝ) / (q : ℝ) := by
      rw [himage]

/-- A finite divisor slice inside a quotient window reindexes to the composite
quotient by `p * ℓ`, losing the explicit reciprocal factor `1 / ℓ`. -/
theorem finite_quotient_divisor_slice_le_inv_mul_quotientBudget
    {A : Set ℕ} (hApos : PositiveSet A) {p ℓ : ℕ} (hℓ : 0 < ℓ)
    (hquot : ReciprocalSummable (quotientSet (p * ℓ) A))
    {F : Finset ℕ}
    (hF : ∀ q ∈ F, q ∈ quotientSet p A ∧ ℓ ∣ q) :
    (∑ q ∈ F, (1 : ℝ) / (q : ℝ)) ≤
      (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) := by
  classical
  have hFlayer : ∀ q ∈ F, q ∈ multipleLayer ℓ (quotientSet p A) := by
    intro q hq
    exact hF q hq
  let R : Finset ℕ := F.image fun q => q / ℓ
  have hscale :
      (∑ q ∈ F, (1 : ℝ) / (q : ℝ)) =
        (1 / (ℓ : ℝ)) * ∑ r ∈ R, (1 : ℝ) / (r : ℝ) := by
    simpa [R] using
      finite_multipleLayer_sum_eq_inv_mul_quotient_image_sum
        hApos.quotientSet hℓ hFlayer
  have hRmem : ∀ r ∈ R, r ∈ quotientSet (p * ℓ) A := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨q, hqF, rfl⟩
    rcases hF q hqF with ⟨hqQuot, hℓq⟩
    have hmul : ℓ * (q / ℓ) = q := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hℓq
    change (p * ℓ) * (q / ℓ) ∈ A
    rw [Nat.mul_assoc, hmul]
    simpa [quotientSet] using hqQuot
  have hRle :
      (∑ r ∈ R, (1 : ℝ) / (r : ℝ)) ≤ primeQuotientBudget A (p * ℓ) :=
    finset_sum_reciprocal_le_primeQuotientBudget hquot hRmem
  have hfactor_nonneg : 0 ≤ (1 / (ℓ : ℝ)) := by positivity
  rw [hscale]
  exact mul_le_mul_of_nonneg_left hRle hfactor_nonneg

/-- If a finite quotient window has mass larger than `C`, and a filtered part
has mass at most `S`, then the complementary part has mass larger than
`C - S`. -/
theorem finite_sum_filter_not_gt_sub_of_lt_sum_of_filter_le
    {Q : Finset ℕ} {P : ℕ → Prop} [DecidablePred P] {C S : ℝ}
    (hlarge : C < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ))
    (hsmall : (∑ q ∈ Q.filter P, (1 : ℝ) / (q : ℝ)) ≤ S) :
    C - S < ∑ q ∈ Q.filter (fun q => ¬ P q), (1 : ℝ) / (q : ℝ) := by
  have hsplit :
      (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) =
        (∑ q ∈ Q.filter P, (1 : ℝ) / (q : ℝ)) +
          ∑ q ∈ Q.filter (fun q => ¬ P q), (1 : ℝ) / (q : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Q P
      (fun q => (1 : ℝ) / (q : ℝ))]
  rw [hsplit] at hlarge
  linarith

/-- Finite averaging with an external cardinal bound.  If a sum over at most
`K` indices is larger than `K * c`, then one summand is larger than `c`. -/
theorem exists_lt_of_card_le_mul_lt_sum {α : Type*}
    {I : Finset α} {w : α → ℝ} {K : ℕ} {c : ℝ}
    (hcard : I.card ≤ K) (hc_nonneg : 0 ≤ c)
    (hlarge : (K : ℝ) * c < ∑ i ∈ I, w i) :
    ∃ i ∈ I, c < w i := by
  classical
  by_contra hnone
  have hpoint : ∀ i ∈ I, w i ≤ c := by
    intro i hi
    exact not_lt.mp fun hlt => hnone ⟨i, hi, hlt⟩
  have hsum_le : (∑ i ∈ I, w i) ≤ ∑ _i ∈ I, c :=
    Finset.sum_le_sum fun i hi => hpoint i hi
  have hconst : (∑ _i ∈ I, c) = (I.card : ℝ) * c := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_real : (I.card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hcard
  have hcard_mul : (I.card : ℝ) * c ≤ (K : ℝ) * c :=
    mul_le_mul_of_nonneg_right hcard_real hc_nonneg
  linarith

/-- A positive reciprocal mass in a filtered finite set witnesses an element
passing the filter. -/
theorem exists_mem_filter_of_pos_sum_reciprocal
    {Q : Finset ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hpos : 0 < ∑ q ∈ Q.filter P, (1 : ℝ) / (q : ℝ)) :
    ∃ q ∈ Q, P q := by
  classical
  by_contra hnone
  push Not at hnone
  have hempty : Q.filter P = ∅ := by
    ext q
    constructor
    · intro hq
      exact False.elim
        (hnone q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2)
    · intro hq
      simp at hq
  simp [hempty] at hpos

/-- A nonnegative lower bound below the large-lift reciprocal mass produces an
actual large lift. -/
theorem exists_large_lift_of_nonneg_lt_large_lift_sum
    {Q : Finset ℕ} {a p : ℕ} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hlarge : C <
      ∑ q ∈ Q.filter (fun q => a ≤ p * q), (1 : ℝ) / (q : ℝ)) :
    ∃ q ∈ Q, a ≤ p * q := by
  have hpos :
      0 < ∑ q ∈ Q.filter (fun q => a ≤ p * q), (1 : ℝ) / (q : ℝ) :=
    lt_of_le_of_lt hC_nonneg hlarge
  exact exists_mem_filter_of_pos_sum_reciprocal hpos

/-- Any large room lift `p*q` gives self-headroom for the core carrier `a`:
the room inequality for `p*q`, together with `a ≤ p*q`, implies
`lcm(J) * a ≤ 2^K`. -/
theorem lcm_mul_carrier_le_of_large_room_quotient_lift
    {A : Set ℕ} {K a p q : ℕ} {J : Finset ℕ}
    (hxRoom : p * q ∈ lcmRoomFinset A K J)
    (hlarge : a ≤ p * q) :
    J.lcm (fun y : ℕ => y) * a ≤ 2 ^ K := by
  exact (Nat.mul_le_mul_left (J.lcm fun y : ℕ => y) hlarge).trans
    (mem_lcmRoomFinset.mp hxRoom).2.2.2.2

/-- If the erased-core composite quotient budget beats `p * c`, then some
erased support prime carries weighted composite quotient budget at least the
scale-normalized amount `(p * c) / K`. -/
theorem exists_erased_support_large_weighted_compositeBudget
    {A : Set ℕ} {K r a p : ℕ} {J : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection A K r J) (haJ : a ∈ J)
    (hc_nonneg : 0 ≤ c)
    (hlarge :
      (p : ℝ) * c <
        ∑ ℓ ∈ corePrimeSupport (J.erase a),
          (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) :
    ∃ ℓ ∈ corePrimeSupport (J.erase a),
      ((p : ℝ) * c) / (K : ℝ) <
        (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) := by
  classical
  let I : Finset ℕ := corePrimeSupport (J.erase a)
  let w : ℕ → ℝ := fun ℓ =>
    (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)
  have hKpos : 0 < K := hJ.scale_pos_of_mem haJ
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hcard : I.card ≤ K := by
    have hsub : I ⊆ corePrimeSupport J := by
      intro ℓ hℓ
      exact corePrimeSupport_erase_subset J a hℓ
    exact (Finset.card_le_card hsub).trans hJ.corePrimeSupport_card_le_scale
  have hc' :
      0 ≤ ((p : ℝ) * c) / (K : ℝ) := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg p) hc_nonneg)
      (le_of_lt (Nat.cast_pos.mpr hKpos))
  have hlarge' : (K : ℝ) * (((p : ℝ) * c) / (K : ℝ)) <
      ∑ ℓ ∈ I, w ℓ := by
    have hscale :
        (K : ℝ) * (((p : ℝ) * c) / (K : ℝ)) = (p : ℝ) * c := by
      field_simp [hKne]
    simpa [I, w, hscale] using hlarge
  simpa [I, w] using
    exists_lt_of_card_le_mul_lt_sum hcard hc' hlarge'

/-- Composite-budget form of the small-lift excision.  In the irreducible
branch, the small part of a fresh `p`-quotient window is paid for by composite
quotient budgets `p * ℓ`, where `ℓ` ranges over the erased core support. -/
theorem CoprimeLCMSelection.LCMMinimal.small_room_quotient_mass_le_erased_support_quotientBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {K r a p : ℕ} {J Q : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) :
    (∑ q ∈ Q.filter (fun q => p * q < a), (1 : ℝ) / (q : ℝ)) ≤
      ∑ ℓ ∈ corePrimeSupport (J.erase a),
        (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) := by
  classical
  have hsmall := hJ.small_room_quotient_mass_le_erased_support_mass
    haJ hp hpa hQroom
  refine hsmall.trans ?_
  refine Finset.sum_le_sum fun ℓ hℓSupport => ?_
  let F : Finset ℕ := (Q.filter (fun q => p * q < a)).filter (fun q => ℓ ∣ q)
  have hℓPrime : Nat.Prime ℓ := prime_of_mem_corePrimeSupport hℓSupport
  have hcomp_gt : 1 < p * ℓ := by
    have h4 : 4 ≤ p * ℓ := by
      calc
        4 = 2 * 2 := by norm_num
        _ ≤ p * ℓ := Nat.mul_le_mul hp.two_le hℓPrime.two_le
    omega
  have hquot : ReciprocalSummable (quotientSet (p * ℓ) A) :=
    hA.reciprocalSummable_quotientSet_of_quotient_irreducible hirred hcomp_gt
  have hF : ∀ q ∈ F, q ∈ quotientSet p A ∧ ℓ ∣ q := by
    intro q hqF
    rcases Finset.mem_filter.mp hqF with ⟨hqSmall, hℓq⟩
    rcases Finset.mem_filter.mp hqSmall with ⟨hqQ, _hqSmall⟩
    have hxRoom : p * q ∈ lcmRoomFinset A K J := hQroom q hqQ
    have hxA : p * q ∈ A := (mem_lcmRoomFinset.mp hxRoom).2.2.1
    exact ⟨hxA, hℓq⟩
  simpa [F] using
    finite_quotient_divisor_slice_le_inv_mul_quotientBudget
      hA.2.1 hℓPrime.pos hquot hF

/-- A large total multiple-layer budget yields a finite quotient window with
the correspondingly scaled reciprocal mass. -/
theorem exists_quotient_finset_sum_gt_of_lt_primeLayerBudget
    {A : Set ℕ} (hApos : PositiveSet A) {d : ℕ} (hd : 0 < d)
    {c : ℝ} (hlarge : c < primeLayerBudget A d) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q ∈ quotientSet d A) ∧
      (d : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
  classical
  rcases exists_lt_finset_sum_of_lt_tsum_nonneg
      (fun n => reciprocalIndicator_nonneg (multipleLayer d A) n)
      (by simpa [primeLayerBudget] using hlarge) with
    ⟨F, hFlarge⟩
  let Fm : Finset ℕ := F.filter fun n => n ∈ multipleLayer d A
  have hsum_filter :
      (∑ n ∈ F, reciprocalIndicator (multipleLayer d A) n) =
        ∑ n ∈ Fm, (1 : ℝ) / (n : ℝ) := by
    dsimp [Fm, reciprocalIndicator]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases hnLayer : n ∈ multipleLayer d A
    · simp [hnLayer]
    · simp [hnLayer]
  have hFmlarge : c < ∑ n ∈ Fm, (1 : ℝ) / (n : ℝ) := by
    simpa [hsum_filter] using hFlarge
  have hFm : ∀ n ∈ Fm, n ∈ multipleLayer d A := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  let Q : Finset ℕ := Fm.image fun n => n / d
  have hQmem : ∀ q ∈ Q, q ∈ quotientSet d A := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hnFm, rfl⟩
    have hnLayer : n ∈ multipleLayer d A := hFm n hnFm
    have hmul : d * (n / d) = n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hnLayer.2
    change d * (n / d) ∈ A
    simpa [hmul] using hnLayer.1
  have hscale :
      (∑ n ∈ Fm, (1 : ℝ) / (n : ℝ)) =
        (1 / (d : ℝ)) *
          ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
    simpa [Q] using
      finite_multipleLayer_sum_eq_inv_mul_quotient_image_sum
        hApos hd hFm
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hFmlarge_scaled :
      c < (1 / (d : ℝ)) *
        ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
    rw [hscale] at hFmlarge
    exact hFmlarge
  have hmul_lt :
      (d : ℝ) * c <
        (d : ℝ) * ((1 / (d : ℝ)) *
          ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := mul_lt_mul_of_pos_left hFmlarge_scaled hdpos
  have hright :
      (d : ℝ) * ((1 / (d : ℝ)) *
          ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) =
        ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
    field_simp [hdne]
  rw [hright] at hmul_lt
  exact ⟨Q, hQmem, hmul_lt⟩

/-- A large prime-divisor contribution inside one LCM-room gives a finite
quotient window whose lifted elements remain in that same LCM-room. -/
theorem exists_room_quotient_finset_sum_gt_of_lt_lcmRoomPrimeDivisorMass
    {A : Set ℕ} (hApos : PositiveSet A) {K : ℕ} {J : Finset ℕ}
    {p : ℕ} (hp : 0 < p) {c : ℝ}
    (hlarge : c < lcmRoomPrimeDivisorMass A K J p) :
    ∃ Q : Finset ℕ,
      (∀ q ∈ Q, q ∈ quotientSet p A) ∧
      (∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) ∧
      (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
  classical
  let F : Finset ℕ := (lcmRoomFinset A K J).filter (fun x => p ∣ x)
  have hF : ∀ n ∈ F, n ∈ multipleLayer p A := by
    intro n hn
    exact ⟨(mem_lcmRoomFinset.mp (Finset.mem_filter.mp hn).1).2.2.1,
      (Finset.mem_filter.mp hn).2⟩
  have hscale :
      (∑ n ∈ F, (1 : ℝ) / (n : ℝ)) =
        (1 / (p : ℝ)) *
          ∑ q ∈ F.image (fun n => n / p), (1 : ℝ) / (q : ℝ) :=
    finite_multipleLayer_sum_eq_inv_mul_quotient_image_sum hApos hp hF
  let Q : Finset ℕ := F.image fun n => n / p
  have hQmem : ∀ q ∈ Q, q ∈ quotientSet p A := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hnF, rfl⟩
    have hnLayer : n ∈ multipleLayer p A := hF n hnF
    have hmul : p * (n / p) = n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hnLayer.2
    change p * (n / p) ∈ A
    simpa [hmul] using hnLayer.1
  have hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hnF, rfl⟩
    have hroom : n ∈ lcmRoomFinset A K J := (Finset.mem_filter.mp hnF).1
    have hpn : p ∣ n := (Finset.mem_filter.mp hnF).2
    have hmul : p * (n / p) = n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hpn
    simpa [hmul] using hroom
  have hlargeF : c < ∑ n ∈ F, (1 : ℝ) / (n : ℝ) := by
    simpa [lcmRoomPrimeDivisorMass, F] using hlarge
  have hp_pos_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos_real
  have hlarge_scaled :
      c < ((p : ℝ)⁻¹) *
        ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
    have hone : ((p : ℝ)⁻¹) = 1 / (p : ℝ) := by
      rw [one_div]
    rw [hone]
    rw [hscale] at hlargeF
    simpa [Q] using hlargeF
  have hmul_lt :
      (p : ℝ) * c <
        (p : ℝ) * (((p : ℝ)⁻¹) *
          ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) :=
    mul_lt_mul_of_pos_left hlarge_scaled hp_pos_real
  have hright :
      (p : ℝ) * (((p : ℝ)⁻¹) *
          ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) =
        ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
    field_simp [hp_ne]
  rw [hright] at hmul_lt
  exact ⟨Q, hQmem, hQroom, hmul_lt⟩

/-- Fresh quotient-window extraction from a heavy delayed room-cover.  After
paying an old finite prime set `P`, any remaining excess that forces a fresh
large prime layer also gives a finite quotient window through that fresh prime
with reciprocal mass larger than `p * c`. -/
theorem SummabilityCounterexample.exists_fresh_quotient_window_of_room_cover_heavy_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN2 : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover :
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (hc_nonneg : 0 ≤ c)
    (hheavy :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
        dyadicPrefixReciprocalMass A N m) :
    ∃ p ∈ corePrimeSupport J, p ∉ P ∧
      ∃ Q : Finset ℕ, (∀ q ∈ Q, q ∈ quotientSet p A) ∧
        (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
  rcases hA.exists_fresh_large_primeLayerBudget_of_room_cover_heavy_prefix
      hirred hJ hN2 hdelay hcover hc_nonneg hheavy with
    ⟨p, hpSupport, hpNotP, hpLarge⟩
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  rcases exists_quotient_finset_sum_gt_of_lt_primeLayerBudget
      hA.2.1 hpPrime.pos hpLarge with
    ⟨Q, hQmem, hQlarge⟩
  exact ⟨p, hpSupport, hpNotP, Q, hQmem, hQlarge⟩

/-- Strong local fresh quotient-window extraction.  The quotient window comes
from mass inside the current LCM-room, so each quotient `q` lifts back to an
element `p*q` of that same room. -/
theorem SummabilityCounterexample.exists_fresh_room_quotient_window_of_heavy_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN2 : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover :
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (hc_nonneg : 0 ≤ c)
    (hheavy :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
        dyadicPrefixReciprocalMass A N m) :
    ∃ p ∈ corePrimeSupport J, p ∉ P ∧
      ∃ Q : Finset ℕ,
        (∀ q ∈ Q, q ∈ quotientSet p A) ∧
        (∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) ∧
        (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
  rcases hA.exists_fresh_large_lcmRoomPrimeDivisorMass
      hirred hJ hN2 hdelay hcover hc_nonneg hheavy with
    ⟨p, hpSupport, hpNotP, hpLarge⟩
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  rcases exists_room_quotient_finset_sum_gt_of_lt_lcmRoomPrimeDivisorMass
      hA.2.1 hpPrime.pos hpLarge with
    ⟨Q, hQmem, hQroom, hQlarge⟩
  exact ⟨p, hpSupport, hpNotP, Q, hQmem, hQroom, hQlarge⟩

/-- Heavy delayed prefixes force a fresh prime whose whole quotient layer has
large finite budget.  This packages the local quotient window into a global
finite bound available in the quotient-irreducible branch. -/
theorem SummabilityCounterexample.exists_fresh_large_primeQuotientBudget_of_heavy_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN2 : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover :
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (hc_nonneg : 0 ≤ c)
    (hheavy :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
        dyadicPrefixReciprocalMass A N m) :
    ∃ p ∈ corePrimeSupport J, p ∉ P ∧
      (p : ℝ) * c < primeQuotientBudget A p := by
  rcases hA.exists_fresh_room_quotient_window_of_heavy_prefix
      hirred hJ hN2 hdelay hcover hc_nonneg hheavy with
    ⟨p, hpSupport, hpNotP, Q, hQmem, _hQroom, hQlarge⟩
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  have hquot : ReciprocalSummable (quotientSet p A) :=
    hA.reciprocalSummable_quotientSet_prime_of_quotient_irreducible
      hirred hpPrime
  have hQle :
      (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) ≤ primeQuotientBudget A p :=
    finset_sum_reciprocal_le_primeQuotientBudget hquot hQmem
  exact ⟨p, hpSupport, hpNotP, hQlarge.trans_le hQle⟩

/-- Fresh room quotient window after small-lift excision.  Once the small
lifts `p*q < a` are paid for by composite quotient budgets from the erased
core, the remaining large-lift part `a ≤ p*q` still carries the leftover
mass. -/
theorem SummabilityCounterexample.exists_fresh_room_quotient_large_lift_remainder_of_heavy_prefix
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J P : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hN2 : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover :
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (hc_nonneg : 0 ≤ c)
    (hheavy :
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
        dyadicPrefixReciprocalMass A N m) :
    ∃ p ∈ corePrimeSupport J, p ∉ P ∧
      ∃ a ∈ J, p ∣ a ∧
        ∃ Q : Finset ℕ,
          (∀ q ∈ Q, q ∈ quotientSet p A) ∧
          (∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) ∧
          (p : ℝ) * c -
              (∑ ℓ ∈ corePrimeSupport (J.erase a),
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) <
            ∑ q ∈ Q.filter (fun q => a ≤ p * q), (1 : ℝ) / (q : ℝ) := by
  classical
  rcases hA.exists_fresh_room_quotient_window_of_heavy_prefix
      hirred hJ hN2 hdelay hcover hc_nonneg hheavy with
    ⟨p, hpSupport, hpNotP, Q, hQmem, hQroom, hQlarge⟩
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  rcases exists_mem_dvd_of_mem_corePrimeSupport hpSupport with ⟨a, haJ, hpa⟩
  let S : ℝ := ∑ ℓ ∈ corePrimeSupport (J.erase a),
    (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)
  have hsmall :
      (∑ q ∈ Q.filter (fun q => p * q < a), (1 : ℝ) / (q : ℝ)) ≤ S := by
    dsimp [S]
    exact hJ.small_room_quotient_mass_le_erased_support_quotientBudget
      hA hirred haJ hpPrime hpa hQroom
  have hremainder_not :
      (p : ℝ) * c - S <
        ∑ q ∈ Q.filter (fun q => ¬ p * q < a), (1 : ℝ) / (q : ℝ) :=
    finite_sum_filter_not_gt_sub_of_lt_sum_of_filter_le
      (Q := Q) (P := fun q => p * q < a) hQlarge hsmall
  have hremainder :
      (p : ℝ) * c - S <
        ∑ q ∈ Q.filter (fun q => a ≤ p * q), (1 : ℝ) / (q : ℝ) := by
    simpa [S, not_lt] using hremainder_not
  exact ⟨p, hpSupport, hpNotP, a, haJ, hpa, Q, hQmem, hQroom, hremainder⟩

/-- Carrier-aware aggregation of small-lift excision and large-lift packing.
For a fixed carrier `a` of the prime `p`, a heavy room quotient window either
has its mass paid by the erased-core composite quotient budgets plus the
large-lift packing allowance, or else one of the large lifts has reciprocal
weight above the chosen threshold `η`. -/
theorem SummabilityCounterexample.carrier_quotient_mass_le_or_large_lift_weight
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {K r a p : ℕ} {J Q : Finset ℕ} {c η : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J)
    (hη : 0 ≤ η)
    (hlarge : (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) :
    (p : ℝ) * c ≤
        (∑ ℓ ∈ corePrimeSupport (J.erase a),
          (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) +
        ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) * η) ∨
      ∃ q ∈ Q, a ≤ p * q ∧ η < (1 : ℝ) / (q : ℝ) := by
  classical
  let S : ℝ := ∑ ℓ ∈ corePrimeSupport (J.erase a),
    (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)
  let B : ℕ := (a / 2 + 1) * ((2 ^ K) / a + 1)
  have hsmall :
      (∑ q ∈ Q.filter (fun q => p * q < a), (1 : ℝ) / (q : ℝ)) ≤ S := by
    dsimp [S]
    exact hJ.small_room_quotient_mass_le_erased_support_quotientBudget
      hA hirred haJ hp hpa hQroom
  by_cases hpay : (p : ℝ) * c ≤ S + (B : ℝ) * η
  · exact Or.inl (by simpa [S, B] using hpay)
  · have hpay_lt : S + (B : ℝ) * η < (p : ℝ) * c := lt_of_not_ge hpay
    have hremainder_not :
        (p : ℝ) * c - S <
          ∑ q ∈ Q.filter (fun q => ¬ p * q < a), (1 : ℝ) / (q : ℝ) :=
      finite_sum_filter_not_gt_sub_of_lt_sum_of_filter_le
        (Q := Q) (P := fun q => p * q < a) hlarge hsmall
    have hremainder :
        (p : ℝ) * c - S <
          ∑ q ∈ Q.filter (fun q => a ≤ p * q), (1 : ℝ) / (q : ℝ) := by
      simpa [not_lt] using hremainder_not
    have hBη_lt :
        (B : ℝ) * η <
          ∑ q ∈ Q.filter (fun q => a ≤ p * q), (1 : ℝ) / (q : ℝ) := by
      linarith
    have hcard :
        (Q.filter fun q => a ≤ p * q).card ≤ B := by
      dsimp [B]
      exact hJ.carrier_large_quotient_card_le_scale_cover
        hA.2.2.1 haJ hp hQroom
    rcases exists_lt_of_card_le_mul_lt_sum
        (I := Q.filter fun q => a ≤ p * q)
        (w := fun q => (1 : ℝ) / (q : ℝ))
        (K := B) (c := η) hcard hη hBη_lt with
      ⟨q, hqLarge, hqη⟩
    rcases Finset.mem_filter.mp hqLarge with ⟨hqQ, hlargeLift⟩
    exact Or.inr ⟨q, hqQ, hlargeLift, hqη⟩

/-- Clearing denominators in the large-lift threshold.  If
`p / a < 1 / q`, then `p*q < a`.  This is the arithmetic reason the packed
carrier fork collapses when the threshold is chosen to be `p/a`. -/
theorem nat_mul_lt_of_div_lt_inv {a p q : ℕ} (ha : 0 < a) (hq : 0 < q)
    (hη : (p : ℝ) / (a : ℝ) < (1 : ℝ) / (q : ℝ)) :
    p * q < a := by
  have hreal : ((p * q : ℕ) : ℝ) < (a : ℝ) := by
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hp_lt : (p : ℝ) < ((1 : ℝ) / (q : ℝ)) * (a : ℝ) := (div_lt_iff₀ haR).mp hη
    have hmul := mul_lt_mul_of_pos_right hp_lt hqR
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
    have hright :
        ((1 : ℝ) / (q : ℝ)) * (a : ℝ) * (q : ℝ) = (a : ℝ) := by
      field_simp [hqne]
    have hleft : (p : ℝ) * (q : ℝ) = ((p * q : ℕ) : ℝ) := by
      norm_num
    rwa [hleft, hright] at hmul
  exact_mod_cast hreal

/-- Carrier-aware quotient mass with the high-lift branch eliminated.  Choosing
the reciprocal threshold `η = p/a` in the packed fork makes a surviving large
lift impossible: `a ≤ p*q` and `p/a < 1/q` would imply `p*q < a`.

Thus every heavy fresh quotient window is paid by erased-core composite
quotient budgets plus the explicit carrier packing error
`((a/2+1) * ((2^K)/a+1)) * p/a`. -/
theorem SummabilityCounterexample.carrier_quotient_mass_le_erased_budget_add_packingRatio
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {K r a p : ℕ} {J Q : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J)
    (hlarge : (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) :
    (p : ℝ) * c ≤
        (∑ ℓ ∈ corePrimeSupport (J.erase a),
          (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) +
        ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
          ((p : ℝ) / (a : ℝ))) := by
  have hapos : 0 < a := hA.2.1 (hJ.1.1 a haJ)
  have hη_nonneg : 0 ≤ (p : ℝ) / (a : ℝ) := div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg a)
  rcases hA.carrier_quotient_mass_le_or_large_lift_weight
      hirred hJ haJ hp hpa hQroom hη_nonneg hlarge with
    hpaid | hheavy
  · simpa using hpaid
  · rcases hheavy with ⟨q, hqQ, hlargeLift, hqη⟩
    have hxA : p * q ∈ A :=
      (mem_lcmRoomFinset.mp (hQroom q hqQ)).2.2.1
    have hxpos : 0 < p * q := hA.2.1 hxA
    have hqpos : 0 < q := by
      rw [Nat.mul_comm] at hxpos
      exact Nat.pos_of_mul_pos_right hxpos
    have hsmall : p * q < a :=
      nat_mul_lt_of_div_lt_inv hapos hqpos hqη
    exact False.elim ((not_lt_of_ge hlargeLift) hsmall)

/-- If `x` is bounded by a sum of two terms, then at least one term carries
half of `x`.  This is the elementary accounting split used after the packed
carrier inequality. -/
theorem half_le_or_half_le_of_le_add {x y z : ℝ} (h : x ≤ y + z) :
    x / 2 ≤ y ∨ x / 2 ≤ z := by
  by_cases hy : x / 2 ≤ y
  · exact Or.inl hy
  · exact Or.inr (by linarith)

/-- Carrier-budget share fork.  Running the deterministic carrier inequality
with threshold `2*c` gives a clean two-way accounting alternative: either the
erased-core composite quotient budgets pay `p*c`, or the explicit packing
ratio pays `p*c`. -/
theorem SummabilityCounterexample.carrier_quotient_mass_share_or_packingRatio
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {K r a p : ℕ} {J Q : Finset ℕ} {c : ℝ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (haJ : a ∈ J)
    (hp : Nat.Prime p) (hpa : p ∣ a)
    (hQroom : ∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J)
    (hlarge : (p : ℝ) * (2 * c) < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) :
    (p : ℝ) * c ≤
        ∑ ℓ ∈ corePrimeSupport (J.erase a),
          (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∨
      (p : ℝ) * c ≤
        ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
          ((p : ℝ) / (a : ℝ))) := by
  have hpaid :=
    hA.carrier_quotient_mass_le_erased_budget_add_packingRatio
      hirred hJ haJ hp hpa hQroom hlarge
  rcases half_le_or_half_le_of_le_add hpaid with hcomp | hpack
  · exact Or.inl (by
      have hscale : ((p : ℝ) * (2 * c)) / 2 = (p : ℝ) * c := by ring
      simpa [hscale] using hcomp)
  · exact Or.inr (by
      have hscale : ((p : ℝ) * (2 * c)) / 2 = (p : ℝ) * c := by ring
      simpa [hscale] using hpack)

/-- The normalized packing-ratio term attached to one carrier at one scale:
the large-lift packing count divided by the carrier.  The factor `p` has been
cancelled from the branch inequality `p*c ≤ packing_count * p/a`. -/
noncomputable def carrierPackingRatioTerm (K a : ℕ) : ℝ :=
  ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) / (a : ℝ))

/-- Finite box for all carrier packing ratios with `K ≤ D` and
`1 ≤ a ≤ 2^D`. -/
noncomputable def carrierPackingRatioBox (D : ℕ) : ℝ :=
  ∑ t ∈ (Finset.Icc 0 D).product (Finset.Icc 1 (2 ^ D)),
    carrierPackingRatioTerm t.1 t.2

/-- The finite carrier-packing box is nonnegative. -/
theorem carrierPackingRatioBox_nonneg (D : ℕ) :
    0 ≤ carrierPackingRatioBox D := by
  dsimp [carrierPackingRatioBox, carrierPackingRatioTerm]
  exact Finset.sum_nonneg fun t _ht => by
    exact div_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg t.2)

/-- Any normalized carrier-packing term inside the finite scale box is bounded
by the whole box. -/
theorem carrierPackingRatioTerm_le_box
    {D K a : ℕ} (hK : K ≤ D) (ha1 : 1 ≤ a) (haD : a ≤ 2 ^ D) :
    carrierPackingRatioTerm K a ≤ carrierPackingRatioBox D := by
  dsimp [carrierPackingRatioBox]
  refine Finset.single_le_sum (a := (K, a))
    (s := (Finset.Icc 0 D).product (Finset.Icc 1 (2 ^ D)))
    (f := fun t : ℕ × ℕ => carrierPackingRatioTerm t.1 t.2) ?_ ?_
  · intro t _ht
    dsimp [carrierPackingRatioTerm]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg t.2)
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le K, hK⟩,
        Finset.mem_Icc.mpr ⟨ha1, haD⟩⟩

/-- The packing-ratio branch is bounded by the finite packing box whenever the
carrier and scale lie inside that box. -/
theorem carrierPackingRatio_branch_le_box
    {D K a p : ℕ} {c : ℝ}
    (hp : 0 < p) (ha1 : 1 ≤ a) (hK : K ≤ D) (haD : a ≤ 2 ^ D)
    (hpack :
      (p : ℝ) * c ≤
        ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
          ((p : ℝ) / (a : ℝ)))) :
    c ≤ carrierPackingRatioBox D := by
  have ha : 0 < a := Nat.lt_of_lt_of_le Nat.zero_lt_one ha1
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hdiv := div_le_div_of_nonneg_right hpack (le_of_lt hpR)
  have hleft : ((p : ℝ) * c) / (p : ℝ) = c := by
    field_simp [ne_of_gt hpR]
  have hright :
      ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
          ((p : ℝ) / (a : ℝ))) / (p : ℝ) =
        carrierPackingRatioTerm K a := by
    dsimp [carrierPackingRatioTerm]
    field_simp [ne_of_gt hpR, ne_of_gt haR]
  have hterm : c ≤ carrierPackingRatioTerm K a := by
    rwa [hleft, hright] at hdiv
  exact hterm.trans (carrierPackingRatioTerm_le_box hK ha1 haD)

/-- Prefix-forcing version of the quotient-window fork.  For fixed rank and
scale ceilings, a sufficiently heavy prefix forces every delayed bounded-rank
room-cover obstruction either above the scale ceiling or into a fresh quotient
window with mass larger than `p * c`. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_freshQuotient
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ Q : Finset ℕ, (∀ q ∈ Q, q ∈ quotientSet p A) ∧
            (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
  rcases hA.exists_prefix_forces_large_scale_or_fresh_primeLayerBudget
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, hpLarge⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    rcases exists_quotient_finset_sum_gt_of_lt_primeLayerBudget
        hA.2.1 hpPrime.pos hpLarge with
      ⟨Q, hQmem, hQlarge⟩
    exact Or.inr ⟨p, hpSupport, hpNotP, Q, hQmem, hQlarge⟩

/-- Strong prefix-forcing quotient fork.  The fresh quotient window is produced
from actual mass in the current LCM-room, so every quotient lifts back into
that same room. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_freshRoomQuotient
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ Q : Finset ℕ,
            (∀ q ∈ Q, q ∈ quotientSet p A) ∧
            (∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) ∧
            (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
  let C : ℝ :=
    (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
      ((∑ p ∈ P, primeLayerBudget A p) + (B : ℝ) * c)
  have hC_nonneg : 0 ≤ C := by
    have hbase_nonneg :
        0 ≤ (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
      positivity
    have hsum_nonneg :
        0 ≤ ∑ p ∈ P, primeLayerBudget A p :=
          Finset.sum_nonneg fun p _hp => primeLayerBudget_nonneg A p
    have hBc_nonneg : 0 ≤ (B : ℝ) * c :=
      mul_nonneg (Nat.cast_nonneg B) hc_nonneg
    dsimp [C]
    linarith
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC_nonneg N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  by_cases hBK : B < K
  · exact Or.inl hBK
  · have hKB : K ≤ B := not_lt.mp hBK
    have hdelay : J.lcm (fun a : ℕ => a) * 2 ^ ((n - 1) + 1) ≤ 2 ^ K :=
      hJ.delay_of_prior_selection hJ₀ hTK hdelay₀
    have hbase_le :
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤
          (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
      have hrR_real : (r : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hrR
      exact div_le_div_of_nonneg_right hrR_real (by positivity)
    have hKc_le : (K : ℝ) * c ≤ (B : ℝ) * c := by
      have hKB_real : (K : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast hKB
      exact mul_le_mul_of_nonneg_right hKB_real hc_nonneg
    have hprefix_m :
        C < dyadicPrefixReciprocalMass A N (n - 1) := by
      simpa using hprefix
    have hheavy :
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            ((∑ p ∈ P, primeLayerBudget A p) + (K : ℝ) * c) <
          dyadicPrefixReciprocalMass A N (n - 1) := by
      dsimp [C] at hprefix_m
      linarith
    exact Or.inr
      (hA.exists_fresh_room_quotient_window_of_heavy_prefix
        hirred hJ hN2 hdelay hcover hc_nonneg hheavy)

/-- Prefix-forcing carrier-aware quotient fork.  The fresh room quotient window
from the heavy-prefix argument can be split at any chosen reciprocal threshold
`η`: either its mass is paid by erased-core composite quotient budgets plus the
carrier packing allowance, or a large lift with reciprocal weight above `η`
survives inside the same LCM-room. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_carrierPackedQuotient
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c η : ℝ}
    (hc_nonneg : 0 ≤ c) (hη : 0 ≤ η) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((p : ℝ) * c ≤
                (∑ ℓ ∈ corePrimeSupport (J.erase a),
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) +
                ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) * η) ∨
              ∃ q, q ∈ quotientSet p A ∧
                p * q ∈ lcmRoomFinset A K J ∧
                a ≤ p * q ∧ η < (1 : ℝ) / (q : ℝ)) := by
  rcases hA.exists_prefix_forces_scale_or_freshRoomQuotient
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, Q, hQmem, hQroom, hQlarge⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    rcases exists_mem_dvd_of_mem_corePrimeSupport hpSupport with ⟨a, haJ, hpa⟩
    have hsplit :=
      hA.carrier_quotient_mass_le_or_large_lift_weight
        hirred hJ haJ hpPrime hpa hQroom hη hQlarge
    rcases hsplit with hpaid | hheavy
    · exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa, Or.inl hpaid⟩
    · rcases hheavy with ⟨q, hqQ, hlargeLift, hqη⟩
      exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa,
          Or.inr ⟨q, hQmem q hqQ, hQroom q hqQ, hlargeLift, hqη⟩⟩

/-- Prefix-forcing deterministic carrier-budget bound.  The local packed fork
can be run with threshold `η = p/a`, eliminating the high-lift alternative.
Thus a fresh room quotient window forces either scale escape or an explicit
carrier inequality with only erased-core composite budgets and the residue
packing error. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_carrierBudgetBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            (p : ℝ) * c ≤
              (∑ ℓ ∈ corePrimeSupport (J.erase a),
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) +
              ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
                ((p : ℝ) / (a : ℝ))) := by
  rcases hA.exists_prefix_forces_scale_or_freshRoomQuotient
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, Q, _hQmem, hQroom, hQlarge⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    rcases exists_mem_dvd_of_mem_corePrimeSupport hpSupport with ⟨a, haJ, hpa⟩
    have hpaid :=
      hA.carrier_quotient_mass_le_erased_budget_add_packingRatio
        hirred hJ haJ hpPrime hpa hQroom hQlarge
    exact Or.inr ⟨p, hpSupport, hpNotP, a, haJ, hpa, hpaid⟩

/-- Prefix-forcing share/packing fork.  By forcing a quotient window of mass
larger than `2*p*c`, the deterministic carrier inequality splits cleanly:
below the scale ceiling, a fresh carrier has either erased-core composite
budget at least `p*c`, or packing-ratio allowance at least `p*c`. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_carrierShareOrPacking
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((p : ℝ) * c ≤
                ∑ ℓ ∈ corePrimeSupport (J.erase a),
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∨
              (p : ℝ) * c ≤
                ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
                  ((p : ℝ) / (a : ℝ)))) := by
  have hc2_nonneg : 0 ≤ 2 * c := by nlinarith
  rcases hA.exists_prefix_forces_scale_or_freshRoomQuotient
      hirred (R := R) (B := B) hN2 P hc2_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, Q, _hQmem, hQroom, hQlarge⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    rcases exists_mem_dvd_of_mem_corePrimeSupport hpSupport with ⟨a, haJ, hpa⟩
    have hfork :=
      hA.carrier_quotient_mass_share_or_packingRatio
        hirred hJ haJ hpPrime hpa hQroom hQlarge
    exact Or.inr ⟨p, hpSupport, hpNotP, a, haJ, hpa, hfork⟩

/-- Prefix-forcing composite-budget fork after boxing the packing branch.
If `c` is larger than the finite packing-ratio box for the scale ceiling `B`,
then the packing-ratio side of the carrier fork is impossible whenever
`K ≤ B`.  Thus below the scale ceiling the fresh carrier must be paid by
erased-core composite quotient budgets. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_carrierCompositeBudget_of_packingBox
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hbox : carrierPackingRatioBox B < c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            (p : ℝ) * c ≤
              ∑ ℓ ∈ corePrimeSupport (J.erase a),
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) := by
  rcases hA.exists_prefix_forces_scale_or_carrierShareOrPacking
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  by_cases hBK : B < K
  · exact Or.inl hBK
  · have hKB : K ≤ B := not_lt.mp hBK
    rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
      hscale | hfresh
    · exact Or.inl hscale
    · rcases hfresh with ⟨p, hpSupport, hpNotP, a, haJ, hpa, hbranch⟩
      rcases hbranch with hcomp | hpack
      · exact Or.inr ⟨p, hpSupport, hpNotP, a, haJ, hpa, hcomp⟩
      · have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
        have ha1 : 1 ≤ a := by
          have ha_large : 4 ≤ a := hJ.1.2.2.2.2.1 a haJ
          omega
        have haD : a ≤ 2 ^ B := by
          have halt : a < 2 ^ K := hJ.1.2.1 a haJ
          have hpow : 2 ^ K ≤ 2 ^ B :=
            Nat.pow_le_pow_right (by norm_num : 0 < 2) hKB
          exact (Nat.le_of_lt halt).trans hpow
        have hleBox : c ≤ carrierPackingRatioBox B :=
          carrierPackingRatio_branch_le_box
            hpPrime.pos ha1 hKB haD hpack
        exact False.elim ((not_lt_of_ge hleBox) hbox)

/-- Prefix-forcing localized weighted composite-budget fork after boxing the
packing branch.  Running the boxed composite fork at threshold `2*c` leaves
strict room to average the erased-core composite-budget sum, producing one
erased support prime `ℓ` whose weighted composite quotient budget beats
`(p*c)/K`. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_weightedBudget_of_packingBox
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_pos : 0 < c) (hbox : carrierPackingRatioBox B < 2 * c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ ℓ ∈ corePrimeSupport (J.erase a),
              ((p : ℝ) * c) / (K : ℝ) <
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) := by
  have hc2_nonneg : 0 ≤ 2 * c := by nlinarith
  rcases hA.exists_prefix_forces_scale_or_carrierCompositeBudget_of_packingBox
      hirred (R := R) (B := B) hN2 P hc2_nonneg hbox with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, a, haJ, hpa, hcomp⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hstrict :
        (p : ℝ) * c <
          ∑ ℓ ∈ corePrimeSupport (J.erase a),
            (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) := by
      have hpc_lt : (p : ℝ) * c < (p : ℝ) * (2 * c) := by
        nlinarith
      exact hpc_lt.trans_le hcomp
    have hℓ :=
      exists_erased_support_large_weighted_compositeBudget
        hJ.1 haJ (le_of_lt hc_pos) hstrict
    exact Or.inr ⟨p, hpSupport, hpNotP, a, haJ, hpa, hℓ⟩

/-- Prefix-forcing normalized composite-budget fork after boxing packing.  If
the packing branch is boxed away and the scale stays below `B`, the localized
weighted composite budget normalizes to a divisor `p*ℓ ≤ 2^K` whose quotient
budget per unit divisor beats the target `C`. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_normalizedBudget_of_packingBox
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {C : ℝ}
    (hC_nonneg : 0 ≤ C) (hBC_pos : 0 < (B : ℝ) * C)
    (hbox : carrierPackingRatioBox B < 2 * ((B : ℝ) * C)) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ ℓ ∈ corePrimeSupport (J.erase a),
              C < primeQuotientBudget A (p * ℓ) /
                  (((p * ℓ : ℕ) : ℝ)) ∧
                p * ℓ ≤ 2 ^ K := by
  rcases hA.exists_prefix_forces_scale_or_weightedBudget_of_packingBox
      hirred (R := R) (B := B) hN2 P hBC_pos hbox with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  by_cases hBK : B < K
  · exact Or.inl hBK
  · have hKB : K ≤ B := not_lt.mp hBK
    rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
      hscale | hfresh
    · exact Or.inl hscale
    · rcases hfresh with
        ⟨p, hpSupport, hpNotP, a, haJ, hpa, ℓ, hℓSupport, hweighted⟩
      have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
      have hℓPrime : Nat.Prime ℓ := prime_of_mem_corePrimeSupport hℓSupport
      have hscaleℓ : p * ℓ ≤ 2 ^ K :=
        hJ.1.mul_erasedSupport_le_two_pow haJ hpPrime hpa hℓSupport
      have hbudget :
          (((p * ℓ : ℕ) : ℝ) * ((B : ℝ) * C)) / (K : ℝ) <
            primeQuotientBudget A (p * ℓ) :=
        compositeQuotientBudget_lt_of_weightedBudget hℓPrime.pos hweighted
      have hKpos : 0 < K := hJ.1.scale_pos_of_mem haJ
      have hdpos : 0 < p * ℓ := Nat.mul_pos hpPrime.pos hℓPrime.pos
      have hnorm :
          C < primeQuotientBudget A (p * ℓ) /
              (((p * ℓ : ℕ) : ℝ)) :=
        normalizedBudget_lt_of_compositeBudget_lt
          (K := K) (D := B) (d := p * ℓ)
          hKpos hdpos hKB hC_nonneg hbudget
      exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa, ℓ, hℓSupport, hnorm,
          hscaleℓ⟩

/-- Prefix-forcing scale escape from the two finite boxes.  For a positive
scale ceiling `B`, choose a target larger than both the finite normalized
composite-budget box and the finite carrier-packing box.  The boxed-packing
normalized fork then has no below-ceiling branch, so every bounded-rank
room-cover obstruction forced by the prefix must satisfy `B < K`. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_of_budgetBoxes
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (hBpos : 0 < B) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K := by
  let C : ℝ :=
    normalizedCompositeQuotientBudgetBox A B + carrierPackingRatioBox B + 1
  have hnorm_nonneg : 0 ≤ normalizedCompositeQuotientBudgetBox A B :=
    normalizedCompositeQuotientBudgetBox_nonneg A B
  have hpack_nonneg : 0 ≤ carrierPackingRatioBox B :=
    carrierPackingRatioBox_nonneg B
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    linarith
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith
  have hBreal_ge_one : (1 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hBpos
  have hBC_pos : 0 < (B : ℝ) * C :=
    mul_pos (lt_of_lt_of_le zero_lt_one hBreal_ge_one) hC_pos
  have hpacking_box : carrierPackingRatioBox B < 2 * ((B : ℝ) * C) := by
    dsimp [C]
    nlinarith
  rcases hA.exists_prefix_forces_scale_or_normalizedBudget_of_packingBox
      hirred (R := R) (B := B) hN2 (∅ : Finset ℕ)
      hC_nonneg hBC_pos hpacking_box with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  by_cases hBK : B < K
  · exact hBK
  · have hKB : K ≤ B := not_lt.mp hBK
    rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
      hscale | hfresh
    · exact hscale
    · rcases hfresh with
        ⟨p, hpSupport, _hpNotP, a, _haJ, _hpa, ℓ, hℓSupport, hnorm,
          hscaleℓ⟩
      exfalso
      have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
      have hℓPrime : Nat.Prime ℓ := prime_of_mem_corePrimeSupport hℓSupport
      have hdpos : 0 < p * ℓ := Nat.mul_pos hpPrime.pos hℓPrime.pos
      have hd1 : 1 ≤ p * ℓ := Nat.succ_le_of_lt hdpos
      have hKDpow : 2 ^ K ≤ 2 ^ B :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hKB
      have hdD : p * ℓ ≤ 2 ^ B := hscaleℓ.trans hKDpow
      have hle :=
        normalizedCompositeQuotientBudget_le_box A hd1 hdD
      have hbox_lt_C : normalizedCompositeQuotientBudgetBox A B < C := by
        dsimp [C]
        linarith
      exact (not_lt_of_ge (le_of_lt hbox_lt_C)) (hnorm.trans_le hle)

/-- Prefix-forcing large-lift remainder fork.  After the small quotient lifts
are paid for by erased-core composite quotient budgets, the large-lift
remainder still carries the leftover mass. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_freshLargeLiftRemainder
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ Q : Finset ℕ,
              (∀ q ∈ Q, q ∈ quotientSet p A) ∧
              (∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) ∧
              (p : ℝ) * c -
                  (∑ ℓ ∈ corePrimeSupport (J.erase a),
                    (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) <
                ∑ q ∈ Q.filter (fun q => a ≤ p * q),
                  (1 : ℝ) / (q : ℝ) := by
  rcases hA.exists_prefix_forces_scale_or_freshRoomQuotient
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, Q, hQmem, hQroom, hQlarge⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    rcases exists_mem_dvd_of_mem_corePrimeSupport hpSupport with ⟨a, haJ, hpa⟩
    let S : ℝ := ∑ ℓ ∈ corePrimeSupport (J.erase a),
      (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)
    have hsmall :
        (∑ q ∈ Q.filter (fun q => p * q < a), (1 : ℝ) / (q : ℝ)) ≤ S := by
      dsimp [S]
      exact hJ.small_room_quotient_mass_le_erased_support_quotientBudget
        hA hirred haJ hpPrime hpa hQroom
    have hremainder_not :
        (p : ℝ) * c - S <
          ∑ q ∈ Q.filter (fun q => ¬ p * q < a), (1 : ℝ) / (q : ℝ) :=
      finite_sum_filter_not_gt_sub_of_lt_sum_of_filter_le
        (Q := Q) (P := fun q => p * q < a) hQlarge hsmall
    have hremainder :
        (p : ℝ) * c - S <
          ∑ q ∈ Q.filter (fun q => a ≤ p * q), (1 : ℝ) / (q : ℝ) := by
      simpa [S, not_lt] using hremainder_not
    exact Or.inr
      ⟨p, hpSupport, hpNotP, a, haJ, hpa, Q, hQmem, hQroom, hremainder⟩

/-- Prefix-forcing structural fork after large-lift excision.  The fresh
large-lift remainder yields one of two concrete obstructions: either the
erased-core composite quotient budgets already exceed `p * c`, or the carrier
`a` of the fresh support prime has self-headroom `lcm(J) * a ≤ 2^K`. -/
theorem SummabilityCounterexample.exists_prefix_forces_compositeBudget_or_headroom
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((p : ℝ) * c <
                ∑ ℓ ∈ corePrimeSupport (J.erase a),
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∨
              J.lcm (fun y : ℕ => y) * a ≤ 2 ^ K) := by
  rcases hA.exists_prefix_forces_scale_or_freshLargeLiftRemainder
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with
      ⟨p, hpSupport, hpNotP, a, haJ, hpa, Q, _hQmem, hQroom, hrem⟩
    let S : ℝ := ∑ ℓ ∈ corePrimeSupport (J.erase a),
      (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)
    by_cases hSlarge : (p : ℝ) * c < S
    · exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa, Or.inl (by simpa [S] using hSlarge)⟩
    · have hSle : S ≤ (p : ℝ) * c := le_of_not_gt hSlarge
      have hnonneg : 0 ≤ (p : ℝ) * c - S := sub_nonneg.mpr hSle
      have hrem' :
          (p : ℝ) * c - S <
            ∑ q ∈ Q.filter (fun q => a ≤ p * q), (1 : ℝ) / (q : ℝ) := by
        simpa [S] using hrem
      rcases exists_large_lift_of_nonneg_lt_large_lift_sum
          hnonneg hrem' with ⟨q, hqQ, hlarge⟩
      have hheadroom :
          J.lcm (fun y : ℕ => y) * a ≤ 2 ^ K :=
        lcm_mul_carrier_le_of_large_room_quotient_lift
          (hQroom q hqQ) hlarge
      exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa, Or.inr hheadroom⟩

/-- Prefix-forcing fork with the composite-budget side localized to one erased
support prime.  Either the obstruction scale escapes, or a fresh support prime
`p` has a carrier `a` such that either some erased support prime `ℓ` carries
weighted composite quotient budget larger than `(p * c) / K`, or `a` has
self-headroom inside the same LCM budget. -/
theorem SummabilityCounterexample.exists_prefix_forces_weightedCompositeBudget_or_headroom
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((∃ ℓ ∈ corePrimeSupport (J.erase a),
                ((p : ℝ) * c) / (K : ℝ) <
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) ∨
              J.lcm (fun y : ℕ => y) * a ≤ 2 ^ K) := by
  rcases hA.exists_prefix_forces_compositeBudget_or_headroom
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, a, haJ, hpa, hfork⟩
    rcases hfork with hcomp | hheadroom
    · have hℓ :=
        exists_erased_support_large_weighted_compositeBudget
          hJ.1 haJ hc_nonneg hcomp
      exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa, Or.inl hℓ⟩
    · exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa, Or.inr hheadroom⟩

/-- Prefix-forcing fork with scale restrictions exposed.  In the localized
composite-budget branch, the composite divisor `p * ℓ` already divides the
current core LCM and hence lies below `2^K`.  In the headroom branch, the
carrier self-headroom forces the square-size restriction `p^2 ≤ 2^K`. -/
theorem SummabilityCounterexample.exists_prefix_forces_weightedBudget_or_squareBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((∃ ℓ ∈ corePrimeSupport (J.erase a),
                ((p : ℝ) * c) / (K : ℝ) <
                    (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∧
                  p * ℓ ≤ 2 ^ K) ∨
              p * p ≤ 2 ^ K) := by
  rcases hA.exists_prefix_forces_weightedCompositeBudget_or_headroom
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, a, haJ, hpa, hfork⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    rcases hfork with hweighted | hheadroom
    · rcases hweighted with ⟨ℓ, hℓSupport, hℓLarge⟩
      have hℓScale : p * ℓ ≤ 2 ^ K :=
        hJ.1.mul_erasedSupport_le_two_pow haJ hpPrime hpa hℓSupport
      exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa,
          Or.inl ⟨ℓ, hℓSupport, hℓLarge, hℓScale⟩⟩
    · have hpSq : p * p ≤ 2 ^ K :=
        hJ.1.prime_sq_le_two_pow_of_carrier_headroom
          haJ hpPrime hpa hheadroom
      exact Or.inr
        ⟨p, hpSupport, hpNotP, a, haJ, hpa, Or.inr hpSq⟩

/-- Prefix-forcing quotient-budget fork.  The fresh quotient window produced
by the room-cover obstruction is absorbed into the finite quotient budget of
that prime. -/
theorem SummabilityCounterexample.exists_prefix_forces_scale_or_freshPrimeQuotientBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N R B : ℕ} (hN2 : 2 ≤ N) (P : Finset ℕ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          (p : ℝ) * c < primeQuotientBudget A p := by
  rcases hA.exists_prefix_forces_scale_or_freshRoomQuotient
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  refine ⟨m, hm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, Q, hQmem, _hQroom, hQlarge⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    have hquot : ReciprocalSummable (quotientSet p A) :=
      hA.reciprocalSummable_quotientSet_prime_of_quotient_irreducible
        hirred hpPrime
    have hQle :
        (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) ≤ primeQuotientBudget A p :=
      finset_sum_reciprocal_le_primeQuotientBudget hquot hQmem
    exact Or.inr ⟨p, hpSupport, hpNotP, hQlarge.trans_le hQle⟩

/-- Sequence-level quotient-window escape.  In bounded rank, endless delayed
room-cover obstructions either occur above any prescribed scale ceiling `B`, or
produce a fresh support prime outside `P` with a finite quotient window of mass
larger than `p * c`. -/
theorem SummabilityCounterexample.exists_scale_or_freshQuotient_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ Q : Finset ℕ, (∀ q ∈ Q, q ∈ quotientSet p A) ∧
            (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := by
  rcases hA.exists_scale_or_freshLayer_of_endless_prior_room_covers_rank_le
      hN2 hirred hendless P hc_nonneg B with
    ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, hfork⟩
  refine ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, ?_⟩
  rcases hfork with hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, hpLarge⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    rcases exists_quotient_finset_sum_gt_of_lt_primeLayerBudget
        hA.2.1 hpPrime.pos hpLarge with
      ⟨Q, hQmem, hQlarge⟩
    exact Or.inr ⟨p, hpSupport, hpNotP, Q, hQmem, hQlarge⟩

/-- Strong sequence-level quotient-window escape: in bounded rank, endless
delayed room-cover obstructions either exceed any scale ceiling or produce a
fresh quotient window whose lifts remain in the current LCM-room. -/
theorem SummabilityCounterexample.exists_scale_or_freshRoomQuotient_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ Q : Finset ℕ,
            (∀ q ∈ Q, q ∈ quotientSet p A) ∧
            (∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) ∧
            (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := by
  rcases hA.exists_prefix_forces_scale_or_freshRoomQuotient
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Sequence-level carrier-aware quotient fork.  In bounded rank, endless
prior room-cover obstructions either exceed any prescribed scale ceiling, or
produce a fresh support prime whose carrier satisfies the packed local
alternative: erased-core composite budgets plus packing allowance pay for the
fresh quotient mass, or a high-reciprocal large lift remains in the room. -/
theorem SummabilityCounterexample.exists_scale_or_carrierPackedQuotient_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c η : ℝ} (hc_nonneg : 0 ≤ c) (hη : 0 ≤ η)
    (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((p : ℝ) * c ≤
                (∑ ℓ ∈ corePrimeSupport (J.erase a),
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) +
                ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) * η) ∨
              ∃ q, q ∈ quotientSet p A ∧
                p * q ∈ lcmRoomFinset A K J ∧
                a ≤ p * q ∧ η < (1 : ℝ) / (q : ℝ))) := by
  rcases hA.exists_prefix_forces_scale_or_carrierPackedQuotient
      hirred (R := R) (B := B) hN2 P hc_nonneg hη with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale carrier-aware quotient fork.  If an endless prior room-cover
branch has bounded rank and bounded scale, then every finite old-prime set
misses a fresh support prime whose carrier satisfies the packed quotient
alternative: either erased-core composite budgets plus the packing allowance
pay for the fresh mass, or a high-reciprocal large lift remains in the same
room. -/
theorem SummabilityCounterexample.exists_carrierPackedQuotient_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c η : ℝ} (hc_nonneg : 0 ≤ c) (hη : 0 ≤ η) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ a ∈ J, p ∣ a ∧
          ((p : ℝ) * c ≤
              (∑ ℓ ∈ corePrimeSupport (J.erase a),
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) +
              ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) * η) ∨
            ∃ q, q ∈ quotientSet p A ∧
              p * q ∈ lcmRoomFinset A K J ∧
              a ≤ p * q ∧ η < (1 : ℝ) / (q : ℝ)) := by
  rcases hA.exists_prefix_forces_scale_or_carrierPackedQuotient
      hirred (R := R) (B := B) hN2 P hc_nonneg hη with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact False.elim ((not_lt_of_ge hKB) hBK)
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Sequence-level deterministic carrier-budget bound.  In bounded rank,
endless prior room-cover obstructions either exceed a prescribed scale ceiling
or produce a fresh carrier satisfying the pure packed-budget inequality with
threshold `p/a` already optimized away. -/
theorem SummabilityCounterexample.exists_scale_or_carrierBudgetBound_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            (p : ℝ) * c ≤
              (∑ ℓ ∈ corePrimeSupport (J.erase a),
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) +
              ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
                ((p : ℝ) / (a : ℝ)))) := by
  rcases hA.exists_prefix_forces_scale_or_carrierBudgetBound
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale deterministic carrier-budget bound.  If a bounded-rank,
bounded-scale prior room-cover branch persists, then every finite old-prime
set misses a fresh carrier satisfying the pure packed-budget inequality. -/
theorem SummabilityCounterexample.exists_carrierBudgetBound_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ a ∈ J, p ∣ a ∧
          (p : ℝ) * c ≤
            (∑ ℓ ∈ corePrimeSupport (J.erase a),
              (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) +
            ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
              ((p : ℝ) / (a : ℝ))) := by
  rcases hA.exists_prefix_forces_scale_or_carrierBudgetBound
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact False.elim ((not_lt_of_ge hKB) hBK)
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Sequence-level share/packing fork.  In bounded rank, endless prior
room-cover obstructions either escape a prescribed scale ceiling, or expose a
fresh carrier where the forced mass is paid by either erased-core composite
budgets or the explicit packing-ratio term. -/
theorem SummabilityCounterexample.exists_scale_or_carrierShareOrPacking_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((p : ℝ) * c ≤
                ∑ ℓ ∈ corePrimeSupport (J.erase a),
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∨
              (p : ℝ) * c ≤
                ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
                  ((p : ℝ) / (a : ℝ))))) := by
  rcases hA.exists_prefix_forces_scale_or_carrierShareOrPacking
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale share/packing fork.  If rank and scale are both bounded
along an endless prior room-cover branch, then every finite old-prime set
misses a fresh carrier whose forced mass is paid by either erased-core
composite budgets or the packing-ratio term. -/
theorem SummabilityCounterexample.exists_carrierShareOrPacking_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ a ∈ J, p ∣ a ∧
          ((p : ℝ) * c ≤
              ∑ ℓ ∈ corePrimeSupport (J.erase a),
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∨
            (p : ℝ) * c ≤
              ((((a / 2 + 1) * ((2 ^ K) / a + 1) : ℕ) : ℝ) *
                ((p : ℝ) / (a : ℝ)))) := by
  rcases hA.exists_prefix_forces_scale_or_carrierShareOrPacking
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact False.elim ((not_lt_of_ge hKB) hBK)
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Sequence-level composite-budget fork after boxing the packing branch.  In
bounded rank, if `c` is larger than the packing-ratio box for the scale ceiling,
then endless prior room-cover obstructions either escape that ceiling or expose
a fresh carrier paid by erased-core composite quotient budgets. -/
theorem SummabilityCounterexample.exists_scale_or_carrierCompositeBudget_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) {B : ℕ}
    (hbox : carrierPackingRatioBox B < c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            (p : ℝ) * c ≤
              ∑ ℓ ∈ corePrimeSupport (J.erase a),
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) := by
  rcases hA.exists_prefix_forces_scale_or_carrierCompositeBudget_of_packingBox
      hirred (R := R) (B := B) hN2 P hc_nonneg hbox with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale composite-budget fork after boxing the packing branch.  If
rank and scale are bounded along an endless branch and `c` beats the packing
box for that scale bound, then a fresh carrier with erased-core composite
budget at least `p*c` must appear outside every finite old-prime set. -/
theorem SummabilityCounterexample.exists_carrierCompositeBudget_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c)
    (hbox : carrierPackingRatioBox B < c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ a ∈ J, p ∣ a ∧
          (p : ℝ) * c ≤
            ∑ ℓ ∈ corePrimeSupport (J.erase a),
              (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) := by
  rcases hA.exists_prefix_forces_scale_or_carrierCompositeBudget_of_packingBox
      hirred (R := R) (B := B) hN2 P hc_nonneg hbox with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact False.elim ((not_lt_of_ge hKB) hBK)
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Sequence-level localized weighted-budget fork after boxing the packing
branch.  This is the boxed-packing analogue of the earlier weighted-budget
fork, but without a headroom alternative. -/
theorem SummabilityCounterexample.exists_scale_or_weightedBudget_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_pos : 0 < c) {B : ℕ}
    (hbox : carrierPackingRatioBox B < 2 * c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ ℓ ∈ corePrimeSupport (J.erase a),
              ((p : ℝ) * c) / (K : ℝ) <
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) := by
  rcases hA.exists_prefix_forces_scale_or_weightedBudget_of_packingBox
      hirred (R := R) (B := B) hN2 P hc_pos hbox with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale localized weighted-budget fork after boxing the packing
branch.  If rank and scale stay bounded, a fresh carrier outside every finite
old-prime set yields a localized weighted composite quotient budget. -/
theorem SummabilityCounterexample.exists_weightedBudget_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_pos : 0 < c)
    (hbox : carrierPackingRatioBox B < 2 * c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ a ∈ J, p ∣ a ∧
          ∃ ℓ ∈ corePrimeSupport (J.erase a),
            ((p : ℝ) * c) / (K : ℝ) <
              (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) := by
  rcases hA.exists_prefix_forces_scale_or_weightedBudget_of_packingBox
      hirred (R := R) (B := B) hN2 P hc_pos hbox with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact False.elim ((not_lt_of_ge hKB) hBK)
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Sequence-level normalized composite-budget fork after boxing packing.  In
bounded rank, endless prior room-cover obstructions either escape the scale
ceiling or produce a below-scale composite divisor with normalized quotient
budget above the target `C`. -/
theorem SummabilityCounterexample.exists_scale_or_normalizedBudget_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {C : ℝ} (hC_nonneg : 0 ≤ C) {B : ℕ}
    (hBC_pos : 0 < (B : ℝ) * C)
    (hbox : carrierPackingRatioBox B < 2 * ((B : ℝ) * C)) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ ℓ ∈ corePrimeSupport (J.erase a),
              C < primeQuotientBudget A (p * ℓ) /
                  (((p * ℓ : ℕ) : ℝ)) ∧
                p * ℓ ≤ 2 ^ K) := by
  rcases hA.exists_prefix_forces_scale_or_normalizedBudget_of_packingBox
      hirred (R := R) (B := B) hN2 P hC_nonneg hBC_pos hbox with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale normalized composite-budget fork after boxing packing.  If
rank and scale stay bounded, the boxed-packing argument produces a fresh
below-scale composite divisor with normalized quotient budget above `C`. -/
theorem SummabilityCounterexample.exists_normalizedBudget_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hBC_pos : 0 < (B : ℝ) * C)
    (hbox : carrierPackingRatioBox B < 2 * ((B : ℝ) * C)) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ a ∈ J, p ∣ a ∧
          ∃ ℓ ∈ corePrimeSupport (J.erase a),
            C < primeQuotientBudget A (p * ℓ) /
                (((p * ℓ : ℕ) : ℝ)) ∧
              p * ℓ ≤ 2 ^ K := by
  rcases hA.exists_prefix_forces_scale_or_normalizedBudget_of_packingBox
      hirred (R := R) (B := B) hN2 P hC_nonneg hBC_pos hbox with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact False.elim ((not_lt_of_ge hKB) hBK)
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Sequence-level scale escape from the two finite boxes.  This packages the
boxed-packing and normalized-composite accounting into the endless-branch
form: a bounded-rank persistent room-cover obstruction must cross any positive
scale ceiling. -/
theorem SummabilityCounterexample.exists_scale_of_budgetBoxes_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    {B : ℕ} (hBpos : 0 < B) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      B < K := by
  rcases hA.exists_prefix_forces_scale_of_budgetBoxes
      hirred (R := R) hN2 hBpos with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Sequence-level large-lift remainder escape.  In bounded rank, endless
delayed room-cover obstructions either exceed any prescribed scale ceiling or
produce a fresh support prime whose room quotient window has leftover mass
after the small lifts are paid for by erased-core composite quotient budgets. -/
theorem SummabilityCounterexample.exists_scale_or_freshLargeLiftRemainder_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ Q : Finset ℕ,
              (∀ q ∈ Q, q ∈ quotientSet p A) ∧
              (∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) ∧
              (p : ℝ) * c -
                  (∑ ℓ ∈ corePrimeSupport (J.erase a),
                    (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) <
                ∑ q ∈ Q.filter (fun q => a ≤ p * q),
                  (1 : ℝ) / (q : ℝ)) := by
  rcases hA.exists_prefix_forces_scale_or_freshLargeLiftRemainder
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale large-lift remainder escape.  If delayed room-cover
obstructions continue forever with bounded rank and bounded scale, then every
finite old-prime set misses a support prime whose room quotient window has
positive large-lift remainder after the erased-core composite budgets are
subtracted. -/
theorem SummabilityCounterexample.exists_freshLargeLiftRemainder_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ a ∈ J, p ∣ a ∧
          ∃ Q : Finset ℕ,
            (∀ q ∈ Q, q ∈ quotientSet p A) ∧
            (∀ q ∈ Q, p * q ∈ lcmRoomFinset A K J) ∧
            (p : ℝ) * c -
                (∑ ℓ ∈ corePrimeSupport (J.erase a),
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) <
              ∑ q ∈ Q.filter (fun q => a ≤ p * q),
                (1 : ℝ) / (q : ℝ) := by
  rcases hA.exists_prefix_forces_scale_or_freshLargeLiftRemainder
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact False.elim ((not_lt_of_ge hKB) hBK)
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Sequence-level localized weighted-budget/headroom fork.  In bounded rank,
endless delayed room-cover obstructions either exceed any prescribed scale
ceiling, or produce a fresh support prime whose carrier has either a localized
erased-support composite quotient budget or self-headroom. -/
theorem SummabilityCounterexample.exists_scale_or_weightedFork_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((∃ ℓ ∈ corePrimeSupport (J.erase a),
                ((p : ℝ) * c) / (K : ℝ) <
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) ∨
              J.lcm (fun y : ℕ => y) * a ≤ 2 ^ K)) := by
  rcases hA.exists_prefix_forces_weightedCompositeBudget_or_headroom
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale localized weighted-budget/headroom fork.  If delayed
room-cover obstructions continue forever with bounded rank and scale, then
every finite old-prime set misses a support prime whose carrier has either a
localized erased-support composite quotient budget or self-headroom. -/
theorem SummabilityCounterexample.exists_weightedFork_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ a ∈ J, p ∣ a ∧
          ((∃ ℓ ∈ corePrimeSupport (J.erase a),
              ((p : ℝ) * c) / (K : ℝ) <
                (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ)) ∨
            J.lcm (fun y : ℕ => y) * a ≤ 2 ^ K) := by
  rcases hA.exists_prefix_forces_weightedCompositeBudget_or_headroom
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  rcases hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover with
    hBK | hfresh
  · exact False.elim ((not_lt_of_ge hKB) hBK)
  · exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀,
      hcover, hfresh⟩

/-- Sequence-level scale-restricted weighted-budget/square-bound fork.  In
bounded rank, endless delayed room-cover obstructions either exceed any scale
ceiling, or expose a fresh support prime whose carrier gives either a localized
weighted composite budget below the current scale or a square-size bound. -/
theorem SummabilityCounterexample.exists_scale_or_weightedBudget_or_squareBound
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          ∃ a ∈ J, p ∣ a ∧
            ((∃ ℓ ∈ corePrimeSupport (J.erase a),
                ((p : ℝ) * c) / (K : ℝ) <
                    (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∧
                  p * ℓ ≤ 2 ^ K) ∨
              p * p ≤ 2 ^ K)) := by
  rcases hA.exists_prefix_forces_weightedBudget_or_squareBound
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Numeric large-prime form of the scale-restricted weighted fork.  The fresh
support prime can be forced above any prescribed bound `M`; at that point every
endless bounded-rank room-cover obstruction either also escapes above the scale
ceiling `B`, or satisfies the weighted composite/square-size alternative for
such a large prime. -/
theorem SummabilityCounterexample.exists_scale_or_largePrime_weightedBudget_or_squareBound
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    {c : ℝ} (hc_nonneg : 0 ≤ c) (M B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, M < p ∧
          ∃ a ∈ J, p ∣ a ∧
            ((∃ ℓ ∈ corePrimeSupport (J.erase a),
                ((p : ℝ) * c) / (K : ℝ) <
                    (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∧
                  p * ℓ ≤ 2 ^ K) ∨
              p * p ≤ 2 ^ K)) := by
  let P : Finset ℕ := (Finset.Icc 2 M).filter fun p => Nat.Prime p
  rcases hA.exists_scale_or_weightedBudget_or_squareBound
      hN2 hirred hendless P hc_nonneg B with
    ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, hfork⟩
  refine ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, ?_⟩
  rcases hfork with hBK | hfresh
  · exact Or.inl hBK
  · rcases hfresh with ⟨p, hpSupport, hpNotP, a, haJ, hpa, hbranch⟩
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    have hMp : M < p := by
      by_contra hnot
      have hpM : p ≤ M := not_lt.mp hnot
      have hpP : p ∈ P := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, hpM⟩, hpPrime⟩
      exact hpNotP hpP
    exact Or.inr ⟨p, hpSupport, hMp, a, haJ, hpa, hbranch⟩

/-- Large-prime fork with the headroom branch absorbed into scale escape.  By
forcing the fresh prime above `2^B`, the square-size headroom alternative
implies `B + B < K`.  Thus below the doubled scale, an endless bounded-rank
room-cover obstruction must produce a localized weighted composite quotient
budget. -/
theorem SummabilityCounterexample.exists_doubleScale_or_largePrime_weightedBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B + B < K ∨
        ∃ p ∈ corePrimeSupport J, 2 ^ B < p ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ ℓ ∈ corePrimeSupport (J.erase a),
              ((p : ℝ) * c) / (K : ℝ) <
                  (1 / (ℓ : ℝ)) * primeQuotientBudget A (p * ℓ) ∧
                p * ℓ ≤ 2 ^ K) := by
  rcases hA.exists_scale_or_largePrime_weightedBudget_or_squareBound
      hN2 hirred hendless hc_nonneg (2 ^ B) (B + B) with
    ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, hfork⟩
  refine ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, ?_⟩
  rcases hfork with hscale | hfresh
  · exact Or.inl hscale
  · rcases hfresh with ⟨p, hpSupport, hpLarge, a, haJ, hpa, hbranch⟩
    rcases hbranch with hweighted | hsquare
    · rcases hweighted with ⟨ℓ, hℓSupport, hℓLarge, hℓScale⟩
      exact Or.inr
        ⟨p, hpSupport, hpLarge, a, haJ, hpa, ℓ, hℓSupport,
          hℓLarge, hℓScale⟩
    · exact Or.inl
        (add_lt_scale_of_two_pow_lt_of_sq_le_two_pow hpLarge hsquare)

/-- Composite-budget form of the doubled-scale fork.  The previous theorem
produces a weighted erased-prime budget; clearing the positive erased prime
factor shows that, below doubled scale, the actual quotient budget at the
composite divisor `p*ℓ` beats the normalized mass `(p*ℓ)*c/K`. -/
theorem SummabilityCounterexample.exists_doubleScale_or_largePrime_compositeBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B + B < K ∨
        ∃ p ∈ corePrimeSupport J, 2 ^ B < p ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ ℓ ∈ corePrimeSupport (J.erase a),
              (((p * ℓ : ℕ) : ℝ) * c) / (K : ℝ) <
                  primeQuotientBudget A (p * ℓ) ∧
                p * ℓ ≤ 2 ^ K) := by
  rcases hA.exists_doubleScale_or_largePrime_weightedBudget
      hN2 hirred hendless hc_nonneg B with
    ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, hfork⟩
  refine ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, ?_⟩
  rcases hfork with hscale | hfresh
  · exact Or.inl hscale
  · rcases hfresh with
      ⟨p, hpSupport, hpLarge, a, haJ, hpa, ℓ, hℓSupport, hweighted,
        hscaleℓ⟩
    have hℓpos : 0 < ℓ := (prime_of_mem_corePrimeSupport hℓSupport).pos
    exact Or.inr
      ⟨p, hpSupport, hpLarge, a, haJ, hpa, ℓ, hℓSupport,
        compositeQuotientBudget_lt_of_weightedBudget hℓpos hweighted,
        hscaleℓ⟩

/-- Normalized composite-budget form of the doubled-scale fork.  For any
target ratio `C`, an endless bounded-rank room-cover obstruction either pushes
the scale past `2B`, or else produces a large composite divisor `p*ℓ ≤ 2^K`
whose quotient budget per unit divisor is larger than `C`. -/
theorem SummabilityCounterexample.exists_doubleScale_or_largePrime_normalizedCompositeBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    {C : ℝ} (hC_nonneg : 0 ≤ C) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B + B < K ∨
        ∃ p ∈ corePrimeSupport J, 2 ^ B < p ∧
          ∃ a ∈ J, p ∣ a ∧
            ∃ ℓ ∈ corePrimeSupport (J.erase a),
              C < primeQuotientBudget A (p * ℓ) / (((p * ℓ : ℕ) : ℝ)) ∧
                p * ℓ ≤ 2 ^ K) := by
  have hc : 0 ≤ ((B + B : ℕ) : ℝ) * C :=
    mul_nonneg (Nat.cast_nonneg _) hC_nonneg
  rcases hA.exists_doubleScale_or_largePrime_compositeBudget
      hN2 hirred hendless hc B with
    ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, hfork⟩
  refine ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, ?_⟩
  rcases hfork with hscale | hfresh
  · exact Or.inl hscale
  · by_cases hscale : B + B < K
    · exact Or.inl hscale
    · have hKB : K ≤ B + B := not_lt.mp hscale
      rcases hfresh with
        ⟨p, hpSupport, hpLarge, a, haJ, hpa, ℓ, hℓSupport, hbudget,
          hscaleℓ⟩
      have hKpos : 0 < K := hJ.1.scale_pos_of_mem haJ
      have hdpos : 0 < p * ℓ := by
        exact Nat.mul_pos (prime_of_mem_corePrimeSupport hpSupport).pos
          (prime_of_mem_corePrimeSupport hℓSupport).pos
      have hnorm :
          C < primeQuotientBudget A (p * ℓ) /
              (((p * ℓ : ℕ) : ℝ)) := by
        exact normalizedBudget_lt_of_compositeBudget_lt
          (K := K) (D := B + B) (d := p * ℓ)
          hKpos hdpos hKB hC_nonneg hbudget
      exact Or.inr
        ⟨p, hpSupport, hpLarge, a, haJ, hpa, ℓ, hℓSupport, hnorm,
          hscaleℓ⟩

/-- Moderate-window version of the normalized fork.  If the doubled-scale
escape fails, the same obstruction has scale strictly above `B` but no larger
than `B+B`, and it carries a normalized composite quotient budget above the
prescribed target `C`. -/
theorem SummabilityCounterexample.exists_doubleScale_or_moderateScale_normalizedCompositeBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    {C : ℝ} (hC_nonneg : 0 ≤ C) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B + B < K ∨
        B < K ∧ K ≤ B + B ∧
          ∃ p ∈ corePrimeSupport J, 2 ^ B < p ∧
            ∃ a ∈ J, p ∣ a ∧
              ∃ ℓ ∈ corePrimeSupport (J.erase a),
                C < primeQuotientBudget A (p * ℓ) /
                    (((p * ℓ : ℕ) : ℝ)) ∧
                  p * ℓ ≤ 2 ^ K) := by
  rcases hA.exists_doubleScale_or_largePrime_normalizedCompositeBudget
      hN2 hirred hendless hC_nonneg B with
    ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, hfork⟩
  refine ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, ?_⟩
  rcases hfork with hscale | hfresh
  · exact Or.inl hscale
  · by_cases hscale : B + B < K
    · exact Or.inl hscale
    · have hKB : K ≤ B + B := not_lt.mp hscale
      rcases hfresh with
        ⟨p, hpSupport, hpLarge, a, haJ, hpa, ℓ, hℓSupport, hnorm,
          hscaleℓ⟩
      have hℓpos : 0 < ℓ := (prime_of_mem_corePrimeSupport hℓSupport).pos
      have hBK : B < K :=
        lt_scale_of_two_pow_lt_of_mul_le_two_pow hpLarge hℓpos hscaleℓ
      exact Or.inr
        ⟨hBK, hKB, p, hpSupport, hpLarge, a, haJ, hpa, ℓ, hℓSupport,
          hnorm, hscaleℓ⟩

/-- The moderate-scale branch is impossible.  For fixed `B`, all divisors in
the moderate branch lie in the finite box `1 ≤ d ≤ 2^(B+B)`.  Taking `C` to be
the sum of all normalized quotient budgets in that box contradicts the branch
inequality `C < budget(d)/d`.  Hence any endless bounded-rank prior room-cover
obstruction must actually cross the doubled scale `B+B`. -/
theorem SummabilityCounterexample.exists_doubleScale_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      B + B < K := by
  let C := normalizedCompositeQuotientBudgetBox A (B + B)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact normalizedCompositeQuotientBudgetBox_nonneg A (B + B)
  rcases hA.exists_doubleScale_or_moderateScale_normalizedCompositeBudget
      hN2 hirred hendless hC_nonneg B with
    ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, hfork⟩
  refine ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover, ?_⟩
  rcases hfork with hscale | hmoderate
  · exact hscale
  · rcases hmoderate with
      ⟨_hBK, hKB, p, hpSupport, _hpLarge, _a, _haJ, _hpa, ℓ,
        hℓSupport, hnorm, hscaleℓ⟩
    exfalso
    have hdpos : 0 < p * ℓ := by
      exact Nat.mul_pos (prime_of_mem_corePrimeSupport hpSupport).pos
        (prime_of_mem_corePrimeSupport hℓSupport).pos
    have hd1 : 1 ≤ p * ℓ := Nat.succ_le_of_lt hdpos
    have hKDpow : 2 ^ K ≤ 2 ^ (B + B) := by
      exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hKB
    have hdD : p * ℓ ≤ 2 ^ (B + B) := hscaleℓ.trans hKDpow
    have hle := normalizedCompositeQuotientBudget_le_box A hd1 hdD
    exact (not_lt_of_ge hle) hnorm

/-- Cofinal doubled-scale escape.  The doubled-scale witness can be forced
after any prescribed prefix index `M` by restarting the preceding theorem at
the larger base `max N M`. -/
theorem SummabilityCounterexample.exists_ge_doubleScale_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (M B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      B + B < K := by
  let N' := max N M
  have hN'2 : 2 ≤ N' := hN2.trans (le_max_left N M)
  have hendless' : ∀ m, N' ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
    intro m hm
    exact hendless m ((le_max_left N M).trans hm)
  rcases hA.exists_doubleScale_of_endless_prior_rank_le
      hN'2 hirred hendless' B with
    ⟨m, T, K, r, J, J₀, hmN', hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
      hscale⟩
  have hMm : M ≤ m := (le_max_right N M).trans hmN'
  have hNm : N ≤ m := (le_max_left N M).trans hmN'
  exact ⟨m, T, K, r, J, J₀, hMm, hNm, hrR, hJ, hJ₀, hTK, hdelay₀,
    hcover, hscale⟩

/-- Cofinal boxed-budget scale escape.  The finite packing and normalized
composite-budget boxes can be forced after any prescribed prefix index `M`:
if bounded-rank delayed room covers persisted forever, then the scale `K`
would eventually exceed any positive ceiling `B`. -/
theorem SummabilityCounterexample.exists_ge_scale_of_budgetBoxes_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (M B : ℕ) (hBpos : 0 < B) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      B < K := by
  let N' := max N M
  have hN'2 : 2 ≤ N' := hN2.trans (le_max_left N M)
  have hendless' : ∀ m, N' ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
    intro m hm
    exact hendless m ((le_max_left N M).trans hm)
  rcases hA.exists_scale_of_budgetBoxes_of_endless_prior_rank_le
      hN'2 hirred hendless' (B := B) hBpos with
    ⟨m, T, K, r, J, J₀, hmN', hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
      hscale⟩
  have hMm : M ≤ m := (le_max_right N M).trans hmN'
  have hNm : N ≤ m := (le_max_left N M).trans hmN'
  exact ⟨m, T, K, r, J, J₀, hMm, hNm, hrR, hJ, hJ₀, hTK, hdelay₀,
    hcover, hscale⟩

/-- Sequence-level quotient-budget escape.  In bounded rank, endless delayed
room-cover obstructions either exceed any prescribed scale ceiling, or produce
a fresh support prime whose whole quotient budget is larger than `p * c`. -/
theorem SummabilityCounterexample.exists_scale_or_freshPrimeQuotientBudget_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (B : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      (B < K ∨
        ∃ p ∈ corePrimeSupport J, p ∉ P ∧
          (p : ℝ) * c < primeQuotientBudget A p) := by
  rcases hA.exists_prefix_forces_scale_or_freshPrimeQuotientBudget
      hirred (R := R) (B := B) hN2 P hc_nonneg with
    ⟨m, hm, hforce⟩
  rcases hendless m hm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hcover⟩

/-- Bounded-scale version of the quotient-window escape.  If rank and scale are
both bounded while delayed room-cover obstructions continue forever, then every
finite old-prime set misses a support prime whose quotient layer contains a
finite window of mass larger than `p * c`. -/
theorem SummabilityCounterexample.exists_freshQuotient_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        ∃ Q : Finset ℕ, (∀ q ∈ Q, q ∈ quotientSet p A) ∧
          (p : ℝ) * c < ∑ q ∈ Q, (1 : ℝ) / (q : ℝ) := by
  rcases hA.exists_freshLayer_of_endless_prior_room_covers_rank_scale_le
      hN2 hirred hendless P hc_nonneg with
    ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover,
      p, hpSupport, hpNotP, hpLarge⟩
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  rcases exists_quotient_finset_sum_gt_of_lt_primeLayerBudget
      hA.2.1 hpPrime.pos hpLarge with
    ⟨Q, hQmem, hQlarge⟩
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover,
    p, hpSupport, hpNotP, Q, hQmem, hQlarge⟩

/-- Bounded-scale quotient-budget escape.  If delayed room-cover obstructions
continue forever with bounded rank and bounded scale, then every finite
old-prime set misses a support prime whose whole quotient budget is larger
than `p * c`. -/
theorem SummabilityCounterexample.exists_freshPrimeQuotientBudget_of_endless_prior_rank_scale_le
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R B : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        K ≤ B ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (P : Finset ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      r ≤ R ∧
      K ≤ B ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, p ∉ P ∧
        (p : ℝ) * c < primeQuotientBudget A p := by
  rcases hA.exists_freshQuotient_of_endless_prior_rank_scale_le
      hN2 hirred hendless P hc_nonneg with
    ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover,
      p, hpSupport, hpNotP, Q, hQmem, hQlarge⟩
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  have hquot : ReciprocalSummable (quotientSet p A) :=
    hA.reciprocalSummable_quotientSet_prime_of_quotient_irreducible
      hirred hpPrime
  have hQle :
      (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) ≤ primeQuotientBudget A p :=
    finset_sum_reciprocal_le_primeQuotientBudget hquot hQmem
  exact ⟨m, T, K, r, J, J₀, hm, hrR, hKB, hJ, hJ₀, hTK, hdelay₀, hcover,
    p, hpSupport, hpNotP, hQlarge.trans_le hQle⟩

/-- Reindexing multiples by `x = p * m`: the reciprocal mass of multiples of a
positive `p` below `2 ^ k` is at most `(1 / p)` times the full dyadic harmonic
mass. -/
theorem multiplesBelowReciprocalMass_le_inv_mul_dyadicHarmonicMass
    {k p : ℕ} (hp : 0 < p) :
    multiplesBelowReciprocalMass k p ≤
      (1 / (p : ℝ)) * dyadicHarmonicMass k := by
  classical
  let F : Finset ℕ := (Finset.Ico (1 : ℕ) (2 ^ k)).filter (fun x => p ∣ x)
  let G : Finset ℕ := F.image (fun x => x / p)
  have hinj : Set.InjOn (fun x : ℕ => x / p) (F : Set ℕ) := by
    intro x hx y hy hxy
    change x / p = y / p at hxy
    have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
    have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
    calc
      x = (x / p) * p := (Nat.div_mul_cancel hpx).symm
      _ = (y / p) * p := by rw [hxy]
      _ = y := Nat.div_mul_cancel hpy
  have hGsub : G ⊆ Finset.Ico (1 : ℕ) (2 ^ k) := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨x, hxF, rfl⟩
    have hxIco : x ∈ Finset.Ico (1 : ℕ) (2 ^ k) :=
      (Finset.mem_filter.mp hxF).1
    have hpdvd : p ∣ x := (Finset.mem_filter.mp hxF).2
    rcases Finset.mem_Ico.mp hxIco with ⟨hx1, hxlt⟩
    have hxpos : 0 < x := by omega
    have hp_le_x : p ≤ x := Nat.le_of_dvd hxpos hpdvd
    refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
    · exact Nat.div_pos hp_le_x hp
    · exact (Nat.div_le_self x p).trans_lt hxlt
  have hrewrite :
      (∑ x ∈ F, (1 : ℝ) / (x : ℝ)) =
        ∑ x ∈ F, (1 / (p : ℝ)) *
          ((1 : ℝ) / ((x / p : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun x hxF => ?_
    have hpdvd : p ∣ x := (Finset.mem_filter.mp hxF).2
    rcases hpdvd with ⟨m, rfl⟩
    have hxIco : p * m ∈ Finset.Ico (1 : ℕ) (2 ^ k) :=
      (Finset.mem_filter.mp hxF).1
    have hpmpos : 0 < p * m := by
      have h1 : 1 ≤ p * m := (Finset.mem_Ico.mp hxIco).1
      omega
    have hm : 0 < m := by
      exact Nat.pos_of_ne_zero (fun hm0 => by
        rw [hm0, Nat.mul_zero] at hpmpos
        exact Nat.lt_irrefl 0 hpmpos)
    have hdiv : p * m / p = m := Nat.mul_div_right m hp
    rw [hdiv]
    exact reciprocal_nat_mul_eq_inv_mul_reciprocal hp hm
  have himage :
      (∑ m ∈ G, (1 / (p : ℝ)) * ((1 : ℝ) / (m : ℝ))) =
        ∑ x ∈ F, (1 / (p : ℝ)) *
          ((1 : ℝ) / ((x / p : ℕ) : ℝ)) := Finset.sum_image hinj
  calc
    multiplesBelowReciprocalMass k p =
        ∑ x ∈ F, (1 : ℝ) / (x : ℝ) := by
      rfl
    _ = ∑ x ∈ F, (1 / (p : ℝ)) *
          ((1 : ℝ) / ((x / p : ℕ) : ℝ)) := hrewrite
    _ = ∑ m ∈ G, (1 / (p : ℝ)) * ((1 : ℝ) / (m : ℝ)) :=
      himage.symm
    _ ≤ ∑ m ∈ Finset.Ico (1 : ℕ) (2 ^ k),
          (1 / (p : ℝ)) * ((1 : ℝ) / (m : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hGsub ?_
      intro m _hmTarget _hmNotSource
      positivity
    _ = (1 / (p : ℝ)) * dyadicHarmonicMass k := by
      simp [dyadicHarmonicMass, Finset.mul_sum]

/-- The absolute multiples majorant is controlled by the dyadic harmonic mass
times the reciprocal-prime weight of the core support. -/
theorem corePrimeSupportMultiplesBelowMass_le_harmonic_mul_primeReciprocalMass
    (k : ℕ) (J : Finset ℕ) :
    corePrimeSupportMultiplesBelowMass k J ≤
      dyadicHarmonicMass k * corePrimeSupportPrimeReciprocalMass J := by
  unfold corePrimeSupportMultiplesBelowMass corePrimeSupportPrimeReciprocalMass
  calc
    ∑ p ∈ corePrimeSupport J, multiplesBelowReciprocalMass k p ≤
        ∑ p ∈ corePrimeSupport J,
          (1 / (p : ℝ)) * dyadicHarmonicMass k := by
      exact Finset.sum_le_sum fun p hp =>
        multiplesBelowReciprocalMass_le_inv_mul_dyadicHarmonicMass
          (prime_of_mem_corePrimeSupport hp).pos
    _ = dyadicHarmonicMass k *
        ∑ p ∈ corePrimeSupport J, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _hp => by ring

/-- If every core-support prime is at least `M`, then its reciprocal-prime mass
is at most `|support| / M`. -/
theorem corePrimeSupportPrimeReciprocalMass_le_card_div
    {J : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hlarge : ∀ p ∈ corePrimeSupport J, M ≤ p) :
    corePrimeSupportPrimeReciprocalMass J ≤
      ((corePrimeSupport J).card : ℝ) / (M : ℝ) := by
  unfold corePrimeSupportPrimeReciprocalMass
  calc
    ∑ p ∈ corePrimeSupport J, (1 : ℝ) / (p : ℝ) ≤
        ∑ _p ∈ corePrimeSupport J, (1 : ℝ) / (M : ℝ) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
      have hMp : (M : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlarge p hp
      exact one_div_le_one_div_of_le hMreal hMp
    _ = ((corePrimeSupport J).card : ℝ) / (M : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Large support primes make the absolute multiples majorant small: it is at
most `H_k * |support| / M`. -/
theorem corePrimeSupportMultiplesBelowMass_le_harmonic_mul_card_div
    {k : ℕ} {J : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hlarge : ∀ p ∈ corePrimeSupport J, M ≤ p) :
    corePrimeSupportMultiplesBelowMass k J ≤
      dyadicHarmonicMass k * (((corePrimeSupport J).card : ℝ) / (M : ℝ)) := by
  exact (corePrimeSupportMultiplesBelowMass_le_harmonic_mul_primeReciprocalMass k J).trans
    (mul_le_mul_of_nonneg_left
      (corePrimeSupportPrimeReciprocalMass_le_card_div hM hlarge)
      (dyadicHarmonicMass_nonneg k))

/-- Using `H_k ≤ k`, the absolute multiples majorant is at most
`k * Σ_{p | core} 1 / p`. -/
theorem corePrimeSupportMultiplesBelowMass_le_scale_mul_primeReciprocalMass
    (k : ℕ) (J : Finset ℕ) :
    corePrimeSupportMultiplesBelowMass k J ≤
      (k : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  exact (corePrimeSupportMultiplesBelowMass_le_harmonic_mul_primeReciprocalMass k J).trans
    (mul_le_mul_of_nonneg_right
      (dyadicHarmonicMass_le k)
      (corePrimeSupportPrimeReciprocalMass_nonneg J))

/-- A set-theoretic room cover by core-support primes is automatically a
scale-prime-support obstruction.  This packages the two coarse losses:
room capture is bounded by all below-scale multiples of the support primes,
and the dyadic harmonic mass below `2^k` is at most `k`. -/
theorem lcmRoomReciprocalMass_le_scalePrimeSupport_of_room_cover
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ}
    (hcover : ((lcmRoomFinset A k J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    lcmRoomReciprocalMass A k J ≤
      (k : ℝ) * corePrimeSupportPrimeReciprocalMass J :=
  (lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover hcover).trans
    ((lcmRoomPrimeSupportMass_le_corePrimeSupportMultiplesBelowMass A k J).trans
      (corePrimeSupportMultiplesBelowMass_le_scale_mul_primeReciprocalMass k J))

/-- If every support prime is at least `M`, the absolute multiples majorant is
at most `k * |support| / M`. -/
theorem corePrimeSupportMultiplesBelowMass_le_scale_mul_card_div
    {k : ℕ} {J : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hlarge : ∀ p ∈ corePrimeSupport J, M ≤ p) :
    corePrimeSupportMultiplesBelowMass k J ≤
      (k : ℝ) * (((corePrimeSupport J).card : ℝ) / (M : ℝ)) := by
  have hcard_nonneg :
      0 ≤ (((corePrimeSupport J).card : ℝ) / (M : ℝ)) :=
        div_nonneg (Nat.cast_nonneg _) (le_of_lt (Nat.cast_pos.mpr hM))
  exact (corePrimeSupportMultiplesBelowMass_le_harmonic_mul_card_div hM hlarge).trans
    (mul_le_mul_of_nonneg_right (dyadicHarmonicMass_le k) hcard_nonneg)

/-- Cover-facing large-prime estimate.  If a delayed LCM-room is completely
covered by core-support primes, and all those primes are at least `M`, then
the whole room mass is bounded by the dyadic scale times
`|support| / M`. -/
theorem lcmRoomReciprocalMass_le_scale_mul_card_div_of_room_cover
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hlarge : ∀ p ∈ corePrimeSupport J, M ≤ p)
    (hcover : ((lcmRoomFinset A k J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    lcmRoomReciprocalMass A k J ≤
      (k : ℝ) * (((corePrimeSupport J).card : ℝ) / (M : ℝ)) := by
  calc
    lcmRoomReciprocalMass A k J ≤ lcmRoomPrimeSupportMass A k J :=
      lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover hcover
    _ ≤ corePrimeSupportMultiplesBelowMass k J :=
      lcmRoomPrimeSupportMass_le_corePrimeSupportMultiplesBelowMass A k J
    _ ≤ (k : ℝ) * (((corePrimeSupport J).card : ℝ) / (M : ℝ)) :=
      corePrimeSupportMultiplesBelowMass_le_scale_mul_card_div hM hlarge

/-- A general finite-set version of the harmonic prime-divisor majorant. -/
theorem finsetMultiplesBelowReciprocalMass_le_harmonic_mul_reciprocalMass
    {k : ℕ} {S : Finset ℕ} (hSpos : ∀ p ∈ S, 0 < p) :
    (∑ p ∈ S, multiplesBelowReciprocalMass k p) ≤
      dyadicHarmonicMass k *
        ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
  calc
    (∑ p ∈ S, multiplesBelowReciprocalMass k p) ≤
        ∑ p ∈ S, (1 / (p : ℝ)) * dyadicHarmonicMass k := by
      exact Finset.sum_le_sum fun p hp =>
        multiplesBelowReciprocalMass_le_inv_mul_dyadicHarmonicMass
          (hSpos p hp)
    _ = dyadicHarmonicMass k *
        ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _hp => by ring

/-- If every element of a finite set is at least `M`, then its reciprocal mass
is at most `|S| / M`. -/
theorem finset_reciprocalMass_le_card_div
    {S : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hlarge : ∀ p ∈ S, M ≤ p) :
    (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) ≤ (S.card : ℝ) / (M : ℝ) := by
  calc
    (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) ≤
        ∑ _p ∈ S, (1 : ℝ) / (M : ℝ) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
      have hMp : (M : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlarge p hp
      exact one_div_le_one_div_of_le hMreal hMp
    _ = (S.card : ℝ) / (M : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Outside a chosen finite prime set, if all remaining support primes are at
least `M`, then the absolute multiples majorant is bounded by
`H_k * |support \\ P| / M`. -/
theorem corePrimeSupportOutsideMultiplesBelowMass_le_harmonic_mul_card_div
    {k : ℕ} {J P : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hlarge : ∀ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P), M ≤ p) :
    corePrimeSupportOutsideMultiplesBelowMass k J P ≤
      dyadicHarmonicMass k *
        ((((corePrimeSupport J).filter (fun p => p ∉ P)).card : ℝ) /
          (M : ℝ)) := by
  let S := (corePrimeSupport J).filter (fun p => p ∉ P)
  have hSpos : ∀ p ∈ S, 0 < p := by
    intro p hp
    exact (prime_of_mem_corePrimeSupport (Finset.mem_filter.mp hp).1).pos
  have hmajor :=
    finsetMultiplesBelowReciprocalMass_le_harmonic_mul_reciprocalMass
      (k := k) (S := S) hSpos
  have hrecip :
      (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) ≤ (S.card : ℝ) / (M : ℝ) :=
    finset_reciprocalMass_le_card_div hM hlarge
  calc
    corePrimeSupportOutsideMultiplesBelowMass k J P =
        ∑ p ∈ S, multiplesBelowReciprocalMass k p := by
      rfl
    _ ≤ dyadicHarmonicMass k *
        ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := hmajor
    _ ≤ dyadicHarmonicMass k * ((S.card : ℝ) / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip (dyadicHarmonicMass_nonneg k)

/-- Dyadic-scale version of the outside-prime estimate. -/
theorem corePrimeSupportOutsideMultiplesBelowMass_le_scale_mul_card_div
    {k : ℕ} {J P : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hlarge : ∀ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P), M ≤ p) :
    corePrimeSupportOutsideMultiplesBelowMass k J P ≤
      (k : ℝ) *
        ((((corePrimeSupport J).filter (fun p => p ∉ P)).card : ℝ) /
          (M : ℝ)) := by
  have hcard_nonneg :
      0 ≤ ((((corePrimeSupport J).filter (fun p => p ∉ P)).card : ℝ) /
        (M : ℝ)) := div_nonneg (Nat.cast_nonneg _) (le_of_lt (Nat.cast_pos.mpr hM))
  exact (corePrimeSupportOutsideMultiplesBelowMass_le_harmonic_mul_card_div
      hM hlarge).trans
    (mul_le_mul_of_nonneg_right (dyadicHarmonicMass_le k) hcard_nonneg)

/-- A core at scale `k` has at most `k` support primes, so outside primes
larger than `M` cost at most `k^2 / M` in the absolute multiples majorant. -/
theorem CoprimeLCMSelection.corePrimeSupportOutsideMultiplesBelowMass_le_scale_sq_div
    {A : Set ℕ} {k r : ℕ} {J P : Finset ℕ} {M : ℕ}
    (hJ : CoprimeLCMSelection A k r J) (hM : 0 < M)
    (hlarge : ∀ p ∈ corePrimeSupport J, p ∉ P → M ≤ p) :
    corePrimeSupportOutsideMultiplesBelowMass k J P ≤
      (k : ℝ) * ((k : ℝ) / (M : ℝ)) := by
  have hlargeFilter :
      ∀ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P), M ≤ p := by
    intro p hp
    exact hlarge p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have hbase :=
    corePrimeSupportOutsideMultiplesBelowMass_le_scale_mul_card_div
      (k := k) (J := J) (P := P) hM hlargeFilter
  have hcard_nat :
      ((corePrimeSupport J).filter (fun p => p ∉ P)).card ≤ k :=
    (Finset.card_le_card (Finset.filter_subset (fun p => p ∉ P)
      (corePrimeSupport J))).trans hJ.corePrimeSupport_card_le_scale
  have hcard_real :
      ((((corePrimeSupport J).filter (fun p => p ∉ P)).card : ℝ)) ≤
        (k : ℝ) := by
    exact_mod_cast hcard_nat
  have hdiv :
      ((((corePrimeSupport J).filter (fun p => p ∉ P)).card : ℝ) /
          (M : ℝ)) ≤
        (k : ℝ) / (M : ℝ) := by
    exact div_le_div_of_nonneg_right hcard_real
      (le_of_lt (Nat.cast_pos.mpr hM))
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg k))

/-- If a prime is not in `M.primesBelow`, then it is at least `M`. -/
theorem prime_ge_of_not_mem_primesBelow {M p : ℕ}
    (hp : Nat.Prime p) (hpnot : p ∉ M.primesBelow) :
    M ≤ p := by
  by_contra hnot
  have hp_lt : p < M := not_le.mp hnot
  exact hpnot (Nat.mem_primesBelow.mpr ⟨hp_lt, hp⟩)

/-- If a core support has more primes than the finite small-prime box below
`M`, then it contains a prime at least `M`. -/
theorem exists_corePrimeSupport_ge_of_primesBelow_card_lt
    {J : Finset ℕ} {M : ℕ}
    (hcard : M.primesBelow.card < (corePrimeSupport J).card) :
    ∃ p ∈ corePrimeSupport J, M ≤ p := by
  by_contra hnone
  push Not at hnone
  have hsub : corePrimeSupport J ⊆ M.primesBelow := by
    intro p hpSupport
    have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
    have hp_lt : p < M := hnone p hpSupport
    exact Nat.mem_primesBelow.mpr ⟨hp_lt, hpPrime⟩
  have hle := Finset.card_le_card hsub
  omega

/-- If a finite set `P` accounts for too few possible support primes, then the
support outside `P` has the corresponding excess cardinality. -/
theorem corePrimeSupport_filter_not_card_gt_of_add_card_lt
    {J P : Finset ℕ} {S : ℕ}
    (hcard : P.card + S < (corePrimeSupport J).card) :
    S < ((corePrimeSupport J).filter (fun p => p ∉ P)).card := by
  classical
  have hinside_le :
      ((corePrimeSupport J).filter (fun p => p ∈ P)).card ≤ P.card := by
    exact Finset.card_le_card (by
      intro p hp
      exact (Finset.mem_filter.mp hp).2)
  have hsplit :
      ((corePrimeSupport J).filter (fun p => p ∈ P)).card +
          ((corePrimeSupport J).filter (fun p => p ∉ P)).card =
        (corePrimeSupport J).card := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := corePrimeSupport J) (p := fun p => p ∈ P))
  omega

/-- Standard small-prime split: outside `M.primesBelow`, every core-support
prime is at least `M`, so the outside absolute sieve cost is at most `k^2/M`. -/
theorem CoprimeLCMSelection.corePrimeSupportOutsideMultiplesBelowMass_le_scale_sq_div_primesBelow
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ} {M : ℕ}
    (hJ : CoprimeLCMSelection A k r J) (hM : 0 < M) :
    corePrimeSupportOutsideMultiplesBelowMass k J M.primesBelow ≤
      (k : ℝ) * ((k : ℝ) / (M : ℝ)) := by
  exact hJ.corePrimeSupportOutsideMultiplesBelowMass_le_scale_sq_div hM
    (fun p hpSupport hpnot =>
      prime_ge_of_not_mem_primesBelow
        (prime_of_mem_corePrimeSupport hpSupport) hpnot)

/-- Prior-witness room-cover obstruction in the irreducible branch, packaged
directly as a prefix-mass bound.  A cover of the delayed LCM-room by the
minimal core's support primes supplies the standard small/large-prime
obstruction bound. -/
theorem SummabilityCounterexample.prefixMass_le_primesBelowBound_of_prior_room_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m T K r M : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hN : 2 ≤ N)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hM : 0 < M)
    (hcover : ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    dyadicPrefixReciprocalMass A N m ≤
      primesBelowPrefixObstructionBound A N K r M := by
  have hroom_le_support :
      lcmRoomReciprocalMass A K J ≤ lcmRoomPrimeSupportMass A K J :=
    lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover hcover
  have hsplit :
      lcmRoomPrimeSupportMass A K J ≤
        lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
          corePrimeSupportOutsideMultiplesBelowMass K J M.primesBelow :=
    lcmRoomPrimeSupportMass_le_within_add_outsideMultiples A K J M.primesBelow
  have houtside :
      corePrimeSupportOutsideMultiplesBelowMass K J M.primesBelow ≤
        (K : ℝ) * ((K : ℝ) / (M : ℝ)) :=
    hJ.1.corePrimeSupportOutsideMultiplesBelowMass_le_scale_sq_div_primesBelow
      hM
  have hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
        (K : ℝ) * ((K : ℝ) / (M : ℝ)) := by
    calc
      lcmRoomReciprocalMass A K J ≤ lcmRoomPrimeSupportMass A K J :=
        hroom_le_support
      _ ≤ lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
          corePrimeSupportOutsideMultiplesBelowMass K J M.primesBelow :=
        hsplit
      _ ≤ lcmRoomPrimeSupportMassWithin A K J M.primesBelow +
          (K : ℝ) * ((K : ℝ) / (M : ℝ)) := add_le_add le_rfl houtside
  exact hA.prefixMass_le_rank_add_budget_add_primesBelowBound_of_prior
    hirred hJ hJ₀ hTK hN hdelay₀ hobstruction

/-- Sharpened prior-room-cover prefix bound.  Instead of replacing the outside
support-prime count by the coarse scale bound `≤ K`, keep the actual number of
support primes outside `Q.primesBelow`.  This is the carrier-aware version of
the standard cutoff obstruction. -/
theorem SummabilityCounterexample.prefixMass_le_primesBelow_outsideCardBound_of_prior_room_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m T K r Q : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hN : 2 ≤ N)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hQ : 0 < Q)
    (hcover : ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    dyadicPrefixReciprocalMass A N m ≤
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (∑ p ∈ Q.primesBelow, ∑' n : ℕ,
            reciprocalIndicator (multipleLayer p A) n) +
          (K : ℝ) *
            ((((corePrimeSupport J).filter
              (fun p => p ∉ Q.primesBelow)).card : ℝ) / (Q : ℝ)) := by
  have hobstruction : lcmRoomReciprocalMass A K J ≤
      lcmRoomPrimeSupportMassWithin A K J Q.primesBelow +
        corePrimeSupportOutsideMultiplesBelowMass K J Q.primesBelow := by
    calc
      lcmRoomReciprocalMass A K J ≤ lcmRoomPrimeSupportMass A K J :=
        lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover hcover
      _ ≤ lcmRoomPrimeSupportMassWithin A K J Q.primesBelow +
          corePrimeSupportOutsideMultiplesBelowMass K J Q.primesBelow :=
        lcmRoomPrimeSupportMass_le_within_add_outsideMultiples
          A K J Q.primesBelow
  have hprefix :=
    hJ.prefixMass_le_rank_div_pow_add_mixedPrimeSupport_of_prior
      hJ₀ hTK hN hdelay₀ hobstruction
  have hPprime : ∀ p ∈ Q.primesBelow, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow hp
  have hfinite :
      lcmRoomPrimeSupportMassWithin A K J Q.primesBelow ≤
        ∑ p ∈ Q.primesBelow, ∑' n : ℕ,
          reciprocalIndicator (multipleLayer p A) n :=
    hA.lcmRoomPrimeSupportMassWithin_le_irreducible_finite_bound
      hirred hPprime
  have hlarge :
      ∀ p ∈ (corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow),
        Q ≤ p := by
    intro p hp
    exact prime_ge_of_not_mem_primesBelow
      (prime_of_mem_corePrimeSupport (Finset.mem_filter.mp hp).1)
      (Finset.mem_filter.mp hp).2
  have houtside :=
    corePrimeSupportOutsideMultiplesBelowMass_le_scale_mul_card_div
      (k := K) (J := J) (P := Q.primesBelow) hQ hlarge
  linarith

/-- Heavy-prefix forcing in the exact room-cover form.  For every target `C`
there is a prefix such that any delayed fixed-prior room-cover witness seeing
that prefix must have standard small/large-prime obstruction bound exceeding
`C`. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_bound_of_prior_room_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    ∃ m, N ≤ m ∧ ∀ (T K r M : ℕ) (J J₀ : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      0 < M →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      C < primesBelowPrefixObstructionBound A N K r M := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro T K r M J J₀ hJ hJ₀ hTK hdelay₀ hM hcover
  have hupper :=
    hA.prefixMass_le_primesBelowBound_of_prior_room_cover
      hirred hJ hJ₀ hTK hN2 hdelay₀ hM hcover
  linarith

/-- Heavy-prefix forcing with the carrier-aware outside-card budget.  Any
delayed fixed-prior room cover seeing a sufficiently heavy prefix must make
the finite small-prime budget plus the scale-weighted outside support count
large. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_outsideCardBound_of_prior_room_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    ∃ m, N ≤ m ∧ ∀ (T K r Q : ℕ) (J J₀ : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      0 < Q →
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} →
      C <
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          (∑ p ∈ Q.primesBelow, ∑' n : ℕ,
              reciprocalIndicator (multipleLayer p A) n) +
            (K : ℝ) *
              ((((corePrimeSupport J).filter
                (fun p => p ∉ Q.primesBelow)).card : ℝ) / (Q : ℝ)) := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro T K r Q J J₀ hJ hJ₀ hTK hdelay₀ hQ hcover
  have hupper :=
    hA.prefixMass_le_primesBelow_outsideCardBound_of_prior_room_cover
      hirred hJ hJ₀ hTK hN2 hdelay₀ hQ hcover
  linarith

/-- At scale `k`, every LCM-minimal valid core below rank `r` has a legal
one-step extension which still fits inside the same dyadic budget.  This is
the frugal version of `CoprimeLCMExtensionProperty`: only cores with minimal
LCM for their current rank have to be extendable; such cores automatically
have exact cardinality equal to that rank. -/
def CoprimeLCMFrugalExtensionProperty (A : Set ℕ) (k r : ℕ) : Prop :=
  ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
    ∃ x : ℕ, x ∈ A ∧ x < 2 ^ k ∧ 4 ≤ x ∧ x ∉ J ∧
      (∀ a ∈ J, Nat.Coprime x a) ∧
      J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k

/-- Failure of the frugal extension property is witnessed by an LCM-minimal
partial core below the target rank which has no legal bounded coprime
extension.  This is the local obstruction one must rule out quantitatively. -/
theorem exists_lcmMinimal_extension_obstruction_of_not_frugal
    {A : Set ℕ} {k r : ℕ}
    (hnot : ¬ CoprimeLCMFrugalExtensionProperty A k r) :
    ∃ s J, s < r ∧ CoprimeLCMSelection.LCMMinimal A k s J ∧
      ∀ x : ℕ, x ∈ A → x < 2 ^ k → 4 ≤ x → x ∉ J →
        (∀ a ∈ J, Nat.Coprime x a) →
        ¬ J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k := by
  unfold CoprimeLCMFrugalExtensionProperty at hnot
  push Not at hnot
  rcases hnot with ⟨s, J, hs, hJ, hno⟩
  refine ⟨s, J, hs, hJ, ?_⟩
  intro x hxA hxlt hxlarge hxnot hxcop
  exact Nat.not_le.mpr (hno x hxA hxlt hxlarge hxnot hxcop)

/-- A failed frugal extension covers the whole LCM-room by the non-coprime
layers of the minimal core. -/
theorem exists_lcmMinimal_room_cover_of_not_frugal
    {A : Set ℕ} {k r : ℕ}
    (hnot : ¬ CoprimeLCMFrugalExtensionProperty A k r) :
    ∃ s J, s < r ∧ CoprimeLCMSelection.LCMMinimal A k s J ∧
      ((lcmRoomFinset A k J : Finset ℕ) : Set ℕ) ⊆
        ⋃ a ∈ J, {x | ¬ Nat.Coprime x a} := by
  rcases exists_lcmMinimal_extension_obstruction_of_not_frugal hnot with
    ⟨s, J, hs, hJ, hno⟩
  refine ⟨s, J, hs, hJ, ?_⟩
  intro x hxRoom
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  simp only [Set.mem_iUnion]
  by_contra hnone
  push Not at hnone
  have hxcop : ∀ a ∈ J, Nat.Coprime x a := by
    intro a ha
    exact not_not.mp (hnone a ha)
  exact hno x hxA hxlt hxlarge hxnot hxcop hxroom

/-- A failed frugal extension also covers the whole LCM-room by prime
divisibility layers from the prime support of the minimal core. -/
theorem exists_lcmMinimal_primeSupport_room_cover_of_not_frugal
    {A : Set ℕ} {k r : ℕ}
    (hnot : ¬ CoprimeLCMFrugalExtensionProperty A k r) :
    ∃ s J, s < r ∧ CoprimeLCMSelection.LCMMinimal A k s J ∧
      ((lcmRoomFinset A k J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  rcases exists_lcmMinimal_room_cover_of_not_frugal hnot with
    ⟨s, J, hs, hJ, hcover⟩
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  exact ⟨s, J, hs, hJ,
    fun x hx => core_noncoprime_cover_subset_primeSupport_cover hJpos
      (hcover hx)⟩

/-- Weighted finite-prefix dominance in the LCM-room gives an actual coprime
room element.  This is the finite estimate we now need mathematically: the
room mass must beat the total non-coprime mass contributed by the core. -/
theorem exists_coprime_mem_lcmRoomFinset_of_sum_noncoprime_lt
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ}
    (hbig : (∑ a ∈ J,
        ∑ x ∈ (lcmRoomFinset A k J).filter
          (fun x => ¬ Nat.Coprime x a),
          (1 : ℝ) / (x : ℝ)) <
      ∑ x ∈ lcmRoomFinset A k J, (1 : ℝ) / (x : ℝ)) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  classical
  let F := lcmRoomFinset A k J
  let B : ℕ → Set ℕ := fun a => {x | ¬ Nat.Coprime x a}
  by_contra hnone
  have hcover : ∀ x ∈ F, ∃ a ∈ J, x ∈ B a := by
    intro x hxF
    by_contra hxnone
    push Not at hxnone
    have hcop : ∀ a ∈ J, Nat.Coprime x a := by
      intro a ha
      exact not_not.mp (hxnone a ha)
    exact hnone ⟨x, hxF, hcop⟩
  have hle : (∑ x ∈ F, (1 : ℝ) / (x : ℝ)) ≤
      ∑ a ∈ J, ∑ x ∈ F.filter (fun x => x ∈ B a),
        (1 : ℝ) / (x : ℝ) := by
    exact finset_sum_le_sum_filter_of_cover
      (w := fun x : ℕ => (1 : ℝ) / (x : ℝ))
      (fun x => one_div_nonneg.mpr (Nat.cast_nonneg x)) hcover
  exact (not_lt_of_ge hle) (by simpa [F, B] using hbig)

/-- Prime-support finite-prefix dominance gives an actual coprime room
element.  This is the prime-by-prime form suggested by sieve and gcd-defect
methods. -/
theorem exists_coprime_mem_lcmRoomFinset_of_primeSupport_mass_lt
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ}
    (hJpos : ∀ a ∈ J, 0 < a)
    (hbig : lcmRoomPrimeSupportMass A k J <
      lcmRoomReciprocalMass A k J) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  classical
  let F := lcmRoomFinset A k J
  let B : ℕ → Set ℕ := fun p => {x | p ∣ x}
  by_contra hnone
  have hcoreCover : (F : Set ℕ) ⊆ ⋃ a ∈ J, {x | ¬ Nat.Coprime x a} := by
    intro x hxF
    simp only [Set.mem_iUnion]
    by_contra hxnone
    push Not at hxnone
    have hcop : ∀ a ∈ J, Nat.Coprime x a := by
      intro a ha
      exact not_not.mp (hxnone a ha)
    exact hnone ⟨x, hxF, hcop⟩
  have hprimeCoverSet : (F : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, B p := by
    intro x hxF
    exact core_noncoprime_cover_subset_primeSupport_cover hJpos
      (hcoreCover hxF)
  have hcover : ∀ x ∈ F, ∃ p ∈ corePrimeSupport J, x ∈ B p := by
    intro x hxF
    have hxcover := hprimeCoverSet hxF
    simpa [B] using hxcover
  have hle : (∑ x ∈ F, (1 : ℝ) / (x : ℝ)) ≤
      ∑ p ∈ corePrimeSupport J, ∑ x ∈ F.filter (fun x => x ∈ B p),
        (1 : ℝ) / (x : ℝ) := by
    exact finset_sum_le_sum_filter_of_cover
      (w := fun x : ℕ => (1 : ℝ) / (x : ℝ))
      (fun x => one_div_nonneg.mpr (Nat.cast_nonneg x)) hcover
  exact (not_lt_of_ge hle)
    (by
      simpa [F, B, lcmRoomPrimeSupportMass, lcmRoomPrimeDivisorMass,
        lcmRoomReciprocalMass] using hbig)

/-- Absolute sieve dominance gives an actual coprime room element.  It suffices
for the LCM-room mass to beat the total mass of all multiples of the core-support
primes below the dyadic cap. -/
theorem exists_coprime_mem_lcmRoomFinset_of_primeSupport_sieve_bound
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ}
    (hJpos : ∀ a ∈ J, 0 < a)
    (hbig : corePrimeSupportMultiplesBelowMass k J <
      lcmRoomReciprocalMass A k J) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  exact exists_coprime_mem_lcmRoomFinset_of_primeSupport_mass_lt hJpos
    (lt_of_le_of_lt
      (lcmRoomPrimeSupportMass_le_corePrimeSupportMultiplesBelowMass A k J)
      hbig)

/-- Mixed small/large prime dominance gives an actual coprime room element:
small support primes are charged by their real room capture, while support
primes outside `P` are charged by the absolute multiples majorant. -/
theorem exists_coprime_mem_lcmRoomFinset_of_mixed_primeSupport_bound
    {A : Set ℕ} {k : ℕ} {J P : Finset ℕ}
    (hJpos : ∀ a ∈ J, 0 < a)
    (hbig : lcmRoomPrimeSupportMassWithin A k J P +
        corePrimeSupportOutsideMultiplesBelowMass k J P <
      lcmRoomReciprocalMass A k J) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  exact exists_coprime_mem_lcmRoomFinset_of_primeSupport_mass_lt hJpos
    (lt_of_le_of_lt
      (lcmRoomPrimeSupportMass_le_within_add_outsideMultiples A k J P)
      hbig)

/-- Standard small-prime split dominance gives a coprime room element.  The
support primes below `M` are charged by their actual room capture; all remaining
support primes cost at most `k^2 / M` by the LCM support budget. -/
theorem exists_coprime_mem_lcmRoomFinset_of_mixed_primesBelow_scale_budget_bound
    {A : Set ℕ} {k r : ℕ} {J : Finset ℕ} {M : ℕ}
    (hJ : CoprimeLCMSelection A k r J) (hM : 0 < M)
    (hbig : lcmRoomPrimeSupportMassWithin A k J M.primesBelow +
        (k : ℝ) * ((k : ℝ) / (M : ℝ)) <
      lcmRoomReciprocalMass A k J) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.2.2.2.2.1 a ha)
  have houtside :=
    hJ.corePrimeSupportOutsideMultiplesBelowMass_le_scale_sq_div_primesBelow
      hM
  have hbig' : lcmRoomPrimeSupportMassWithin A k J M.primesBelow +
        corePrimeSupportOutsideMultiplesBelowMass k J M.primesBelow <
      lcmRoomReciprocalMass A k J := lt_of_le_of_lt (add_le_add_right houtside _) hbig
  exact exists_coprime_mem_lcmRoomFinset_of_mixed_primeSupport_bound
    hJpos hbig'

/-- Harmonic-prime-reciprocal dominance gives an actual coprime room element.
This is the reindexed large-prime form of the local target. -/
theorem exists_coprime_mem_lcmRoomFinset_of_primeSupport_harmonic_bound
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ}
    (hJpos : ∀ a ∈ J, 0 < a)
    (hbig : dyadicHarmonicMass k *
        corePrimeSupportPrimeReciprocalMass J <
      lcmRoomReciprocalMass A k J) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  exact exists_coprime_mem_lcmRoomFinset_of_primeSupport_sieve_bound hJpos
    (lt_of_le_of_lt
      (corePrimeSupportMultiplesBelowMass_le_harmonic_mul_primeReciprocalMass
        k J)
      hbig)

/-- If all support primes are at least `M`, the harmonic-cardinality estimate
is enough to produce a coprime room element. -/
theorem exists_coprime_mem_lcmRoomFinset_of_large_primeSupport_bound
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ} {M : ℕ}
    (hJpos : ∀ a ∈ J, 0 < a) (hM : 0 < M)
    (hlarge : ∀ p ∈ corePrimeSupport J, M ≤ p)
    (hbig : dyadicHarmonicMass k *
        (((corePrimeSupport J).card : ℝ) / (M : ℝ)) <
      lcmRoomReciprocalMass A k J) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  exact exists_coprime_mem_lcmRoomFinset_of_primeSupport_sieve_bound hJpos
    (lt_of_le_of_lt
      (corePrimeSupportMultiplesBelowMass_le_harmonic_mul_card_div hM hlarge)
      hbig)

/-- Scale-prime-reciprocal dominance gives an actual coprime room element. -/
theorem exists_coprime_mem_lcmRoomFinset_of_primeSupport_scale_bound
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ}
    (hJpos : ∀ a ∈ J, 0 < a)
    (hbig : (k : ℝ) * corePrimeSupportPrimeReciprocalMass J <
      lcmRoomReciprocalMass A k J) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  exact exists_coprime_mem_lcmRoomFinset_of_primeSupport_sieve_bound hJpos
    (lt_of_le_of_lt
      (corePrimeSupportMultiplesBelowMass_le_scale_mul_primeReciprocalMass
        k J)
      hbig)

/-- If all support primes are at least `M`, the scale-cardinality estimate is
enough to produce a coprime room element. -/
theorem exists_coprime_mem_lcmRoomFinset_of_large_primeSupport_scale_bound
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ} {M : ℕ}
    (hJpos : ∀ a ∈ J, 0 < a) (hM : 0 < M)
    (hlarge : ∀ p ∈ corePrimeSupport J, M ≤ p)
    (hbig : (k : ℝ) * (((corePrimeSupport J).card : ℝ) / (M : ℝ)) <
      lcmRoomReciprocalMass A k J) :
    ∃ x ∈ lcmRoomFinset A k J, ∀ a ∈ J, Nat.Coprime x a := by
  exact exists_coprime_mem_lcmRoomFinset_of_primeSupport_sieve_bound hJpos
    (lt_of_le_of_lt
      (corePrimeSupportMultiplesBelowMass_le_scale_mul_card_div hM hlarge)
      hbig)

/-- Finite-prefix dominance for every minimal partial core implies the frugal
extension property at that scale. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_mass_dominance
    {A : Set ℕ} {k r : ℕ}
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      (∑ a ∈ J,
          ∑ x ∈ (lcmRoomFinset A k J).filter
            (fun x => ¬ Nat.Coprime x a),
            (1 : ℝ) / (x : ℝ)) <
        ∑ x ∈ lcmRoomFinset A k J, (1 : ℝ) / (x : ℝ)) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  rcases exists_coprime_mem_lcmRoomFinset_of_sum_noncoprime_lt
      (hdom s J hs hJ) with ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Prime-support finite-prefix dominance for every minimal partial core
implies the frugal extension property at that scale. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_primeSupport_mass_dominance
    {A : Set ℕ} {k r : ℕ}
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      lcmRoomPrimeSupportMass A k J < lcmRoomReciprocalMass A k J) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  rcases exists_coprime_mem_lcmRoomFinset_of_primeSupport_mass_lt
      hJpos (hdom s J hs hJ) with ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Absolute sieve dominance for every minimal partial core implies the frugal
extension property at that scale.  This is the most concrete local target in the
large-prime branch: the possible bad primes are paid for by all of their dyadic
multiples, even before using membership in `A`. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_primeSupport_sieve_bound
    {A : Set ℕ} {k r : ℕ}
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      corePrimeSupportMultiplesBelowMass k J <
        lcmRoomReciprocalMass A k J) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  rcases exists_coprime_mem_lcmRoomFinset_of_primeSupport_sieve_bound
      hJpos (hdom s J hs hJ) with ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Mixed small/large prime dominance for every minimal partial core implies
the frugal extension property.  This is the refined branch useful after
quotient-irreducibility: fixed small primes are paid by actual mass, while
moving large primes are paid by the coarse sieve bound. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_mixed_primeSupport_bound
    {A : Set ℕ} {k r : ℕ} {P : Finset ℕ}
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      lcmRoomPrimeSupportMassWithin A k J P +
          corePrimeSupportOutsideMultiplesBelowMass k J P <
        lcmRoomReciprocalMass A k J) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  rcases exists_coprime_mem_lcmRoomFinset_of_mixed_primeSupport_bound
      hJpos (hdom s J hs hJ) with ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Standard small-prime split criterion for the frugal extension property:
actual capture by primes below `M`, plus the universal `k^2/M` outside-prime
budget, must be strictly smaller than the LCM-room mass. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_mixed_primesBelow_scale_budget_bound
    {A : Set ℕ} {k r M : ℕ} (hM : 0 < M)
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      lcmRoomPrimeSupportMassWithin A k J M.primesBelow +
          (k : ℝ) * ((k : ℝ) / (M : ℝ)) <
        lcmRoomReciprocalMass A k J) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  rcases exists_coprime_mem_lcmRoomFinset_of_mixed_primesBelow_scale_budget_bound
      hJ.1 hM (hdom s J hs hJ) with ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Harmonic-prime-reciprocal dominance for every minimal partial core implies
the frugal extension property at that scale. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_primeSupport_harmonic_bound
    {A : Set ℕ} {k r : ℕ}
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      dyadicHarmonicMass k * corePrimeSupportPrimeReciprocalMass J <
        lcmRoomReciprocalMass A k J) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  rcases exists_coprime_mem_lcmRoomFinset_of_primeSupport_harmonic_bound
      hJpos (hdom s J hs hJ) with ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Large-prime support dominance for every minimal partial core implies the
frugal extension property at that scale. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_largePrimeSupport_bound
    {A : Set ℕ} {k r M : ℕ} (hM : 0 < M)
    (hlarge : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      ∀ p ∈ corePrimeSupport J, M ≤ p)
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      dyadicHarmonicMass k *
          (((corePrimeSupport J).card : ℝ) / (M : ℝ)) <
        lcmRoomReciprocalMass A k J) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  rcases exists_coprime_mem_lcmRoomFinset_of_large_primeSupport_bound
      hJpos hM (hlarge s J hs hJ) (hdom s J hs hJ) with
    ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Scale-prime-reciprocal dominance for every minimal partial core implies the
frugal extension property at that scale. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_primeSupport_scale_bound
    {A : Set ℕ} {k r : ℕ}
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      (k : ℝ) * corePrimeSupportPrimeReciprocalMass J <
        lcmRoomReciprocalMass A k J) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  rcases exists_coprime_mem_lcmRoomFinset_of_primeSupport_scale_bound
      hJpos (hdom s J hs hJ) with ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Large-prime scale-cardinality dominance for every minimal partial core
implies the frugal extension property at that scale. -/
theorem CoprimeLCMFrugalExtensionProperty.of_lcmRoom_largePrimeSupport_scale_bound
    {A : Set ℕ} {k r M : ℕ} (hM : 0 < M)
    (hlarge : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      ∀ p ∈ corePrimeSupport J, M ≤ p)
    (hdom : ∀ s J, s < r → CoprimeLCMSelection.LCMMinimal A k s J →
      (k : ℝ) * (((corePrimeSupport J).card : ℝ) / (M : ℝ)) <
        lcmRoomReciprocalMass A k J) :
    CoprimeLCMFrugalExtensionProperty A k r := by
  intro s J hs hJ
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  rcases exists_coprime_mem_lcmRoomFinset_of_large_primeSupport_scale_bound
      hJpos hM (hlarge s J hs hJ) (hdom s J hs hJ) with
    ⟨x, hxRoom, hxcop⟩
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  exact ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩

/-- Bounded greedy selection with frugal cores.  To build rank `r`, it is
enough to know that every LCM-minimal partial core below rank `r` can be
extended within the same scale. -/
theorem exists_coprime_lcm_selection_of_frugal_extension_property
    {A : Set ℕ} {k r : ℕ}
    (hExt : CoprimeLCMFrugalExtensionProperty A k r) :
    ∃ J, CoprimeLCMSelection A k r J := by
  induction r with
  | zero =>
      exact ⟨∅, CoprimeLCMSelection.empty A k⟩
  | succ r ih =>
      have hExt_r : CoprimeLCMFrugalExtensionProperty A k r := by
        intro s J hs hJ
        exact hExt s J (Nat.lt_trans hs (Nat.lt_succ_self r)) hJ
      rcases ih hExt_r with ⟨J₀, hJ₀⟩
      rcases CoprimeLCMSelection.exists_lcmMinimal_of_exists_selection
          (A := A) (k := k) (r := r) ⟨J₀, hJ₀⟩ with
        ⟨J, hJmin⟩
      rcases hExt r J (Nat.lt_succ_self r) hJmin with
        ⟨x, hxA, hxlt, hxlarge, hxnot, hxcop, hxroom⟩
      exact ⟨Insert.insert x J,
        hJmin.1.insert hxA hxlt hxlarge hxnot hxcop hxroom⟩

/-- Eventual bounded-greedy criterion.  A summably strong rank schedule closes
the reciprocal-summability problem as soon as the fixed-scale extension
property holds eventually for that schedule. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_extension_property
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hExt : ∀ k, N ≤ k → CoprimeLCMExtensionProperty A k (f k)) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventually_exists_coprime_lcm_selection
    hpos hfSummable (N := N) ?_
  intro k hk
  exact exists_coprime_lcm_selection_of_extension_property (hExt k hk)

/-- Counterexample form of the eventual bounded-greedy criterion.  Any
counterexample must violate the local extension property at arbitrarily late
scales for every summably strong rank schedule. -/
theorem SummabilityCounterexample.exists_ge_not_extension_property
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k, N ≤ k ∧ ¬ CoprimeLCMExtensionProperty A k (f k) := by
  by_contra hnone
  have hExt : ∀ k, N ≤ k → CoprimeLCMExtensionProperty A k (f k) := by
    intro k hk
    by_contra hkExt
    exact hnone ⟨k, hk, hkExt⟩
  exact hA.2.2.2
    (hA.2.2.1.reciprocalSummable_of_eventual_extension_property
      hA.2.1 hfSummable hExt)

/-- Eventual frugal bounded-greedy criterion.  It suffices to extend
LCM-minimal partial cores at each sufficiently large scale. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_frugal_extension_property
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hExt : ∀ k, N ≤ k → CoprimeLCMFrugalExtensionProperty A k (f k)) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventually_exists_coprime_lcm_selection
    hpos hfSummable (N := N) ?_
  intro k hk
  exact exists_coprime_lcm_selection_of_frugal_extension_property (hExt k hk)

/-- Eventual finite-prefix dominance closes the coprime-selection branch.  The
remaining mathematical task is exactly to prove this strict room-mass
inequality for a summably strong rank schedule. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_mass_dominance
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        (∑ a ∈ J,
            ∑ x ∈ (lcmRoomFinset A k J).filter
              (fun x => ¬ Nat.Coprime x a),
              (1 : ℝ) / (x : ℝ)) <
          ∑ x ∈ lcmRoomFinset A k J, (1 : ℝ) / (x : ℝ)) :
      ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_mass_dominance
    (hdom k hk)

/-- Eventual prime-support finite-prefix dominance closes the coprime-selection
branch.  This is the sieve-ready version of the remaining estimate: the room
mass captured by primes dividing the minimal core is a strict minority. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_primeSupport_dominance
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        lcmRoomPrimeSupportMass A k J < lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_primeSupport_mass_dominance
    (hdom k hk)

/-- Eventual absolute sieve dominance closes the coprime-selection branch.  This
reduces the large-prime side to a dyadic estimate which no longer depends on the
internal structure of `A`: multiples of the core-support primes below `2 ^ k`
must have smaller total reciprocal mass than the actual LCM-room. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_primeSupport_sieve_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        corePrimeSupportMultiplesBelowMass k J <
          lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_primeSupport_sieve_bound
    (hdom k hk)

/-- Eventual mixed small/large prime dominance closes the coprime-selection
branch.  A fixed finite prime set `P` is charged by actual room capture, and
all support primes outside `P` are charged by the absolute dyadic multiples
majorant. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_mixed_primeSupport_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {f : ℕ → ℕ} {P : Finset ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        lcmRoomPrimeSupportMassWithin A k J P +
            corePrimeSupportOutsideMultiplesBelowMass k J P <
          lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_mixed_primeSupport_bound
    (hdom k hk)

/-- Eventual standard small-prime split closes the coprime-selection branch.
For a cutoff `M k`, it is enough that actual capture by support primes below
`M k`, plus the universal outside-prime budget `k^2 / M k`, is strictly smaller
than the LCM-room mass for every exact minimal partial core. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_mixed_primesBelow_scale_budget_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {f M : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hM : ∀ k, N ≤ k → 0 < M k)
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        lcmRoomPrimeSupportMassWithin A k J (M k).primesBelow +
            (k : ℝ) * ((k : ℝ) / (M k : ℝ)) <
          lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_mixed_primesBelow_scale_budget_bound
    (hM k hk) (hdom k hk)

/-- Eventual harmonic-prime-reciprocal dominance closes the coprime-selection
branch.  This is the most compact quantitative target after reindexing multiples
by `x = p * m`. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_primeSupport_harmonic_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        dyadicHarmonicMass k * corePrimeSupportPrimeReciprocalMass J <
          lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_primeSupport_harmonic_bound
    (hdom k hk)

/-- Eventual large-prime support bounds close the coprime-selection branch.  The
remaining numerical estimate becomes `H_k * |support| / M_k < room mass`. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_largePrimeSupport_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f M : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hM : ∀ k, N ≤ k → 0 < M k)
    (hlarge : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        ∀ p ∈ corePrimeSupport J, M k ≤ p)
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        dyadicHarmonicMass k *
            (((corePrimeSupport J).card : ℝ) / (M k : ℝ)) <
          lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_largePrimeSupport_bound
    (hM k hk) (hlarge k hk) (hdom k hk)

/-- Eventual scale-prime-reciprocal dominance closes the coprime-selection
branch.  After bounding the dyadic harmonic term by `k`, this is the cleanest
positive-side target: `k * Σ_{p | core} 1 / p < room mass`. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_primeSupport_scale_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        (k : ℝ) * corePrimeSupportPrimeReciprocalMass J <
          lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_primeSupport_scale_bound
    (hdom k hk)

/-- Eventual large-prime scale-cardinality dominance closes the
coprime-selection branch. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_lcmRoom_largePrimeSupport_scale_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {f M : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hM : ∀ k, N ≤ k → 0 < M k)
    (hlarge : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        ∀ p ∈ corePrimeSupport J, M k ≤ p)
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < f k → CoprimeLCMSelection.LCMMinimal A k s J →
        (k : ℝ) * (((corePrimeSupport J).card : ℝ) / (M k : ℝ)) <
          lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_frugal_extension_property
    hpos hfSummable (N := N) ?_
  intro k hk
  exact CoprimeLCMFrugalExtensionProperty.of_lcmRoom_largePrimeSupport_scale_bound
    (hM k hk) (hlarge k hk) (hdom k hk)

/-- Counterexample form of the frugal criterion.  Any counterexample must have
arbitrarily late scales at which some LCM-minimal partial core below the target
rank cannot be extended inside the same dyadic budget. -/
theorem SummabilityCounterexample.exists_ge_not_frugal_extension_property
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k, N ≤ k ∧ ¬ CoprimeLCMFrugalExtensionProperty A k (f k) := by
  by_contra hnone
  have hExt : ∀ k, N ≤ k →
      CoprimeLCMFrugalExtensionProperty A k (f k) := by
    intro k hk
    by_contra hkExt
    exact hnone ⟨k, hk, hkExt⟩
  exact hA.2.2.2
    (hA.2.2.1.reciprocalSummable_of_eventual_frugal_extension_property
      hA.2.1 hfSummable hExt)

/-- Explicit obstruction forced in every counterexample.  For any summably
strong rank schedule, there are arbitrarily late scales with an LCM-minimal
partial core below the target rank and no admissible coprime extension inside
the same dyadic budget. -/
theorem SummabilityCounterexample.exists_ge_lcmMinimal_extension_obstruction
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k s J, N ≤ k ∧ s < f k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      ∀ x : ℕ, x ∈ A → x < 2 ^ k → 4 ≤ x → x ∉ J →
        (∀ a ∈ J, Nat.Coprime x a) →
        ¬ J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k := by
  rcases hA.exists_ge_not_frugal_extension_property hfSummable N with
    ⟨k, hk, hnot⟩
  rcases exists_lcmMinimal_extension_obstruction_of_not_frugal hnot with
    ⟨s, J, hs, hJ, hno⟩
  exact ⟨k, s, J, hk, hs, hJ, hno⟩

/-- Mass-dominance failure forced in every counterexample.  For any summably
strong rank schedule, there are arbitrarily late exact minimal cores for which
the LCM-room reciprocal mass is no larger than the total non-coprime mass
generated by the core. -/
theorem SummabilityCounterexample.exists_ge_lcmRoom_mass_dominated
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k s J, N ≤ k ∧ s < f k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      (∑ x ∈ lcmRoomFinset A k J, (1 : ℝ) / (x : ℝ)) ≤
        ∑ a ∈ J,
          ∑ x ∈ (lcmRoomFinset A k J).filter
            (fun x => ¬ Nat.Coprime x a),
            (1 : ℝ) / (x : ℝ) := by
  rcases hA.exists_ge_not_frugal_extension_property hfSummable N with
    ⟨k, hk, hnot⟩
  rcases exists_lcmMinimal_room_cover_of_not_frugal hnot with
    ⟨s, J, hs, hJ, hcoverSet⟩
  let F := lcmRoomFinset A k J
  let B : ℕ → Set ℕ := fun a => {x | ¬ Nat.Coprime x a}
  have hcover : ∀ x ∈ F, ∃ a ∈ J, x ∈ B a := by
    intro x hxF
    have hxcover := hcoverSet hxF
    simpa [B] using hxcover
  have hle : (∑ x ∈ F, (1 : ℝ) / (x : ℝ)) ≤
      ∑ a ∈ J, ∑ x ∈ F.filter (fun x => x ∈ B a),
        (1 : ℝ) / (x : ℝ) := by
    exact finset_sum_le_sum_filter_of_cover
      (w := fun x : ℕ => (1 : ℝ) / (x : ℝ))
      (fun x => one_div_nonneg.mpr (Nat.cast_nonneg x)) hcover
  exact ⟨k, s, J, hk, hs, hJ, by simpa [F, B] using hle⟩

/-- Prime-support mass-dominance failure forced in every counterexample.  For
any summably strong rank schedule, there are arbitrarily late exact minimal
cores for which the whole LCM-room mass is dominated by the prime-divisibility
layers coming from the core support. -/
theorem SummabilityCounterexample.exists_ge_lcmRoom_primeSupport_mass_dominated
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k s J, N ≤ k ∧ s < f k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      lcmRoomReciprocalMass A k J ≤ lcmRoomPrimeSupportMass A k J := by
  rcases hA.exists_ge_not_frugal_extension_property hfSummable N with
    ⟨k, hk, hnot⟩
  rcases exists_lcmMinimal_primeSupport_room_cover_of_not_frugal hnot with
    ⟨s, J, hs, hJ, hcoverSet⟩
  let F := lcmRoomFinset A k J
  let B : ℕ → Set ℕ := fun p => {x | p ∣ x}
  have hcover : ∀ x ∈ F, ∃ p ∈ corePrimeSupport J, x ∈ B p := by
    intro x hxF
    have hxcover := hcoverSet hxF
    simpa [B] using hxcover
  have hle : (∑ x ∈ F, (1 : ℝ) / (x : ℝ)) ≤
      ∑ p ∈ corePrimeSupport J, ∑ x ∈ F.filter (fun x => x ∈ B p),
        (1 : ℝ) / (x : ℝ) := by
    exact finset_sum_le_sum_filter_of_cover
      (w := fun x : ℕ => (1 : ℝ) / (x : ℝ))
      (fun x => one_div_nonneg.mpr (Nat.cast_nonneg x)) hcover
  exact ⟨k, s, J, hk, hs, hJ, by
    simpa [F, B, lcmRoomPrimeSupportMass, lcmRoomPrimeDivisorMass,
      lcmRoomReciprocalMass] using hle⟩

/-- Absolute sieve obstruction forced in every counterexample.  For any summably
strong rank schedule, arbitrarily late exact minimal cores have LCM-room mass no
larger than the total reciprocal mass of all dyadic multiples of their
core-support primes. -/
theorem SummabilityCounterexample.exists_ge_lcmRoom_primeSupport_sieve_bound_obstruction
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k s J, N ≤ k ∧ s < f k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      lcmRoomReciprocalMass A k J ≤
        corePrimeSupportMultiplesBelowMass k J := by
  rcases hA.exists_ge_lcmRoom_primeSupport_mass_dominated
      hfSummable N with ⟨k, s, J, hk, hs, hJ, hdom⟩
  exact ⟨k, s, J, hk, hs, hJ,
    hdom.trans
      (lcmRoomPrimeSupportMass_le_corePrimeSupportMultiplesBelowMass A k J)⟩

/-- Mixed small/large prime obstruction forced in every counterexample.  For
any fixed finite prime set `P`, arbitrarily late exact minimal cores have room
mass bounded by actual capture from support primes in `P` plus the absolute
multiples bound for support primes outside `P`. -/
theorem SummabilityCounterexample.exists_ge_lcmRoom_mixed_primeSupport_obstruction
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (P : Finset ℕ) (N : ℕ) :
    ∃ k s J, N ≤ k ∧ s < f k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      lcmRoomReciprocalMass A k J ≤
        lcmRoomPrimeSupportMassWithin A k J P +
          corePrimeSupportOutsideMultiplesBelowMass k J P := by
  rcases hA.exists_ge_lcmRoom_primeSupport_mass_dominated
      hfSummable N with ⟨k, s, J, hk, hs, hJ, hdom⟩
  exact ⟨k, s, J, hk, hs, hJ,
    hdom.trans
      (lcmRoomPrimeSupportMass_le_within_add_outsideMultiples A k J P)⟩

/-- Standard small-prime split obstruction forced in every counterexample.
Given any positive cutoff schedule `M`, arbitrarily late exact minimal cores
have LCM-room mass bounded by actual capture from support primes below `M k`
plus the universal outside-prime budget `k^2 / M k`. -/
theorem SummabilityCounterexample.exists_ge_lcmRoom_mixed_primesBelow_scale_budget_obstruction
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f M : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (N : ℕ) (hM : ∀ k, N ≤ k → 0 < M k) :
    ∃ k s J, N ≤ k ∧ s < f k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      lcmRoomReciprocalMass A k J ≤
        lcmRoomPrimeSupportMassWithin A k J (M k).primesBelow +
          (k : ℝ) * ((k : ℝ) / (M k : ℝ)) := by
  rcases hA.exists_ge_lcmRoom_primeSupport_mass_dominated
      hfSummable N with ⟨k, s, J, hk, hs, hJ, hdom⟩
  have hsplit :=
    lcmRoomPrimeSupportMass_le_within_add_outsideMultiples
      A k J (M k).primesBelow
  have houtside :=
    hJ.1.corePrimeSupportOutsideMultiplesBelowMass_le_scale_sq_div_primesBelow
      (hM k hk)
  have hsupport :
      lcmRoomPrimeSupportMass A k J ≤
        lcmRoomPrimeSupportMassWithin A k J (M k).primesBelow +
          (k : ℝ) * ((k : ℝ) / (M k : ℝ)) := hsplit.trans (add_le_add_right houtside _)
  exact ⟨k, s, J, hk, hs, hJ, hdom.trans hsupport⟩

/-- Harmonic-prime-reciprocal obstruction forced in every counterexample.  Thus
any counterexample must find arbitrarily late exact minimal cores whose room
mass is no larger than `H_k * Σ_{p | core} 1 / p`. -/
theorem SummabilityCounterexample.exists_ge_lcmRoom_primeSupport_harmonic_obstruction
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k s J, N ≤ k ∧ s < f k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      lcmRoomReciprocalMass A k J ≤
        dyadicHarmonicMass k * corePrimeSupportPrimeReciprocalMass J := by
  rcases hA.exists_ge_lcmRoom_primeSupport_sieve_bound_obstruction
      hfSummable N with ⟨k, s, J, hk, hs, hJ, hdom⟩
  exact ⟨k, s, J, hk, hs, hJ,
    hdom.trans
      (corePrimeSupportMultiplesBelowMass_le_harmonic_mul_primeReciprocalMass
        k J)⟩

/-- Scale-prime-reciprocal obstruction forced in every counterexample.  After
the dyadic harmonic estimate, a counterexample must have arbitrarily late exact
minimal cores with `room mass ≤ k * Σ_{p | core} 1 / p`. -/
theorem SummabilityCounterexample.exists_ge_lcmRoom_primeSupport_scale_obstruction
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) (N : ℕ) :
    ∃ k s J, N ≤ k ∧ s < f k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      lcmRoomReciprocalMass A k J ≤
        (k : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  rcases hA.exists_ge_lcmRoom_primeSupport_harmonic_obstruction
      hfSummable N with ⟨k, s, J, hk, hs, hJ, hdom⟩
  exact ⟨k, s, J, hk, hs, hJ,
    hdom.trans
      (mul_le_mul_of_nonneg_right
        (dyadicHarmonicMass_le k)
        (corePrimeSupportPrimeReciprocalMass_nonneg J))⟩

/-- Once prime-support capture dominates the LCM-room, any lower bound on the
room mass larger than `|prime support| * c` forces one prime divisor layer to
carry more than `c` reciprocal mass. -/
theorem exists_prime_large_lcmRoomPrimeDivisorMass_of_primeSupport_dominated
    {A : Set ℕ} {k : ℕ} {J : Finset ℕ} {c : ℝ}
    (hdom : lcmRoomReciprocalMass A k J ≤ lcmRoomPrimeSupportMass A k J)
    (hbig : ((corePrimeSupport J).card : ℝ) * c <
      lcmRoomReciprocalMass A k J) :
    ∃ p ∈ corePrimeSupport J, c < lcmRoomPrimeDivisorMass A k J p := by
  classical
  by_contra hnone
  have hpiece_le : ∀ p ∈ corePrimeSupport J,
      lcmRoomPrimeDivisorMass A k J p ≤ c := by
    intro p hp
    exact not_lt.mp fun hlt => hnone ⟨p, hp, hlt⟩
  have hsum_le : lcmRoomPrimeSupportMass A k J ≤
      ∑ p ∈ corePrimeSupport J, c := by
    unfold lcmRoomPrimeSupportMass
    exact Finset.sum_le_sum fun p hp => hpiece_le p hp
  have hconst : (∑ _p ∈ corePrimeSupport J, c) =
      ((corePrimeSupport J).card : ℝ) * c := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Minimal-core room-cover descent.  If exact minimal obstruction cores have
LCM-room covers which see every sufficiently late shell, and all core elements
belong to a fixed finite positive universe, then quotient descent follows. -/
theorem SummabilityCounterexample.quotient_of_lcmMinimal_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A) {C : Finset ℕ}
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hJsub : ∀ k, N ≤ k → J k ⊆ C)
    (hJmin : ∀ k, N ≤ k →
      CoprimeLCMSelection.LCMMinimal A (K k) (r k) (J k))
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ a ∈ J k, {x | ¬ Nat.Coprime x a}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hCpos : ∀ a ∈ C, 0 < a) :
    ∃ a ∈ C, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) :=
  hA.quotient_of_moving_finite_universe_lcm_room_covers
    hN2 hJsub (fun k hk => (hJmin k hk).1) hcoverRoom hdelay hCpos

/-- Minimal-core room-cover descent with bounded prime support.  The core
values themselves need not be bounded: it is enough that every core prime
divisor belongs to one fixed finite prime set `P`. -/
theorem SummabilityCounterexample.quotient_of_lcmMinimal_room_covers_finite_primeSupport
    {A : Set ℕ} (hA : SummabilityCounterexample A) {P : Finset ℕ}
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hPsub : ∀ k, N ≤ k → corePrimeSupport (J k) ⊆ P)
    (hJmin : ∀ k, N ≤ k →
      CoprimeLCMSelection.LCMMinimal A (K k) (r k) (J k))
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport (J k), {x | p ∣ x}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k)) :
    ∃ p ∈ P, ∃ d : ℕ, d ∣ p ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  refine hA.quotient_of_moving_finite_prime_universe_lcm_room_covers
    (P := P) (J := J) (r := r) (K := K) (N := N)
    hN2 hPprime (fun k hk => (hJmin k hk).1) ?_ ?_ hdelay
  · intro k hk x hxJ
    rcases (hJmin k hk).1.exists_prime_mem_corePrimeSupport_dvd_of_mem hxJ with
      ⟨p, hpSupport, hpx⟩
    exact ⟨p, hPsub k hk hpSupport, hpx⟩
  · intro k hk x hxRoom
    have hxCover := hcoverRoom k hk hxRoom
    simp only [Set.mem_iUnion] at hxCover ⊢
    rcases hxCover with ⟨p, hpSupport, hpx⟩
    exact ⟨p, hPsub k hk hpSupport, hpx⟩

/-- Bounded minimal-core room covers force bounded quotient descent.  This is
the contrapositive tool for the irreducible branch: if no bounded descent is
available, a room-cover obstruction sequence cannot remain bounded. -/
theorem SummabilityCounterexample.quotient_of_bounded_lcmMinimal_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {M N : ℕ}
    (hN2 : 2 ≤ N)
    (hJmin : ∀ k, N ≤ k →
      CoprimeLCMSelection.LCMMinimal A (K k) (r k) (J k))
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ a ∈ J k, {x | ¬ Nat.Coprime x a}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hbound : ∀ k, N ≤ k → ∀ a ∈ J k, a ≤ M) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ M ∧ ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) :=
  hA.quotient_of_bounded_moving_core_lcm_room_covers
    hN2 (fun k hk => (hJmin k hk).1) hcoverRoom hdelay hbound

/-- Irreducible minimal-core room-cover obstruction.  In a quotient-irreducible
counterexample, any sequence of exact minimal room-cover obstructions whose
LCM rooms see every late shell must contain arbitrarily large core elements. -/
theorem SummabilityCounterexample.forall_exists_large_core_of_irreducible_lcmMinimal_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hJmin : ∀ k, N ≤ k →
      CoprimeLCMSelection.LCMMinimal A (K k) (r k) (J k))
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ a ∈ J k, {x | ¬ Nat.Coprime x a}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∀ M, ∃ k, N ≤ k ∧ ∃ a ∈ J k, M < a := by
  intro M
  by_contra hlarge
  have hbound : ∀ k, N ≤ k → ∀ a ∈ J k, a ≤ M := by
    intro k hk a ha
    by_contra hle
    exact hlarge ⟨k, hk, ⟨a, ha, lt_of_not_ge hle⟩⟩
  rcases hA.quotient_of_bounded_lcmMinimal_room_covers
      hN2 hJmin hcoverRoom hdelay hbound with
    ⟨a, _ha1, _haM, d, hda, hdgt, hcounter⟩
  exact hirred a d hda hdgt hcounter

/-- Irreducible finite-prime-support escape.  In a quotient-irreducible
counterexample, any sequence of exact minimal room-cover obstructions whose
LCM rooms see every late shell must eventually use a prime divisor outside
every prescribed finite prime set. -/
theorem SummabilityCounterexample.forall_finite_primeSupport_escape_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hJmin : ∀ k, N ≤ k →
      CoprimeLCMSelection.LCMMinimal A (K k) (r k) (J k))
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport (J k), {x | p ∣ x}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
      ∃ k, N ≤ k ∧ ∃ p ∈ corePrimeSupport (J k), p ∉ P := by
  intro P hPprime
  by_contra hbounded
  have hPsub : ∀ k, N ≤ k → corePrimeSupport (J k) ⊆ P := by
    intro k hk p hp
    by_contra hpP
    exact hbounded ⟨k, hk, p, hp, hpP⟩
  rcases hA.quotient_of_lcmMinimal_room_covers_finite_primeSupport
      hN2 hPprime hPsub hJmin hcoverRoom hdelay with
    ⟨p, _hpP, d, hdp, hdgt, hcounter⟩
  exact hirred p d hdp hdgt hcounter

/-- Numeric large-prime version of finite-prime-support escape.  Under the
same irreducible room-cover hypotheses, the core prime supports contain primes
larger than every prescribed bound. -/
theorem SummabilityCounterexample.forall_exists_large_primeSupport_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hJmin : ∀ k, N ≤ k →
      CoprimeLCMSelection.LCMMinimal A (K k) (r k) (J k))
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport (J k), {x | p ∣ x}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∀ M, ∃ k, N ≤ k ∧ ∃ p ∈ corePrimeSupport (J k), M < p := by
  intro M
  let P : Finset ℕ := (Finset.Icc 2 M).filter fun p => Nat.Prime p
  have hPprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  rcases hA.forall_finite_primeSupport_escape_of_irreducible
      hN2 hJmin hcoverRoom hdelay hirred P hPprime with
    ⟨k, hk, p, hpSupport, hpNotP⟩
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  have hMp : M < p := by
    by_contra hnot
    have hpM : p ≤ M := not_lt.mp hnot
    have hpP : p ∈ P := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, hpM⟩, hpPrime⟩
    exact hpNotP hpP
  exact ⟨k, hk, p, hpSupport, hMp⟩

/-- Persistent prior-witness room-cover obstructions with bounded prime
support force quotient descent.  This is the incompatibility half of the
fresh-prime fork: if every delayed LCM-room is covered by the core's prime
support and all those support primes lie in one fixed finite prime set `P`,
then the counterexample descends through a prime in `P`. -/
theorem SummabilityCounterexample.quotient_of_endless_prior_room_covers_finite_primeSupport
    {A : Set ℕ} (hA : SummabilityCounterexample A) {P : Finset ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        corePrimeSupport J ⊆ P) :
    ∃ p ∈ P, ∃ d : ℕ, d ∣ p ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  classical
  let T : ℕ → ℕ := fun m =>
    if h : N ≤ m then (hendless m h).choose else 0
  let K : ℕ → ℕ := fun m =>
    if h : N ≤ m then (hendless m h).choose_spec.choose else 0
  let r : ℕ → ℕ := fun m =>
    if h : N ≤ m then (hendless m h).choose_spec.choose_spec.choose else 0
  let J : ℕ → Finset ℕ := fun m =>
    if h : N ≤ m then
      (hendless m h).choose_spec.choose_spec.choose_spec.choose
    else ∅
  let J₀ : ℕ → Finset ℕ := fun m =>
    if h : N ≤ m then
      (hendless m h).choose_spec.choose_spec.choose_spec.choose_spec.choose
    else ∅
  have hpack : ∀ m, N ≤ m →
      CoprimeLCMSelection.LCMMinimal A (K m) (r m) (J m) ∧
      CoprimeLCMSelection A (T m) (r m) (J₀ m) ∧
      T m ≤ K m ∧
      (J₀ m).lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ (K m) ∧
      ((lcmRoomFinset A (K m) (J m) : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport (J m), {x | p ∣ x} ∧
      corePrimeSupport (J m) ⊆ P := by
    intro m hm
    dsimp [T, K, r, J, J₀]
    simpa [hm] using
      (hendless m hm).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  refine hA.quotient_of_lcmMinimal_room_covers_finite_primeSupport
    (P := P) (J := J) (r := r) (K := K) (N := N)
    hN2 hPprime ?_ ?_ ?_ ?_
  · intro m hm
    exact (hpack m hm).2.2.2.2.2
  · intro m hm
    exact (hpack m hm).1
  · intro m hm
    exact (hpack m hm).2.2.2.2.1
  · intro m hm
    exact (hpack m hm).1.delay_of_prior_selection
      (hpack m hm).2.1 (hpack m hm).2.2.1 (hpack m hm).2.2.2.1

/-- Cofinal finite-prime-support room-cover descent.  It is enough to have
room-cover witnesses for arbitrarily long prefixes, rather than for every
prefix with the same index.  Given a shell `k`, choose a witnessed prefix
`m ≥ k`; the delay for `m` makes the shell visible inside the same LCM-room.
If all such core supports lie in one fixed finite prime set, quotient descent
follows. -/
theorem SummabilityCounterexample.quotient_of_cofinal_prior_room_covers_finite_primeSupport
    {A : Set ℕ} (hA : SummabilityCounterexample A) {P : Finset ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hcofinal : ∀ n, N ≤ n →
      ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
        n ≤ m ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        corePrimeSupport J ⊆ P) :
    ∃ p ∈ P, ∃ d : ℕ, d ∣ p ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  refine hA.quotient_of_eventual_dyadic_shell_prime_cover
      (P := P) (N := N) ?_ hPprime
  intro k hk x hx
  rcases hcofinal k hk with
    ⟨m, T, K, r, J, J₀, hkm, hJ, hJ₀, hTK, hdelay₀, hcover, hPsub⟩
  have hxShell : x ∈ dyadicShellFinset A k := (Finset.mem_filter.mp hx).1
  by_cases hxJ : x ∈ J
  · rcases hJ.1.exists_prime_mem_corePrimeSupport_dvd_of_mem hxJ with
      ⟨p, hpSupport, hpx⟩
    simp only [Set.mem_iUnion]
    exact ⟨p, hPsub hpSupport, hpx⟩
  · have hdelay_m : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K :=
      hJ.delay_of_prior_selection hJ₀ hTK hdelay₀
    have hpow : 2 ^ (k + 1) ≤ 2 ^ (m + 1) := by
      exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    have hdelay_k : J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ K :=
      (Nat.mul_le_mul_left _ hpow).trans hdelay_m
    have hxRoom :=
      mem_lcmRoomFinset_of_mem_dyadicShellFinset
        hJ.1 (hN2.trans hk) hxShell hxJ hdelay_k
    have hxCover := hcover hxRoom
    simp only [Set.mem_iUnion] at hxCover ⊢
    rcases hxCover with ⟨p, hpSupport, hpx⟩
    exact ⟨p, hPsub hpSupport, hpx⟩

/-- Fixed-prior induction obstruction.  Suppose a rank-`r` witness `J₀` is
already available at scale `T`.  If, for every late prefix, some later
LCM-minimal rank-`r` core has its room covered by its own prime support and
the LCM headroom is certified by `J₀`, then quotient descent follows.

The point is minimality: every later minimal rank-`r` core has LCM at most
`lcm(J₀)`, hence all of its support primes lie in the fixed finite set of
primes up to `lcm(J₀)`. -/
theorem SummabilityCounterexample.quotient_of_endless_fixed_prior_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N T r : ℕ}
    {J₀ : Finset ℕ}
    (hN2 : 2 ≤ N)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hendless : ∀ m, N ≤ m →
      ∃ (K : ℕ) (J : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    ∃ p ∈ (Finset.Icc 2 (J₀.lcm fun a : ℕ => a)).filter
        (fun p => Nat.Prime p),
      ∃ d : ℕ, d ∣ p ∧ 1 < d ∧
        SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  let P : Finset ℕ :=
    (Finset.Icc 2 (J₀.lcm fun a : ℕ => a)).filter fun p => Nat.Prime p
  have hPprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hendlessP : ∀ m, N ≤ m →
      ∃ (T' K r' : ℕ) (J J₀' : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r' J ∧
        CoprimeLCMSelection A T' r' J₀' ∧
        T' ≤ K ∧
        J₀'.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        corePrimeSupport J ⊆ P := by
    intro m hm
    rcases hendless m hm with ⟨K, J, hJ, hTK, hdelay₀, hcover⟩
    exact ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hcover,
      hJ.corePrimeSupport_subset_primesBelow_lcm_of_prior_selection hJ₀ hTK⟩
  simpa [P] using
    hA.quotient_of_endless_prior_room_covers_finite_primeSupport
      (P := P) hN2 hPprime hendlessP

/-- In the quotient-irreducible branch, fixed-prior room-cover delay cannot
continue forever.  This is the nonquantitative induction step: once rank `r`
has a witness, a persistent obstruction to rank `r+1` would reuse only the
finitely many primes below that witness's LCM and therefore force quotient
descent. -/
theorem SummabilityCounterexample.not_endless_fixed_prior_room_covers_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N T r : ℕ}
    {J₀ : Finset ℕ}
    (hN2 : 2 ≤ N)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ¬ ∀ m, N ≤ m →
      ∃ (K : ℕ) (J : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  intro hendless
  rcases hA.quotient_of_endless_fixed_prior_room_covers
      hN2 hJ₀ hendless with
    ⟨p, _hpP, d, hdp, hdgt, hcounter⟩
  exact hirred p d hdp hdgt hcounter

/-- A fixed-prior room-cover delay breaks at prefix length `m` if no later
LCM-minimal rank-`r` core can have all of its remaining LCM room covered by
its own prime support while the fixed prior `J₀` still certifies the delayed
headroom. -/
def FixedPriorRoomCoverDelayBreak
    (A : Set ℕ) (T r m : ℕ) (J₀ : Finset ℕ) : Prop :=
  ∀ (K : ℕ) (J : Finset ℕ),
    ¬ (CoprimeLCMSelection.LCMMinimal A K r J ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})

/-- A bound `B` is a uniform fixed-prior delay-break bound at scale `T` and
rank `r` if every valid rank-`r` prior at that scale breaks at some delay
`m` with additive cost `m+1 ≤ B`. -/
def UniformFixedPriorRoomCoverDelayBreakBound
    (A : Set ℕ) (T r B : ℕ) : Prop :=
  ∀ J₀ : Finset ℕ, CoprimeLCMSelection A T r J₀ →
    ∃ m, m + 1 ≤ B ∧ FixedPriorRoomCoverDelayBreak A T r m J₀

/-- Once fixed-prior room-cover delay breaks, it remains broken for every
larger delayed prefix. -/
theorem FixedPriorRoomCoverDelayBreak.mono
    {A : Set ℕ} {T r m m' : ℕ} {J₀ : Finset ℕ}
    (hbreak : FixedPriorRoomCoverDelayBreak A T r m J₀)
    (hmm' : m ≤ m') :
    FixedPriorRoomCoverDelayBreak A T r m' J₀ := by
  intro K J hprops
  rcases hprops with ⟨hJ, hTK, hdelay, hcover⟩
  have hpow : 2 ^ (m + 1) ≤ 2 ^ (m' + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdelay' : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K :=
    (Nat.mul_le_mul_left _ hpow).trans hdelay
  exact hbreak K J ⟨hJ, hTK, hdelay', hcover⟩

/-- A larger numerical bound remains a valid uniform fixed-prior delay-break
bound. -/
theorem UniformFixedPriorRoomCoverDelayBreakBound.mono
    {A : Set ℕ} {T r B B' : ℕ}
    (hB : UniformFixedPriorRoomCoverDelayBreakBound A T r B)
    (hBB' : B ≤ B') :
    UniformFixedPriorRoomCoverDelayBreakBound A T r B' := by
  intro J₀ hJ₀
  rcases hB J₀ hJ₀ with ⟨m, hmB, hbreak⟩
  exact ⟨m, hmB.trans hBB', hbreak⟩

/-- A fixed prior must break once the visible prefix mass exceeds the finite
prime-layer budget forced by that prior.  This is the sharp quantitative form
of fixed-prior delay escape. -/
theorem SummabilityCounterexample.fixedPriorRoomCoverDelayBreak_of_fixedPriorBound_lt_prefixMass
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N T r m : ℕ} {J₀ : Finset ℕ}
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hN2 : 2 ≤ N)
    (hlarge :
      fixedPriorPrimeLayerPrefixBound A N r J₀ <
        dyadicPrefixReciprocalMass A N m) :
    FixedPriorRoomCoverDelayBreak A T r m J₀ := by
  intro K J hprops
  rcases hprops with ⟨hJ, hTK, hdelay₀, hcover⟩
  have hupper :=
    hA.prefixMass_le_fixedPriorPrimeLayerBound_of_room_cover
      hirred hJ hJ₀ hTK hN2 hdelay₀ hcover
  exact (not_lt_of_ge hupper) hlarge

/-- Exact support-budget break criterion.  A fixed-prior delay must break at
prefix `m` if every possible delayed covering core has actual support-prime
budget smaller than the visible prefix mass. -/
theorem SummabilityCounterexample.fixedPriorRoomCoverDelayBreak_of_corePrimeLayerBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N T r m : ℕ} {J₀ : Finset ℕ}
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hN2 : 2 ≤ N)
    (hsmall : ∀ (K : ℕ) (J : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      corePrimeLayerPrefixBound A N r J <
        dyadicPrefixReciprocalMass A N m) :
    FixedPriorRoomCoverDelayBreak A T r m J₀ := by
  intro K J hprops
  rcases hprops with ⟨hJ, hTK, hdelay₀, hcover⟩
  have hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K :=
    hJ.delay_of_prior_selection hJ₀ hTK hdelay₀
  have hupper :=
    hA.prefixMass_le_corePrimeLayerBound_of_room_cover
      hirred hJ hN2 hdelay hcover
  exact (not_lt_of_ge hupper) (hsmall K J hJ hTK hdelay₀)

/-- Uniform fixed-prior delay breaks follow if every valid prior has some
visible prefix, within the proposed bound, whose mass beats its own fixed-prior
prime-layer budget. -/
theorem SummabilityCounterexample.uniformFixedPriorRoomCoverDelayBreakBound_of_prefixMass
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N T r B : ℕ}
    (hN2 : 2 ≤ N)
    (hdom : ∀ J₀ : Finset ℕ, CoprimeLCMSelection A T r J₀ →
      ∃ m, m + 1 ≤ B ∧
        fixedPriorPrimeLayerPrefixBound A N r J₀ <
          dyadicPrefixReciprocalMass A N m) :
    UniformFixedPriorRoomCoverDelayBreakBound A T r B := by
  intro J₀ hJ₀
  rcases hdom J₀ hJ₀ with ⟨m, hmB, hlarge⟩
  exact ⟨m, hmB,
    hA.fixedPriorRoomCoverDelayBreak_of_fixedPriorBound_lt_prefixMass
      hirred hJ₀ hN2 hlarge⟩

/-- Every scale-`T` selection belongs to the finite powerset of numbers below
`2^T`.  This is the finiteness input for uniformizing fixed-prior delay
breaks. -/
theorem CoprimeLCMSelection.mem_powerset_Ico_two_pow
    {A : Set ℕ} {T r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection A T r J) :
    J ∈ (Finset.Ico 0 (2 ^ T)).powerset := by
  exact Finset.mem_powerset.mpr fun a ha =>
    Finset.mem_Ico.mpr ⟨Nat.zero_le a, hJ.2.1 a ha⟩

/-- In the irreducible branch, a fixed prior has some finite room-cover
delay-break point.  This is the break statement without immediately converting
it into a successor threshold. -/
theorem SummabilityCounterexample.exists_fixedPriorRoomCoverDelayBreak_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N T r : ℕ}
    {J₀ : Finset ℕ}
    (hN2 : 2 ≤ N)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∃ m, N ≤ m ∧ FixedPriorRoomCoverDelayBreak A T r m J₀ := by
  have hnotEndless :=
    hA.not_endless_fixed_prior_room_covers_of_irreducible
      hN2 hJ₀ hirred
  by_contra hnone
  apply hnotEndless
  intro m hm
  by_contra hnoWitness
  apply hnone
  refine ⟨m, hm, ?_⟩
  intro K J hprops
  exact hnoWitness ⟨K, J, hprops⟩

/-- At a fixed scale and rank there are only finitely many possible priors, so
irreducibility gives a single finite delay-break bound for all of them.  This
is the canonical finite maximum whose growth rate remains to be estimated. -/
theorem SummabilityCounterexample.exists_uniform_fixedPriorRoomCoverDelayBreakBound_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N T r : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∃ B, UniformFixedPriorRoomCoverDelayBreakBound A T r B := by
  classical
  let C : Finset (Finset ℕ) := (Finset.Ico 0 (2 ^ T)).powerset
  have hfiniteBound :
      ∀ D : Finset (Finset ℕ),
        ∃ B, ∀ J₀ ∈ D, CoprimeLCMSelection A T r J₀ →
          ∃ m, m + 1 ≤ B ∧
            FixedPriorRoomCoverDelayBreak A T r m J₀ := by
    intro D
    induction D using Finset.induction with
    | empty =>
        refine ⟨0, ?_⟩
        simp
    | insert J D hnotMem ih =>
        rcases ih with ⟨B, hB⟩
        by_cases hJsel : CoprimeLCMSelection A T r J
        · rcases hA.exists_fixedPriorRoomCoverDelayBreak_of_irreducible
            hN2 hJsel hirred with ⟨m, _hmN, hbreak⟩
          refine ⟨max B (m + 1), ?_⟩
          intro J₀ hJ₀mem hJ₀sel
          rw [Finset.mem_insert] at hJ₀mem
          rcases hJ₀mem with hJ₀eq | hJ₀D
          · subst J₀
            exact ⟨m, le_max_right B (m + 1), hbreak⟩
          · rcases hB J₀ hJ₀D hJ₀sel with ⟨m₀, hm₀B, hbreak₀⟩
            exact ⟨m₀, hm₀B.trans (le_max_left B (m + 1)), hbreak₀⟩
        · refine ⟨B, ?_⟩
          intro J₀ hJ₀mem hJ₀sel
          rw [Finset.mem_insert] at hJ₀mem
          rcases hJ₀mem with hJ₀eq | hJ₀D
          · subst J₀
            exact False.elim (hJsel hJ₀sel)
          · exact hB J₀ hJ₀D hJ₀sel
  rcases hfiniteBound C with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro J₀ hJ₀
  exact hB J₀ hJ₀.mem_powerset_Ico_two_pow hJ₀

/-- A concrete fixed-prior room-cover break extends a minimal rank-`r` core.
This is the local conversion from "the cover failed" to "rank `r+1` is now
available." -/
theorem CoprimeLCMSelection.threshold_succ_of_fixedPriorRoomCoverDelayBreak
    {A : Set ℕ} {T r m K : ℕ} {J₀ : Finset ℕ}
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hTK : T ≤ K)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hbreak : FixedPriorRoomCoverDelayBreak A T r m J₀) :
    CoprimeLCMSelectionThreshold A (r + 1) K := by
  classical
  have hsel_r : ∃ J : Finset ℕ, CoprimeLCMSelection A K r J :=
    ⟨J₀, hJ₀.scale_mono hTK⟩
  rcases CoprimeLCMSelection.exists_lcmMinimal_of_exists_selection
      hsel_r with ⟨J, hJ⟩
  have hnotCover :
      ¬ (((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) := by
    intro hcover
    exact hbreak K J ⟨hJ, hTK, hdelay₀, hcover⟩
  have hx :
      ∃ x, x ∈ lcmRoomFinset A K J ∧
        x ∉ (⋃ p ∈ corePrimeSupport J, {x | p ∣ x} : Set ℕ) := by
    by_contra hnone
    apply hnotCover
    intro x hxRoom
    by_contra hxNotCover
    exact hnone ⟨x, hxRoom, hxNotCover⟩
  rcases hx with ⟨x, hxRoom, hxNotCover⟩
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  have hxcop : ∀ a ∈ J, Nat.Coprime x a := by
    intro a ha
    by_contra hnotcop
    have hxNoncop :
        x ∈ (⋃ a ∈ J, {x | ¬ Nat.Coprime x a} : Set ℕ) := by
      simp only [Set.mem_iUnion]
      exact ⟨a, ha, hnotcop⟩
    exact hxNotCover
      (core_noncoprime_cover_subset_primeSupport_cover hJpos hxNoncop)
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  have hsel_succ : CoprimeLCMSelection A K (r + 1)
      (Insert.insert x J : Finset ℕ) :=
    hJ.1.insert hxA hxlt hxlarge hxnot hxcop hxroom
  exact CoprimeLCMSelection.threshold hsel_succ

/-- Quantified successor step from a fixed-prior witness.  The first prefix
length `m` where fixed-prior room-cover delay breaks gives a concrete
successor threshold at scale `T + m + 1`.

This is the sharpened additive form: since `J₀.lcm ≤ 2^T`, the delayed
headroom `J₀.lcm * 2^(m+1)` fits inside `2^(T+m+1)`. -/
theorem SummabilityCounterexample.exists_delayBreak_threshold_succ_of_fixed_prior_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N T r : ℕ}
    {J₀ : Finset ℕ}
    (hN2 : 2 ≤ N)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∃ m, N ≤ m ∧
      CoprimeLCMSelectionThreshold A (r + 1) (T + (m + 1)) := by
  classical
  have hnotEndless :=
    hA.not_endless_fixed_prior_room_covers_of_irreducible
      hN2 hJ₀ hirred
  have hbreak : ∃ m, N ≤ m ∧ ∀ (K : ℕ) (J : Finset ℕ),
      ¬ (CoprimeLCMSelection.LCMMinimal A K r J ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) := by
    by_contra hnone
    apply hnotEndless
    intro m hm
    by_contra hnoWitness
    apply hnone
    refine ⟨m, hm, ?_⟩
    intro K J hprops
    exact hnoWitness ⟨K, J, hprops⟩
  rcases hbreak with ⟨m, hNm, hnoCoverWitness⟩
  let K := T + (m + 1)
  have hTK : T ≤ K := by
    dsimp [K]
    omega
  have hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K := by
    calc
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤
          2 ^ T * 2 ^ (m + 1) :=
        Nat.mul_le_mul_right _ hJ₀.2.2.1
      _ = 2 ^ K := by
        simp [K, pow_add]
  have hsel_r : ∃ J : Finset ℕ, CoprimeLCMSelection A K r J :=
    ⟨J₀, hJ₀.scale_mono hTK⟩
  rcases CoprimeLCMSelection.exists_lcmMinimal_of_exists_selection
      hsel_r with ⟨J, hJ⟩
  have hnotCover :
      ¬ (((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) := by
    intro hcover
    exact hnoCoverWitness K J ⟨hJ, hTK, hdelay₀, hcover⟩
  have hx :
      ∃ x, x ∈ lcmRoomFinset A K J ∧
        x ∉ (⋃ p ∈ corePrimeSupport J, {x | p ∣ x} : Set ℕ) := by
    by_contra hnone
    apply hnotCover
    intro x hxRoom
    by_contra hxNotCover
    exact hnone ⟨x, hxRoom, hxNotCover⟩
  rcases hx with ⟨x, hxRoom, hxNotCover⟩
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      (hJ.1.2.2.2.2.1 a ha)
  have hxcop : ∀ a ∈ J, Nat.Coprime x a := by
    intro a ha
    by_contra hnotcop
    have hxNoncop :
        x ∈ (⋃ a ∈ J, {x | ¬ Nat.Coprime x a} : Set ℕ) := by
      simp only [Set.mem_iUnion]
      exact ⟨a, ha, hnotcop⟩
    exact hxNotCover
      (core_noncoprime_cover_subset_primeSupport_cover hJpos hxNoncop)
  rcases mem_lcmRoomFinset.mp hxRoom with
    ⟨hxlarge, hxlt, hxA, hxnot, hxroom⟩
  have hsel_succ : CoprimeLCMSelection A K (r + 1)
      (Insert.insert x J : Finset ℕ) :=
    hJ.1.insert hxA hxlt hxlarge hxnot hxcop hxroom
  exact ⟨m, hNm, CoprimeLCMSelection.threshold hsel_succ⟩

/-- Nonquantitative induction step in the irreducible branch.  A concrete
rank-`r` witness eventually yields an eventual rank-`r+1` threshold.

The proof is the contrapositive of endless fixed-prior delay.  If every later
attempt to pass from rank `r` to rank `r+1` had its LCM-room covered by the
rank-`r` core primes, the preceding theorem would give quotient descent.  At
the first prefix where this fails, a room element outside the prime-support
cover is coprime to the minimal rank-`r` core and extends it. -/
theorem SummabilityCounterexample.exists_threshold_succ_of_fixed_prior_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N T r : ℕ}
    {J₀ : Finset ℕ}
    (hN2 : 2 ≤ N)
    (hJ₀ : CoprimeLCMSelection A T r J₀)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∃ K, T ≤ K ∧ CoprimeLCMSelectionThreshold A (r + 1) K := by
  rcases hA.exists_delayBreak_threshold_succ_of_fixed_prior_irreducible
      hN2 hJ₀ hirred with ⟨m, _hNm, hthreshold⟩
  exact ⟨T + (m + 1), by omega, hthreshold⟩

/-- Fixed-rank thresholds by induction from the fixed-prior successor step.
This recovers eventual success of every fixed rank in the irreducible branch,
but now through the finite-prime-support obstruction: a permanent delay from
rank `r` to rank `r+1` would force quotient descent. -/
theorem SummabilityCounterexample.exists_threshold_of_rank_by_fixed_prior_induction_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) :
    ∀ r, ∃ K, N ≤ K ∧ CoprimeLCMSelectionThreshold A r K := by
  intro r
  induction r with
  | zero =>
      exact ⟨N, le_rfl,
        CoprimeLCMSelection.threshold (CoprimeLCMSelection.empty A N)⟩
  | succ r ih =>
      rcases ih with ⟨T, hNT, hT⟩
      rcases hT T le_rfl with ⟨J₀, hJ₀⟩
      rcases hA.exists_threshold_succ_of_fixed_prior_irreducible
          hN2 hJ₀ hirred with ⟨K, hTK, hK⟩
      exact ⟨K, hNT.trans hTK, hK⟩

/-- Bounded-rank endless prior room-cover delay is impossible in the
quotient-irreducible branch.  The doubled-scale escape supplies cofinally
large-scale witnesses.  Once `K` is beyond a fixed threshold for rank `R`,
minimality compares every rank-`r ≤ R` core to one fixed rank-`R` prior, so all
core-support primes lie in a single finite prime set.  Cofinal finite-prime
descent then contradicts quotient irreducibility. -/
theorem SummabilityCounterexample.not_endless_prior_room_covers_rank_le_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N R : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ¬ ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  intro hendless
  rcases hA.exists_threshold_of_rank_by_fixed_prior_induction_irreducible
      hirred hN2 R with ⟨B, _hNB, hThresholdR⟩
  rcases hThresholdR B le_rfl with ⟨Jstar, hJstar⟩
  have hBpos : 0 < B := by omega
  let P : Finset ℕ :=
    (Finset.Icc 2 (Jstar.lcm fun a : ℕ => a)).filter fun p => Nat.Prime p
  have hPprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hcofinal : ∀ n, N ≤ n →
      ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
        n ≤ m ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        corePrimeSupport J ⊆ P := by
    intro n hn
    rcases hA.exists_ge_scale_of_budgetBoxes_of_endless_prior_rank_le
        hN2 hirred hendless n B hBpos with
      ⟨m, T, K, r, J, J₀, hnm, _hNm, hrR, hJ, hJ₀, hTK, hdelay₀,
        hcover, hscale⟩
    have hBK : B ≤ K := Nat.le_of_lt hscale
    have hJstar_r : CoprimeLCMSelection A B r Jstar := hJstar.rank_mono hrR
    have hPsub : corePrimeSupport J ⊆ P := by
      simpa [P] using
        hJ.corePrimeSupport_subset_primesBelow_lcm_of_prior_selection hJstar_r hBK
    exact ⟨m, T, K, r, J, J₀, hnm, hJ, hJ₀, hTK, hdelay₀, hcover,
      hPsub⟩
  rcases hA.quotient_of_cofinal_prior_room_covers_finite_primeSupport
      hN2 hPprime hcofinal with ⟨p, _hpP, d, hdp, hdgt, hcounter⟩
  exact hirred p d hdp hdgt hcounter

/-- If endless prior room-cover delay survives without an a priori rank bound,
then its ranks must exceed every fixed bound.  This is the precise remaining
shape after the bounded-rank branch has been eliminated. -/
theorem SummabilityCounterexample.exists_high_rank_prior_room_cover_of_endless_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (R : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      R < r ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  by_contra hnone
  have hendlessR : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
    intro m hm
    rcases hendless m hm with
      ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hcover⟩
    have hrR : r ≤ R := by
      by_contra hrnot
      exact hnone
        ⟨m, T, K, r, J, J₀, hm, not_le.mp hrnot, hJ, hJ₀, hTK,
          hdelay₀, hcover⟩
    exact ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact hA.not_endless_prior_room_covers_rank_le_of_irreducible
    hN2 hirred hendlessR

/-- Cofinal high-rank form: the high-rank prior room-cover witness can be
forced after any prescribed prefix index. -/
theorem SummabilityCounterexample.exists_ge_high_rank_prior_room_cover_of_endless_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (M R : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      R < r ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  let N' := max N M
  have hN'2 : 2 ≤ N' := hN2.trans (le_max_left N M)
  have hendless' : ∀ m, N' ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
    intro m hm
    exact hendless m ((le_max_left N M).trans hm)
  rcases hA.exists_high_rank_prior_room_cover_of_endless_irreducible
      hN'2 hirred hendless' R with
    ⟨m, T, K, r, J, J₀, hmN', hRr, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, (le_max_right N M).trans hmN',
    (le_max_left N M).trans hmN', hRr, hJ, hJ₀, hTK, hdelay₀, hcover⟩

/-- Cofinal support-prime explosion in the remaining endless prior room-cover
case.  Since every rank-`r` coprime core uses at least `r` distinct prime
divisors, the high-rank obstruction carries more than any prescribed number of
support primes. -/
theorem SummabilityCounterexample.exists_ge_large_support_prior_room_cover_of_endless_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (M R : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      R < (corePrimeSupport J).card := by
  rcases hA.exists_ge_high_rank_prior_room_cover_of_endless_irreducible
      hN2 hirred hendless M R with
    ⟨m, T, K, r, J, J₀, hMm, hNm, hRr, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  exact ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
    hRr.trans_le hJ.1.rank_le_corePrimeSupport_card⟩

/-- The remaining endless prior room-cover obstruction must also have
arbitrarily large scale gap.  Large support consumes LCM budget, and delayed
visibility consumes another `m+1` dyadic exponents, so high support after a
late prefix forces `K` beyond `R + M + 1`. -/
theorem SummabilityCounterexample.exists_ge_large_scaleGap_prior_room_cover_of_endless_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (M R : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      R < (corePrimeSupport J).card ∧
      R + M + 1 < K := by
  rcases hA.exists_ge_large_support_prior_room_cover_of_endless_irreducible
      hN2 hirred hendless M R with
    ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover, hRcard⟩
  have hbudget :=
    hJ.corePrimeSupport_card_add_delay_le_scale_of_prior hJ₀ hTK hdelay₀
  have hgap : R + M + 1 < K := by omega
  exact ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
    hRcard, hgap⟩

/-- Large-gap room-cover witnesses can be forced to carry a genuinely large
support prime.  Apply the large-support extraction with
`R = Q.primesBelow.card`: more support primes than the small-prime box below
`Q` guarantees a support prime at least `Q`. -/
theorem SummabilityCounterexample.exists_ge_largePrime_scaleGap_prior_cover_of_endless_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (M Q : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ) (p : ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      p ∈ corePrimeSupport J ∧
      Q ≤ p ∧
      Q.primesBelow.card + M + 1 < K := by
  rcases hA.exists_ge_large_scaleGap_prior_room_cover_of_endless_irreducible
      hN2 hirred hendless M Q.primesBelow.card with
    ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
      hQcard, hgap⟩
  rcases exists_corePrimeSupport_ge_of_primesBelow_card_lt hQcard with
    ⟨p, hpSupport, hQp⟩
  exact ⟨m, T, K, r, J, J₀, p, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
    hpSupport, hQp, hgap⟩

/-- Large-gap room-cover witnesses can be forced to carry many support primes
outside any prescribed small-prime box.  This is the finite-box form of the
fresh-carrier extraction. -/
theorem SummabilityCounterexample.exists_ge_manyFresh_scaleGap_prior_cover_of_endless_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (M Q S : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      S < ((corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow)).card ∧
      (∀ p ∈ corePrimeSupport J, p ∉ Q.primesBelow → Q ≤ p) ∧
      Q.primesBelow.card + S + M + 1 < K := by
  rcases hA.exists_ge_large_scaleGap_prior_room_cover_of_endless_irreducible
      hN2 hirred hendless M (Q.primesBelow.card + S) with
    ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
      hcard, hgap⟩
  have houtside :
      S < ((corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow)).card :=
    corePrimeSupport_filter_not_card_gt_of_add_card_lt hcard
  have hlarge : ∀ p ∈ corePrimeSupport J, p ∉ Q.primesBelow → Q ≤ p := by
    intro p hpSupport hpnot
    exact prime_ge_of_not_mem_primesBelow
      (prime_of_mem_corePrimeSupport hpSupport) hpnot
  exact ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
    houtside, hlarge, hgap⟩

/-- The remaining quantitative target for the fixed-prior route: after some
prefix/support thresholds, no LCM-minimal delayed room can be completely
covered by the prime support of its core when the scale gap is also large.

This predicate isolates the last mathematical estimate needed to rule out the
endless prior-room-cover obstruction in the quotient-irreducible branch. -/
def NoLargeScaleGapPriorRoomCover (A : Set ℕ) (N : ℕ) : Prop :=
  ∃ M R : ℕ, ∀ (m T K r : ℕ) (J J₀ : Finset ℕ),
    M ≤ m →
    N ≤ m →
    CoprimeLCMSelection.LCMMinimal A K r J →
    CoprimeLCMSelection A T r J₀ →
    T ≤ K →
    J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
    R < (corePrimeSupport J).card →
    R + M + 1 < K →
    ¬ (((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})

/-- If the large-scale-gap room-cover target holds, then endless prior
room-cover delay is impossible in the quotient-irreducible branch.

The proof is exactly the high-rank/high-support/high-gap extraction above:
an endless obstruction would produce, after the thresholds promised by
`NoLargeScaleGapPriorRoomCover`, a witness satisfying the forbidden large-gap
cover conditions. -/
theorem SummabilityCounterexample.not_endless_prior_room_covers_of_no_largeScaleGap
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hnoGap : NoLargeScaleGapPriorRoomCover A N) :
    ¬ ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  rintro hendless
  rcases hnoGap with ⟨M, R, hnoGap⟩
  rcases hA.exists_ge_large_scaleGap_prior_room_cover_of_endless_irreducible
      hN2 hirred hendless M R with
    ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
      hRcard, hgap⟩
  exact (hnoGap m T K r J J₀ hMm hNm hJ hJ₀ hTK hdelay₀ hRcard hgap)
    hcover

/-- Contradiction form of
`not_endless_prior_room_covers_of_no_largeScaleGap`, convenient when an
endless obstruction has already been produced. -/
theorem SummabilityCounterexample.false_of_endless_prior_room_covers_of_no_largeScaleGap
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hnoGap : NoLargeScaleGapPriorRoomCover A N)
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    False :=
  (hA.not_endless_prior_room_covers_of_no_largeScaleGap hN2 hirred hnoGap)
    hendless

/-- A geometric sequence sampled along natural-number division is still
summable: each exponent appears only finitely many times. -/
theorem summable_three_four_pow_nat_div (q : ℕ) [NeZero q] :
    Summable fun k : ℕ => (3 / 4 : ℝ) ^ (k / q) := by
  have hgeom : Summable fun n : ℕ => (3 / 4 : ℝ) ^ n :=
    summable_geometric_of_lt_one
      (by norm_num : 0 ≤ (3 / 4 : ℝ))
      (by norm_num : (3 / 4 : ℝ) < 1)
  let g : ℕ × Fin q → ℝ := fun p => (3 / 4 : ℝ) ^ p.1
  have hprod : Summable g := by
    refine (summable_prod_of_nonneg (f := g) ?_).2 ?_
    · intro p
      dsimp [g]
      positivity
    · constructor
      · intro n
        exact Summable.of_finite (f := fun i : Fin q => g (n, i))
      · have hsum_eq : (fun n : ℕ => ∑' i : Fin q, g (n, i)) =
            fun n : ℕ => (q : ℝ) * ((3 / 4 : ℝ) ^ n) := by
          funext n
          rw [tsum_fintype]
          simp [g, Finset.sum_const, nsmul_eq_mul]
        rw [hsum_eq]
        exact hgeom.mul_left (q : ℝ)
  have hdiv : Summable (g ∘ (Nat.divModEquiv q)) :=
    (Nat.divModEquiv q).summable_iff.mpr hprod
  simpa [g, Function.comp_def, Nat.divModEquiv] using hdiv

/-- The dyadic packing majorant remains summable for the rank schedule
`k ↦ k / q`. -/
theorem summable_two_mul_three_four_pow_nat_div (q : ℕ) [NeZero q] :
    Summable fun k : ℕ => 2 * ((3 / 4 : ℝ) ^ (k / q)) :=
  (summable_three_four_pow_nat_div q).mul_left 2

/-- Shifted version of the divided geometric summability lemma. -/
theorem summable_two_mul_three_four_pow_nat_sub_div (q b : ℕ) [NeZero q] :
    Summable fun k : ℕ => 2 * ((3 / 4 : ℝ) ^ ((k - b) / q)) := by
  refine (summable_nat_add_iff (f := fun k : ℕ =>
    2 * ((3 / 4 : ℝ) ^ ((k - b) / q))) b).1 ?_
  simpa using summable_two_mul_three_four_pow_nat_div q

/-- A rank-threshold schedule assigns to each rank `r` a dyadic scale from
which rank `r` selections exist forever. -/
def CoprimeLCMSelectionThresholdSchedule (A : Set ℕ) (τ : ℕ → ℕ) : Prop :=
  ∀ r, CoprimeLCMSelectionThreshold A r (τ r)

/-- Threshold schedule generated from an initial scale `b` and allowed
successor increments `g r`.  Thus
`rankThresholdFromIncrements b g (r+1) = rankThresholdFromIncrements b g r + g r`. -/
def rankThresholdFromIncrements (b : ℕ) (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => b
  | r + 1 => rankThresholdFromIncrements b g r + g r

/-- A cumulative rank-threshold schedule never drops below its initial scale. -/
theorem le_rankThresholdFromIncrements (b : ℕ) (g : ℕ → ℕ) :
    ∀ r, b ≤ rankThresholdFromIncrements b g r := by
  intro r
  induction r with
  | zero =>
      simp [rankThresholdFromIncrements]
  | succ r ih =>
      simp [rankThresholdFromIncrements]
      omega

/-- If every successor increment is at most `q`, the cumulative threshold is
bounded by the affine schedule `b + q*r`. -/
theorem rankThresholdFromIncrements_le_affine_of_increments_le
    (b q : ℕ) (g : ℕ → ℕ) (hg : ∀ r, g r ≤ q) :
    ∀ r, rankThresholdFromIncrements b g r ≤ b + q * r := by
  intro r
  induction r with
  | zero =>
      simp [rankThresholdFromIncrements]
  | succ r ih =>
      have hgr : g r ≤ q := hg r
      simp [rankThresholdFromIncrements, Nat.mul_succ]
      omega

/-- The divided inverse schedule is fast for any cumulative threshold whose
increments are bounded by `q`. -/
theorem rankThresholdFromIncrements_le_of_nat_sub_div
    (b q : ℕ) [NeZero q] (g : ℕ → ℕ) (hg : ∀ r, g r ≤ q) :
    ∀ k, b ≤ k →
      rankThresholdFromIncrements b g ((k - b) / q) ≤ k := by
  intro k hbk
  have hlin :=
    rankThresholdFromIncrements_le_affine_of_increments_le b q g hg
      ((k - b) / q)
  have hmul : q * ((k - b) / q) ≤ k - b := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (k - b) q
  omega

/-- Bounded successor increments generate a rank-threshold schedule. -/
theorem coprimeLCMSelectionThresholdSchedule_of_successor_increment_bound
    (A : Set ℕ) (b : ℕ) (g : ℕ → ℕ)
    (hincr : ∀ r,
      CoprimeLCMSelectionThreshold A r (rankThresholdFromIncrements b g r) →
        ∃ d, d ≤ g r ∧
          CoprimeLCMSelectionThreshold A (r + 1)
            (rankThresholdFromIncrements b g r + d)) :
    CoprimeLCMSelectionThresholdSchedule A
      (rankThresholdFromIncrements b g) := by
  intro r
  induction r with
  | zero =>
      simpa [rankThresholdFromIncrements] using
        CoprimeLCMSelection.threshold (CoprimeLCMSelection.empty A b)
  | succ r ih =>
      rcases hincr r ih with ⟨d, hdg, hsucc⟩
      have hle : rankThresholdFromIncrements b g r + d ≤
          rankThresholdFromIncrements b g (r + 1) := by
        simp [rankThresholdFromIncrements]
        omega
      exact hsucc.mono hle

/-- A fast rank-threshold schedule closes reciprocal summability.  This is the
clean rate target: choose a summably strong rank schedule `f`, and prove that
the threshold for rank `f k` is already at or before scale `k` eventually. -/
theorem AvoidingSet.reciprocalSummable_of_fast_rankThresholdSchedule
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {τ f : ℕ → ℕ}
    (hτ : CoprimeLCMSelectionThresholdSchedule A τ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hfast : ∀ k, N ≤ k → τ (f k) ≤ k) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventually_exists_coprime_lcm_selection
    hpos hfSummable (N := N) ?_
  intro k hk
  exact (hτ (f k)).exists_selection_at (hfast k hk)

/-- Linear rank-threshold growth is enough to prove reciprocal summability.
If rank `r` is always available by scale `q * r`, then the summably strong
schedule `f k = k / q` supplies the dyadic packing criterion. -/
theorem AvoidingSet.reciprocalSummable_of_rankThresholdSchedule_linear_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {τ : ℕ → ℕ} (hτ : CoprimeLCMSelectionThresholdSchedule A τ)
    (q : ℕ) [NeZero q]
    (hlinear : ∀ r, τ r ≤ q * r) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_fast_rankThresholdSchedule
    hpos hτ (summable_two_mul_three_four_pow_nat_div q) (N := 0) ?_
  intro k _hk
  exact (hlinear (k / q)).trans (Nat.mul_div_le k q)

/-- Affine rank-threshold growth is enough to prove reciprocal summability.
The inverse schedule is `f k = (k - b) / q`; discarding the first `b` scales
does not affect summability. -/
theorem AvoidingSet.reciprocalSummable_of_rankThresholdSchedule_affine_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {τ : ℕ → ℕ} (hτ : CoprimeLCMSelectionThresholdSchedule A τ)
    (q b : ℕ) [NeZero q]
    (haffine : ∀ r, τ r ≤ q * r + b) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_fast_rankThresholdSchedule
    hpos hτ (summable_two_mul_three_four_pow_nat_sub_div q b) (N := b) ?_
  intro k hk
  have hmul : q * ((k - b) / q) ≤ k - b := Nat.mul_div_le (k - b) q
  have hle : q * ((k - b) / q) + b ≤ k := by
    omega
  exact (haffine ((k - b) / q)).trans hle

/-- An affine successor step produces an affine rank-threshold schedule. -/
theorem coprimeLCMSelectionThresholdSchedule_affine_of_successor_step
    (A : Set ℕ) (q b : ℕ)
    (hsucc : ∀ r,
      CoprimeLCMSelectionThreshold A r (q * r + b) →
      CoprimeLCMSelectionThreshold A (r + 1) (q * (r + 1) + b)) :
    CoprimeLCMSelectionThresholdSchedule A (fun r => q * r + b) := by
  intro r
  induction r with
  | zero =>
      simpa using
        CoprimeLCMSelection.threshold (CoprimeLCMSelection.empty A b)
  | succ r ih =>
      exact hsucc r ih

/-- Affine successor-step criterion for reciprocal summability.  To win, it is
enough to prove that rank `r` at scale `q*r+b` always forces rank `r+1` by
scale `q*(r+1)+b`. -/
theorem AvoidingSet.reciprocalSummable_of_affine_successor_threshold_step
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    (q b : ℕ) [NeZero q]
    (hsucc : ∀ r,
      CoprimeLCMSelectionThreshold A r (q * r + b) →
      CoprimeLCMSelectionThreshold A (r + 1) (q * (r + 1) + b)) :
    ReciprocalSummable A := by
  let τ : ℕ → ℕ := fun r => q * r + b
  have hτ : CoprimeLCMSelectionThresholdSchedule A τ :=
    coprimeLCMSelectionThresholdSchedule_affine_of_successor_step A q b hsucc
  exact hA.reciprocalSummable_of_rankThresholdSchedule_affine_bound
    hpos hτ q b (fun r => le_rfl)

/-- Counterexample form of the fast-threshold criterion. -/
theorem SummabilityCounterexample.false_of_fast_rankThresholdSchedule
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {τ f : ℕ → ℕ}
    (hτ : CoprimeLCMSelectionThresholdSchedule A τ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hfast : ∀ k, N ≤ k → τ (f k) ≤ k) :
    False :=
  hA.2.2.2
    (hA.2.2.1.reciprocalSummable_of_fast_rankThresholdSchedule
      hA.2.1 hτ hfSummable hfast)

/-- Counterexample form for an arbitrary bounded-increment threshold
recurrence.  To rule out a counterexample it is enough to bound each successor
increment by `g r` and prove that the cumulative schedule has a summably strong
inverse rank schedule. -/
theorem SummabilityCounterexample.false_of_successor_increment_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (b : ℕ) (g f : ℕ → ℕ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hfast : ∀ k, N ≤ k →
      rankThresholdFromIncrements b g (f k) ≤ k)
    (hincr : ∀ r,
      CoprimeLCMSelectionThreshold A r (rankThresholdFromIncrements b g r) →
        ∃ d, d ≤ g r ∧
          CoprimeLCMSelectionThreshold A (r + 1)
            (rankThresholdFromIncrements b g r + d)) :
    False := by
  let τ := rankThresholdFromIncrements b g
  have hτ : CoprimeLCMSelectionThresholdSchedule A τ :=
    coprimeLCMSelectionThresholdSchedule_of_successor_increment_bound
      A b g hincr
  exact hA.false_of_fast_rankThresholdSchedule hτ hfSummable hfast

/-- Counterexample form of the linear-threshold criterion. -/
theorem SummabilityCounterexample.false_of_rankThresholdSchedule_linear_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {τ : ℕ → ℕ} (hτ : CoprimeLCMSelectionThresholdSchedule A τ)
    (q : ℕ) [NeZero q]
    (hlinear : ∀ r, τ r ≤ q * r) :
    False :=
  hA.2.2.2
    (hA.2.2.1.reciprocalSummable_of_rankThresholdSchedule_linear_bound
      hA.2.1 hτ q hlinear)

/-- Counterexample form of the affine-threshold criterion. -/
theorem SummabilityCounterexample.false_of_rankThresholdSchedule_affine_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {τ : ℕ → ℕ} (hτ : CoprimeLCMSelectionThresholdSchedule A τ)
    (q b : ℕ) [NeZero q]
    (haffine : ∀ r, τ r ≤ q * r + b) :
    False :=
  hA.2.2.2
    (hA.2.2.1.reciprocalSummable_of_rankThresholdSchedule_affine_bound
      hA.2.1 hτ q b haffine)

/-- Counterexample form of the affine successor-step criterion. -/
theorem SummabilityCounterexample.false_of_affine_successor_threshold_step
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (q b : ℕ) [NeZero q]
    (hsucc : ∀ r,
      CoprimeLCMSelectionThreshold A r (q * r + b) →
      CoprimeLCMSelectionThreshold A (r + 1) (q * (r + 1) + b)) :
    False :=
  hA.2.2.2
    (hA.2.2.1.reciprocalSummable_of_affine_successor_threshold_step
      hA.2.1 q b hsucc)

/-- Bounded affine successor increments are enough to rule out a
counterexample.  This is the form that matches the additive delay-break
theorem: if rank `r+1` is always available within at most `q` additional
dyadic scales after the affine rank-`r` threshold `q*r+b`, then the affine
successor-step criterion closes the argument. -/
theorem SummabilityCounterexample.false_of_affine_successor_increment_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (q b : ℕ) [NeZero q]
    (hincr : ∀ r,
      CoprimeLCMSelectionThreshold A r (q * r + b) →
      ∃ d, d ≤ q ∧
        CoprimeLCMSelectionThreshold A (r + 1) (q * r + b + d)) :
    False := by
  refine hA.false_of_affine_successor_threshold_step q b ?_
  intro r hT
  rcases hincr r hT with ⟨d, hdq, hsucc⟩
  have hle : q * r + b + d ≤ q * (r + 1) + b := by
    rw [Nat.mul_succ]
    omega
  exact hsucc.mono hle

/-- If fixed-prior room-cover delay always breaks within one affine step, then
there is no counterexample.  This is the quantitative target for the
fixed-prior route: at affine scale `q*r+b`, every rank-`r` prior must break at
some prefix whose induced additive cost `m+1` is at most `q`. -/
theorem SummabilityCounterexample.false_of_affine_fixedPriorRoomCoverDelayBreak_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (q b : ℕ) [NeZero q]
    (hquick : ∀ r (J₀ : Finset ℕ),
      CoprimeLCMSelection A (q * r + b) r J₀ →
        ∃ m, m + 1 ≤ q ∧
          FixedPriorRoomCoverDelayBreak A (q * r + b) r m J₀) :
    False := by
  refine hA.false_of_affine_successor_increment_bound q b ?_
  intro r hT
  rcases hT (q * r + b) le_rfl with ⟨J₀, hJ₀⟩
  rcases hquick r J₀ hJ₀ with ⟨m, hmq, hbreak⟩
  refine ⟨m + 1, hmq, ?_⟩
  let T := q * r + b
  let K := q * r + b + (m + 1)
  have hTK : T ≤ K := by
    dsimp [T, K]
    omega
  have hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K := by
    calc
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤
          2 ^ T * 2 ^ (m + 1) :=
        Nat.mul_le_mul_right _ hJ₀.2.2.1
      _ = 2 ^ K := by
        simp [T, K, pow_add]
  exact CoprimeLCMSelection.threshold_succ_of_fixedPriorRoomCoverDelayBreak
    hJ₀ hTK hdelay₀ hbreak

/-- Variable-increment fixed-prior delay-break criterion.  This is the more
flexible target: if rank `r` at the cumulative threshold always breaks after
at most `g r` additional dyadic scales, and the cumulative thresholds are fast
enough for some summably strong rank schedule, then no counterexample exists. -/
theorem SummabilityCounterexample.false_of_fixedPriorRoomCoverDelayBreak_increment_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (b : ℕ) (g f : ℕ → ℕ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hfast : ∀ k, N ≤ k →
      rankThresholdFromIncrements b g (f k) ≤ k)
    (hquick : ∀ r (J₀ : Finset ℕ),
      CoprimeLCMSelection A (rankThresholdFromIncrements b g r) r J₀ →
        ∃ m, m + 1 ≤ g r ∧
          FixedPriorRoomCoverDelayBreak A
            (rankThresholdFromIncrements b g r) r m J₀) :
    False := by
  refine hA.false_of_successor_increment_bound b g f hfSummable hfast ?_
  intro r hT
  let T := rankThresholdFromIncrements b g r
  rcases hT T le_rfl with ⟨J₀, hJ₀⟩
  rcases hquick r J₀ hJ₀ with ⟨m, hmg, hbreak⟩
  refine ⟨m + 1, hmg, ?_⟩
  let K := T + (m + 1)
  have hTK : T ≤ K := by
    dsimp [K]
    omega
  have hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K := by
    calc
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤
          2 ^ T * 2 ^ (m + 1) :=
        Nat.mul_le_mul_right _ hJ₀.2.2.1
      _ = 2 ^ K := by
        simp [K, pow_add]
  exact CoprimeLCMSelection.threshold_succ_of_fixedPriorRoomCoverDelayBreak
    hJ₀ hTK hdelay₀ hbreak

/-- Uniform fixed-prior delay bounds are the packaged form needed by the
variable-increment criterion. -/
theorem SummabilityCounterexample.false_of_uniformFixedPriorRoomCoverDelayBreakBounds
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (b : ℕ) (g f : ℕ → ℕ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hfast : ∀ k, N ≤ k →
      rankThresholdFromIncrements b g (f k) ≤ k)
    (hbounds : ∀ r,
      UniformFixedPriorRoomCoverDelayBreakBound A
        (rankThresholdFromIncrements b g r) r (g r)) :
    False := by
  refine hA.false_of_fixedPriorRoomCoverDelayBreak_increment_bound
    b g f hfSummable hfast ?_
  intro r J₀ hJ₀
  exact hbounds r J₀ hJ₀

/-- If the large-scale-gap room-cover target holds in the quotient-irreducible
branch, then the counterexample is impossible.

Indeed, let `M, R` be the thresholds from
`NoLargeScaleGapPriorRoomCover`.  For ranks `r > R`, any fixed prior at a
scale above `R + M + 1` has its delay break by the single prefix
`max M N`; otherwise the large-gap target forbids the resulting room cover.
The finitely many ranks `r ≤ R` are paid for by arbitrary finite increments
coming from the nonquantitative fixed-prior induction.  Thus the whole rank
threshold schedule has bounded increments, hence a summably strong inverse,
contradicting nonsummability. -/
theorem SummabilityCounterexample.false_of_no_largeScaleGapPriorRoomCover_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hnoGap : NoLargeScaleGapPriorRoomCover A N) :
    False := by
  classical
  rcases hnoGap with ⟨M, R, hnoGap⟩
  let L : ℕ := max M N
  let thresholdSucc : ℕ → ℕ := fun r =>
    Classical.choose
      (hA.exists_threshold_of_rank_by_fixed_prior_induction_irreducible
        hirred hN2 (r + 1))
  have hthresholdSucc : ∀ r,
      CoprimeLCMSelectionThreshold A (r + 1) (thresholdSucc r) := by
    intro r
    exact (Classical.choose_spec
      (hA.exists_threshold_of_rank_by_fixed_prior_induction_irreducible
        hirred hN2 (r + 1))).2
  let g : ℕ → ℕ := fun r => if r ≤ R then thresholdSucc r else L + 1
  let q : ℕ :=
    (∑ r ∈ Finset.range (R + 1), thresholdSucc r) + (L + 1)
  let b : ℕ := max N (R + M + 2)
  have hqpos : 0 < q := by
    dsimp [q, L]
    omega
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hg_le : ∀ r, g r ≤ q := by
    intro r
    by_cases hr : r ≤ R
    · have hrmem : r ∈ Finset.range (R + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hr)
      have hterm_le :
          thresholdSucc r ≤
            ∑ x ∈ Finset.range (R + 1), thresholdSucc x := by
        exact Finset.single_le_sum (fun x _hx => Nat.zero_le (thresholdSucc x))
          hrmem
      dsimp [g, q]
      simp [hr]
      omega
    · dsimp [g, q]
      simp [hr]
  refine hA.false_of_successor_increment_bound
    b g (fun k => (k - b) / q)
    (summable_two_mul_three_four_pow_nat_sub_div q b) (N := b) ?_ ?_
  · intro k hbk
    exact rankThresholdFromIncrements_le_of_nat_sub_div b q g hg_le k hbk
  · intro r hT
    by_cases hr : r ≤ R
    · refine ⟨thresholdSucc r, ?_, ?_⟩
      · dsimp [g]
        simp [hr]
      · exact (hthresholdSucc r).mono (by omega)
    · let T := rankThresholdFromIncrements b g r
      rcases hT T le_rfl with ⟨J₀, hJ₀⟩
      have hbreak : FixedPriorRoomCoverDelayBreak A T r L J₀ := by
        intro K J hprops
        rcases hprops with ⟨hJ, hTK, hdelay₀, hcover⟩
        have hRr : R < r := Nat.lt_of_not_ge hr
        have hRcard : R < (corePrimeSupport J).card :=
          hRr.trans_le hJ.1.rank_le_corePrimeSupport_card
        have hML : M ≤ L := by
          dsimp [L]
          exact le_max_left M N
        have hNL : N ≤ L := by
          dsimp [L]
          exact le_max_right M N
        have hbGap : R + M + 1 < b := by
          dsimp [b]
          omega
        have hbT : b ≤ T := le_rankThresholdFromIncrements b g r
        have hgap : R + M + 1 < K := by
          omega
        exact (hnoGap L T K r J J₀ hML hNL hJ hJ₀ hTK hdelay₀
          hRcard hgap) hcover
      refine ⟨L + 1, ?_, ?_⟩
      · dsimp [g]
        simp [hr]
      · let T := rankThresholdFromIncrements b g r
        let K := T + (L + 1)
        have hTK : T ≤ K := by
          dsimp [K]
          omega
        have hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (L + 1) ≤ 2 ^ K := by
          calc
            J₀.lcm (fun a : ℕ => a) * 2 ^ (L + 1) ≤
                2 ^ T * 2 ^ (L + 1) :=
              Nat.mul_le_mul_right _ hJ₀.2.2.1
            _ = 2 ^ K := by
              simp [K, pow_add]
        exact CoprimeLCMSelection.threshold_succ_of_fixedPriorRoomCoverDelayBreak
          hJ₀ hTK hdelay₀ hbreak

/-- Necessity form of the preceding contradiction.  Any quotient-irreducible
counterexample must violate the large-scale-gap no-cover target.  Thus proving
`NoLargeScaleGapPriorRoomCover` in this branch is exactly the remaining
contradiction, not a consequence of the existing machinery. -/
theorem SummabilityCounterexample.not_no_largeScaleGapPriorRoomCover_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ¬ NoLargeScaleGapPriorRoomCover A N := by
  intro hnoGap
  exact hA.false_of_no_largeScaleGapPriorRoomCover_irreducible
    hN2 hirred hnoGap

/-- Good-prior fixed-prior criterion.  For the successor step it is enough to
find one rank-`r` prior at the current cumulative threshold whose fixed-prime
budget is beaten by a visible prefix inside the allowed increment `g r`.

This is weaker than a uniform bound over all priors and is the natural target
for a controlled-core induction: maintain or select priors with small enough
finite prime-layer budget. -/
theorem SummabilityCounterexample.false_of_goodPrior_prefixMass_increment_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (b : ℕ) (g f : ℕ → ℕ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ} (hN2 : 2 ≤ N)
    (hfast : ∀ k, N ≤ k →
      rankThresholdFromIncrements b g (f k) ≤ k)
    (hgood : ∀ r,
      ∃ J₀ : Finset ℕ,
        CoprimeLCMSelection A (rankThresholdFromIncrements b g r) r J₀ ∧
        ∃ m, m + 1 ≤ g r ∧
          fixedPriorPrimeLayerPrefixBound A N r J₀ <
            dyadicPrefixReciprocalMass A N m) :
    False := by
  refine hA.false_of_successor_increment_bound b g f hfSummable hfast ?_
  intro r _hT
  let T := rankThresholdFromIncrements b g r
  rcases hgood r with ⟨J₀, hJ₀, m, hmg, hlarge⟩
  have hbreak : FixedPriorRoomCoverDelayBreak A T r m J₀ :=
    hA.fixedPriorRoomCoverDelayBreak_of_fixedPriorBound_lt_prefixMass
      hirred hJ₀ hN2 hlarge
  refine ⟨m + 1, hmg, ?_⟩
  let K := T + (m + 1)
  have hTK : T ≤ K := by
    dsimp [K]
    omega
  have hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K := by
    calc
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤
          2 ^ T * 2 ^ (m + 1) :=
        Nat.mul_le_mul_right _ hJ₀.2.2.1
      _ = 2 ^ K := by
        simp [K, pow_add]
  exact CoprimeLCMSelection.threshold_succ_of_fixedPriorRoomCoverDelayBreak
    hJ₀ hTK hdelay₀ hbreak

/-- Scale-budget criterion.  It is enough to beat the crude scale-only
prime-layer budget at the current cumulative threshold; then every threshold
witness at that rank is a good fixed prior. -/
theorem SummabilityCounterexample.false_of_scalePrimeLayerPrefixBound_increment_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (b : ℕ) (g f : ℕ → ℕ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ} (hN2 : 2 ≤ N)
    (hfast : ∀ k, N ≤ k →
      rankThresholdFromIncrements b g (f k) ≤ k)
    (hscale : ∀ r,
      ∃ m, m + 1 ≤ g r ∧
        scalePrimeLayerPrefixBound A N r (rankThresholdFromIncrements b g r) <
          dyadicPrefixReciprocalMass A N m) :
    False := by
  refine hA.false_of_successor_increment_bound b g f hfSummable hfast ?_
  intro r hT
  let T := rankThresholdFromIncrements b g r
  rcases hT T le_rfl with ⟨J₀, hJ₀⟩
  rcases hscale r with ⟨m, hmg, hlargeScale⟩
  have hprior_le :
      fixedPriorPrimeLayerPrefixBound A N r J₀ ≤
        scalePrimeLayerPrefixBound A N r T :=
    hJ₀.fixedPriorPrimeLayerPrefixBound_le_scaleBound
  have hlarge :
      fixedPriorPrimeLayerPrefixBound A N r J₀ <
        dyadicPrefixReciprocalMass A N m :=
    lt_of_le_of_lt hprior_le hlargeScale
  have hbreak : FixedPriorRoomCoverDelayBreak A T r m J₀ :=
    hA.fixedPriorRoomCoverDelayBreak_of_fixedPriorBound_lt_prefixMass
      hirred hJ₀ hN2 hlarge
  refine ⟨m + 1, hmg, ?_⟩
  let K := T + (m + 1)
  have hTK : T ≤ K := by
    dsimp [K]
    omega
  have hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K := by
    calc
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤
          2 ^ T * 2 ^ (m + 1) :=
        Nat.mul_le_mul_right _ hJ₀.2.2.1
      _ = 2 ^ K := by
        simp [K, pow_add]
  exact CoprimeLCMSelection.threshold_succ_of_fixedPriorRoomCoverDelayBreak
    hJ₀ hTK hdelay₀ hbreak

/-- Exact support-budget successor criterion.  This is the sharp fresh-mass
target: at each rank, choose one prior and one visible prefix inside the
allowed increment such that every possible delayed room-cover core has
support-prime budget below that prefix mass. -/
theorem SummabilityCounterexample.false_of_corePrimeLayerPrefixBound_increment_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (b : ℕ) (g f : ℕ → ℕ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ} (hN2 : 2 ≤ N)
    (hfast : ∀ k, N ≤ k →
      rankThresholdFromIncrements b g (f k) ≤ k)
    (hcore : ∀ r,
      ∃ J₀ : Finset ℕ,
        CoprimeLCMSelection A (rankThresholdFromIncrements b g r) r J₀ ∧
        ∃ m, m + 1 ≤ g r ∧
          ∀ (K : ℕ) (J : Finset ℕ),
            CoprimeLCMSelection.LCMMinimal A K r J →
            rankThresholdFromIncrements b g r ≤ K →
            J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
            corePrimeLayerPrefixBound A N r J <
              dyadicPrefixReciprocalMass A N m) :
    False := by
  refine hA.false_of_successor_increment_bound b g f hfSummable hfast ?_
  intro r _hT
  let T := rankThresholdFromIncrements b g r
  rcases hcore r with ⟨J₀, hJ₀, m, hmg, hsmall⟩
  have hbreak : FixedPriorRoomCoverDelayBreak A T r m J₀ :=
    hA.fixedPriorRoomCoverDelayBreak_of_corePrimeLayerBound
      hirred hJ₀ hN2 hsmall
  refine ⟨m + 1, hmg, ?_⟩
  let K := T + (m + 1)
  have hTK : T ≤ K := by
    dsimp [K]
    omega
  have hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K := by
    calc
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤
          2 ^ T * 2 ^ (m + 1) :=
        Nat.mul_le_mul_right _ hJ₀.2.2.1
      _ = 2 ^ K := by
        simp [K, pow_add]
  exact CoprimeLCMSelection.threshold_succ_of_fixedPriorRoomCoverDelayBreak
    hJ₀ hTK hdelay₀ hbreak

/-- A uniform affine fixed-prior delay-break bound would prove the summability
form of Erdős problem #12. -/
theorem Erdos12SummabilityQuestion.of_affine_fixedPriorRoomCoverDelayBreak_bound
    (q b : ℕ) [NeZero q]
    (hquick : ∀ {A : Set ℕ}, SummabilityCounterexample A →
      ∀ r (J₀ : Finset ℕ),
        CoprimeLCMSelection A (q * r + b) r J₀ →
          ∃ m, m + 1 ≤ q ∧
            FixedPriorRoomCoverDelayBreak A (q * r + b) r m J₀) :
    Erdos12SummabilityQuestion := by
  intro A hInf hPos hAvoid
  by_contra hnotSummable
  have hA : SummabilityCounterexample A :=
    ⟨hInf, hPos, hAvoid, hnotSummable⟩
  exact hA.false_of_affine_fixedPriorRoomCoverDelayBreak_bound q b
    (hquick hA)

/-- Contrapositive form of the preceding theorem.  Any counterexample must
contain, on every affine line `q*r+b`, a fixed prior whose room-cover delay
does not break within the next `q` dyadic scales. -/
theorem SummabilityCounterexample.exists_slow_fixedPriorRoomCoverDelay_of_affine_counterexample
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (q b : ℕ) [NeZero q] :
    ∃ (r : ℕ) (J₀ : Finset ℕ),
      CoprimeLCMSelection A (q * r + b) r J₀ ∧
      ∀ m, m + 1 ≤ q →
        ∃ (K : ℕ) (J : Finset ℕ),
          CoprimeLCMSelection.LCMMinimal A K r J ∧
          q * r + b ≤ K ∧
          J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
          ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
            ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  classical
  by_contra hnone
  have hquick : ∀ r (J₀ : Finset ℕ),
      CoprimeLCMSelection A (q * r + b) r J₀ →
        ∃ m, m + 1 ≤ q ∧
          FixedPriorRoomCoverDelayBreak A (q * r + b) r m J₀ := by
    intro r J₀ hJ₀
    by_contra hnoBreak
    apply hnone
    refine ⟨r, J₀, hJ₀, ?_⟩
    intro m hmq
    by_contra hnoCover
    apply hnoBreak
    refine ⟨m, hmq, ?_⟩
    intro K J hprops
    exact hnoCover ⟨K, J, hprops⟩
  exact hA.false_of_affine_fixedPriorRoomCoverDelayBreak_bound q b hquick

/-- Every counterexample has a prior room-cover obstruction at any prescribed
prefix length.  This is the affine slow-delay theorem with the one-off choice
`q = m + 1`: if all priors broke by that prefix, the affine successor criterion
would prove summability. -/
theorem SummabilityCounterexample.exists_prior_room_cover_at
    {A : Set ℕ} (hA : SummabilityCounterexample A) (m : ℕ) :
    ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  classical
  let q : ℕ := m + 1
  have hqpos : 0 < q := by
    dsimp [q]
    omega
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  rcases hA.exists_slow_fixedPriorRoomCoverDelay_of_affine_counterexample
      q 0 with ⟨r, J₀, hJ₀, hslow⟩
  rcases hslow m (by dsimp [q]; omega) with
    ⟨K, J, hJ, hTK, hdelay₀, hcover⟩
  exact ⟨q * r + 0, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hcover⟩

/-- Counterexamples have endless prior room-cover delay: every sufficiently
late prefix is witnessed by some fixed prior and a later LCM-minimal covered
room. -/
theorem SummabilityCounterexample.endless_prior_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A) (N : ℕ) :
    ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} := by
  intro m _hm
  exact hA.exists_prior_room_cover_at m

/-- Direct counterexample form of the large-prime/large-gap extraction. -/
theorem SummabilityCounterexample.exists_ge_largePrime_scaleGap_prior_cover_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (M Q : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ) (p : ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      p ∈ corePrimeSupport J ∧
      Q ≤ p ∧
      Q.primesBelow.card + M + 1 < K :=
  hA.exists_ge_largePrime_scaleGap_prior_cover_of_endless_irreducible
    hN2 hirred (hA.endless_prior_room_covers N) M Q

/-- Direct counterexample form of the many-fresh-primes large-gap extraction. -/
theorem SummabilityCounterexample.exists_ge_manyFresh_scaleGap_prior_cover_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (M Q S : ℕ) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      S < ((corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow)).card ∧
      (∀ p ∈ corePrimeSupport J, p ∉ Q.primesBelow → Q ≤ p) ∧
      Q.primesBelow.card + S + M + 1 < K :=
  hA.exists_ge_manyFresh_scaleGap_prior_cover_of_endless_irreducible
    hN2 hirred (hA.endless_prior_room_covers N) M Q S

/-- The surviving irreducible branch can force one prior room-cover witness
that is simultaneously late, has many support primes outside a chosen
small-prime box, has large scale gap, and has arbitrarily large
carrier-aware obstruction budget. -/
theorem SummabilityCounterexample.exists_manyFresh_largeBudget_scaleGap_prior_cover_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (M Q S : ℕ) (hQ : 0 < Q) {C : ℝ} (hC : 0 ≤ C) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      S < ((corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow)).card ∧
      (∀ p ∈ corePrimeSupport J, p ∉ Q.primesBelow → Q ≤ p) ∧
      Q.primesBelow.card + S + M + 1 < K ∧
      Q ^ ((corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow)).card ≤
        2 ^ K ∧
      Q ^ (S + 1) ≤ 2 ^ K ∧
      C <
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          (∑ p ∈ Q.primesBelow, ∑' n : ℕ,
              reciprocalIndicator (multipleLayer p A) n) +
            (K : ℝ) *
              ((((corePrimeSupport J).filter
                (fun p => p ∉ Q.primesBelow)).card : ℝ) / (Q : ℝ)) := by
  rcases hA.exists_prefix_forces_large_outsideCardBound_of_prior_room_cover
      hirred hN2 hC with ⟨m₀, _hNm₀, hforce⟩
  let M' : ℕ := max M m₀
  rcases hA.exists_ge_manyFresh_scaleGap_prior_cover_irreducible
      hN2 hirred M' Q S with
    ⟨m, T, K, r, J, J₀, hM'm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
      hfresh, hlarge, hgap'⟩
  have hMm : M ≤ m := (le_max_left M m₀).trans hM'm
  have hm₀m : m₀ ≤ m := (le_max_right M m₀).trans hM'm
  have hpow : 2 ^ (m₀ + 1) ≤ 2 ^ (m + 1) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hdelay₀' : J₀.lcm (fun a : ℕ => a) * 2 ^ (m₀ + 1) ≤ 2 ^ K :=
    (Nat.mul_le_mul_left _ hpow).trans hdelay₀
  have hbudget :=
    hforce T K r Q J J₀ hJ hJ₀ hTK hdelay₀' hQ hcover
  have hgap : Q.primesBelow.card + S + M + 1 < K := by
    dsimp [M'] at hgap'
    omega
  have hprod :
      Q ^ ((corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow)).card ≤
        2 ^ K := by
    have hlargeFilter :
        ∀ p ∈ (corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow),
          Q ≤ p := by
      intro p hp
      exact hlarge p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
    exact hJ.1.pow_outsideSupport_card_le_two_pow
      (P := Q.primesBelow) hlargeFilter
  have hprodS : Q ^ (S + 1) ≤ 2 ^ K := by
    have hSle :
        S + 1 ≤
          ((corePrimeSupport J).filter (fun p => p ∉ Q.primesBelow)).card := by
      omega
    exact (Nat.pow_le_pow_right hQ hSle).trans hprod
  exact ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
    hfresh, hlarge, hgap, hprod, hprodS, hbudget⟩

/-- Contrapositive of the fast-threshold criterion.  In a counterexample, no
threshold schedule can keep up with a summably strong rank schedule eventually:
for every tail there is a scale `k` where the threshold for rank `f k` is still
strictly beyond `k`. -/
theorem SummabilityCounterexample.exists_ge_rankThreshold_lag
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {τ f : ℕ → ℕ}
    (hτ : CoprimeLCMSelectionThresholdSchedule A τ)
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (N : ℕ) :
    ∃ k, N ≤ k ∧ k < τ (f k) := by
  by_contra hnone
  have hfast : ∀ k, N ≤ k → τ (f k) ≤ k := by
    intro k hk
    by_contra hnot
    exact hnone ⟨k, hk, not_le.mp hnot⟩
  exact hA.false_of_fast_rankThresholdSchedule hτ hfSummable hfast

/-- Concrete dyadic-log threshold lag.  Since `f k = k` is summably strong,
any threshold schedule in a counterexample must have `τ k > k` arbitrarily
late. -/
theorem SummabilityCounterexample.exists_ge_logRankThreshold_lag
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {τ : ℕ → ℕ}
    (hτ : CoprimeLCMSelectionThresholdSchedule A τ)
    (N : ℕ) :
    ∃ k, N ≤ k ∧ k < τ k :=
  hA.exists_ge_rankThreshold_lag hτ
    ((summable_geometric_of_lt_one
        (by norm_num : 0 ≤ (3 / 4 : ℝ))
        (by norm_num : (3 / 4 : ℝ) < 1)).mul_left 2) N

/-- The fixed-prior induction produces a threshold schedule in the
quotient-irreducible branch.  This is intentionally nonquantitative: the
remaining task is to prove that some such schedule is fast enough. -/
theorem SummabilityCounterexample.exists_rankThresholdSchedule_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) :
    ∃ τ : ℕ → ℕ, (∀ r, N ≤ τ r) ∧
      CoprimeLCMSelectionThresholdSchedule A τ := by
  classical
  have hthreshold :=
    hA.exists_threshold_of_rank_by_fixed_prior_induction_irreducible
      hirred hN2
  let τ : ℕ → ℕ := fun r => Classical.choose (hthreshold r)
  refine ⟨τ, ?_, ?_⟩
  · intro r
    exact (Classical.choose_spec (hthreshold r)).1
  · intro r
    exact (Classical.choose_spec (hthreshold r)).2

/-- In an irreducible counterexample, the threshold schedule produced by
fixed-prior induction must lag behind the diagonal arbitrarily far out.  Thus
the remaining quantitative problem is exactly to rule out this lag. -/
theorem SummabilityCounterexample.exists_irreducible_rankThresholdSchedule_with_logRank_lag
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N) :
    ∃ τ : ℕ → ℕ, (∀ r, N ≤ τ r) ∧
      CoprimeLCMSelectionThresholdSchedule A τ ∧
      ∀ M, ∃ k, M ≤ k ∧ k < τ k := by
  rcases hA.exists_rankThresholdSchedule_of_irreducible hirred hN2 with
    ⟨τ, hNτ, hτ⟩
  exact ⟨τ, hNτ, hτ, fun M =>
    hA.exists_ge_logRankThreshold_lag hτ M⟩

/-- If every threshold schedule supplied by the irreducible fixed-prior
induction is fast enough for some summably strong rank schedule, then the
quotient-irreducible counterexample is impossible. -/
theorem SummabilityCounterexample.false_of_fast_irreducible_rankThresholdSchedule
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN2 : 2 ≤ N)
    (hfast : ∀ τ : ℕ → ℕ, (∀ r, N ≤ τ r) →
      CoprimeLCMSelectionThresholdSchedule A τ →
      ∃ f : ℕ → ℕ,
        (Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k)) ∧
        ∀ k, N ≤ k → τ (f k) ≤ k) :
    False := by
  rcases hA.exists_rankThresholdSchedule_of_irreducible hirred hN2 with
    ⟨τ, hNτ, hτ⟩
  rcases hfast τ hNτ hτ with ⟨f, hfSummable, hτfast⟩
  exact hA.false_of_fast_rankThresholdSchedule hτ hfSummable hτfast

/-- Irreducible fresh-prime escape for persistent prior room-cover
obstructions.  If such obstructions continue forever in a quotient-irreducible
counterexample, their core prime supports cannot be confined to any prescribed
finite prime set. -/
theorem SummabilityCounterexample.exists_fresh_primeSupport_of_endless_prior_room_covers_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
      ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
        N ≤ m ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        ∃ p ∈ corePrimeSupport J, p ∉ P := by
  intro P hPprime
  by_contra hnone
  have hbounded : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        corePrimeSupport J ⊆ P := by
    intro m hm
    rcases hendless m hm with
      ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hcover⟩
    have hsub : corePrimeSupport J ⊆ P := by
      intro p hpSupport
      by_contra hpP
      exact hnone ⟨m, T, K, r, J, J₀, hm, hJ, hJ₀, hTK, hdelay₀,
        hcover, p, hpSupport, hpP⟩
    exact ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hcover, hsub⟩
  rcases hA.quotient_of_endless_prior_room_covers_finite_primeSupport
      hN2 hPprime hbounded with
    ⟨p, _hpP, d, hdp, hdgt, hcounter⟩
  exact hirred p d hdp hdgt hcounter

/-- Numeric form of the preceding fresh-prime escape: in the irreducible
branch, persistent prior room-cover obstructions must contain core-support
primes larger than every prescribed bound. -/
theorem SummabilityCounterexample.exists_large_primeSupport_of_endless_prior_room_covers_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    ∀ M, ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      ∃ p ∈ corePrimeSupport J, M < p := by
  intro M
  let P : Finset ℕ := (Finset.Icc 2 M).filter fun p => Nat.Prime p
  have hPprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  rcases hA.exists_fresh_primeSupport_of_endless_prior_room_covers_irreducible
      hN2 hirred hendless P hPprime with
    ⟨m, T, K, r, J, J₀, hm, hJ, hJ₀, hTK, hdelay₀, hcover,
      p, hpSupport, hpNotP⟩
  have hpPrime : Nat.Prime p := prime_of_mem_corePrimeSupport hpSupport
  have hMp : M < p := by
    by_contra hnot
    have hpM : p ≤ M := not_lt.mp hnot
    have hpP : p ∈ P := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, hpM⟩, hpPrime⟩
    exact hpNotP hpP
  exact ⟨m, T, K, r, J, J₀, hm, hJ, hJ₀, hTK, hdelay₀, hcover,
    p, hpSupport, hMp⟩

/-- The dyadic-log rank schedule `f k = k` is summably strong.  Since dyadic
scale `k` corresponds to integers below `2 ^ k`, this is logarithmic in the
original cutoff. -/
theorem summable_two_mul_three_four_pow_id :
    Summable fun k : ℕ => 2 * ((3 / 4 : ℝ) ^ k) := by
  exact (summable_geometric_of_lt_one
      (by norm_num : 0 ≤ (3 / 4 : ℝ))
      (by norm_num : (3 / 4 : ℝ) < 1)).mul_left 2

/-- Concrete dyadic-log positive target.  To prove reciprocal summability of
an avoiding set, it is enough to prove that every sufficiently late
LCM-minimal core of rank below the dyadic scale `k` has LCM-room mass larger
than the scale-weighted reciprocal prime support. -/
theorem AvoidingSet.reciprocalSummable_of_eventual_logRank_lcmRoom_primeSupport_scale_bound
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A) {N : ℕ}
    (hdom : ∀ k, N ≤ k → ∀ s J,
      s < k → CoprimeLCMSelection.LCMMinimal A k s J →
        (k : ℝ) * corePrimeSupportPrimeReciprocalMass J <
          lcmRoomReciprocalMass A k J) :
    ReciprocalSummable A := by
  refine hA.reciprocalSummable_of_eventual_lcmRoom_primeSupport_scale_bound
    hpos summable_two_mul_three_four_pow_id (N := N) ?_
  intro k hk s J hs hJ
  exact hdom k hk s J hs hJ

/-- Concrete dyadic-log obstruction forced in every counterexample.  If the
positive target above fails globally, then at arbitrarily late scales there is
an exact LCM-minimal core of rank below `k` whose LCM-room is dominated by the
scale-weighted reciprocal mass of its prime support. -/
theorem SummabilityCounterexample.exists_ge_logRank_lcmRoom_primeSupport_scale_obstruction
    {A : Set ℕ} (hA : SummabilityCounterexample A) (N : ℕ) :
    ∃ k s J, N ≤ k ∧ s < k ∧
      CoprimeLCMSelection.LCMMinimal A k s J ∧
      lcmRoomReciprocalMass A k J ≤
        (k : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  exact hA.exists_ge_lcmRoom_primeSupport_scale_obstruction
    summable_two_mul_three_four_pow_id N

/-- In the quotient-irreducible branch, dyadic-log failures occur only after
passing every prescribed fixed rank.  Thus the surviving obstruction is not
fixed-rank: it must keep pushing the requested rank upward with the scale. -/
theorem SummabilityCounterexample.exists_ge_logRank_selection_failure_with_rank_gap
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (r N : ℕ) :
    ∃ k, N ≤ k ∧ r < k ∧ CoprimeLCMSelectionFailure A k k := by
  exact hA.exists_ge_selection_failure_with_rank_gap
    hirred summable_two_mul_three_four_pow_id r N

/-- A log-rank obstruction cannot coexist with a delayed prefix whose reciprocal
mass beats the finite-rank payment plus the scale-weighted reciprocal prime
support.  This is the local contradiction we must arrange for every bad core. -/
theorem CoprimeLCMSelection.LCMMinimal.no_logRank_obstruction_of_heavy_delayed_prefix
    {A : Set ℕ} {N m k s : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A k s J)
    (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ k)
    (hheavy : (s : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (k : ℝ) * corePrimeSupportPrimeReciprocalMass J <
      dyadicPrefixReciprocalMass A N m) :
    ¬ lcmRoomReciprocalMass A k J ≤
      (k : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  intro hobstruction
  have hprefix :=
    hJ.prefixMass_le_rank_div_pow_add_scalePrimeSupport
      hN hdelay hobstruction
  exact (not_lt_of_ge hprefix) hheavy

/-- Prior-witness version of the same local contradiction.  If an earlier
rank-`s` selection already gives enough LCM headroom to see a heavy prefix,
then any later LCM-minimal log-rank obstruction of the same rank is impossible. -/
theorem CoprimeLCMSelection.LCMMinimal.no_logRank_obstruction_of_heavy_delayed_prefix_of_prior
    {A : Set ℕ} {N m T k s : ℕ} {J J₀ : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A k s J)
    (hJ₀ : CoprimeLCMSelection A T s J₀)
    (hTk : T ≤ k)
    (hN : 2 ≤ N)
    (hdelay₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ k)
    (hheavy : (s : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (k : ℝ) * corePrimeSupportPrimeReciprocalMass J <
      dyadicPrefixReciprocalMass A N m) :
    ¬ lcmRoomReciprocalMass A k J ≤
      (k : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  intro hobstruction
  have hprefix :=
    hJ.prefixMass_le_rank_div_pow_add_scalePrimeSupport_of_prior
      hJ₀ hTk hN hdelay₀ hobstruction
  exact (not_lt_of_ge hprefix) hheavy

/-- Heavy-prefix forcing form for the scale-prime-support obstruction.  In any
counterexample, every target `C` has a dyadic prefix such that any delayed
LCM-minimal scale-prime-support obstruction seeing that prefix must have
obstruction budget larger than `C`. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_scalePrimeSupportBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    ∃ m, N ≤ m ∧ ∀ (K r : ℕ) (J : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J →
      J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      lcmRoomReciprocalMass A K J ≤
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J →
      C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro K r J hJ hdelay hobstruction
  have hupper :=
    hJ.prefixMass_le_rank_div_pow_add_scalePrimeSupport
      hN2 hdelay hobstruction
  linarith

/-- Bounded-rank version of the heavy-prefix forcing.  If the delayed
obstruction cores have rank at most `R`, and the prefix starts far enough out
that `R / 2^N ≤ ε`, then a prefix forcing level `C + ε` forces the
scale-weighted reciprocal prime support itself to exceed `C`. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_scalePrimeSupport_of_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N R : ℕ} (hN2 : 2 ≤ N) {C ε : ℝ}
    (hCε : 0 ≤ C + ε)
    (hRε : (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤ ε) :
    ∃ m, N ≤ m ∧ ∀ (K r : ℕ) (J : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      lcmRoomReciprocalMass A K J ≤
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J →
      C < (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  rcases hA.exists_prefix_forces_large_scalePrimeSupportBound hN2 hCε with
    ⟨m, hNm, hforce⟩
  refine ⟨m, hNm, ?_⟩
  intro K r J hrR hJ hdelay hobstruction
  have hbudget := hforce K r J hJ hdelay hobstruction
  have hden_nonneg : 0 ≤ (((2 ^ N : ℕ) : ℝ)) := by positivity
  have hr_le : (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤
      (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hrR) hden_nonneg
  linarith

/-- Prior-witness heavy-prefix forcing form.  The delayed visibility may be
certified by an earlier rank witness and transferred to the later
LCM-minimal core. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_scalePrimeSupportBound_of_prior
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      lcmRoomReciprocalMass A K J ≤
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J →
      C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  refine ⟨n - 1, by omega, ?_⟩
  intro T K r J J₀ hJ hJ₀ hTK hdelay₀ hobstruction
  have hupper :=
    hJ.prefixMass_le_rank_div_pow_add_scalePrimeSupport_of_prior
      hJ₀ hTK hN2 hdelay₀ hobstruction
  linarith

/-- Bounded-rank prior-witness forcing.  This is the form aimed at the
irreducible threshold machinery: for ranks bounded by `R`, delayed
prior-witness obstructions must force arbitrarily large
`K * Σ_{p | J} 1/p`. -/
theorem SummabilityCounterexample.exists_prefix_forces_large_scalePrimeSupport_of_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N R : ℕ} (hN2 : 2 ≤ N) {C ε : ℝ}
    (hCε : 0 ≤ C + ε)
    (hRε : (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤ ε) :
    ∃ m, N ≤ m ∧ ∀ (T K r : ℕ) (J J₀ : Finset ℕ),
      r ≤ R →
      CoprimeLCMSelection.LCMMinimal A K r J →
      CoprimeLCMSelection A T r J₀ →
      T ≤ K →
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K →
      lcmRoomReciprocalMass A K J ≤
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J →
      C < (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  rcases hA.exists_prefix_forces_large_scalePrimeSupportBound_of_prior hN2 hCε with
    ⟨m, hNm, hforce⟩
  refine ⟨m, hNm, ?_⟩
  intro T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hobstruction
  have hbudget := hforce T K r J J₀ hJ hJ₀ hTK hdelay₀ hobstruction
  have hden_nonneg : 0 ≤ (((2 ^ N : ℕ) : ℝ)) := by positivity
  have hr_le : (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤
      (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hrR) hden_nonneg
  linarith

/-- Endless delayed scale-prime-support obstructions have unbounded total
budget.  If, after every sufficiently late prefix, some LCM-minimal bad core
still sees that prefix, then the quantities
`r / 2^N + K * Σ_{p | J} 1/p` cannot remain bounded. -/
theorem SummabilityCounterexample.unbounded_budget_of_endless_delayed_scalePrimeSupport
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hendless : ∀ m, N ≤ m →
      ∃ (K r : ℕ) (J : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    ∀ C : ℝ, 0 ≤ C →
      ∃ (m K r : ℕ) (J : Finset ℕ),
        N ≤ m ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ∧
        C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  intro C hC
  rcases hA.exists_prefix_forces_large_scalePrimeSupportBound hN2 hC with
    ⟨m, hNm, hforce⟩
  rcases hendless m hNm with ⟨K, r, J, hJ, hdelay, hobstruction⟩
  exact ⟨m, K, r, J, hNm, hJ, hdelay, hobstruction,
    hforce K r J hJ hdelay hobstruction⟩

/-- Prior-witness version of the endless-delay escape.  If every late prefix is
visible from an earlier rank witness and then blocked by a later LCM-minimal
core, the corresponding obstruction budgets are unbounded. -/
theorem SummabilityCounterexample.unbounded_budget_of_endless_prior_scalePrimeSupport
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    ∀ C : ℝ, 0 ≤ C →
      ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
        N ≤ m ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ∧
        C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  intro C hC
  rcases hA.exists_prefix_forces_large_scalePrimeSupportBound_of_prior hN2 hC with
    ⟨m, hNm, hforce⟩
  rcases hendless m hNm with
    ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hobstruction⟩
  exact ⟨m, T, K, r, J, J₀, hNm, hJ, hJ₀, hTK, hdelay₀,
    hobstruction, hforce T K r J J₀ hJ hJ₀ hTK hdelay₀ hobstruction⟩

/-- Endless delayed room-cover obstructions have unbounded total numerical
budget.  A room cover is first converted to the scale-prime-support
obstruction, then the heavy-prefix forcing argument applies. -/
theorem SummabilityCounterexample.unbounded_budget_of_endless_delayed_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hendless : ∀ m, N ≤ m →
      ∃ (K r : ℕ) (J : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    ∀ C : ℝ, 0 ≤ C →
      ∃ (m K r : ℕ) (J : Finset ℕ),
        N ≤ m ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  intro C hC
  rcases hA.exists_prefix_forces_large_scalePrimeSupportBound hN2 hC with
    ⟨m, hNm, hforce⟩
  rcases hendless m hNm with ⟨K, r, J, hJ, hdelay, hcover⟩
  have hobstruction :
      lcmRoomReciprocalMass A K J ≤
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J :=
    lcmRoomReciprocalMass_le_scalePrimeSupport_of_room_cover hcover
  exact ⟨m, K, r, J, hNm, hJ, hdelay, hcover,
    hforce K r J hJ hdelay hobstruction⟩

/-- Prior-witness version of the room-cover budget escape.  Persistent prior
room covers cannot keep the combined finite-rank and scale-prime-support
budget bounded. -/
theorem SummabilityCounterexample.unbounded_budget_of_endless_prior_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    ∀ C : ℝ, 0 ≤ C →
      ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
        N ≤ m ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  intro C hC
  rcases hA.exists_prefix_forces_large_scalePrimeSupportBound_of_prior
      hN2 hC with ⟨m, hNm, hforce⟩
  rcases hendless m hNm with
    ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hcover⟩
  have hobstruction :
      lcmRoomReciprocalMass A K J ≤
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J :=
    lcmRoomReciprocalMass_le_scalePrimeSupport_of_room_cover hcover
  exact ⟨m, T, K, r, J, J₀, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
    hforce T K r J J₀ hJ hJ₀ hTK hdelay₀ hobstruction⟩

/-- The surviving irreducible prior-room-cover branch escapes every fixed box:
after prescribing a minimum prefix, a minimum support size, and a numerical
budget, one can find a delayed room-cover witness beyond all three thresholds
and with large scale gap. -/
theorem SummabilityCounterexample.exists_largeGap_budget_prior_room_cover_of_endless_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x})
    (M R : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      R < (corePrimeSupport J).card ∧
      R + M + 1 < K ∧
      C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  rcases hA.exists_prefix_forces_large_scalePrimeSupportBound_of_prior
      hN2 hC with ⟨m₀, _hNm₀, hforce⟩
  let M' : ℕ := max M m₀
  rcases hA.exists_ge_large_scaleGap_prior_room_cover_of_endless_irreducible
      hN2 hirred hendless M' R with
    ⟨m, T, K, r, J, J₀, hM'm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
      hRcard, hgap'⟩
  have hMm : M ≤ m := (le_max_left M m₀).trans hM'm
  have hm₀m : m₀ ≤ m := (le_max_right M m₀).trans hM'm
  have hdelay_m₀ : J₀.lcm (fun a : ℕ => a) * 2 ^ (m₀ + 1) ≤ 2 ^ K := by
    have hpow : 2 ^ (m₀ + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    exact (Nat.mul_le_mul_left (J₀.lcm fun a : ℕ => a) hpow).trans hdelay₀
  have hobstruction :
      lcmRoomReciprocalMass A K J ≤
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J :=
    lcmRoomReciprocalMass_le_scalePrimeSupport_of_room_cover hcover
  have hbudget :
      C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J :=
    hforce T K r J J₀ hJ hJ₀ hTK hdelay_m₀ hobstruction
  have hgap : R + M + 1 < K := by
    dsimp [M'] at hgap'
    omega
  exact ⟨m, T, K, r, J, J₀, hMm, hNm, hJ, hJ₀, hTK, hdelay₀, hcover,
    hRcard, hgap, hbudget⟩

/-- Direct counterexample form of the preceding escape theorem.  In any
quotient-irreducible counterexample, the large-gap/high-support room-cover
witnesses can also be forced to have arbitrarily large combined obstruction
budget. -/
theorem SummabilityCounterexample.exists_largeGap_budget_prior_room_cover_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {N : ℕ}
    (hN2 : 2 ≤ N)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (M R : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
      M ≤ m ∧
      N ≤ m ∧
      CoprimeLCMSelection.LCMMinimal A K r J ∧
      CoprimeLCMSelection A T r J₀ ∧
      T ≤ K ∧
      J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
      ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
      R < (corePrimeSupport J).card ∧
      R + M + 1 < K ∧
      C < (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        (K : ℝ) * corePrimeSupportPrimeReciprocalMass J :=
  hA.exists_largeGap_budget_prior_room_cover_of_endless_irreducible
    hN2 hirred (hA.endless_prior_room_covers N) M R hC

/-- Bounded-rank endless delayed obstructions force the scale-weighted
reciprocal prime support itself to escape to infinity.  The bounded-rank
hypothesis absorbs the finite-rank payment `r / 2^N`. -/
theorem SummabilityCounterexample.unbounded_scalePrimeSupport_of_endless_delayed_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N R : ℕ} (hN2 : 2 ≤ N)
    (hendless : ∀ m, N ≤ m →
      ∃ (K r : ℕ) (J : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    ∀ C : ℝ, 0 ≤ C →
      ∃ (m K r : ℕ) (J : Finset ℕ),
        N ≤ m ∧
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ∧
        C < (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  intro C hC
  let ε : ℝ := (R : ℝ) / (((2 ^ N : ℕ) : ℝ))
  have hCε : 0 ≤ C + ε := by
    have hε : 0 ≤ ε := by
      dsimp [ε]
      positivity
    linarith
  rcases hA.exists_prefix_forces_large_scalePrimeSupport_of_rank_le
      hN2 hCε (show (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤ ε from le_rfl) with
    ⟨m, hNm, hforce⟩
  rcases hendless m hNm with ⟨K, r, J, hrR, hJ, hdelay, hobstruction⟩
  exact ⟨m, K, r, J, hNm, hrR, hJ, hdelay, hobstruction,
    hforce K r J hrR hJ hdelay hobstruction⟩

/-- Prior-witness bounded-rank endless obstructions force
`K * Σ_{p | J} 1/p` to be unbounded.  This is the formal version of the
"endless delay escapes to infinity" step for the current positive route. -/
theorem SummabilityCounterexample.unbounded_scalePrimeSupport_of_endless_prior_rank_le
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N R : ℕ} (hN2 : 2 ≤ N)
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J) :
    ∀ C : ℝ, 0 ≤ C →
      ∃ (m T K r : ℕ) (J J₀ : Finset ℕ),
        N ≤ m ∧
        r ≤ R ∧
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ∧
        C < (K : ℝ) * corePrimeSupportPrimeReciprocalMass J := by
  intro C hC
  let ε : ℝ := (R : ℝ) / (((2 ^ N : ℕ) : ℝ))
  have hCε : 0 ≤ C + ε := by
    have hε : 0 ≤ ε := by
      dsimp [ε]
      positivity
    linarith
  rcases hA.exists_prefix_forces_large_scalePrimeSupport_of_prior_rank_le
      hN2 hCε (show (R : ℝ) / (((2 ^ N : ℕ) : ℝ)) ≤ ε from le_rfl) with
    ⟨m, hNm, hforce⟩
  rcases hendless m hNm with
    ⟨T, K, r, J, J₀, hrR, hJ, hJ₀, hTK, hdelay₀, hobstruction⟩
  exact ⟨m, T, K, r, J, J₀, hNm, hrR, hJ, hJ₀, hTK, hdelay₀,
    hobstruction, hforce T K r J J₀ hrR hJ hJ₀ hTK hdelay₀ hobstruction⟩

/-- Uniform delayed scale-prime-support bounds are impossible in a
counterexample.  If every heavy prefix could be seen by some delayed bad core
whose obstruction budget stayed below one fixed constant `C`, nonsummability
would produce a prefix heavier than `C`, contradicting the delayed-prefix
upper bound. -/
theorem SummabilityCounterexample.false_of_uniform_delayed_scalePrimeSupportBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hbounded : ∀ m, N ≤ m →
      ∃ (K r : ℕ) (J : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ∧
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ≤ C) :
    False := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  let m := n - 1
  have hNm : N ≤ m := by omega
  rcases hbounded m hNm with
    ⟨K, r, J, hJ, hdelay, hobstruction, hbudget⟩
  have hupper :=
    hJ.prefixMass_le_rank_div_pow_add_scalePrimeSupport
      hN2 hdelay hobstruction
  have hprefix_m : C < dyadicPrefixReciprocalMass A N m := by
    simpa [m] using hprefix
  linarith

/-- Prior-witness version of the uniform delayed bound obstruction.  The
headroom may be certified by an earlier rank-`r` witness and then transferred
to the later LCM-minimal bad core by minimality. -/
theorem SummabilityCounterexample.false_of_uniform_prior_scalePrimeSupportBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hbounded : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        lcmRoomReciprocalMass A K J ≤
          (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ∧
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ≤ C) :
    False := by
  rcases exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N with ⟨n, hNn, hprefix⟩
  let m := n - 1
  have hNm : N ≤ m := by omega
  rcases hbounded m hNm with
    ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hobstruction, hbudget⟩
  have hupper :=
    hJ.prefixMass_le_rank_div_pow_add_scalePrimeSupport_of_prior
      hJ₀ hTK hN2 hdelay₀ hobstruction
  have hprefix_m : C < dyadicPrefixReciprocalMass A N m := by
    simpa [m] using hprefix
  linarith

/-- Uniform delayed room-cover budgets are impossible in a counterexample.
This is the set-cover version of `false_of_uniform_delayed_scalePrimeSupportBound`:
the cover itself supplies the scale-prime-support obstruction. -/
theorem SummabilityCounterexample.false_of_uniform_delayed_roomCoverBudgetBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hbounded : ∀ m, N ≤ m →
      ∃ (K r : ℕ) (J : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ≤ C) :
    False := by
  refine hA.false_of_uniform_delayed_scalePrimeSupportBound hN2 hC ?_
  intro m hm
  rcases hbounded m hm with ⟨K, r, J, hJ, hdelay, hcover, hbudget⟩
  exact ⟨K, r, J, hJ, hdelay,
    lcmRoomReciprocalMass_le_scalePrimeSupport_of_room_cover hcover,
    hbudget⟩

/-- Prior-witness version of the uniform room-cover budget obstruction.  A
persistent prior room-cover branch in a counterexample must make the combined
budget `r/2^N + K * Σ_{p | J} 1/p` escape every fixed bound. -/
theorem SummabilityCounterexample.false_of_uniform_prior_roomCoverBudgetBound
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {N : ℕ} (hN2 : 2 ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hbounded : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
            (K : ℝ) * corePrimeSupportPrimeReciprocalMass J ≤ C) :
    False := by
  refine hA.false_of_uniform_prior_scalePrimeSupportBound hN2 hC ?_
  intro m hm
  rcases hbounded m hm with
    ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hcover, hbudget⟩
  exact ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀,
    lcmRoomReciprocalMass_le_scalePrimeSupport_of_room_cover hcover,
    hbudget⟩

/-- No hypothetical counterexample has the concrete dyadic-log LCM-room
obstruction eventually.  This is the named `hno` condition for the current
positive route. -/
def NoLogRankLCMRoomPrimeSupportScaleObstruction : Prop :=
  ∀ A : Set ℕ, SummabilityCounterexample A → ∃ N,
    ∀ k s J, N ≤ k → s < k →
      CoprimeLCMSelection.LCMMinimal A k s J →
      ¬ lcmRoomReciprocalMass A k J ≤
        (k : ℝ) * corePrimeSupportPrimeReciprocalMass J

/-- Contradiction template for the positive route.  To prove the reciprocal-sum
part of Erdős problem #12, it is enough to rule out the concrete dyadic-log
obstruction in every hypothetical counterexample.

The proof is by contradiction: assume `A` is a counterexample.  The log-rank
obstruction theorem then produces arbitrarily late LCM-minimal cores with
`room mass ≤ k * prime-support reciprocal mass`, contradicting `hno`. -/
theorem erdos12Summability_of_no_logRank_lcmRoom_primeSupport_scale_obstruction
    (hno : NoLogRankLCMRoomPrimeSupportScaleObstruction) :
    Erdos12SummabilityQuestion := by
  intro A hAinf hApos hAavoid
  by_contra hnot
  have hcounter : SummabilityCounterexample A :=
    ⟨hAinf, hApos, hAavoid, hnot⟩
  rcases hno A hcounter with ⟨N, hN⟩
  rcases hcounter.exists_ge_logRank_lcmRoom_primeSupport_scale_obstruction N with
    ⟨k, s, J, hk, hs, hJ, hobstruction⟩
  exact (hN k s J hk hs hJ) hobstruction

/-- If the reciprocal-summability question is already known, then the named
`hno` obstruction condition holds vacuously because no summability
counterexample exists. -/
theorem no_logRank_lcmRoom_primeSupport_scale_obstruction_of_erdos12Summability
    (h : Erdos12SummabilityQuestion) :
    NoLogRankLCMRoomPrimeSupportScaleObstruction := by
  intro A hcounter
  exfalso
  exact hcounter.2.2.2
    (h A hcounter.1 hcounter.2.1 hcounter.2.2.1)

/-- The named `hno` condition is equivalent to the reciprocal-summability part
of Erdős problem #12.  Thus proving `hno` unconditionally is not a bookkeeping
step: it is precisely the remaining mathematical problem in the current
positive strategy. -/
theorem erdos12Summability_iff_no_logRank_lcmRoom_primeSupport_scale_obstruction :
    Erdos12SummabilityQuestion ↔
      NoLogRankLCMRoomPrimeSupportScaleObstruction := by
  constructor
  · exact no_logRank_lcmRoom_primeSupport_scale_obstruction_of_erdos12Summability
  · exact erdos12Summability_of_no_logRank_lcmRoom_primeSupport_scale_obstruction

end DivisibilityAvoidingSets
