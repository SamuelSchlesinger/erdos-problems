import Erdos.DivisibilityAvoidingSets.CoprimeSelection
import Erdos.DivisibilityAvoidingSets.ReciprocalCriteria

/-!
# Common-factor descent

The coprime-selection branch leaves a natural obstruction: many candidate
moduli may share large common factors.  This file records the first descent
move for that structured branch.  If we pass to a common-divisor layer and
divide by the common divisor, the forbidden divisibility pattern is preserved.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- Divide a set by a common factor: `n` is in the quotient if `d * n` was in
the original set. -/
def quotientSet (d : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | d * n ∈ A}

theorem mem_quotientSet {d n : ℕ} {A : Set ℕ} :
    n ∈ quotientSet d A ↔ d * n ∈ A := by
  rfl

/-- The part of `A` consisting of multiples of `d`. -/
def multipleLayer (d : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | n ∈ A ∧ d ∣ n}

theorem mem_multipleLayer {d n : ℕ} {A : Set ℕ} :
    n ∈ multipleLayer d A ↔ n ∈ A ∧ d ∣ n := by
  rfl

/-- The part of `A` consisting of elements not coprime to a fixed modulus. -/
def noncoprimeLayer (a : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | n ∈ A ∧ ¬ Nat.Coprime n a}

theorem mem_noncoprimeLayer {a n : ℕ} {A : Set ℕ} :
    n ∈ noncoprimeLayer a A ↔ n ∈ A ∧ ¬ Nat.Coprime n a := by
  rfl

/-- The shell charge counted outside a finite core and non-coprime to `a` is
bounded by the actual dyadic shell mass of the full non-coprime layer. -/
theorem dyadicShellNoncoreNoncoprimeMass_le_noncoprimeLayer
    (A : Set ℕ) (k : ℕ) (J : Finset ℕ) (a : ℕ) :
    dyadicShellNoncoreNoncoprimeMass A k J a ≤
      dyadicShellReciprocalMass (noncoprimeLayer a A) k := by
  unfold dyadicShellNoncoreNoncoprimeMass dyadicShellReciprocalMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
  · intro x hx
    have hx1 := (Finset.mem_filter.mp hx).1
    have hxnoncop := (Finset.mem_filter.mp hx).2
    have hxShell := (Finset.mem_filter.mp hx1).1
    have hxA_shell := mem_dyadicShellFinset.mp hxShell
    exact mem_dyadicShellFinset.mpr ⟨⟨hxA_shell.1, hxnoncop⟩, hxA_shell.2⟩
  · intro x _hxTarget _hxNotSource
    exact one_div_nonneg.mpr (Nat.cast_nonneg x)

/-- If a fixed non-coprime layer receives a nonsummable sequence of lower
bounds from shell charges, then that layer is itself nonsummable. -/
theorem not_reciprocalSummable_noncoprimeLayer_of_not_summable_charge_lower_bound
    {A : Set ℕ} (hApos : PositiveSet A) {a : ℕ}
    {J : ℕ → Finset ℕ} {c : ℕ → ℝ}
    (hc_nonneg : ∀ k, 0 ≤ c k) (hcnot : ¬ Summable c)
    (hlower : ∀ k, c k ≤ dyadicShellNoncoreNoncoprimeMass A k (J k) a) :
    ¬ ReciprocalSummable (noncoprimeLayer a A) := by
  have hLayerPos : PositiveSet (noncoprimeLayer a A) := by
    intro n hn
    exact hApos hn.1
  refine not_reciprocalSummable_of_not_summable_shell_lower_bound
    hLayerPos hc_nonneg hcnot ?_
  intro k
  exact (hlower k).trans
    (dyadicShellNoncoreNoncoprimeMass_le_noncoprimeLayer A k (J k) a)

/-- A concrete counterexample package for the still-open reciprocal-summability
part of Erdős problem #12. -/
def SummabilityCounterexample (A : Set ℕ) : Prop :=
  A.Infinite ∧ PositiveSet A ∧ AvoidingSet A ∧ ¬ ReciprocalSummable A

/-- The quotient by `d` is equivalent to the layer of multiples of `d`,
provided `d` is positive. -/
noncomputable def quotientEquivMultipleLayer (d : ℕ) (A : Set ℕ) (hd : 0 < d) :
    quotientSet d A ≃ multipleLayer d A where
  toFun q :=
    ⟨d * (q : ℕ), ⟨q.property, dvd_mul_right d (q : ℕ)⟩⟩
  invFun n :=
    ⟨(n : ℕ) / d, by
      rcases n.property with ⟨hnA, hdvd⟩
      change d * ((n : ℕ) / d) ∈ A
      rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]
      exact hnA⟩
  left_inv q := by
    apply Subtype.ext
    change d * (q : ℕ) / d = (q : ℕ)
    rw [Nat.mul_comm d (q : ℕ), Nat.mul_div_left _ hd]
  right_inv n := by
    apply Subtype.ext
    rcases n.property with ⟨_hnA, hdvd⟩
    change d * ((n : ℕ) / d) = (n : ℕ)
    rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]

/-- If every element of an infinite set is divisible by a positive `d`, then
the quotient by `d` is still infinite. -/
theorem quotientSet_infinite_of_forall_dvd
    {A : Set ℕ} (hAinf : A.Infinite) {d : ℕ} (_hd : 0 < d)
    (hdiv : ∀ ⦃n : ℕ⦄, n ∈ A → d ∣ n) :
    (quotientSet d A).Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have himage : ((fun n : ℕ => d * n) '' quotientSet d A).Finite :=
    hfin.image _
  have hsubset : A ⊆ (fun n : ℕ => d * n) '' quotientSet d A := by
    intro n hn
    rcases hdiv hn with ⟨q, hq⟩
    refine ⟨q, ?_, ?_⟩
    · change d * q ∈ A
      rwa [← hq]
    · exact hq.symm
  exact hAinf (himage.subset hsubset)

/-- Multiplying a forbidden triple by a positive common factor gives a forbidden
triple in the original set. -/
theorem ForbiddenTriple.mul_left {A : Set ℕ} {a b c d : ℕ}
    (hd : 0 < d) (h : ForbiddenTriple (quotientSet d A) a b c) :
    ForbiddenTriple A (d * a) (d * b) (d * c) := by
  rcases h with ⟨ha, hb, hc, hab, hac, hbc, hdvd, hablt, haclt⟩
  refine ⟨ha, hb, hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hda
    exact hab (mul_left_cancel₀ hd.ne' hda)
  · intro hda
    exact hac (mul_left_cancel₀ hd.ne' hda)
  · intro hdb
    exact hbc (mul_left_cancel₀ hd.ne' hdb)
  · rcases hdvd with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      d * b + d * c = d * (b + c) := by ring
      _ = d * (a * t) := by rw [ht]
      _ = d * a * t := by ring
  · exact (Nat.mul_lt_mul_left hd).mpr hablt
  · exact (Nat.mul_lt_mul_left hd).mpr haclt

/-- Avoidance descends through division by a positive common factor. -/
theorem AvoidingSet.quotientSet {A : Set ℕ} (hA : AvoidingSet A) {d : ℕ}
    (hd : 0 < d) :
    AvoidingSet (quotientSet d A) := by
  intro a b c h
  exact hA (h.mul_left hd)

/-- Positivity also descends through division by a positive common factor. -/
theorem PositiveSet.quotientSet {A : Set ℕ} (hpos : PositiveSet A) {d : ℕ} :
    PositiveSet (quotientSet d A) := by
  intro n hn
  by_contra hn0
  have hn_eq : n = 0 := Nat.eq_zero_of_not_pos hn0
  have hmem : 0 ∈ A := by
    simpa [hn_eq] using hn
  exact Nat.not_lt_zero 0 (hpos hmem)

theorem reciprocal_on_multipleLayer_comp_quotientEquiv
    {A : Set ℕ} (hpos : PositiveSet A) {d : ℕ} (hd : 0 < d)
    (q : quotientSet d A) :
    (1 : ℝ) /
        (((quotientEquivMultipleLayer d A hd q : multipleLayer d A) : ℕ) : ℝ) =
      (1 / (d : ℝ)) * ((1 : ℝ) / ((q : ℕ) : ℝ)) := by
  have hqpos : 0 < (q : ℕ) := hpos.quotientSet q.property
  have hd_ne : ((d : ℝ) ≠ 0) := by exact_mod_cast hd.ne'
  have hq_ne : ((((q : ℕ) : ℝ)) ≠ 0) := by exact_mod_cast hqpos.ne'
  change (1 : ℝ) / ((d * (q : ℕ) : ℕ) : ℝ) =
    (1 / (d : ℝ)) * ((1 : ℝ) / ((q : ℕ) : ℝ))
  rw [Nat.cast_mul]
  field_simp [hd_ne, hq_ne]

/-- If the quotient by a positive common divisor has convergent reciprocal sum,
then the corresponding multiple layer in the original set also has convergent
reciprocal sum. -/
theorem reciprocalSummable_multipleLayer_of_quotientSet
    {A : Set ℕ} (hpos : PositiveSet A) {d : ℕ} (hd : 0 < d)
    (hquot : ReciprocalSummable (quotientSet d A)) :
    ReciprocalSummable (multipleLayer d A) := by
  let e := quotientEquivMultipleLayer d A hd
  unfold ReciprocalSummable at hquot ⊢
  refine e.summable_iff.mp ?_
  have hscaled :
      Summable fun q : quotientSet d A =>
        (1 / (d : ℝ)) * ((1 : ℝ) / ((q : ℕ) : ℝ)) :=
    hquot.mul_left (1 / (d : ℝ))
  exact hscaled.congr fun q => by
    exact (reciprocal_on_multipleLayer_comp_quotientEquiv hpos hd q).symm

/-- If every member of `A` is divisible by a positive `d`, summability of the
quotient by `d` implies summability of `A`.  This is the direct analytic
payload of common-factor descent. -/
theorem reciprocalSummable_of_forall_dvd_of_quotientSet
    {A : Set ℕ} (hpos : PositiveSet A) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ ⦃n : ℕ⦄, n ∈ A → d ∣ n)
    (hquot : ReciprocalSummable (quotientSet d A)) :
    ReciprocalSummable A := by
  have hlayer : ReciprocalSummable (multipleLayer d A) :=
    reciprocalSummable_multipleLayer_of_quotientSet hpos hd hquot
  exact hlayer.mono fun n hn => ⟨hn, hdiv hn⟩

/-- Contrapositive form: a nonsummable set all of whose elements share a
positive divisor descends to a nonsummable quotient. -/
theorem not_reciprocalSummable_quotientSet_of_forall_dvd
    {A : Set ℕ} (hpos : PositiveSet A) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ ⦃n : ℕ⦄, n ∈ A → d ∣ n)
    (hnot : ¬ ReciprocalSummable A) :
    ¬ ReciprocalSummable (quotientSet d A) := by
  intro hquot
  exact hnot (reciprocalSummable_of_forall_dvd_of_quotientSet
    hpos hd hdiv hquot)

/-- If the layer of elements of `A` not coprime to a positive `a` is
nonsummable, then one nontrivial divisor of `a` supports a nonsummable multiple
layer of `A`.  This is the finite-cover step that turns a local common-factor
obstruction into an actual common-divisor descent candidate. -/
theorem exists_not_reciprocalSummable_multipleLayer_of_noncoprimeLayer
    {A : Set ℕ} {a : ℕ} (ha : 0 < a)
    (hnot : ¬ ReciprocalSummable (noncoprimeLayer a A)) :
    ∃ d : ℕ, d ∣ a ∧ 1 < d ∧ ¬ ReciprocalSummable (multipleLayer d A) := by
  classical
  let I : Finset ℕ := a.divisors.filter fun d => 1 < d
  let B : ℕ → Set ℕ := fun d => {n | d ∣ n}
  have hcover : noncoprimeLayer a A ⊆ ⋃ d ∈ I, B d := by
    intro n hn
    rcases Nat.Prime.not_coprime_iff_dvd.mp hn.2 with ⟨p, hp, hpn, hpa⟩
    have hpI : p ∈ I := by
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hpa, ha.ne'⟩, hp.one_lt⟩
    simp only [Set.mem_iUnion, B]
    exact ⟨p, ⟨hpI, hpn⟩⟩
  rcases DivisibilityAvoidingSets.exists_not_reciprocalSummable_inter_of_finite_cover
      hnot hcover with
    ⟨d, hdI, hdnot⟩
  have hddiv : d ∣ a := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdI).1
  have hdgt : 1 < d := (Finset.mem_filter.mp hdI).2
  have hsubset : noncoprimeLayer a A ∩ B d ⊆ multipleLayer d A := by
    intro n hn
    exact ⟨hn.1.1, hn.2⟩
  have hdnot_layer : ¬ ReciprocalSummable (multipleLayer d A) := by
    intro hs
    exact hdnot (hs.mono hsubset)
  exact ⟨d, hddiv, hdgt, hdnot_layer⟩

/-- A nonsummable multiple layer of a counterexample is itself a counterexample. -/
theorem SummabilityCounterexample.multipleLayer_of_not_reciprocalSummable
    {A : Set ℕ} (hA : SummabilityCounterexample A) {d : ℕ}
    (hnot : ¬ ReciprocalSummable (multipleLayer d A)) :
    SummabilityCounterexample (multipleLayer d A) := by
  rcases hA with ⟨_hAinf, hpos, havoid, _hnotA⟩
  exact ⟨DivisibilityAvoidingSets.infinite_of_not_reciprocalSummable hnot,
    PositiveSet.mono hpos fun n hn => hn.1,
    AvoidingSet.mono havoid fun n hn => hn.1,
    hnot⟩

/-- A full counterexample descends through any positive common divisor shared
by all its elements.  Thus a minimal nonsummable obstruction cannot live
entirely inside one nontrivial multiple layer. -/
theorem SummabilityCounterexample.quotientSet_of_forall_dvd
    {A : Set ℕ} (hA : SummabilityCounterexample A) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ ⦃n : ℕ⦄, n ∈ A → d ∣ n) :
    SummabilityCounterexample (quotientSet d A) := by
  rcases hA with ⟨hAinf, hpos, havoid, hnot⟩
  exact ⟨quotientSet_infinite_of_forall_dvd hAinf hd hdiv,
    hpos.quotientSet, havoid.quotientSet hd,
    not_reciprocalSummable_quotientSet_of_forall_dvd hpos hd hdiv hnot⟩

/-- If a counterexample has a nonsummable layer of elements not coprime to a
positive core element `a`, then some nontrivial divisor of `a` gives a
quotiented counterexample.  This packages the common-factor branch into the
exact descent form needed for a minimal-counterexample strategy. -/
theorem SummabilityCounterexample.quotient_of_not_reciprocalSummable_noncoprimeLayer
    {A : Set ℕ} (hA : SummabilityCounterexample A) {a : ℕ} (ha : 0 < a)
    (hnot : ¬ ReciprocalSummable (noncoprimeLayer a A)) :
    ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  rcases exists_not_reciprocalSummable_multipleLayer_of_noncoprimeLayer
      ha hnot with ⟨d, hda, hdgt, hdnot⟩
  have hdpos : 0 < d := Nat.lt_trans Nat.zero_lt_one hdgt
  have hLayer : SummabilityCounterexample (multipleLayer d A) :=
    hA.multipleLayer_of_not_reciprocalSummable hdnot
  have hdiv : ∀ ⦃n : ℕ⦄, n ∈ multipleLayer d A → d ∣ n :=
    fun _ hn => hn.2
  exact ⟨d, hda, hdgt,
    hLayer.quotientSet_of_forall_dvd hdpos hdiv⟩

/-- Quotient irreducibility forces every fixed non-coprime layer to have
convergent reciprocal sum.  Otherwise that layer supplies a nontrivial common
divisor and hence a quotient counterexample. -/
theorem SummabilityCounterexample.reciprocalSummable_noncoprimeLayer_of_quotient_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {a : ℕ} (ha : 0 < a) :
    ReciprocalSummable (noncoprimeLayer a A) := by
  by_contra hnot
  rcases hA.quotient_of_not_reciprocalSummable_noncoprimeLayer ha hnot with
    ⟨d, hda, hdgt, hdesc⟩
  exact hirred a d hda hdgt hdesc

/-- Under quotient irreducibility, finitely many fixed non-coprime layers
contribute only summably many reciprocals. -/
theorem SummabilityCounterexample.reciprocalSummable_finite_iUnion_noncoprimeLayer
    {A : Set ℕ} (hA : SummabilityCounterexample A) {C : Finset ℕ}
    (hCpos : ∀ a ∈ C, 0 < a)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ReciprocalSummable (⋃ a ∈ C, noncoprimeLayer a A) := by
  exact ReciprocalSummable.biUnion_finset fun a ha =>
    hA.reciprocalSummable_noncoprimeLayer_of_quotient_irreducible
      hirred (hCpos a ha)

/-- Greedy extension step for the irreducible branch.  After excluding all
elements sharing a factor with a fixed finite positive core `C`, the remaining
part of `A` is still nonsummable; in particular it contains arbitrarily large
elements coprime to every member of `C`. -/
theorem SummabilityCounterexample.exists_mem_ge_coprime_to_finset_of_quotient_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A) {C : Finset ℕ}
    (hCpos : ∀ a ∈ C, 0 < a)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (N : ℕ) :
    ∃ n, n ∈ A ∧ N ≤ n ∧ ∀ a ∈ C, Nat.Coprime n a := by
  classical
  let U : Set ℕ := ⋃ a ∈ C, noncoprimeLayer a A
  have hU : ReciprocalSummable U := by
    simpa [U] using
      hA.reciprocalSummable_finite_iUnion_noncoprimeLayer hCpos hirred
  have hdiff : ¬ ReciprocalSummable (A \ U) :=
    not_reciprocalSummable_diff_of_reciprocalSummable hA.2.2.2 hU
  rcases exists_mem_ge_of_not_reciprocalSummable hdiff N with
    ⟨n, hnDiff, hnN⟩
  refine ⟨n, hnDiff.1, hnN, ?_⟩
  intro a ha
  by_contra hnotcop
  exact hnDiff.2 (by
    simp only [U, Set.mem_iUnion]
    exact ⟨a, ha, ⟨hnDiff.1, hnotcop⟩⟩)

/-- In the quotient-irreducible branch, one can greedily build finite
pairwise-coprime cores of any prescribed rank.  The construction repeatedly
removes the finitely many summable non-coprime layers generated by the current
core and picks a new large element outside them. -/
theorem SummabilityCounterexample.exists_pairwise_coprime_finset_of_quotient_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (r N : ℕ) :
    ∃ J : Finset ℕ, J.card = r ∧
      (∀ a ∈ J, a ∈ A) ∧
      (∀ a ∈ J, N ≤ a) ∧
      (∀ a ∈ J, 4 ≤ a) ∧
      (J : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun a : ℕ => a) := by
  classical
  induction r with
  | zero =>
      refine ⟨∅, by simp, by simp, by simp, by simp, ?_⟩
      simp
  | succ r ih =>
      rcases ih with ⟨J, hJcard, hJA, hJN, hJlarge, hJcop⟩
      have hJpos : ∀ a ∈ J, 0 < a := by
        intro a ha
        exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4) (hJlarge a ha)
      rcases hA.exists_mem_ge_coprime_to_finset_of_quotient_irreducible
          hJpos hirred (max N 4) with
        ⟨x, hxA, hxge, hxcop⟩
      have hxN : N ≤ x := (le_max_left N 4).trans hxge
      have hxlarge : 4 ≤ x := (le_max_right N 4).trans hxge
      have hxnot : x ∉ J := by
        intro hxJ
        have hxx : Nat.Coprime x x := hxcop x hxJ
        have hxone : x = 1 := by
          simpa [Nat.Coprime] using hxx
        omega
      have hcop_symm :
          Symmetric (Function.onFun Nat.Coprime fun a : ℕ => a) := by
        intro a b hab
        exact hab.symm
      have hcop_insert :
          ((Insert.insert x J : Finset ℕ) : Set ℕ).Pairwise
            (Function.onFun Nat.Coprime fun a : ℕ => a) := by
        rw [Finset.coe_insert]
        exact hJcop.insert_of_symmetric hcop_symm fun a ha _hxa => hxcop a ha
      refine ⟨Insert.insert x J, ?_, ?_, ?_, ?_, hcop_insert⟩
      · simp [hxnot, hJcard]
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | haJ
        · exact hxA
        · exact hJA a haJ
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | haJ
        · exact hxN
        · exact hJN a haJ
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | haJ
        · exact hxlarge
        · exact hJlarge a haJ

/-- Arbitrary-rank coprime selections exist somewhere in the irreducible
branch.  After the greedy construction produces a finite pairwise-coprime core,
we move to a dyadic scale large enough for every selected element and for the
whole LCM to fit below `2 ^ K`. -/
theorem SummabilityCounterexample.exists_coprime_lcm_selection_of_rank_of_quotient_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (r N : ℕ) :
    ∃ K J, N ≤ K ∧ CoprimeLCMSelection A K r J := by
  classical
  rcases hA.exists_pairwise_coprime_finset_of_quotient_irreducible
      hirred r 4 with
    ⟨J, hJcard, hJA, _hJge4, hJlarge, hJcop⟩
  let K0 := J.lcm (fun a : ℕ => a) + (∑ a ∈ J, a) + 1
  let K := max N K0
  have hK0K : K0 ≤ K := le_max_right N K0
  have hpow_mono : 2 ^ K0 ≤ 2 ^ K :=
    Nat.pow_le_pow_right (by norm_num) hK0K
  have hK0_pow : K0 < 2 ^ K0 := K0.lt_two_pow_self
  have hK0_lt_powK : K0 < 2 ^ K := hK0_pow.trans_le hpow_mono
  have hLleK0 : J.lcm (fun a : ℕ => a) ≤ K0 := by
    dsimp [K0]
    omega
  have hLle : J.lcm (fun a : ℕ => a) ≤ 2 ^ K :=
    hLleK0.trans (Nat.le_of_lt hK0_lt_powK)
  have hlt : ∀ a ∈ J, a < 2 ^ K := by
    intro a ha
    have ha_sum : a ≤ ∑ x ∈ J, x :=
      Finset.single_le_sum (fun x _hx => Nat.zero_le x) ha
    have haK0 : a ≤ K0 := by
      dsimp [K0]
      omega
    exact lt_of_le_of_lt haK0 hK0_lt_powK
  refine ⟨K, J, le_max_left N K0, ?_⟩
  refine ⟨hJA, hlt, hLle, hJcop, hJlarge, ?_⟩
  omega

/-- Selection-failure corollary of the irreducible branch: no fixed coprime
rank can fail forever.  Equivalently, the maximal coprime-LCM selection rank is
cofinally unbounded along the dyadic scales. -/
theorem SummabilityCounterexample.exists_late_selection_not_failure_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (r N : ℕ) :
    ∃ K, N ≤ K ∧ ¬ CoprimeLCMSelectionFailure A K r := by
  rcases hA.exists_coprime_lcm_selection_of_rank_of_quotient_irreducible
      hirred r N with ⟨K, J, hNK, hJ⟩
  exact ⟨K, hNK, fun hfail => hfail J hJ⟩

/-- Strong fixed-rank form: in the quotient-irreducible branch, every fixed
rank succeeds at all sufficiently late dyadic scales.  The only remaining
question is the rate at which this eventual rank threshold grows with the
scale. -/
theorem SummabilityCounterexample.eventually_selection_of_rank_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (r N : ℕ) :
    ∃ K₀, N ≤ K₀ ∧ ∀ K, K₀ ≤ K → ∃ J, CoprimeLCMSelection A K r J := by
  rcases hA.exists_coprime_lcm_selection_of_rank_of_quotient_irreducible
      hirred r N with ⟨K₀, J, hNK₀, hJ⟩
  refine ⟨K₀, hNK₀, ?_⟩
  intro K hK
  exact ⟨J, CoprimeLCMSelection.scale_mono hJ hK⟩

/-- Failure form of the preceding theorem: no fixed rank-selection failure can
persist beyond some scale in a quotient-irreducible counterexample. -/
theorem SummabilityCounterexample.eventually_not_selection_failure_of_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    (r N : ℕ) :
    ∃ K₀, N ≤ K₀ ∧ ∀ K, K₀ ≤ K → ¬ CoprimeLCMSelectionFailure A K r := by
  rcases hA.eventually_selection_of_rank_of_irreducible hirred r N with
    ⟨K₀, hNK₀, hsel⟩
  refine ⟨K₀, hNK₀, ?_⟩
  intro K hK hfail
  rcases hsel K hK with ⟨J, hJ⟩
  exact hfail J hJ

/-- The exact slow-growth obstruction left by the positive strategy.  Let
`f` be any rank schedule strong enough that `2 * (3/4) ^ f k` is summable.  In
a quotient-irreducible counterexample, there are arbitrarily late scales where
rank `f k` fails; however every fixed rank succeeds eventually.  Hence those
failure scales must occur only where `f k` has already passed any prescribed
fixed rank `r`.

This is the present hard core of the argument: ruling out this escaping
schedule, for a logarithmic `f`, would close the positive side. -/
theorem SummabilityCounterexample.exists_ge_selection_failure_with_rank_gap
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (r N : ℕ) :
    ∃ k, N ≤ k ∧ r < f k ∧ CoprimeLCMSelectionFailure A k (f k) := by
  rcases hA.eventually_selection_of_rank_of_irreducible hirred r N with
    ⟨K₀, hNK₀, hsel_r⟩
  rcases hA.2.2.1.exists_ge_coprime_lcm_selection_failure_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hfSummable K₀ with
    ⟨k, hK₀k, hfail⟩
  have hNk : N ≤ k := hNK₀.trans hK₀k
  have hsel_at_k := hsel_r k hK₀k
  have hgap : r < f k := by
    by_contra hnot
    have hfr : f k ≤ r := not_lt.mp hnot
    rcases hsel_at_k with ⟨J, hJ⟩
    exact hfail J (hJ.rank_mono hfr)
  exact ⟨k, hNk, hgap, hfail⟩

/-- Threshold-sharp form of the slow-growth obstruction.  At the bad scale
`k`, not only does rank `f k` fail, but `k` must lie before every scale
threshold from which rank `f k` would succeed forever. -/
theorem SummabilityCounterexample.exists_ge_rank_gap_before_threshold
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (r N : ℕ) :
    ∃ k, N ≤ k ∧ r < f k ∧ CoprimeLCMSelectionFailure A k (f k) ∧
      ∀ T, (∀ K, T ≤ K → ∃ J, CoprimeLCMSelection A K (f k) J) → k < T := by
  rcases hA.exists_ge_selection_failure_with_rank_gap
      hirred hfSummable r N with
    ⟨k, hNk, hgap, hfail⟩
  refine ⟨k, hNk, hgap, hfail, ?_⟩
  intro T hT
  exact hfail.lt_eventual_selection_threshold hT

/-- Escaping-threshold form of the obstruction.  In an irreducible
counterexample, every summably strong schedule `f` has arbitrarily late scales
`k` such that rank `f k` does eventually succeed, but only after a strict
threshold `T > k`; at scale `k` itself rank `f k` still fails. -/
theorem SummabilityCounterexample.exists_ge_escaping_selection_threshold
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (r N : ℕ) :
    ∃ k T, N ≤ k ∧ k < T ∧ r < f k ∧
      CoprimeLCMSelectionFailure A k (f k) ∧
      (∀ K, T ≤ K → ∃ J, CoprimeLCMSelection A K (f k) J) := by
  rcases hA.exists_ge_selection_failure_with_rank_gap
      hirred hfSummable r N with
    ⟨k, hNk, hgap, hfail⟩
  rcases hA.eventually_selection_of_rank_of_irreducible
      hirred (f k) k with
    ⟨T, _hkT, hT⟩
  have hkT : k < T := hfail.lt_eventual_selection_threshold hT
  exact ⟨k, T, hNk, hkT, hgap, hfail, hT⟩

/-- A self-bounded eventual rank threshold rules out counterexamples.  If one
can find a summably strong schedule `f` such that, for all sufficiently large
`k`, the eventual-success threshold for rank `f k` is already at most `k`,
then the dyadic packing criterion proves reciprocal summability, contradicting
`SummabilityCounterexample`.

This is the exact quantitative lemma needed to kill the slow-rank branch. -/
theorem SummabilityCounterexample.false_of_self_bounded_selection_threshold
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    {N : ℕ}
    (hthreshold : ∀ k, N ≤ k → ∃ T, T ≤ k ∧
      ∀ K, T ≤ K → ∃ J, CoprimeLCMSelection A K (f k) J) :
    False := by
  have hsel : ∀ k, N ≤ k → ∃ J, CoprimeLCMSelection A k (f k) J := by
    intro k hk
    rcases hthreshold k hk with ⟨T, hTk, hT⟩
    exact hT k hTk
  exact hA.2.2.2
    (hA.2.2.1.reciprocalSummable_of_eventually_exists_coprime_lcm_selection
      hA.2.1 hfSummable hsel)

/-- Current frontier dichotomy for the positive strategy.  For any summably
strong rank schedule `f`, either the counterexample already admits quotient
descent through a nontrivial common divisor, or the remaining obstruction is a
slow-rank phenomenon: arbitrarily late failures of rank `f k`, and those
failures occur only after `f k` has passed any prescribed fixed rank.

Closing the conjecture in the positive direction is now reduced to ruling out
this second alternative for one concrete summably strong schedule, such as a
sufficiently large logarithmic rank target. -/
theorem SummabilityCounterexample.quotient_descent_or_rank_gap_obstruction
    {A : Set ℕ} (hA : SummabilityCounterexample A) {f : ℕ → ℕ}
    (hfSummable : Summable fun k => 2 * ((3 / 4 : ℝ) ^ f k))
    (r N : ℕ) :
    (∃ a d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A))) ∨
      ∃ k, N ≤ k ∧ r < f k ∧ CoprimeLCMSelectionFailure A k (f k) := by
  classical
  by_cases hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))
  · exact Or.inr
      (hA.exists_ge_selection_failure_with_rank_gap hirred hfSummable r N)
  · push Not at hirred
    rcases hirred with ⟨a, d, hda, hdgt, hdesc⟩
    exact Or.inl ⟨a, d, hda, hdgt, hdesc⟩

/-- Shell-charge version of the common-factor descent trigger.  If a fixed
core element `a` receives a nonsummable sequence of lower bounds through the
non-coprime shell charges, then a nontrivial divisor of `a` yields a quotient
counterexample. -/
theorem SummabilityCounterexample.quotient_of_not_summable_charge_lower_bound
    {A : Set ℕ} (hA : SummabilityCounterexample A) {a : ℕ} (ha : 0 < a)
    {J : ℕ → Finset ℕ} {c : ℕ → ℝ}
    (hc_nonneg : ∀ k, 0 ≤ c k) (hcnot : ¬ Summable c)
    (hlower : ∀ k, c k ≤ dyadicShellNoncoreNoncoprimeMass A k (J k) a) :
    ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  have hnotLayer :
      ¬ ReciprocalSummable (noncoprimeLayer a A) :=
    not_reciprocalSummable_noncoprimeLayer_of_not_summable_charge_lower_bound
      hA.2.1 hc_nonneg hcnot hlower
  exact hA.quotient_of_not_reciprocalSummable_noncoprimeLayer ha hnotLayer

/-- If a nonsummable subset of `A` is covered by finitely many non-coprime
layers, then one core element has a nonsummable non-coprime layer in `A`. -/
theorem exists_not_reciprocalSummable_noncoprimeLayer_of_finite_core_cover
    {A S : Set ℕ} {J : Finset ℕ}
    (hSnot : ¬ ReciprocalSummable S)
    (hSsubA : S ⊆ A)
    (hcover : S ⊆ ⋃ a ∈ J, {n | ¬ Nat.Coprime n a}) :
    ∃ a ∈ J, ¬ ReciprocalSummable (noncoprimeLayer a A) := by
  let B : ℕ → Set ℕ := fun a => {n | ¬ Nat.Coprime n a}
  have hcoverB : S ⊆ ⋃ a ∈ J, B a := hcover
  rcases DivisibilityAvoidingSets.exists_not_reciprocalSummable_inter_of_finite_cover
      hSnot hcoverB with ⟨a, haJ, hanot⟩
  refine ⟨a, haJ, ?_⟩
  intro hlayer
  exact hanot (hlayer.mono fun n hn => ⟨hSsubA hn.1, hn.2⟩)

/-- A finite core cover by non-coprime alternatives forces quotient descent
from any counterexample, provided the core elements are positive. -/
theorem SummabilityCounterexample.quotient_of_finite_core_noncoprime_cover
    {A S : Set ℕ} (hA : SummabilityCounterexample A) {J : Finset ℕ}
    (hSnot : ¬ ReciprocalSummable S)
    (hSsubA : S ⊆ A)
    (hcover : S ⊆ ⋃ a ∈ J, {n | ¬ Nat.Coprime n a})
    (hJpos : ∀ a ∈ J, 0 < a) :
    ∃ a ∈ J, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  rcases exists_not_reciprocalSummable_noncoprimeLayer_of_finite_core_cover
      hSnot hSsubA hcover with ⟨a, haJ, hanot⟩
  rcases hA.quotient_of_not_reciprocalSummable_noncoprimeLayer
      (hJpos a haJ) hanot with ⟨d, hda, hdgt, hdesc⟩
  exact ⟨a, haJ, d, hda, hdgt, hdesc⟩

/-- Eventual finite-core cover descent.  If, outside finitely many initial
values and outside the core itself, all elements of a counterexample share a
factor with one of the finitely many core elements, then the counterexample
descends through a nontrivial divisor of one core element.

This is the bounded-core branch of the combinatorial attack: a stable maximal
core cannot be the final obstruction unless it yields quotient descent. -/
theorem SummabilityCounterexample.quotient_of_eventual_finite_core_noncoprime_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A) {J : Finset ℕ} {N : ℕ}
    (hcover : ((A ∩ Set.Ici N) \ (J : Set ℕ)) ⊆
      ⋃ a ∈ J, {n | ¬ Nat.Coprime n a})
    (hJpos : ∀ a ∈ J, 0 < a) :
    ∃ a ∈ J, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  have htail_not : ¬ ReciprocalSummable (A ∩ Set.Ici N) :=
    not_reciprocalSummable_inter_Ici hA.2.2.2 N
  have hSnot : ¬ ReciprocalSummable ((A ∩ Set.Ici N) \ (J : Set ℕ)) :=
    not_reciprocalSummable_diff_finset (A := A ∩ Set.Ici N) (F := J) htail_not
  have hSsubA : ((A ∩ Set.Ici N) \ (J : Set ℕ)) ⊆ A := by
    intro n hn
    exact hn.1.1
  exact hA.quotient_of_finite_core_noncoprime_cover hSnot hSsubA hcover hJpos

/-- Shell-cover form of eventual finite-core descent.  If every dyadic shell
from index `N` onward, after removing the fixed core, is covered by the
non-coprime alternatives from that core, then the counterexample descends. -/
theorem SummabilityCounterexample.quotient_of_eventual_dyadic_shell_core_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A) {J : Finset ℕ} {N : ℕ}
    (hcoverShell : ∀ k, N ≤ k →
      (((dyadicShellFinset A k).filter (fun x => x ∉ J) : Set ℕ) ⊆
        ⋃ a ∈ J, {n | ¬ Nat.Coprime n a}))
    (hJpos : ∀ a ∈ J, 0 < a) :
    ∃ a ∈ J, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  refine hA.quotient_of_eventual_finite_core_noncoprime_cover
    (N := 2 ^ N) ?_ hJpos
  intro x hx
  rcases exists_ge_mem_dyadicShellFinset_of_mem_Ici_pow
      hA.2.1 hx.1.1 hx.1.2 with ⟨k, hNk, hxShell⟩
  exact hcoverShell k hNk (Finset.mem_filter.mpr ⟨hxShell, hx.2⟩)

/-- Prime-cover form of eventual dyadic-shell descent.  If every late shell,
after removing the finitely many primes in `P` themselves, is covered by
divisibility by primes in `P`, then a quotient descent occurs through a
nontrivial divisor of one of those primes. -/
theorem SummabilityCounterexample.quotient_of_eventual_dyadic_shell_prime_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A) {P : Finset ℕ} {N : ℕ}
    (hcoverShell : ∀ k, N ≤ k →
      (((dyadicShellFinset A k).filter (fun x => x ∉ P) : Set ℕ) ⊆
        ⋃ p ∈ P, {n | p ∣ n}))
    (hPprime : ∀ p ∈ P, Nat.Prime p) :
    ∃ p ∈ P, ∃ d : ℕ, d ∣ p ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  have hPpos : ∀ p ∈ P, 0 < p := by
    intro p hp
    exact (hPprime p hp).pos
  refine hA.quotient_of_eventual_dyadic_shell_core_cover
    (J := P) (N := N) ?_ hPpos
  intro k hk x hx
  have hxCover := hcoverShell k hk hx
  simp only [Set.mem_iUnion] at hxCover ⊢
  rcases hxCover with ⟨p, hpP, hpx⟩
  exact ⟨p, hpP,
    Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hPprime p hpP, hpx, dvd_rfl⟩⟩

/-- Moving finite-universe shell-cover descent.  If every late shell is covered
by a possibly-moving core, and all those cores are contained in one fixed finite
positive universe `C`, then the counterexample descends through a nontrivial
divisor of an element of `C`.

Thus a non-descending counterexample cannot have all of its delayed cores drawn
from a bounded finite reservoir; genuinely new core elements must keep entering
the picture. -/
theorem SummabilityCounterexample.quotient_of_eventual_dyadic_shell_moving_core_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A) {C : Finset ℕ}
    {J : ℕ → Finset ℕ} {N : ℕ}
    (hJsub : ∀ k, N ≤ k → J k ⊆ C)
    (hcoverShell : ∀ k, N ≤ k →
      (((dyadicShellFinset A k).filter (fun x => x ∉ J k) : Set ℕ) ⊆
        ⋃ a ∈ J k, {n | ¬ Nat.Coprime n a}))
    (hCpos : ∀ a ∈ C, 0 < a) :
    ∃ a ∈ C, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  refine hA.quotient_of_eventual_finite_core_noncoprime_cover
    (J := C) (N := 2 ^ N) ?_ hCpos
  intro x hx
  rcases exists_ge_mem_dyadicShellFinset_of_mem_Ici_pow
      hA.2.1 hx.1.1 hx.1.2 with ⟨k, hNk, hxShell⟩
  have hxnotJ : x ∉ J k := by
    intro hxJ
    exact hx.2 (hJsub k hNk hxJ)
  have hxCovered := hcoverShell k hNk (Finset.mem_filter.mpr ⟨hxShell, hxnotJ⟩)
  simp only [Set.mem_iUnion] at hxCovered ⊢
  rcases hxCovered with ⟨a, haJ, hxa⟩
  exact ⟨a, hJsub k hNk haJ, hxa⟩

/-- Fixed-core delayed-failure descent.  Suppose one finite core `J` remains a
valid rank-`r` core along a cofinal schedule of later scales, every next-rank
extension fails there, and the later LCM budget sees each earlier shell.  Then
the bounded/stable-core obstruction forces quotient descent.

This is the first genuine combinatorial branch: bounded coprime content cannot
survive as an irreducible counterexample. -/
theorem SummabilityCounterexample.quotient_of_fixed_core_delayed_failures
    {A : Set ℕ} (hA : SummabilityCounterexample A) {J : Finset ℕ}
    {r N : ℕ} {K : ℕ → ℕ}
    (hN2 : 2 ≤ N)
    (hJ : ∀ k, N ≤ k → CoprimeLCMSelection A (K k) r J)
    (hfail : ∀ k, N ≤ k → CoprimeLCMSelectionFailure A (K k) (r + 1))
    (hdelay : ∀ k, N ≤ k →
      J.lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k)) :
    ∃ a ∈ J, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4)
      ((hJ N le_rfl).2.2.2.2.1 a ha)
  refine hA.quotient_of_eventual_dyadic_shell_core_cover
    (N := N) ?_ hJpos
  intro k hk
  exact (hfail k hk).noncoprime_core_cover_of_delayed_shell
    (hJ k hk) (hN2.trans hk) (hdelay k hk)

/-- Moving finite-universe delayed-failure descent.  Suppose the delayed cores
may vary with the shell, but all lie inside a fixed finite positive universe
`C`.  If every delayed scale fails to extend the corresponding core and has
enough LCM budget to see its shell, then the counterexample descends through
an element of `C`.

This is the flexible bounded-core branch: without quotient descent, the
sequence of successful cores cannot remain inside any fixed finite universe. -/
theorem SummabilityCounterexample.quotient_of_moving_finite_universe_delayed_failures
    {A : Set ℕ} (hA : SummabilityCounterexample A) {C : Finset ℕ}
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hJsub : ∀ k, N ≤ k → J k ⊆ C)
    (hJ : ∀ k, N ≤ k → CoprimeLCMSelection A (K k) (r k) (J k))
    (hfail : ∀ k, N ≤ k → CoprimeLCMSelectionFailure A (K k) (r k + 1))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hCpos : ∀ a ∈ C, 0 < a) :
    ∃ a ∈ C, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  refine hA.quotient_of_eventual_dyadic_shell_moving_core_cover
    (C := C) (J := J) (N := N) hJsub ?_ hCpos
  intro k hk
  exact (hfail k hk).noncoprime_core_cover_of_delayed_shell
    (hJ k hk) (hN2.trans hk) (hdelay k hk)

/-- Moving finite-universe LCM-room-cover descent.  Suppose each late dyadic
shell is visible inside the LCM-room of a possibly moving later core, and that
room is covered by the core's non-coprime alternatives.  If all core elements
come from one fixed finite positive universe, then the counterexample descends
through a nontrivial divisor of an element of that universe.

This separates the descent mechanism from the reason the room-cover holds:
it can come from maximal-rank failure, frugal minimal-core failure, or any
other local obstruction. -/
theorem SummabilityCounterexample.quotient_of_moving_finite_universe_lcm_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A) {C : Finset ℕ}
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hJsub : ∀ k, N ≤ k → J k ⊆ C)
    (hJ : ∀ k, N ≤ k → CoprimeLCMSelection A (K k) (r k) (J k))
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ a ∈ J k, {x | ¬ Nat.Coprime x a}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hCpos : ∀ a ∈ C, 0 < a) :
    ∃ a ∈ C, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  refine hA.quotient_of_eventual_dyadic_shell_moving_core_cover
    (C := C) (J := J) (N := N) hJsub ?_ hCpos
  intro k hk x hx
  have hxShell : x ∈ dyadicShellFinset A k := (Finset.mem_filter.mp hx).1
  have hxnot : x ∉ J k := (Finset.mem_filter.mp hx).2
  have hxRoom :=
    mem_lcmRoomFinset_of_mem_dyadicShellFinset
      (hJ k hk) (hN2.trans hk) hxShell hxnot (hdelay k hk)
  exact hcoverRoom k hk hxRoom

/-- Moving finite-prime-universe LCM-room-cover descent.  Suppose every late
LCM-room is covered by divisibility by primes from one fixed finite set `P`,
and every element of each moving core is also divisible by some prime in `P`.
If the LCM-room sees every late shell, then quotient descent follows through
one of the primes in `P`.

This is stronger than bounded-core descent: the core values may grow without
bound, but reusing only finitely many prime factors is still fatal in an
irreducible counterexample. -/
theorem SummabilityCounterexample.quotient_of_moving_finite_prime_universe_lcm_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A) {P : Finset ℕ}
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hJ : ∀ k, N ≤ k → CoprimeLCMSelection A (K k) (r k) (J k))
    (hJprimeCover : ∀ k, N ≤ k → ∀ x ∈ J k, ∃ p ∈ P, p ∣ x)
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ p ∈ P, {x | p ∣ x}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k)) :
    ∃ p ∈ P, ∃ d : ℕ, d ∣ p ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  refine hA.quotient_of_eventual_dyadic_shell_prime_cover
    (P := P) (N := N) ?_ hPprime
  intro k hk x hx
  have hxShell : x ∈ dyadicShellFinset A k := (Finset.mem_filter.mp hx).1
  by_cases hxJ : x ∈ J k
  · simp only [Set.mem_iUnion]
    rcases hJprimeCover k hk x hxJ with ⟨p, hpP, hpx⟩
    exact ⟨p, hpP, hpx⟩
  · have hxRoom :=
      mem_lcmRoomFinset_of_mem_dyadicShellFinset
        (hJ k hk) (hN2.trans hk) hxShell hxJ (hdelay k hk)
    exact hcoverRoom k hk hxRoom

/-- Bounded moving-core delayed-failure descent.  If all delayed core elements
are bounded by one number `M`, the preceding finite-universe theorem applies
with the finite interval `[1, M]`.

Consequently, an irreducible counterexample must force the values appearing in
the delayed cores to become arbitrarily large. -/
theorem SummabilityCounterexample.quotient_of_bounded_moving_core_delayed_failures
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {M N : ℕ}
    (hN2 : 2 ≤ N)
    (hJ : ∀ k, N ≤ k → CoprimeLCMSelection A (K k) (r k) (J k))
    (hfail : ∀ k, N ≤ k → CoprimeLCMSelectionFailure A (K k) (r k + 1))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hbound : ∀ k, N ≤ k → ∀ a ∈ J k, a ≤ M) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ M ∧ ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  have hJsub : ∀ k, N ≤ k → J k ⊆ Finset.Icc 1 M := by
    intro k hk a ha
    have ha4 : 4 ≤ a := (hJ k hk).2.2.2.2.1 a ha
    exact Finset.mem_Icc.mpr ⟨by omega, hbound k hk a ha⟩
  have hCpos : ∀ a ∈ Finset.Icc 1 M, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1
  rcases hA.quotient_of_moving_finite_universe_delayed_failures
      (C := Finset.Icc 1 M) (J := J) (r := r) (K := K) (N := N)
      hN2 hJsub hJ hfail hdelay hCpos with
    ⟨a, haC, d, hda, hdgt, hdesc⟩
  rcases Finset.mem_Icc.mp haC with ⟨ha1, haM⟩
  exact ⟨a, ha1, haM, d, hda, hdgt, hdesc⟩

/-- Bounded moving-core LCM-room-cover descent.  If all room-cover core
elements are bounded by one number `M`, the finite-universe room-cover theorem
applies with the finite interval `[1, M]`. -/
theorem SummabilityCounterexample.quotient_of_bounded_moving_core_lcm_room_covers
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {M N : ℕ}
    (hN2 : 2 ≤ N)
    (hJ : ∀ k, N ≤ k → CoprimeLCMSelection A (K k) (r k) (J k))
    (hcoverRoom : ∀ k, N ≤ k →
      (((lcmRoomFinset A (K k) (J k) : Finset ℕ) : Set ℕ) ⊆
        ⋃ a ∈ J k, {x | ¬ Nat.Coprime x a}))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hbound : ∀ k, N ≤ k → ∀ a ∈ J k, a ≤ M) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ M ∧ ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  have hJsub : ∀ k, N ≤ k → J k ⊆ Finset.Icc 1 M := by
    intro k hk a ha
    have ha4 : 4 ≤ a := (hJ k hk).2.2.2.2.1 a ha
    exact Finset.mem_Icc.mpr ⟨by omega, hbound k hk a ha⟩
  have hCpos : ∀ a ∈ Finset.Icc 1 M, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1
  rcases hA.quotient_of_moving_finite_universe_lcm_room_covers
      (C := Finset.Icc 1 M) (J := J) (r := r) (K := K) (N := N)
      hN2 hJsub hJ hcoverRoom hdelay hCpos with
    ⟨a, haC, d, hda, hdgt, hdesc⟩
  rcases Finset.mem_Icc.mp haC with ⟨ha1, haM⟩
  exact ⟨a, ha1, haM, d, hda, hdgt, hdesc⟩

/-- Contrapositive bounded-core form.  If the delayed-failure hypotheses hold
but no quotient descent is available through any core value at most `M`, then
some late delayed core contains an element larger than `M`.

This turns the bounded-core branch into a clean growth obligation for the
remaining positive attack. -/
theorem SummabilityCounterexample.exists_large_core_of_no_bounded_descent
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {M N : ℕ}
    (hN2 : 2 ≤ N)
    (hJ : ∀ k, N ≤ k → CoprimeLCMSelection A (K k) (r k) (J k))
    (hfail : ∀ k, N ≤ k → CoprimeLCMSelectionFailure A (K k) (r k + 1))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hnoDescent : ¬ ∃ a : ℕ, 1 ≤ a ∧ a ≤ M ∧ ∃ d : ℕ,
      d ∣ a ∧ 1 < d ∧
        SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∃ k, N ≤ k ∧ ∃ a ∈ J k, M < a := by
  by_contra hlarge
  have hbound : ∀ k, N ≤ k → ∀ a ∈ J k, a ≤ M := by
    intro k hk a ha
    by_contra hle
    exact hlarge ⟨k, hk, ⟨a, ha, lt_of_not_ge hle⟩⟩
  exact hnoDescent
    (hA.quotient_of_bounded_moving_core_delayed_failures
      hN2 hJ hfail hdelay hbound)

/-- Globally irreducible form of the bounded-core fork.  If no quotient descent
through any nontrivial divisor is available, then the delayed cores are
unbounded in value: every numerical bound is exceeded by some late core
element. -/
theorem SummabilityCounterexample.forall_exists_large_core_of_quotient_irreducible
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    {J : ℕ → Finset ℕ} {r K : ℕ → ℕ} {N : ℕ}
    (hN2 : 2 ≤ N)
    (hJ : ∀ k, N ≤ k → CoprimeLCMSelection A (K k) (r k) (J k))
    (hfail : ∀ k, N ≤ k → CoprimeLCMSelectionFailure A (K k) (r k + 1))
    (hdelay : ∀ k, N ≤ k →
      (J k).lcm (fun a : ℕ => a) * 2 ^ (k + 1) ≤ 2 ^ (K k))
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A))) :
    ∀ M, ∃ k, N ≤ k ∧ ∃ a ∈ J k, M < a := by
  intro M
  refine hA.exists_large_core_of_no_bounded_descent hN2 hJ hfail hdelay ?_
  intro hdesc
  rcases hdesc with ⟨a, _ha1, _haM, d, hda, hdgt, hcounter⟩
  exact hirred a d hda hdgt hcounter

/-- The composed obstruction-to-descent step.  If a failed coprime-selection
step has a nonsummable family of admissible elements still inside the remaining
LCM budget, then the counterexample descends through a nontrivial divisor of
one element of the finite core.

This is the current theorem-shaped hard target: to close the positive argument,
it remains to produce such an `S` whenever the coprime-selection branch fails
often enough. -/
theorem SummabilityCounterexample.quotient_of_selection_failure_lcm_room_subset
    {A S : Set ℕ} (hA : SummabilityCounterexample A) {k r : ℕ} {J : Finset ℕ}
    (hfail : CoprimeLCMSelectionFailure A k (r + 1))
    (hJ : CoprimeLCMSelection A k r J)
    (hSnot : ¬ ReciprocalSummable S)
    (hS : ∀ ⦃x : ℕ⦄, x ∈ S →
      x ∈ A ∧ x < 2 ^ k ∧ 4 ≤ x ∧ x ∉ J ∧
        J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k) :
    ∃ a ∈ J, ∃ d : ℕ, d ∣ a ∧ 1 < d ∧
      SummabilityCounterexample (quotientSet d (multipleLayer d A)) := by
  have hSsubA : S ⊆ A := by
    intro x hx
    exact (hS hx).1
  have hcover : S ⊆ ⋃ a ∈ J, {x | ¬ Nat.Coprime x a} :=
    hfail.noncoprime_core_cover_of_lcm_room hJ hS
  have hJpos : ∀ a ∈ J, 0 < a := by
    intro a ha
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4) (hJ.2.2.2.2.1 a ha)
  exact hA.quotient_of_finite_core_noncoprime_cover hSnot hSsubA hcover hJpos

/-- At a fixed dyadic scale the LCM-room family is bounded, hence automatically
reciprocal-summable.  Therefore the previous theorem is only useful as a local
finite-mass reduction; a global descent argument has to aggregate such room
across infinitely many scales or force a recurring core/divisor. -/
theorem reciprocalSummable_of_fixed_scale_lcm_room_subset
    {A S : Set ℕ} {k : ℕ} {J : Finset ℕ}
    (hS : ∀ ⦃x : ℕ⦄, x ∈ S →
      x ∈ A ∧ x < 2 ^ k ∧ 4 ≤ x ∧ x ∉ J ∧
        J.lcm (fun a : ℕ => a) * x ≤ 2 ^ k) :
    ReciprocalSummable S := by
  exact reciprocalSummable_of_subset_Iio (N := 2 ^ k) fun x hx => (hS hx).2.1

end DivisibilityAvoidingSets
