import Erdos.DivisibilityAvoidingSets.TailResidues

/-!
# Residue packing for the reciprocal-sum attack

The tail obstruction modulo a fixed element `a` says that used residue classes
cannot contain two distinct complementary classes.  Folding each residue `r`
to `min r (a - r)` gives an injection from the used residue classes into
`{0, ..., a / 2}`.

This is a small finite form of the local packing constraint behind any
larger-sieve approach to the still-open reciprocal-sum part of Erdős problem
`#12`.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- Fold a residue together with its negative modulo `a`. -/
def foldedResidue (a r : ℕ) : ℕ :=
  min r (a - r)

/-- The folded representative lies in `{0, ..., a / 2}`. -/
theorem foldedResidue_lt_succ_half {a r : ℕ} (hr : r < a) :
    foldedResidue a r < a / 2 + 1 := by
  unfold foldedResidue
  by_cases h : r ≤ a / 2
  · exact lt_of_le_of_lt (min_le_left _ _) (Nat.lt_succ_of_le h)
  · have hle : a - r ≤ a / 2 := by omega
    exact lt_of_le_of_lt (min_le_right _ _) (Nat.lt_succ_of_le hle)

/-- If two residues below `a` have the same fold, then they are equal or
complementary. -/
theorem foldedResidue_eq_iff_eq_or_add_eq {a r s : ℕ}
    (hr : r < a) (hs : s < a)
    (hfold : foldedResidue a r = foldedResidue a s) :
    r = s ∨ r + s = a := by
  unfold foldedResidue at hfold
  by_cases hrle : r ≤ a - r
  · by_cases hsle : s ≤ a - s
    · left
      rwa [min_eq_left hrle, min_eq_left hsle] at hfold
    · right
      rw [min_eq_left hrle, min_eq_right (le_of_not_ge hsle)] at hfold
      omega
  · by_cases hsle : s ≤ a - s
    · right
      rw [min_eq_right (le_of_not_ge hrle), min_eq_left hsle] at hfold
      omega
    · left
      rw [min_eq_right (le_of_not_ge hrle), min_eq_right (le_of_not_ge hsle)] at hfold
      omega

/-- The residue classes modulo `a` represented by a set `B`, as ordinary
natural residues in `[0, a)`. -/
noncomputable def residueFinset (a : ℕ) (B : Set ℕ) : Finset ℕ := by
  classical
  exact (Finset.range a).filter fun r => ∃ b ∈ B, b % a = r

theorem mem_residueFinset {a : ℕ} {B : Set ℕ} {r : ℕ} :
    r ∈ residueFinset a B ↔ r < a ∧ ∃ b ∈ B, b % a = r := by
  classical
  unfold residueFinset
  simp

/-- A set with no complementary residue pairs uses at most one class from each
two-element complementary pair, together with the fixed classes `0` and
possibly `a / 2`. -/
theorem residueFinset_card_le_of_pairwiseNoZeroResidueSum {a : ℕ} {B : Set ℕ}
    (hB : PairwiseNoZeroResidueSum a B) :
    (residueFinset a B).card ≤ a / 2 + 1 := by
  classical
  let R := residueFinset a B
  have hinj :
      ∀ x ∈ R, ∀ y ∈ R, foldedResidue a x = foldedResidue a y → x = y := by
    intro r hr s hs hfold
    have hr' : r < a ∧ ∃ b ∈ B, b % a = r := by
      simpa [R] using (mem_residueFinset.mp hr)
    have hs' : s < a ∧ ∃ c ∈ B, c % a = s := by
      simpa [R] using (mem_residueFinset.mp hs)
    rcases foldedResidue_eq_iff_eq_or_add_eq hr'.1 hs'.1 hfold with hrs | hrs
    · exact hrs
    · rcases hr'.2 with ⟨b, hbB, hbr⟩
      rcases hs'.2 with ⟨c, hcB, hcs⟩
      have hres : (b % a + c % a) % a = 0 := by
        rw [hbr, hcs, hrs]
        exact Nat.mod_self a
      have hbc : b = c :=
        PairwiseNoZeroResidueSum.eq_of_zero_residue_sum hB hbB hcB hres
      calc
        r = b % a := hbr.symm
        _ = c % a := by rw [hbc]
        _ = s := hcs
  have hcard_image : (R.image (foldedResidue a)).card = R.card := by
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    exact hinj x hx y hy hxy
  have hsub : R.image (foldedResidue a) ⊆ Finset.range (a / 2 + 1) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨s, hs, rfl⟩
    rw [Finset.mem_range]
    exact foldedResidue_lt_succ_half (mem_residueFinset.mp hs).1
  calc
    R.card = (R.image (foldedResidue a)).card := hcard_image.symm
    _ ≤ (Finset.range (a / 2 + 1)).card := Finset.card_le_card hsub
    _ = a / 2 + 1 := Finset.card_range _

/-- If a finite set injects into its residue classes modulo `a`, the local
tail obstruction gives the same half-modulus bound for the set itself. -/
theorem finset_card_le_of_pairwiseNoZeroResidueSum_of_inj_mod {a : ℕ}
    {B : Set ℕ} {F : Finset ℕ}
    (ha : 0 < a)
    (hB : PairwiseNoZeroResidueSum a B)
    (hF : ∀ n ∈ F, n ∈ B)
    (hinj : ∀ ⦃m n : ℕ⦄, m ∈ F → n ∈ F → m % a = n % a → m = n) :
    F.card ≤ a / 2 + 1 := by
  classical
  have hcard_image : (F.image fun n => n % a).card = F.card := by
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    exact hinj hx hy hxy
  have hsub : F.image (fun n => n % a) ⊆ residueFinset a B := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨n, hnF, rfl⟩
    rw [mem_residueFinset]
    exact ⟨Nat.mod_lt n ha, n, hF n hnF, rfl⟩
  calc
    F.card = (F.image fun n => n % a).card := hcard_image.symm
    _ ≤ (residueFinset a B).card := Finset.card_le_card hsub
    _ ≤ a / 2 + 1 := residueFinset_card_le_of_pairwiseNoZeroResidueSum hB

/-- A self-complementary residue class contains at most one element of any
finite subset satisfying the local obstruction. -/
theorem finset_filter_mod_eq_card_le_one_of_pairwiseNoZeroResidueSum {a r : ℕ}
    {B : Set ℕ} {F : Finset ℕ}
    (hB : PairwiseNoZeroResidueSum a B)
    (hF : ∀ n ∈ F, n ∈ B)
    (hr : (r + r) % a = 0) :
    (F.filter fun n => n % a = r).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro b c hb hc
  rw [Finset.mem_filter] at hb hc
  have hres : (b % a + c % a) % a = 0 := by
    rw [hb.2, hc.2]
    exact hr
  exact PairwiseNoZeroResidueSum.eq_of_zero_residue_sum hB
    (hF b hb.1) (hF c hc.1) hres

/-- Congruence modulo `a` is injective on any half-open interval of length
`a`. -/
theorem eq_of_mod_eq_of_mem_Ico_length {N a x y : ℕ}
    (hx : x ∈ Set.Ico N (N + a)) (hy : y ∈ Set.Ico N (N + a))
    (hmod : x % a = y % a) :
    x = y := by
  wlog hxy : x ≤ y generalizing x y with H
  · exact (H hy hx hmod.symm (le_of_not_ge hxy)).symm
  have hmodeq : x ≡ y [MOD a] := hmod
  rcases (Nat.modEq_iff_exists_eq_add hxy).mp hmodeq with ⟨t, rfl⟩
  by_cases ht : t = 0
  · simp [ht]
  · exfalso
    have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hmul : a ≤ a * t := by
      simpa using Nat.mul_le_mul_left a (Nat.succ_le_iff.mpr htpos)
    have hlower : N + a ≤ x + a * t := Nat.add_le_add hx.1 hmul
    exact (not_le_of_gt hy.2) hlower

/-- In a length-`a` window of a tail satisfying the local obstruction, there
are at most `a / 2 + 1` elements. -/
theorem finset_card_le_of_pairwiseNoZeroResidueSum_of_subset_Ico {a N : ℕ}
    {B : Set ℕ} {F : Finset ℕ}
    (ha : 0 < a)
    (hB : PairwiseNoZeroResidueSum a B)
    (hF : ∀ n ∈ F, n ∈ B)
    (hIco : ∀ n ∈ F, n ∈ Set.Ico N (N + a)) :
    F.card ≤ a / 2 + 1 := by
  refine finset_card_le_of_pairwiseNoZeroResidueSum_of_inj_mod ha hB hF ?_
  intro m n hm hn hmod
  exact eq_of_mod_eq_of_mem_Ico_length (hIco m hm) (hIco n hn) hmod

/-- Two independent local residue obstructions give a product bound whenever
the pair of residues is injective on the finite set.  This is the two-modulus
prototype for the later LCM packing bound. -/
theorem finset_card_le_two_moduli_of_pairwiseNoZeroResidueSum {a b : ℕ}
    {B C : Set ℕ} {F : Finset ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hB : PairwiseNoZeroResidueSum a B)
    (hC : PairwiseNoZeroResidueSum b C)
    (hFB : ∀ n ∈ F, n ∈ B)
    (hFC : ∀ n ∈ F, n ∈ C)
    (hinj : ∀ ⦃m n : ℕ⦄, m ∈ F → n ∈ F →
      m % a = n % a → m % b = n % b → m = n) :
    F.card ≤ (a / 2 + 1) * (b / 2 + 1) := by
  classical
  let Ra := residueFinset a B
  let Rb := residueFinset b C
  let phi : ℕ → ℕ × ℕ := fun n => (n % a, n % b)
  have hcard_image : (F.image phi).card = F.card := by
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    exact hinj hx hy (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have hsub : F.image phi ⊆ (Ra ×ˢ Rb) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨n, hnF, rfl⟩
    rw [Finset.mem_product]
    constructor
    · rw [mem_residueFinset]
      exact ⟨Nat.mod_lt n ha, n, hFB n hnF, rfl⟩
    · rw [mem_residueFinset]
      exact ⟨Nat.mod_lt n hb, n, hFC n hnF, rfl⟩
  calc
    F.card = (F.image phi).card := hcard_image.symm
    _ ≤ (Ra ×ˢ Rb).card := Finset.card_le_card hsub
    _ = Ra.card * Rb.card := Finset.card_product _ _
    _ ≤ (a / 2 + 1) * (b / 2 + 1) := Nat.mul_le_mul
        (residueFinset_card_le_of_pairwiseNoZeroResidueSum hB)
        (residueFinset_card_le_of_pairwiseNoZeroResidueSum hC)

/-- A finite family of independent local residue obstructions gives a product
bound whenever the full vector of residues is injective on the finite set.

This is the finite packing statement needed before introducing a concrete LCM
window: in a window shorter than the least common multiple of the moduli, the
residue vector is injective, so the cardinality is bounded by the product of
the local half-modulus bounds. -/
theorem finset_card_le_multi_moduli_of_pairwiseNoZeroResidueSum {ι : Type*}
    {J : Finset ι} {m : ι → ℕ} {B : ι → Set ℕ} {F : Finset ℕ}
    (hm : ∀ i ∈ J, 0 < m i)
    (hB : ∀ i ∈ J, PairwiseNoZeroResidueSum (m i) (B i))
    (hF : ∀ i ∈ J, ∀ n ∈ F, n ∈ B i)
    (hinj : ∀ ⦃x y : ℕ⦄, x ∈ F → y ∈ F →
      (∀ i ∈ J, x % m i = y % m i) → x = y) :
    F.card ≤ ∏ i ∈ J, (m i / 2 + 1) := by
  classical
  let Target := ∀ i : ↥J, {r : ℕ // r ∈ residueFinset (m i.1) (B i.1)}
  let phi : {n // n ∈ F} → Target := fun n i =>
    ⟨n.1 % m i.1, by
      rw [mem_residueFinset]
      exact ⟨Nat.mod_lt n.1 (hm i.1 i.2), n.1, hF i.1 i.2 n.1 n.2, rfl⟩⟩
  have hphi_inj : Function.Injective phi := by
    intro x y hxy
    apply Subtype.ext
    refine hinj x.2 y.2 ?_
    intro i hi
    have hcoord := congrFun hxy (⟨i, hi⟩ : ↥J)
    exact Subtype.ext_iff.mp hcoord
  have hFcard : F.card = Fintype.card {n // n ∈ F} := (Fintype.card_coe F).symm
  have htarget_eq :
      Fintype.card Target =
        ∏ i ∈ J, (residueFinset (m i) (B i)).card := by
    simpa [Target, Fintype.card_pi] using
      Finset.prod_attach J fun i => (residueFinset (m i) (B i)).card
  calc
    F.card = Fintype.card {n // n ∈ F} := hFcard
    _ ≤ Fintype.card Target := Fintype.card_le_of_injective phi hphi_inj
    _ = ∏ i ∈ J, (residueFinset (m i) (B i)).card := htarget_eq
    _ ≤ ∏ i ∈ J, (m i / 2 + 1) := Finset.prod_le_prod' fun i hi =>
        residueFinset_card_le_of_pairwiseNoZeroResidueSum (hB i hi)

/-- If two numbers agree modulo every modulus in a finite family, they agree
modulo the least common multiple of the family. -/
theorem mod_eq_finset_lcm_of_forall_mod_eq {ι : Type*}
    {J : Finset ι} {m : ι → ℕ} {x y : ℕ}
    (h : ∀ i ∈ J, x % m i = y % m i) :
    x % J.lcm m = y % J.lcm m := by
  classical
  change x ≡ y [MOD J.lcm m]
  induction J using Finset.induction with
  | empty =>
      change x % ((∅ : Finset ι).lcm m) = y % ((∅ : Finset ι).lcm m)
      rw [Finset.lcm_empty, Nat.mod_one, Nat.mod_one]
  | insert a s has ih =>
      rw [Finset.lcm_insert]
      have ha : x ≡ y [MOD m a] := h a (Finset.mem_insert_self a s)
      have hs : x ≡ y [MOD s.lcm m] := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      simpa using Nat.mod_lcm ha hs

/-- In a window of length the finite LCM, the full residue vector determines
the number. -/
theorem eq_of_forall_mod_eq_of_mem_Ico_lcm {ι : Type*}
    {J : Finset ι} {m : ι → ℕ} {N x y : ℕ}
    (hx : x ∈ Set.Ico N (N + J.lcm m))
    (hy : y ∈ Set.Ico N (N + J.lcm m))
    (hmods : ∀ i ∈ J, x % m i = y % m i) :
    x = y :=
  eq_of_mod_eq_of_mem_Ico_length hx hy
    (mod_eq_finset_lcm_of_forall_mod_eq hmods)

/-- Product packing inside a concrete LCM window. -/
theorem finset_card_le_multi_moduli_of_pairwiseNoZeroResidueSum_of_subset_Ico_lcm
    {ι : Type*} {J : Finset ι} {m : ι → ℕ} {B : ι → Set ℕ}
    {F : Finset ℕ} {N : ℕ}
    (hm : ∀ i ∈ J, 0 < m i)
    (hB : ∀ i ∈ J, PairwiseNoZeroResidueSum (m i) (B i))
    (hF : ∀ i ∈ J, ∀ n ∈ F, n ∈ B i)
    (hIco : ∀ n ∈ F, n ∈ Set.Ico N (N + J.lcm m)) :
    F.card ≤ ∏ i ∈ J, (m i / 2 + 1) := by
  refine finset_card_le_multi_moduli_of_pairwiseNoZeroResidueSum hm hB hF ?_
  intro x y hx hy hmods
  exact eq_of_forall_mod_eq_of_mem_Ico_lcm (hIco x hx) (hIco y hy) hmods

/-- Avoiding-set specialization of the two-modulus product bound. -/
theorem AvoidingSet.finset_card_le_two_tail_moduli {A : Set ℕ}
    (hA : AvoidingSet A) {a b : ℕ} (haA : a ∈ A) (hbA : b ∈ A)
    (ha_pos : 0 < a) (hb_pos : 0 < b) {F : Finset ℕ}
    (hFa : ∀ n ∈ F, n ∈ tailAbove A a)
    (hFb : ∀ n ∈ F, n ∈ tailAbove A b)
    (hinj : ∀ ⦃m n : ℕ⦄, m ∈ F → n ∈ F →
      m % a = n % a → m % b = n % b → m = n) :
    F.card ≤ (a / 2 + 1) * (b / 2 + 1) :=
  finset_card_le_two_moduli_of_pairwiseNoZeroResidueSum
    ha_pos hb_pos (hA.tail_pairwiseNoZeroResidueSum haA)
    (hA.tail_pairwiseNoZeroResidueSum hbA) hFa hFb hinj

theorem AvoidingSet.finset_card_le_two_tail_moduli_of_positive {A : Set ℕ}
    (hA : AvoidingSet A) (hpos : PositiveSet A)
    {a b : ℕ} (haA : a ∈ A) (hbA : b ∈ A) {F : Finset ℕ}
    (hFa : ∀ n ∈ F, n ∈ tailAbove A a)
    (hFb : ∀ n ∈ F, n ∈ tailAbove A b)
    (hinj : ∀ ⦃m n : ℕ⦄, m ∈ F → n ∈ F →
      m % a = n % a → m % b = n % b → m = n) :
    F.card ≤ (a / 2 + 1) * (b / 2 + 1) :=
  hA.finset_card_le_two_tail_moduli haA hbA
    (hpos haA) (hpos hbA) hFa hFb hinj

/-- Avoiding-set specialization of the multi-modulus product bound. -/
theorem AvoidingSet.finset_card_le_multi_tail_moduli {ι : Type*} {A : Set ℕ}
    (hA : AvoidingSet A) {J : Finset ι} {m : ι → ℕ}
    (hmA : ∀ i ∈ J, m i ∈ A) (hmpos : ∀ i ∈ J, 0 < m i)
    {F : Finset ℕ}
    (hFtail : ∀ i ∈ J, ∀ n ∈ F, n ∈ tailAbove A (m i))
    (hinj : ∀ ⦃x y : ℕ⦄, x ∈ F → y ∈ F →
      (∀ i ∈ J, x % m i = y % m i) → x = y) :
    F.card ≤ ∏ i ∈ J, (m i / 2 + 1) :=
  finset_card_le_multi_moduli_of_pairwiseNoZeroResidueSum hmpos
    (fun i hi => hA.tail_pairwiseNoZeroResidueSum (hmA i hi)) hFtail hinj

theorem AvoidingSet.finset_card_le_multi_tail_moduli_of_positive
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {J : Finset ι} {m : ι → ℕ} (hmA : ∀ i ∈ J, m i ∈ A)
    {F : Finset ℕ}
    (hFtail : ∀ i ∈ J, ∀ n ∈ F, n ∈ tailAbove A (m i))
    (hinj : ∀ ⦃x y : ℕ⦄, x ∈ F → y ∈ F →
      (∀ i ∈ J, x % m i = y % m i) → x = y) :
    F.card ≤ ∏ i ∈ J, (m i / 2 + 1) :=
  hA.finset_card_le_multi_tail_moduli hmA
    (fun i hi => hpos (hmA i hi)) hFtail hinj

/-- Avoiding-set LCM-window specialization of the multi-modulus product bound. -/
theorem AvoidingSet.finset_card_le_multi_tail_moduli_of_subset_Ico_lcm
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A)
    {J : Finset ι} {m : ι → ℕ}
    (hmA : ∀ i ∈ J, m i ∈ A) (hmpos : ∀ i ∈ J, 0 < m i)
    {F : Finset ℕ} {N : ℕ}
    (hFtail : ∀ i ∈ J, ∀ n ∈ F, n ∈ tailAbove A (m i))
    (hIco : ∀ n ∈ F, n ∈ Set.Ico N (N + J.lcm m)) :
    F.card ≤ ∏ i ∈ J, (m i / 2 + 1) :=
  finset_card_le_multi_moduli_of_pairwiseNoZeroResidueSum_of_subset_Ico_lcm
    hmpos (fun i hi => hA.tail_pairwiseNoZeroResidueSum (hmA i hi))
    hFtail hIco

theorem AvoidingSet.finset_card_le_multi_tail_moduli_of_subset_Ico_lcm_of_positive
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {J : Finset ι} {m : ι → ℕ} (hmA : ∀ i ∈ J, m i ∈ A)
    {F : Finset ℕ} {N : ℕ}
    (hFtail : ∀ i ∈ J, ∀ n ∈ F, n ∈ tailAbove A (m i))
    (hIco : ∀ n ∈ F, n ∈ Set.Ico N (N + J.lcm m)) :
    F.card ≤ ∏ i ∈ J, (m i / 2 + 1) :=
  hA.finset_card_le_multi_tail_moduli_of_subset_Ico_lcm hmA
    (fun i hi => hpos (hmA i hi)) hFtail hIco

/-- The common LCM window of numbers lying in all tails above the selected
moduli. -/
noncomputable def multiTailLCMWindowFinset {ι : Type*} (A : Set ℕ)
    (J : Finset ι) (m : ι → ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (N + J.lcm m)).filter fun n =>
    ∀ i ∈ J, n ∈ tailAbove A (m i)

theorem mem_multiTailLCMWindowFinset {ι : Type*} {A : Set ℕ}
    {J : Finset ι} {m : ι → ℕ} {N n : ℕ} :
    n ∈ multiTailLCMWindowFinset A J m N ↔
      n ∈ Set.Ico N (N + J.lcm m) ∧
        ∀ i ∈ J, n ∈ tailAbove A (m i) := by
  classical
  unfold multiTailLCMWindowFinset
  simp [Set.mem_Ico]

theorem AvoidingSet.multiTailLCMWindow_card_le {ι : Type*} {A : Set ℕ}
    (hA : AvoidingSet A) {J : Finset ι} {m : ι → ℕ}
    (hmA : ∀ i ∈ J, m i ∈ A) (hmpos : ∀ i ∈ J, 0 < m i) (N : ℕ) :
    (multiTailLCMWindowFinset A J m N).card ≤
      ∏ i ∈ J, (m i / 2 + 1) := by
  refine hA.finset_card_le_multi_tail_moduli_of_subset_Ico_lcm
    (J := J) (m := m) (F := multiTailLCMWindowFinset A J m N) (N := N)
    hmA hmpos ?_ ?_
  · intro i hi n hn
    exact (mem_multiTailLCMWindowFinset.mp hn).2 i hi
  · intro n hn
    exact (mem_multiTailLCMWindowFinset.mp hn).1

theorem AvoidingSet.multiTailLCMWindow_card_le_of_positive
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    {J : Finset ι} {m : ι → ℕ} (hmA : ∀ i ∈ J, m i ∈ A) (N : ℕ) :
    (multiTailLCMWindowFinset A J m N).card ≤
      ∏ i ∈ J, (m i / 2 + 1) :=
  hA.multiTailLCMWindow_card_le hmA (fun i hi => hpos (hmA i hi)) N

theorem finset_lcm_pos_of_forall_pos {ι : Type*}
    {J : Finset ι} {m : ι → ℕ} (hmpos : ∀ i ∈ J, 0 < m i) :
    0 < J.lcm m := by
  classical
  induction J using Finset.induction with
  | empty =>
      simp
  | insert a s has ih =>
      rw [Finset.lcm_insert]
      exact Nat.lcm_pos (hmpos a (Finset.mem_insert_self a s))
        (ih fun i hi => hmpos i (Finset.mem_insert_of_mem hi))

/-- A finite set contained in a length-`H` interval, and in every selected tail,
is covered by `H / L + 1` consecutive LCM windows, where
`L = J.lcm m`.  Combining the cover with the LCM-window packing gives the
global interval bound used by the dyadic attack. -/
theorem AvoidingSet.finset_card_le_multi_tail_moduli_of_subset_Ico_lcm_cover
    {ι : Type*} {A : Set ℕ} (hA : AvoidingSet A)
    {J : Finset ι} {m : ι → ℕ} (hmA : ∀ i ∈ J, m i ∈ A)
    (hmpos : ∀ i ∈ J, 0 < m i) {F : Finset ℕ} {X H : ℕ}
    (hFtail : ∀ i ∈ J, ∀ n ∈ F, n ∈ tailAbove A (m i))
    (hFIco : ∀ n ∈ F, n ∈ Set.Ico X (X + H))
    (hL : 0 < J.lcm m := finset_lcm_pos_of_forall_pos hmpos) :
    F.card ≤ (∏ i ∈ J, (m i / 2 + 1)) * (H / J.lcm m + 1) := by
  classical
  let L := J.lcm m
  let W : Finset ℕ :=
    (Finset.range (H / L + 1)).biUnion fun t =>
      multiTailLCMWindowFinset A J m (X + t * L)
  have hsub : F ⊆ W := by
    intro n hn
    have hnIco := hFIco n hn
    have hX_le_n : X ≤ n := hnIco.1
    have hn_lt : n < X + H := hnIco.2
    let t := (n - X) / L
    have hn_sub_le : n - X ≤ H := by omega
    have ht_le : t ≤ H / L := Nat.div_le_div_right hn_sub_le
    have ht_mem : t ∈ Finset.range (H / L + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le ht_le)
    have hdiv_le : t * L ≤ n - X := Nat.div_mul_le_self (n - X) L
    have hlow : X + t * L ≤ n := by
      omega
    have hsub_lt' : n - X < ((n - X) / L + 1) * L := by
      simpa [Nat.add_mul] using Nat.lt_div_mul_add (a := n - X) hL
    have hsub_lt : n - X < (t + 1) * L := by
      simpa [t] using hsub_lt'
    have hhigh : n < X + (t + 1) * L := by
      omega
    change n ∈
      (Finset.range (H / L + 1)).biUnion
        (fun t => multiTailLCMWindowFinset A J m (X + t * L))
    rw [Finset.mem_biUnion]
    refine ⟨t, ht_mem, ?_⟩
    rw [mem_multiTailLCMWindowFinset]
    constructor
    · refine ⟨hlow, ?_⟩
      convert hhigh using 1
      ring
    · intro i hi
      exact hFtail i hi n hn
  have hWcard :
      W.card ≤ (∏ i ∈ J, (m i / 2 + 1)) * (H / L + 1) := by
    simpa [W, L, Nat.mul_comm] using
      Finset.card_biUnion_le_card_mul
        (Finset.range (H / L + 1))
        (fun t => multiTailLCMWindowFinset A J m (X + t * L))
        (∏ i ∈ J, (m i / 2 + 1))
        (fun t _ht => hA.multiTailLCMWindow_card_le hmA hmpos (X + t * L))
  exact (Finset.card_le_card hsub).trans hWcard

/-- The length-`a` window of the tail above `a`. -/
noncomputable def tailWindowFinset (A : Set ℕ) (a N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (N + a)).filter fun n => n ∈ tailAbove A a

theorem mem_tailWindowFinset {A : Set ℕ} {a N n : ℕ} :
    n ∈ tailWindowFinset A a N ↔
      n ∈ Set.Ico N (N + a) ∧ n ∈ tailAbove A a := by
  classical
  unfold tailWindowFinset
  simp [Set.mem_Ico]

/-- In an avoiding set, every length-`a` window in the tail above `a` contains
at most `a / 2 + 1` elements. -/
theorem AvoidingSet.tailWindow_card_le {A : Set ℕ} (hA : AvoidingSet A)
    {a : ℕ} (haA : a ∈ A) (ha_pos : 0 < a) (N : ℕ) :
    (tailWindowFinset A a N).card ≤ a / 2 + 1 := by
  refine finset_card_le_of_pairwiseNoZeroResidueSum_of_subset_Ico
    (a := a) (N := N) (B := tailAbove A a) (F := tailWindowFinset A a N)
    ha_pos (hA.tail_pairwiseNoZeroResidueSum haA) ?_ ?_
  · intro n hn
    exact (mem_tailWindowFinset.mp hn).2
  · intro n hn
    exact (mem_tailWindowFinset.mp hn).1

theorem AvoidingSet.tailWindow_card_le_of_positive {A : Set ℕ}
    (hA : AvoidingSet A) (hpos : PositiveSet A)
    {a : ℕ} (haA : a ∈ A) (N : ℕ) :
    (tailWindowFinset A a N).card ≤ a / 2 + 1 :=
  hA.tailWindow_card_le haA (hpos haA) N

/-- Any finite union of length-`a` windows in the tail above `a` has size at
most the single-window bound times the number of windows.  Later interval and
LCM packing bounds can supply concrete covering families. -/
theorem AvoidingSet.tailWindow_biUnion_card_le {ι : Type*} {A : Set ℕ}
    (hA : AvoidingSet A) {a : ℕ} (haA : a ∈ A) (ha_pos : 0 < a)
    (J : Finset ι) (N : ι → ℕ) :
    (J.biUnion fun j => tailWindowFinset A a (N j)).card ≤
      (a / 2 + 1) * J.card := by
  simpa [Nat.mul_comm] using
    Finset.card_biUnion_le_card_mul J (fun j => tailWindowFinset A a (N j))
      (a / 2 + 1) (fun j _hj => hA.tailWindow_card_le haA ha_pos (N j))

theorem AvoidingSet.finset_card_le_of_subset_tailWindow_biUnion {ι : Type*}
    {A : Set ℕ} (hA : AvoidingSet A) {a : ℕ} (haA : a ∈ A) (ha_pos : 0 < a)
    {F : Finset ℕ} (J : Finset ι) (N : ι → ℕ)
    (hsub : F ⊆ J.biUnion fun j => tailWindowFinset A a (N j)) :
    F.card ≤ (a / 2 + 1) * J.card :=
  (Finset.card_le_card hsub).trans
    (hA.tailWindow_biUnion_card_le haA ha_pos J N)

end DivisibilityAvoidingSets
