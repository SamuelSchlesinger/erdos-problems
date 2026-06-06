/-
# Maximal Strong Almost-Sidon Sets

This file starts the local-replacement side of the rigidity program for
Problem #864.  The basic observation is that if an almost-Sidon set is maximal
in `{1, ..., N}`, then every missing point is blocked by an old pair-sum:
inserting the missing point creates a new repeated sum away from the original
exception, and that repeated sum must compare an inserted-point pair with an
old pair from `A`.

For a missing reflection `y = n* - x`, this gives the first formal "shadow"
obstruction

  `2y = b + c ≠ n*` or `y + a = b + c ≠ n*`,
  with `a, b, c ∈ A`.

This is intentionally local: it does not close the `√2` gap, but it packages
the replacement obstruction needed for future extras-exclusion arguments.
-/
import Erdos.AlmostSidonSets.Rigidity

namespace AlmostSidonSets

/-- Maximality among almost-Sidon subsets of `{1, ..., N}`. -/
def IsMaximalAlmostSidonInInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  AlmostSidonInInterval A N ∧
    ∀ x ∈ ground N, x ∉ A → ¬ AlmostSidonFinset (insert x A)

/-- Cardinality extremality among almost-Sidon subsets of `{1, ..., N}`. -/
def IsCardinalityMaximalAlmostSidonInInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  AlmostSidonInInterval A N ∧
    ∀ B : Finset ℕ, AlmostSidonInInterval B N → B.card ≤ A.card

/-- A cardinality extremizer is maximal under insertion. -/
theorem IsCardinalityMaximalAlmostSidonInInterval.isMaximal
    {A : Finset ℕ} {N : ℕ}
    (hopt : IsCardinalityMaximalAlmostSidonInInterval A N) :
    IsMaximalAlmostSidonInInterval A N := by
  refine ⟨hopt.1, ?_⟩
  intro x hxN hxA hInsertAlmost
  have hInsertInterval : AlmostSidonInInterval (insert x A) N := by
    refine ⟨hInsertAlmost, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haA
    · exact hxN
    · exact hopt.1.2 a haA
  have hcard_le : (insert x A).card ≤ A.card :=
    hopt.2 (insert x A) hInsertInterval
  have hcard_gt : A.card < (insert x A).card := by
    simp [hxA]
  omega

/-- A witnessed repeated sum remains witnessed after inserting a new point. -/
theorem HasTwoSumReprs.insert {A : Finset ℕ} {n y : ℕ}
    (h : HasTwoSumReprs A n) :
    HasTwoSumReprs (insert y A) n := by
  rcases h with
    ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hle₁, hle₂, hsum₁, hsum₂, hneq⟩
  exact ⟨a₁, Finset.mem_insert_of_mem ha₁,
    a₂, Finset.mem_insert_of_mem ha₂,
    b₁, Finset.mem_insert_of_mem hb₁,
    b₂, Finset.mem_insert_of_mem hb₂,
    hle₁, hle₂, hsum₁, hsum₂, hneq⟩

/-- If inserting a point breaks almost-Sidonness, then for any reference value
`nstar`, insertion creates a repeated sum at some value different from
`nstar`. -/
theorem not_almostSidon_insert_creates_offAxis_exception
    {A : Finset ℕ} {nstar y : ℕ}
    (hnot : ¬ AlmostSidonFinset (insert y A)) :
    ∃ m : ℕ, m ≠ nstar ∧ HasTwoSumReprs (insert y A) m := by
  classical
  rw [AlmostSidonFinset] at hnot
  push Not at hnot
  rcases hnot with ⟨m, n, hm, hn, hmn⟩
  by_cases hmstar : m = nstar
  · refine ⟨n, ?_, hn⟩
    intro hnstar
    exact hmn (by omega)
  · exact ⟨m, hmstar, hm⟩

/-- Two sorted pairs with the same sum and a common distinguished element are
the same sorted pair. -/
private theorem sorted_pair_eq_of_mem_of_add_eq
    {a₁ a₂ b₁ b₂ y : ℕ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (hsum : a₁ + a₂ = b₁ + b₂)
    (hya : a₁ = y ∨ a₂ = y) (hyb : b₁ = y ∨ b₂ = y) :
    a₁ = b₁ ∧ a₂ = b₂ := by
  rcases hya with rfl | rfl <;> rcases hyb with rfl | rfl <;> omega

/-- An off-axis repeated sum created by insertion must use the inserted point
on one side and an old pair on the other. Consequently either the self-pair
`y + y` hits an old pair-sum, or a translate `y + a` with `a ∈ A` does.

This is the core local-replacement obstruction: off-axis failure of inserting
`y` is witnessed by `{2y} ∪ (y + A)` hitting an old pair-sum of `A`. -/
theorem offAxis_insert_collision_has_shadow
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar y m : ℕ} (_hyA : y ∉ A)
    (h_exception : HasTwoSumReprs A nstar)
    (hm_ne : m ≠ nstar) (hm : HasTwoSumReprs (insert y A) m) :
    (∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar) ∨
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, y + a = b + c ∧ y + a ≠ nstar := by
  classical
  rcases hm with
    ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hle₁, hle₂, hsum₁, hsum₂, hneq⟩
  have ha₁_cases := Finset.mem_insert.mp ha₁
  have ha₂_cases := Finset.mem_insert.mp ha₂
  have hb₁_cases := Finset.mem_insert.mp hb₁
  have hb₂_cases := Finset.mem_insert.mp hb₂
  let usesFirst : Prop := a₁ = y ∨ a₂ = y
  let usesSecond : Prop := b₁ = y ∨ b₂ = y
  have not_neither : ¬ (¬ usesFirst ∧ ¬ usesSecond) := by
    rintro ⟨hfirst, hsecond⟩
    have ha₁A : a₁ ∈ A := by
      rcases ha₁_cases with h | h
      · exact (hfirst (Or.inl h)).elim
      · exact h
    have ha₂A : a₂ ∈ A := by
      rcases ha₂_cases with h | h
      · exact (hfirst (Or.inr h)).elim
      · exact h
    have hb₁A : b₁ ∈ A := by
      rcases hb₁_cases with h | h
      · exact (hsecond (Or.inl h)).elim
      · exact h
    have hb₂A : b₂ ∈ A := by
      rcases hb₂_cases with h | h
      · exact (hsecond (Or.inr h)).elim
      · exact h
    have hmA : HasTwoSumReprs A m :=
      ⟨a₁, ha₁A, a₂, ha₂A, b₁, hb₁A, b₂, hb₂A,
        hle₁, hle₂, hsum₁, hsum₂, hneq⟩
    exact hm_ne (hA m nstar hmA h_exception)
  have not_both : ¬ (usesFirst ∧ usesSecond) := by
    rintro ⟨hfirst, hsecond⟩
    have heq := sorted_pair_eq_of_mem_of_add_eq hle₁ hle₂ (by omega : a₁ + a₂ = b₁ + b₂)
      hfirst hsecond
    rcases heq with ⟨h₁, h₂⟩
    rcases hneq with h | h
    · exact h h₁
    · exact h h₂
  by_cases hfirst : usesFirst
  · have hsecond_not : ¬ usesSecond := by
      intro hsecond
      exact not_both ⟨hfirst, hsecond⟩
    have hb₁A : b₁ ∈ A := by
      rcases hb₁_cases with h | h
      · exact (hsecond_not (Or.inl h)).elim
      · exact h
    have hb₂A : b₂ ∈ A := by
      rcases hb₂_cases with h | h
      · exact (hsecond_not (Or.inr h)).elim
      · exact h
    rcases hfirst with ha₁y | ha₂y
    · rcases ha₂_cases with ha₂y | ha₂A
      · left
        refine ⟨b₁, hb₁A, b₂, hb₂A, ?_, ?_⟩
        · omega
        · intro hstar
          exact hm_ne (by omega)
      · right
        refine ⟨a₂, ha₂A, b₁, hb₁A, b₂, hb₂A, ?_, ?_⟩
        · omega
        · intro hstar
          exact hm_ne (by omega)
    · rcases ha₁_cases with ha₁y' | ha₁A
      · left
        refine ⟨b₁, hb₁A, b₂, hb₂A, ?_, ?_⟩
        · omega
        · intro hstar
          exact hm_ne (by omega)
      · right
        refine ⟨a₁, ha₁A, b₁, hb₁A, b₂, hb₂A, ?_, ?_⟩
        · omega
        · intro hstar
          exact hm_ne (by omega)
  · have hsecond : usesSecond := by
      by_contra hsecond_not
      exact not_neither ⟨hfirst, hsecond_not⟩
    have ha₁A : a₁ ∈ A := by
      rcases ha₁_cases with h | h
      · exact (hfirst (Or.inl h)).elim
      · exact h
    have ha₂A : a₂ ∈ A := by
      rcases ha₂_cases with h | h
      · exact (hfirst (Or.inr h)).elim
      · exact h
    rcases hsecond with hb₁y | hb₂y
    · rcases hb₂_cases with hb₂y' | hb₂A
      · left
        refine ⟨a₁, ha₁A, a₂, ha₂A, ?_, ?_⟩
        · omega
        · intro hstar
          exact hm_ne (by omega)
      · right
        refine ⟨b₂, hb₂A, a₁, ha₁A, a₂, ha₂A, ?_, ?_⟩
        · omega
        · intro hstar
          exact hm_ne (by omega)
    · rcases hb₁_cases with hb₁y' | hb₁A
      · left
        refine ⟨a₁, ha₁A, a₂, ha₂A, ?_, ?_⟩
        · omega
        · intro hstar
          exact hm_ne (by omega)
      · right
        refine ⟨b₁, hb₁A, a₁, ha₁A, a₂, ha₂A, ?_, ?_⟩
        · omega
        · intro hstar
          exact hm_ne (by omega)

/-- All pair-sum values generated by ordered pairs from `A`. -/
def pairSumsFinset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image fun p : ℕ × ℕ => p.1 + p.2

@[simp] theorem mem_pairSumsFinset {A : Finset ℕ} {s : ℕ} :
    s ∈ pairSumsFinset A ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = s := by
  classical
  constructor
  · intro hs
    rw [pairSumsFinset, Finset.mem_image] at hs
    rcases hs with ⟨p, hp, hp_eq⟩
    rw [Finset.mem_product] at hp
    exact ⟨p.1, hp.1, p.2, hp.2, hp_eq⟩
  · rintro ⟨a, ha, b, hb, hsum⟩
    rw [pairSumsFinset, Finset.mem_image]
    exact ⟨(a, b), by simp [ha, hb], hsum⟩

/-- Old pair-sums of `A`, excluding the distinguished exception axis. -/
def offAxisPairSumsFinset (A : Finset ℕ) (nstar : ℕ) : Finset ℕ :=
  (pairSumsFinset A).erase nstar

@[simp] theorem mem_offAxisPairSumsFinset {A : Finset ℕ} {nstar s : ℕ} :
    s ∈ offAxisPairSumsFinset A nstar ↔
      s ≠ nstar ∧ ∃ a ∈ A, ∃ b ∈ A, a + b = s := by
  simp [offAxisPairSumsFinset]

/-- The values by which a candidate insertion `y` can be blocked: the self-pair
`2y` and all translates `y + a` with `a ∈ A`, intersected with the old
off-axis pair-sums of `A`. -/
def insertionShadowFinset (A : Finset ℕ) (nstar y : ℕ) : Finset ℕ :=
  (insert (2 * y) (A.image fun a => y + a)) ∩ offAxisPairSumsFinset A nstar

@[simp] theorem mem_insertionShadowFinset {A : Finset ℕ} {nstar y s : ℕ} :
    s ∈ insertionShadowFinset A nstar y ↔
      (s = 2 * y ∨ ∃ a ∈ A, y + a = s) ∧
        s ≠ nstar ∧ ∃ b ∈ A, ∃ c ∈ A, b + c = s := by
  classical
  constructor
  · intro hs
    rw [insertionShadowFinset, Finset.mem_inter] at hs
    constructor
    · rw [Finset.mem_insert, Finset.mem_image] at hs
      rcases hs.1 with h | h
      · exact Or.inl h
      · rcases h with ⟨a, ha, hsa⟩
        exact Or.inr ⟨a, ha, hsa⟩
    · exact mem_offAxisPairSumsFinset.mp hs.2
  · rintro ⟨hleft, hoff⟩
    rw [insertionShadowFinset, Finset.mem_inter]
    constructor
    · rw [Finset.mem_insert, Finset.mem_image]
      rcases hleft with h | ⟨a, ha, hsum⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, hsum⟩
    · exact mem_offAxisPairSumsFinset.mpr hoff

/-- The blocker-triple form of `offAxis_insert_collision_has_shadow` packaged
as nonemptiness of the insertion-shadow set. -/
theorem offAxis_insert_collision_shadow_nonempty
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar y m : ℕ} (hyA : y ∉ A)
    (h_exception : HasTwoSumReprs A nstar)
    (hm_ne : m ≠ nstar) (hm : HasTwoSumReprs (insert y A) m) :
    (insertionShadowFinset A nstar y).Nonempty := by
  classical
  rcases offAxis_insert_collision_has_shadow hA hyA h_exception hm_ne hm with
    ⟨b, hb, c, hc, hsum, hne⟩ | ⟨a, ha, b, hb, c, hc, hsum, hne⟩
  · refine ⟨2 * y, ?_⟩
    rw [mem_insertionShadowFinset]
    exact ⟨Or.inl rfl, hne, b, hb, c, hc, hsum.symm⟩
  · refine ⟨y + a, ?_⟩
    rw [mem_insertionShadowFinset]
    exact ⟨Or.inr ⟨a, ha, rfl⟩, hne, b, hb, c, hc, hsum.symm⟩

/-- In a maximal almost-Sidon set, every missing point in the interval creates
an off-axis shadow against an old pair-sum. -/
theorem maximal_missing_point_has_shadow
    {A : Finset ℕ} {N nstar y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hyN : y ∈ ground N) (hyA : y ∉ A) :
    (∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar) ∨
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, y + a = b + c ∧ y + a ≠ nstar := by
  have hA : AlmostSidonFinset A := hmax.1.1
  have hnot : ¬ AlmostSidonFinset (insert y A) := hmax.2 y hyN hyA
  rcases not_almostSidon_insert_creates_offAxis_exception hnot with
    ⟨m, hm_ne, hm⟩
  exact offAxis_insert_collision_has_shadow hA hyA h_exception hm_ne hm

/-- Set-valued version of `maximal_missing_point_has_shadow`. -/
theorem maximal_missing_point_shadow_nonempty
    {A : Finset ℕ} {N nstar y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hyN : y ∈ ground N) (hyA : y ∉ A) :
    (insertionShadowFinset A nstar y).Nonempty := by
  have hA : AlmostSidonFinset A := hmax.1.1
  have hnot : ¬ AlmostSidonFinset (insert y A) := hmax.2 y hyN hyA
  rcases not_almostSidon_insert_creates_offAxis_exception hnot with
    ⟨m, hm_ne, hm⟩
  exact offAxis_insert_collision_shadow_nonempty hA hyA h_exception hm_ne hm

/-- Specialization of `maximal_missing_point_has_shadow` to a missing reflection
`y = nstar - x` of an existing element `x ∈ A`. -/
theorem maximal_missing_reflection_has_shadow
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (_hxA : x ∈ A) (hy : y = nstar - x)
    (hyN : y ∈ ground N) (hyA : y ∉ A) :
    (∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar) ∨
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, y + a = b + c ∧ y + a ≠ nstar := by
  subst hy
  exact maximal_missing_point_has_shadow hmax h_exception hyN hyA

/-- Set-valued shadow nonemptiness for missing reflections. -/
theorem maximal_missing_reflection_shadow_nonempty
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (_hxA : x ∈ A) (hy : y = nstar - x)
    (hyN : y ∈ ground N) (hyA : y ∉ A) :
    (insertionShadowFinset A nstar y).Nonempty := by
  subst hy
  exact maximal_missing_point_shadow_nonempty hmax h_exception hyN hyA

/-- Extremizer-level shadow nonemptiness for missing reflections. -/
theorem cardinalityMaximal_missing_reflection_shadow_nonempty
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hopt : IsCardinalityMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hy : y = nstar - x)
    (hyN : y ∈ ground N) (hyA : y ∉ A) :
    (insertionShadowFinset A nstar y).Nonempty :=
  maximal_missing_reflection_shadow_nonempty
    hopt.isMaximal h_exception hxA hy hyN hyA

/-! ## Translate shadows

The translate branch of a missing-point shadow has the form `y + a = b + c`,
where `a, b, c ∈ A` and the value is not the exception axis.  We keep the old
pair `(b, c)` sorted so that R3 applies directly. -/

/-- A sorted translate-shadow witness for the insertion candidate `y`. -/
def TranslateShadow (A : Finset ℕ) (nstar y a b c : ℕ) : Prop :=
  a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ b ≤ c ∧ y + a = b + c ∧ y + a ≠ nstar

/-- Any unsorted translate blocker can be normalized into `TranslateShadow`. -/
theorem translateShadow_of_blocker {A : Finset ℕ} {nstar y a b c : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (h : y + a = b + c) (hne : y + a ≠ nstar) :
    ∃ b' : ℕ, ∃ c' : ℕ, TranslateShadow A nstar y a b' c' := by
  rcases le_or_gt b c with hbc | hcb
  · exact ⟨b, c, ha, hb, hc, hbc, h, hne⟩
  · exact ⟨c, b, ha, hc, hb, le_of_lt hcb, by omega, hne⟩

/-- Two translate shadows with the same value must use the same old sorted
pair.  This is just R3 applied to the two old representations of that off-axis
value. -/
theorem translateShadow_same_value_forces_same_oldPair
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar y₁ y₂ a₁ a₂ b₁ b₂ c₁ c₂ : ℕ}
    (h_exception : HasTwoSumReprs A nstar)
    (h1 : TranslateShadow A nstar y₁ a₁ b₁ c₁)
    (h2 : TranslateShadow A nstar y₂ a₂ b₂ c₂)
    (hval : y₁ + a₁ = y₂ + a₂) :
    b₁ = b₂ ∧ c₁ = c₂ := by
  rcases h1 with ⟨_ha₁, hb₁, hc₁, hbc₁, hsum₁, hne₁⟩
  rcases h2 with ⟨_ha₂, hb₂, hc₂, hbc₂, hsum₂, _hne₂⟩
  have hpair₁ : b₁ + c₁ = y₁ + a₁ := by omega
  have hpair₂ : b₂ + c₂ = y₁ + a₁ := by omega
  exact r3_off_axis_unique_representation A hA h_exception (y₁ + a₁) hne₁
    b₁ c₁ b₂ c₂ hb₁ hc₁ hb₂ hc₂ hbc₁ hbc₂ hpair₁ hpair₂

/-- A translate shadow is the unique old sorted pair for its off-axis value. -/
theorem translateShadow_value_forces_oldPair
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar y a b c d e : ℕ}
    (h_exception : HasTwoSumReprs A nstar)
    (hT : TranslateShadow A nstar y a b c)
    (hd : d ∈ A) (he : e ∈ A) (hde : d ≤ e)
    (hval : y + a = d + e) :
    b = d ∧ c = e := by
  rcases hT with ⟨_ha, hb, hc, hbc, hsum, hne⟩
  have hpair : b + c = y + a := by omega
  exact r3_off_axis_unique_representation A hA h_exception (y + a) hne
    b c d e hb hc hd he hbc hde hpair hval.symm

/-- If a translate-shadow value is pinned to `min A + u`, then the old pair is
exactly `(min A, u)`. -/
theorem translateShadow_lowerExtreme_value_forces_pair
    {A : Finset ℕ} (hA : AlmostSidonFinset A) (h_card : 2 ≤ A.card)
    {nstar y a b c u : ℕ}
    (h_exception : HasTwoSumReprs A nstar) :
    let m := A.min' (Finset.card_pos.mp (by omega : 0 < A.card))
    u ∈ A →
      TranslateShadow A nstar y a b c →
      y + a = m + u →
      b = m ∧ c = u := by
  intro m huA hT hval
  have hmA : m ∈ A := A.min'_mem _
  have hm_le_u : m ≤ u := A.min'_le _ huA
  exact translateShadow_value_forces_oldPair hA h_exception hT hmA huA hm_le_u hval

/-- If a translate-shadow value is pinned to `u + max A`, then the old pair is
exactly `(u, max A)`. -/
theorem translateShadow_upperExtreme_value_forces_pair
    {A : Finset ℕ} (hA : AlmostSidonFinset A) (h_card : 2 ≤ A.card)
    {nstar y a b c u : ℕ}
    (h_exception : HasTwoSumReprs A nstar) :
    let M := A.max' (Finset.card_pos.mp (by omega : 0 < A.card))
    u ∈ A →
      TranslateShadow A nstar y a b c →
      y + a = u + M →
      b = u ∧ c = M := by
  intro M huA hT hval
  have hMA : M ∈ A := A.max'_mem _
  have hu_le_M : u ≤ M := A.le_max' _ huA
  exact translateShadow_value_forces_oldPair hA h_exception hT huA hMA hu_le_M hval

/-- For two missing reflections, equal diagonal offset forces equal translate
values; hence distinct old pairs are impossible by R3. -/
theorem reflectionTranslate_equalOffset_distinctOldPair_false
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x₁ x₂ y₁ y₂ a₁ a₂ b₁ b₂ c₁ c₂ : ℕ}
    (h_exception : HasTwoSumReprs A nstar)
    (hxy₁ : x₁ + y₁ = nstar) (hxy₂ : x₂ + y₂ = nstar)
    (h1 : TranslateShadow A nstar y₁ a₁ b₁ c₁)
    (h2 : TranslateShadow A nstar y₂ a₂ b₂ c₂)
    (hoffset : a₁ + x₂ = a₂ + x₁)
    (hpair_ne : b₁ ≠ b₂ ∨ c₁ ≠ c₂) :
    False := by
  have hval : y₁ + a₁ = y₂ + a₂ := by omega
  have heq :=
    translateShadow_same_value_forces_same_oldPair hA h_exception h1 h2 hval
  rcases heq with ⟨hb, hc⟩
  rcases hpair_ne with hne | hne
  · exact hne hb
  · exact hne hc

/-- If `x₁ < x₂`, then equal translate-shadow values force the second anchor
to be strictly larger. -/
theorem reflectionTranslate_sameValue_forces_anchor_order
    {nstar x₁ x₂ y₁ y₂ a₁ a₂ : ℕ}
    (hxy₁ : x₁ + y₁ = nstar) (hxy₂ : x₂ + y₂ = nstar)
    (hxlt : x₁ < x₂) (hval : y₁ + a₁ = y₂ + a₂) :
    a₁ < a₂ := by
  omega

/-- A difference-set exclusion prevents two missing reflections from sharing a
translate-shadow value. -/
theorem reflectionTranslate_noAnchorDifference_disjoint
    {A : Finset ℕ} {nstar x₁ x₂ y₁ y₂ a₁ a₂ : ℕ}
    (hxy₁ : x₁ + y₁ = nstar) (hxy₂ : x₂ + y₂ = nstar)
    (hNoDiff : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + x₂ ≠ a₂ + x₁)
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) :
    y₁ + a₁ ≠ y₂ + a₂ := by
  intro hval
  exact hNoDiff a₁ ha₁ a₂ ha₂ (by omega)

/-- If maximality gives a shadow and the self-shadow branch is impossible, the
blocker can be normalized into a sorted translate shadow. -/
theorem maximal_missing_point_has_translateShadow
    {A : Finset ℕ} {N nstar y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hNoSelf : ¬ ∃ b ∈ A, ∃ c ∈ A, b + c = 2 * y) :
    ∃ a ∈ A, ∃ b : ℕ, ∃ c : ℕ, TranslateShadow A nstar y a b c := by
  rcases maximal_missing_point_has_shadow hmax h_exception hyN hyA with
    ⟨b, hb, c, hc, hself, _hne⟩ | ⟨a, ha, b, hb, c, hc, hsum, hne⟩
  · exact (hNoSelf ⟨b, hb, c, hc, hself.symm⟩).elim
  · rcases translateShadow_of_blocker ha hb hc hsum hne with ⟨b', c', hT⟩
    exact ⟨a, ha, b', c', hT⟩

/-- Missing-reflection version of `maximal_missing_point_has_translateShadow`. -/
theorem maximal_missing_reflection_has_translateShadow
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (_hxA : x ∈ A) (hy : y = nstar - x)
    (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hNoSelf : ¬ ∃ b ∈ A, ∃ c ∈ A, b + c = 2 * y) :
    ∃ a ∈ A, ∃ b : ℕ, ∃ c : ℕ, TranslateShadow A nstar y a b c := by
  subst hy
  exact maximal_missing_point_has_translateShadow hmax h_exception hyN hyA hNoSelf

/-! ## Self-shadow descent for extras

The self-shadow branch `2y = b + c` is much more rigid than it first appears.
If `y = n* - x` is the missing reflection of an extra point `x`, then the old
pair `(b, c)` blocking the insertion cannot be made entirely of paired
elements.  Otherwise reflecting `(b, c)` across the exception axis gives an
off-axis representation of `2x`, colliding with the self-pair `(x, x)`.

Consequently, in the high region `2y < x`, a self-shadow blocker produces a
strictly smaller extra.  This is the first formal descent obstruction against
missing reflections. -/

/-- Every element participating in an `nstar`-pair is at most `nstar`. -/
theorem le_nstar_of_mem_pairElements {A : Finset ℕ} {nstar x : ℕ}
    (hx : x ∈ pairElements A nstar) :
    x ≤ nstar := by
  unfold pairElements at hx
  rw [Finset.mem_union] at hx
  rcases hx with h | h
  · rw [Finset.mem_image] at h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    have hp := mem_sumReprsFinset.mp hp_mem
    have hx_eq : x = p.1 := hp_eq.symm
    omega
  · rw [Finset.mem_image] at h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    have hp := mem_sumReprsFinset.mp hp_mem
    have hx_eq : x = p.2 := hp_eq.symm
    omega

/-- The `nstar`-paired elements are closed under reflection across the
exception axis. -/
theorem pairElements_reflection_mem {A : Finset ℕ} {nstar x : ℕ}
    (hx : x ∈ pairElements A nstar) :
    nstar - x ∈ pairElements A nstar := by
  unfold pairElements at hx ⊢
  rw [Finset.mem_union] at hx ⊢
  rcases hx with h | h
  · rw [Finset.mem_image] at h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    right
    rw [Finset.mem_image]
    refine ⟨p, hp_mem, ?_⟩
    have hp := mem_sumReprsFinset.mp hp_mem
    have hx_eq : x = p.1 := hp_eq.symm
    omega
  · rw [Finset.mem_image] at h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    left
    rw [Finset.mem_image]
    refine ⟨p, hp_mem, ?_⟩
    have hp := mem_sumReprsFinset.mp hp_mem
    have hx_eq : x = p.2 := hp_eq.symm
    omega

/-- If `x ∈ A` has `2x = nstar`, then `x` participates in an `nstar`-pair. -/
theorem mem_pairElements_of_self_pair {A : Finset ℕ} {nstar x : ℕ}
    (hxA : x ∈ A) (h2x : 2 * x = nstar) :
    x ∈ pairElements A nstar := by
  unfold pairElements
  rw [Finset.mem_union]
  left
  rw [Finset.mem_image]
  refine ⟨(x, x), ?_, rfl⟩
  rw [mem_sumReprsFinset]
  exact ⟨hxA, hxA, le_rfl, by omega⟩

/-- An extra point cannot be the midpoint self-pair of the exception axis. -/
theorem extra_not_self_pair {A : Finset ℕ} {nstar x : ℕ}
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar) :
    2 * x ≠ nstar := by
  intro h2x
  exact hxExtra (mem_pairElements_of_self_pair hxA h2x)

/-- If `x` is extra, then any `nstar`-reflection of `x` is absent from `A`. -/
theorem reflection_not_mem_of_extra {A : Finset ℕ} {nstar x y : ℕ}
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) :
    y ∉ A := by
  intro hyA
  have hxPE : x ∈ pairElements A nstar := by
    unfold pairElements
    rw [Finset.mem_union]
    rcases le_or_gt x y with hle | hgt
    · left
      rw [Finset.mem_image]
      refine ⟨(x, y), ?_, rfl⟩
      rw [mem_sumReprsFinset]
      exact ⟨hxA, hyA, hle, hxy⟩
    · right
      rw [Finset.mem_image]
      refine ⟨(y, x), ?_, rfl⟩
      rw [mem_sumReprsFinset]
      exact ⟨hyA, hxA, le_of_lt hgt, by omega⟩
  exact hxExtra hxPE

/-- The missing reflection of an extra is not the midpoint of the exception
axis. -/
theorem two_mul_reflection_ne_exception_of_extra
    {A : Finset ℕ} {nstar x y : ℕ}
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) :
    2 * y ≠ nstar := by
  intro h2y
  have hxy_eq : x = y := by omega
  have h2x : 2 * x = nstar := by omega
  exact extra_not_self_pair hxA hxExtra h2x

/-- Elements of `A` that do not participate in any `nstar`-pair. -/
def extraElements (A : Finset ℕ) (nstar : ℕ) : Finset ℕ :=
  A \ pairElements A nstar

@[simp] theorem mem_extraElements {A : Finset ℕ} {nstar x : ℕ} :
    x ∈ extraElements A nstar ↔ x ∈ A ∧ x ∉ pairElements A nstar := by
  simp [extraElements]

/-! ## Extra defect

The shadow lemmas below are most useful when phrased quantitatively.  The
`extraDefect` is the exact number of elements of `A` not covered by the
exception-axis pairs.  Later, the R4 counting lemmas identify this same number
with the saturation deficit from the Erdős-Freud half-multiplicity identity. -/

/-- The number of elements of `A` not participating in an `nstar`-pair. -/
def extraDefect (A : Finset ℕ) (nstar : ℕ) : ℕ :=
  (extraElements A nstar).card

@[simp] theorem extraDefect_eq_zero {A : Finset ℕ} {nstar : ℕ} :
    extraDefect A nstar = 0 ↔ extraElements A nstar = ∅ := by
  simp [extraDefect]

/-- The extra defect is exactly the complement of the paired elements inside
`A`. -/
theorem extraDefect_add_pairElements_card (A : Finset ℕ) (nstar : ℕ) :
    extraDefect A nstar + (pairElements A nstar).card = A.card := by
  classical
  have h_pair_sub : pairElements A nstar ⊆ A := pairElements_subset A nstar
  have hdisj : Disjoint (extraElements A nstar) (pairElements A nstar) := by
    rw [Finset.disjoint_left]
    intro x hx hpe
    rw [mem_extraElements] at hx
    exact hx.2 hpe
  have hunion : extraElements A nstar ∪ pairElements A nstar = A := by
    ext x
    rw [Finset.mem_union, mem_extraElements]
    constructor
    · intro hx
      rcases hx with h | h
      · exact h.1
      · exact h_pair_sub h
    · intro hxA
      by_cases hxPE : x ∈ pairElements A nstar
      · exact Or.inr hxPE
      · exact Or.inl ⟨hxA, hxPE⟩
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  simpa [extraDefect] using hcard.symm

/-- Difference form of the extra-defect decomposition. -/
theorem extraDefect_eq_card_sub_pairElements_card (A : Finset ℕ) (nstar : ℕ) :
    extraDefect A nstar = A.card - (pairElements A nstar).card := by
  have h := extraDefect_add_pairElements_card A nstar
  omega

/-- If the extra defect is at most one and one extra is specified, then it is
the unique extra. -/
theorem unique_extra_of_extraDefect_le_one
    {A : Finset ℕ} {nstar x : ℕ}
    (hxExtra : x ∈ extraElements A nstar)
    (hdef : extraDefect A nstar ≤ 1) :
    ∀ z ∈ extraElements A nstar, z = x := by
  intro z hz
  by_contra hzx
  have hsub : ({x, z} : Finset ℕ) ⊆ extraElements A nstar := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hxExtra
    · exact hz
  have htwo : 2 ≤ (extraElements A nstar).card := by
    have hcard_pair : ({x, z} : Finset ℕ).card = 2 := by
      have hxz : x ≠ z := Ne.symm hzx
      simp [hxz]
    calc
      2 = ({x, z} : Finset ℕ).card := hcard_pair.symm
      _ ≤ (extraElements A nstar).card := Finset.card_le_card hsub
  have hcard_le : (extraElements A nstar).card ≤ 1 := by
    simpa [extraDefect] using hdef
  omega

/-- A translate shadow for a missing reflection cannot be made entirely from
paired elements: at least one of the anchor `a` and old-pair endpoints `b, c`
is extra.

If all three participated in `nstar`-pairs, reflecting the equation
`y + a = b + c` across the exception axis would give an off-axis old
representation of `x + (nstar - a)`. R3 would force the reflected old pair to
equal the sorted pair containing `x` and `nstar - a`, so one of `b, c` would
have to equal the missing point `y`. -/
theorem translateShadow_forces_extra_participant
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxy : x + y = nstar) (hyA : y ∉ A)
    (hT : TranslateShadow A nstar y a b c) :
    a ∉ pairElements A nstar ∨
      b ∉ pairElements A nstar ∨ c ∉ pairElements A nstar := by
  rcases hT with ⟨haA, hbA, hcA, hbc, hsum, hne⟩
  by_cases haPE : a ∈ pairElements A nstar
  · by_cases hbPE : b ∈ pairElements A nstar
    · by_cases hcPE : c ∈ pairElements A nstar
      · have ha_le : a ≤ nstar := le_nstar_of_mem_pairElements haPE
        have hb_le : b ≤ nstar := le_nstar_of_mem_pairElements hbPE
        have hc_le : c ≤ nstar := le_nstar_of_mem_pairElements hcPE
        have ha_refl : nstar - a ∈ A := pairElements_has_reflection haPE
        have hb_refl : nstar - b ∈ A := pairElements_has_reflection hbPE
        have hc_refl : nstar - c ∈ A := pairElements_has_reflection hcPE
        have h_ref_sort : nstar - c ≤ nstar - b := by omega
        have h_ref_sum : (nstar - c) + (nstar - b) = x + (nstar - a) := by
          omega
        have h_ref_ne : x + (nstar - a) ≠ nstar := by
          intro haxis
          have ha_eq_x : a = x := by omega
          exact hne (by omega)
        rcases le_or_gt x (nstar - a) with hxa | hax
        · have huniq :=
            r3_off_axis_unique_representation A hA h_exception
              (x + (nstar - a)) h_ref_ne
              (nstar - c) (nstar - b) x (nstar - a)
              hc_refl hb_refl hxA ha_refl h_ref_sort hxa h_ref_sum rfl
          have hc_eq_y : c = y := by omega
          have hy_mem : y ∈ A := by rwa [hc_eq_y] at hcA
          exact (hyA hy_mem).elim
        · have hax_le : nstar - a ≤ x := le_of_lt hax
          have h_pair_sum : (nstar - a) + x = x + (nstar - a) := by omega
          have huniq :=
            r3_off_axis_unique_representation A hA h_exception
              (x + (nstar - a)) h_ref_ne
              (nstar - c) (nstar - b) (nstar - a) x
              hc_refl hb_refl ha_refl hxA h_ref_sort hax_le h_ref_sum h_pair_sum
          have hb_eq_y : b = y := by omega
          have hy_mem : y ∈ A := by rwa [hb_eq_y] at hbA
          exact (hyA hy_mem).elim
      · exact Or.inr (Or.inr hcPE)
    · exact Or.inr (Or.inl hbPE)
  · exact Or.inl haPE

/-- Endpoint version of the paired-anchor obstruction.  If `x + y = nstar`,
`x` is extra, the translate equation `y + a = d + e` holds, and both the anchor
`a` and endpoint `d` are paired, then contradiction.

Reflecting `d` across the exception axis turns the translate equation into
`a + (nstar - d) = x + e`.  This is off-axis; otherwise `a = d` and hence
`e = y`.  R3 then forces either `a = x` (so `x` is paired) or
`nstar - d = x` (so `d = y`). -/
theorem translateShadow_pairedAnchor_endpoint_not_pairElements
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a d e : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (haA : a ∈ A) (hdA : d ∈ A) (heA : e ∈ A)
    (haPE : a ∈ pairElements A nstar)
    (hdPE : d ∈ pairElements A nstar)
    (hsum : y + a = d + e) :
    False := by
  have hd_le : d ≤ nstar := le_nstar_of_mem_pairElements hdPE
  have hd_refl : nstar - d ∈ A := pairElements_has_reflection hdPE
  have h_ref_sum : a + (nstar - d) = x + e := by
    omega
  have h_ref_ne : a + (nstar - d) ≠ nstar := by
    intro haxis
    have had : a = d := by omega
    have he_eq_y : e = y := by omega
    have hy_mem : y ∈ A := by rwa [he_eq_y] at heA
    exact hyA hy_mem
  rcases le_or_gt a (nstar - d) with had_sort | hda_sort
  · rcases le_or_gt x e with hxe_sort | hex_sort
    · have huniq :=
        r3_off_axis_unique_representation A hA h_exception
          (a + (nstar - d)) h_ref_ne
          a (nstar - d) x e
          haA hd_refl hxA heA had_sort hxe_sort rfl (by omega)
      have hxPE : x ∈ pairElements A nstar := by
        simpa [huniq.1] using haPE
      exact hxExtra hxPE
    · have hex_le : e ≤ x := le_of_lt hex_sort
      have huniq :=
        r3_off_axis_unique_representation A hA h_exception
          (a + (nstar - d)) h_ref_ne
          a (nstar - d) e x
          haA hd_refl heA hxA had_sort hex_le rfl (by omega)
      have hd_eq_y : d = y := by omega
      have hy_mem : y ∈ A := by rwa [hd_eq_y] at hdA
      exact hyA hy_mem
  · have hda_le : nstar - d ≤ a := le_of_lt hda_sort
    rcases le_or_gt x e with hxe_sort | hex_sort
    · have huniq :=
        r3_off_axis_unique_representation A hA h_exception
          (a + (nstar - d)) h_ref_ne
          (nstar - d) a x e
          hd_refl haA hxA heA hda_le hxe_sort (by omega) (by omega)
      have hd_eq_y : d = y := by omega
      have hy_mem : y ∈ A := by rwa [hd_eq_y] at hdA
      exact hyA hy_mem
    · have hex_le : e ≤ x := le_of_lt hex_sort
      have huniq :=
        r3_off_axis_unique_representation A hA h_exception
          (a + (nstar - d)) h_ref_ne
          (nstar - d) a e x
          hd_refl haA heA hxA hda_le hex_le (by omega) (by omega)
      have hxPE : x ∈ pairElements A nstar := by
        simpa [huniq.2] using haPE
      exact hxExtra hxPE

/-- Strong endpoint obstruction for translate shadows.  If `y` is the missing
reflection of `x`, then no endpoint of an old pair blocking `y + a` can be
paired on the exception axis.

Reflecting a paired endpoint `d` turns `y + a = d + e` into the old
off-axis collision `(nstar - d) + a = x + e`.  R3 then forces either
`a = x`, which would put `y + a` back on the exception axis, or `d = y`,
contradicting that `y` is missing. -/
theorem translateShadow_endpoint_not_pairElements
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a d e : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxy : x + y = nstar) (hyA : y ∉ A)
    (haA : a ∈ A) (hdA : d ∈ A) (heA : e ∈ A)
    (hsum : y + a = d + e) (hne : y + a ≠ nstar)
    (hdPE : d ∈ pairElements A nstar) :
    False := by
  have hd_le : d ≤ nstar := le_nstar_of_mem_pairElements hdPE
  have hd_refl : nstar - d ∈ A := pairElements_has_reflection hdPE
  have h_ref_sum : (nstar - d) + a = x + e := by
    omega
  have h_ref_ne : (nstar - d) + a ≠ nstar := by
    intro haxis
    have had : a = d := by omega
    have he_eq_y : e = y := by omega
    have hy_mem : y ∈ A := by rwa [he_eq_y] at heA
    exact hyA hy_mem
  rcases le_or_gt (nstar - d) a with hda_sort | had_sort
  · rcases le_or_gt x e with hxe_sort | hex_sort
    · have huniq :=
        r3_off_axis_unique_representation A hA h_exception
          ((nstar - d) + a) h_ref_ne
          (nstar - d) a x e
          hd_refl haA hxA heA hda_sort hxe_sort rfl h_ref_sum.symm
      have hd_eq_y : d = y := by omega
      have hy_mem : y ∈ A := by rwa [hd_eq_y] at hdA
      exact hyA hy_mem
    · have hex_le : e ≤ x := le_of_lt hex_sort
      have huniq :=
        r3_off_axis_unique_representation A hA h_exception
          ((nstar - d) + a) h_ref_ne
          (nstar - d) a e x
          hd_refl haA heA hxA hda_sort hex_le rfl (by omega)
      exact hne (by omega)
  · have had_le : a ≤ nstar - d := le_of_lt had_sort
    rcases le_or_gt x e with hxe_sort | hex_sort
    · have huniq :=
        r3_off_axis_unique_representation A hA h_exception
          (a + (nstar - d)) (by omega)
          a (nstar - d) x e
          haA hd_refl hxA heA had_le hxe_sort rfl (by omega)
      exact hne (by omega)
    · have hex_le : e ≤ x := le_of_lt hex_sort
      have huniq :=
        r3_off_axis_unique_representation A hA h_exception
          (a + (nstar - d)) (by omega)
          a (nstar - d) e x
          haA hd_refl heA hxA had_le hex_le rfl (by omega)
      have hd_eq_y : d = y := by omega
      have hy_mem : y ∈ A := by rwa [hd_eq_y] at hdA
      exact hyA hy_mem

/-- Consequently, both endpoints of any translate-shadow old pair for a
missing reflection are extras. -/
theorem translateShadow_forces_oldPair_endpoints_extra
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxy : x + y = nstar) (hyA : y ∉ A)
    (hT : TranslateShadow A nstar y a b c) :
    b ∉ pairElements A nstar ∧ c ∉ pairElements A nstar := by
  rcases hT with ⟨haA, hbA, hcA, _hbc, hsum, hne⟩
  constructor
  · intro hbPE
    exact translateShadow_endpoint_not_pairElements hA h_exception hxA hxy hyA
      haA hbA hcA hsum hne hbPE
  · intro hcPE
    exact translateShadow_endpoint_not_pairElements hA h_exception hxA hxy hyA
      haA hcA hbA (by omega) hne hcPE

/-- An unpaired translate anchor is a genuine move to a distinct extra.  This
is the directed-edge packaging for the residual translate-shadow graph. -/
theorem unpairedAnchor_translateShadow_moves_to_distinct_extra
    {A : Finset ℕ} {nstar x y a b c : ℕ}
    (hxy : x + y = nstar)
    (haExtra : a ∉ pairElements A nstar)
    (hT : TranslateShadow A nstar y a b c) :
    a ∈ extraElements A nstar ∧ a ≠ x := by
  rcases hT with ⟨haA, _hbA, _hcA, _hbc, _hsum, hne⟩
  constructor
  · rw [mem_extraElements]
    exact ⟨haA, haExtra⟩
  · intro hax
    exact hne (by omega)

/-- If the anchor of a translate shadow is paired, then both old-pair endpoints
are extras. -/
theorem translateShadow_pairedAnchor_forces_oldPair_endpoints_extra
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (haPE : a ∈ pairElements A nstar)
    (hT : TranslateShadow A nstar y a b c) :
    b ∉ pairElements A nstar ∧ c ∉ pairElements A nstar := by
  rcases hT with ⟨haA, hbA, hcA, _hbc, hsum, _hne⟩
  constructor
  · intro hbPE
    exact translateShadow_pairedAnchor_endpoint_not_pairElements hA h_exception
      hxA hxExtra hxy hyA haA hbA hcA haPE hbPE hsum
  · intro hcPE
    exact translateShadow_pairedAnchor_endpoint_not_pairElements hA h_exception
      hxA hxExtra hxy hyA haA hcA hbA haPE hcPE (by omega)

/-- If `x` is the unique extra, every translate shadow for its missing
reflection is forced into the rigid self-pair shape `y + a = x + x`, with a
paired anchor `a`. -/
theorem uniqueExtra_translateShadow_forces_selfPair
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar)
    (hunique : ∀ z ∈ extraElements A nstar, z = x)
    (hT : TranslateShadow A nstar y a b c) :
    a ∈ pairElements A nstar ∧ b = x ∧ c = x ∧ y + a = 2 * x := by
  rw [mem_extraElements] at hxExtra
  rcases hT with ⟨haA, hbA, hcA, hbc, hsum, hne⟩
  have hyA : y ∉ A := reflection_not_mem_of_extra hxExtra.1 hxExtra.2 hxy
  have haPE : a ∈ pairElements A nstar := by
    by_contra haExtra
    have haExtraElem : a ∈ extraElements A nstar := by
      rw [mem_extraElements]
      exact ⟨haA, haExtra⟩
    have ha_eq_x : a = x := hunique a haExtraElem
    exact hne (by omega)
  have hendpoints :=
    translateShadow_pairedAnchor_forces_oldPair_endpoints_extra hA h_exception
      hxExtra.1 hxExtra.2 hxy hyA haPE ⟨haA, hbA, hcA, hbc, hsum, hne⟩
  have hbExtraElem : b ∈ extraElements A nstar := by
    rw [mem_extraElements]
    exact ⟨hbA, hendpoints.1⟩
  have hcExtraElem : c ∈ extraElements A nstar := by
    rw [mem_extraElements]
    exact ⟨hcA, hendpoints.2⟩
  have hb_eq_x : b = x := hunique b hbExtraElem
  have hc_eq_x : c = x := hunique c hcExtraElem
  exact ⟨haPE, hb_eq_x, hc_eq_x, by omega⟩

/-- In a maximal set with a unique extra, every in-range missing reflection has
a very rigid shadow: either a self-shadow at `2y`, or a translate shadow of the
form `y + a = 2x` with paired anchor `a`. -/
theorem uniqueExtra_maximal_missingReflection_shadow_shape
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hunique : ∀ z ∈ extraElements A nstar, z = x) :
    (∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar) ∨
      ∃ a ∈ A, a ∈ pairElements A nstar ∧ y + a = 2 * x ∧ y + a ≠ nstar := by
  have hxExtra_unpacked : x ∈ A ∧ x ∉ pairElements A nstar := by
    rw [mem_extraElements] at hxExtra
    exact hxExtra
  have hyA : y ∉ A :=
    reflection_not_mem_of_extra hxExtra_unpacked.1 hxExtra_unpacked.2 hxy
  rcases maximal_missing_point_has_shadow hmax h_exception hyN hyA with
    ⟨b, hb, c, hc, hsum, hne⟩ | ⟨a, ha, b, hb, c, hc, hsum, hne⟩
  · exact Or.inl ⟨b, hb, c, hc, hsum, hne⟩
  · rcases translateShadow_of_blocker ha hb hc hsum hne with ⟨b', c', hT⟩
    have hshape :=
      uniqueExtra_translateShadow_forces_selfPair hmax.1.1 h_exception
        (by rw [mem_extraElements]; exact hxExtra_unpacked) hxy hunique hT
    exact Or.inr ⟨a, ha, hshape.1, hshape.2.2.2, hne⟩

/-- If the self-shadow branch is absent in the unique-extra situation, the
translate shadow has the exact self-pair shape `y + a = 2x`. -/
theorem uniqueExtra_noSelf_maximal_missingReflection_translate_selfPair
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hunique : ∀ z ∈ extraElements A nstar, z = x)
    (hNoSelf : ¬ ∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar) :
    ∃ a ∈ A, a ∈ pairElements A nstar ∧ y + a = 2 * x ∧ y + a ≠ nstar := by
  rcases uniqueExtra_maximal_missingReflection_shadow_shape
      hmax h_exception hxExtra hxy hyN hunique with hself | htranslate
  · exact (hNoSelf hself).elim
  · exact htranslate

/-- In the unique-extra situation, the rigid translate shape collapses back to
a self-shadow by reflecting its paired anchor. -/
theorem uniqueExtra_translateSelfPair_gives_selfShadow
    {A : Finset ℕ} {nstar x y a : ℕ}
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar)
    (haPE : a ∈ pairElements A nstar)
    (hshape : y + a = 2 * x) :
    ∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar := by
  have hxExtra_unpacked : x ∈ A ∧ x ∉ pairElements A nstar := by
    rw [mem_extraElements] at hxExtra
    exact hxExtra
  have ha_le : a ≤ nstar := le_nstar_of_mem_pairElements haPE
  have ha_refl : nstar - a ∈ A := pairElements_has_reflection haPE
  have h2y_ne : 2 * y ≠ nstar :=
    two_mul_reflection_ne_exception_of_extra hxExtra_unpacked.1 hxExtra_unpacked.2 hxy
  refine ⟨x, hxExtra_unpacked.1, nstar - a, ha_refl, ?_, h2y_ne⟩
  omega

/-- A unique extra with an in-range missing reflection always has a self-shadow
blocker.  The translate alternative from maximality collapses to a self-shadow
by reflecting the paired anchor. -/
theorem uniqueExtra_maximal_missingReflection_has_selfShadow
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hunique : ∀ z ∈ extraElements A nstar, z = x) :
    ∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar := by
  rcases uniqueExtra_maximal_missingReflection_shadow_shape
      hmax h_exception hxExtra hxy hyN hunique with hself | htranslate
  · exact hself
  · rcases htranslate with ⟨a, _haA, haPE, hshape, _hne⟩
    exact uniqueExtra_translateSelfPair_gives_selfShadow hxExtra hxy haPE hshape

/-- Therefore the no-self-shadow unique-extra middle escape is impossible. -/
theorem uniqueExtra_noSelf_maximal_missingReflection_false
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hunique : ∀ z ∈ extraElements A nstar, z = x)
    (hNoSelf : ¬ ∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar) :
    False := by
  exact hNoSelf
    (uniqueExtra_maximal_missingReflection_has_selfShadow
      hmax h_exception hxExtra hxy hyN hunique)

/-- If `x` is the least extra, then every translate shadow for its missing
reflection contains an extra participant no smaller than `x`. -/
theorem translateShadow_has_large_extra_participant_of_leastExtra
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxy : x + y = nstar) (hyA : y ∉ A)
    (hleast : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z)
    (hT : TranslateShadow A nstar y a b c) :
    ∃ z ∈ A, z ∉ pairElements A nstar ∧ x ≤ z ∧
      (z = a ∨ z = b ∨ z = c) := by
  rcases hT with ⟨haA, hbA, hcA, _hbc, _hsum, _hne⟩
  have h_participant :=
    translateShadow_forces_extra_participant hA h_exception hxA hxy hyA
      ⟨haA, hbA, hcA, _hbc, _hsum, _hne⟩
  rcases h_participant with haExtra | hbExtra | hcExtra
  · exact ⟨a, haA, haExtra, hleast a haA haExtra, Or.inl rfl⟩
  · exact ⟨b, hbA, hbExtra, hleast b hbA hbExtra, Or.inr (Or.inl rfl)⟩
  · exact ⟨c, hcA, hcExtra, hleast c hcA hcExtra, Or.inr (Or.inr rfl)⟩

/-- If a translate shadow for the missing reflection of `x` has a paired
anchor and the old pair contains `x`, then it secretly gives a self-shadow
blocker for `y`.

Algebraically, from `y + a = x + d` and `x + y = nstar`, the reflected anchor
`nstar - a` satisfies `d + (nstar - a) = 2y`. -/
theorem translateShadow_contains_x_with_pairedAnchor_gives_selfShadow
    {A : Finset ℕ} {nstar x y a b c : ℕ}
    (hxy : x + y = nstar)
    (haPE : a ∈ pairElements A nstar)
    (hT : TranslateShadow A nstar y a b c)
    (hcontains : b = x ∨ c = x) :
    ∃ d ∈ A, ∃ e ∈ A, d + e = 2 * y := by
  rcases hT with ⟨_haA, hbA, hcA, _hbc, hsum, _hne⟩
  have ha_le : a ≤ nstar := le_nstar_of_mem_pairElements haPE
  have ha_refl : nstar - a ∈ A := pairElements_has_reflection haPE
  rcases hcontains with hbx | hcx
  · refine ⟨c, hcA, nstar - a, ha_refl, ?_⟩
    omega
  · refine ⟨b, hbA, nstar - a, ha_refl, ?_⟩
    omega

/-- If the missing reflection of an extra is blocked by a self-shadow
`b + c = 2y`, then at least one endpoint of that old pair is itself extra.

The proof reflects the pair `(b, c)` across the exception axis.  If both
endpoints were paired, the reflected pair would be an old representation of
`2x`; off-axis uniqueness then forces it to be the self-pair `(x, x)`, hence
`b = c = y`, contradicting that `y` is missing. -/
theorem selfShadow_forces_extra_endpoint
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (hbA : b ∈ A) (hcA : c ∈ A)
    (hself : b + c = 2 * y) :
    b ∉ pairElements A nstar ∨ c ∉ pairElements A nstar := by
  by_cases hbPE : b ∈ pairElements A nstar
  · by_cases hcPE : c ∈ pairElements A nstar
    · have hb_le : b ≤ nstar := le_nstar_of_mem_pairElements hbPE
      have hc_le : c ≤ nstar := le_nstar_of_mem_pairElements hcPE
      have hb_refl : nstar - b ∈ A := pairElements_has_reflection hbPE
      have hc_refl : nstar - c ∈ A := pairElements_has_reflection hcPE
      have h2x_ne : 2 * x ≠ nstar := extra_not_self_pair hxA hxExtra
      have h_refl_sum : (nstar - c) + (nstar - b) = 2 * x := by
        omega
      rcases le_or_gt (nstar - c) (nstar - b) with hle | hgt
      · have huniq :=
          r3_off_axis_unique_representation A hA h_exception (2 * x) h2x_ne
            (nstar - c) (nstar - b) x x
            hc_refl hb_refl hxA hxA hle le_rfl h_refl_sum (by omega)
        have hc_eq_y : c = y := by omega
        have hy_mem : y ∈ A := by rwa [hc_eq_y] at hcA
        exact (hyA hy_mem).elim
      · have hle' : nstar - b ≤ nstar - c := le_of_lt hgt
        have h_refl_sum' : (nstar - b) + (nstar - c) = 2 * x := by
          omega
        have huniq :=
          r3_off_axis_unique_representation A hA h_exception (2 * x) h2x_ne
            (nstar - b) (nstar - c) x x
            hb_refl hc_refl hxA hxA hle' le_rfl h_refl_sum' (by omega)
        have hb_eq_y : b = y := by omega
        have hy_mem : y ∈ A := by rwa [hb_eq_y] at hbA
        exact (hyA hy_mem).elim
    · exact Or.inr hcPE
  · exact Or.inl hbPE

/-- In the unique-extra situation, any self-shadow blocker for the missing
reflection contains `x`; the other endpoint is paired. -/
theorem uniqueExtra_selfShadow_forces_x_and_paired_endpoint
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar)
    (hunique : ∀ z ∈ extraElements A nstar, z = x)
    (hbA : b ∈ A) (hcA : c ∈ A)
    (hself : b + c = 2 * y) :
    (b = x ∧ c ∈ pairElements A nstar) ∨
      (c = x ∧ b ∈ pairElements A nstar) := by
  have hxExtra_unpacked : x ∈ A ∧ x ∉ pairElements A nstar := by
    rw [mem_extraElements] at hxExtra
    exact hxExtra
  have hyA : y ∉ A :=
    reflection_not_mem_of_extra hxExtra_unpacked.1 hxExtra_unpacked.2 hxy
  have hendpoint :=
    selfShadow_forces_extra_endpoint hA h_exception hxExtra_unpacked.1
      hxExtra_unpacked.2 hxy hyA hbA hcA hself
  rcases hendpoint with hbExtra | hcExtra
  · have hbExtraElem : b ∈ extraElements A nstar := by
      rw [mem_extraElements]
      exact ⟨hbA, hbExtra⟩
    have hb_eq_x : b = x := hunique b hbExtraElem
    have hcPE : c ∈ pairElements A nstar := by
      by_contra hcExtra
      have hcExtraElem : c ∈ extraElements A nstar := by
        rw [mem_extraElements]
        exact ⟨hcA, hcExtra⟩
      have hc_eq_x : c = x := hunique c hcExtraElem
      have h2x : 2 * x = nstar := by
        have h2y_ne : 2 * y ≠ nstar :=
          two_mul_reflection_ne_exception_of_extra hxExtra_unpacked.1
            hxExtra_unpacked.2 hxy
        omega
      exact extra_not_self_pair hxExtra_unpacked.1 hxExtra_unpacked.2 h2x
    exact Or.inl ⟨hb_eq_x, hcPE⟩
  · have hcExtraElem : c ∈ extraElements A nstar := by
      rw [mem_extraElements]
      exact ⟨hcA, hcExtra⟩
    have hc_eq_x : c = x := hunique c hcExtraElem
    have hbPE : b ∈ pairElements A nstar := by
      by_contra hbExtra
      have hbExtraElem : b ∈ extraElements A nstar := by
        rw [mem_extraElements]
        exact ⟨hbA, hbExtra⟩
      have hb_eq_x : b = x := hunique b hbExtraElem
      have h2x : 2 * x = nstar := by
        have h2y_ne : 2 * y ≠ nstar :=
          two_mul_reflection_ne_exception_of_extra hxExtra_unpacked.1
            hxExtra_unpacked.2 hxy
        omega
      exact extra_not_self_pair hxExtra_unpacked.1 hxExtra_unpacked.2 h2x
    exact Or.inr ⟨hc_eq_x, hbPE⟩

/-- Maximality plus a unique extra gives a paired endpoint `d` with
`x + d = 2y`. -/
theorem uniqueExtra_maximal_missingReflection_has_paired_selfShadow_endpoint
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hunique : ∀ z ∈ extraElements A nstar, z = x) :
    ∃ d ∈ A, d ∈ pairElements A nstar ∧ x + d = 2 * y := by
  obtain ⟨b, hbA, c, hcA, hself, _hne⟩ :=
    uniqueExtra_maximal_missingReflection_has_selfShadow
      hmax h_exception hxExtra hxy hyN hunique
  have hshape :=
    uniqueExtra_selfShadow_forces_x_and_paired_endpoint hmax.1.1 h_exception
      hxExtra hxy hunique hbA hcA hself.symm
  rcases hshape with ⟨hb_eq_x, hcPE⟩ | ⟨hc_eq_x, hbPE⟩
  · exact ⟨c, hcA, hcPE, by omega⟩
  · exact ⟨b, hbA, hbPE, by omega⟩

/-- In the unique-extra case, the pinned self-shadow endpoint has a reflected
paired anchor on the exception axis.  Thus the local obstruction has the exact
shape `x + d = 2y`, `y + a = 2x`, and `a + d = nstar`. -/
theorem uniqueExtra_maximal_missingReflection_exact_pairEndpoints
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hunique : ∀ z ∈ extraElements A nstar, z = x) :
    ∃ d ∈ A, d ∈ pairElements A nstar ∧ x + d = 2 * y ∧
      ∃ a ∈ A, a ∈ pairElements A nstar ∧ y + a = 2 * x ∧
        a + d = nstar := by
  obtain ⟨d, hdA, hdPE, hxd⟩ :=
    uniqueExtra_maximal_missingReflection_has_paired_selfShadow_endpoint
      hmax h_exception hxExtra hxy hyN hunique
  have hd_le : d ≤ nstar := le_nstar_of_mem_pairElements hdPE
  have hd_reflA : nstar - d ∈ A := pairElements_has_reflection hdPE
  have hd_reflPE : nstar - d ∈ pairElements A nstar :=
    pairElements_reflection_mem hdPE
  exact ⟨d, hdA, hdPE, hxd, nstar - d, hd_reflA, hd_reflPE, by omega, by omega⟩

/-- Defect-one endpoint rigidity.  If the extra defect is at most one, then a
specified extra with an in-range missing reflection is forced into the exact
unique-extra endpoint configuration.

This is the finite stability form compatible with the `N = 9` counterexample:
defect one is not impossible, but it has the rigid endpoint shape. -/
theorem extraDefect_le_one_maximal_missingReflection_exact_pairEndpoints
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hdef : extraDefect A nstar ≤ 1) :
    ∃ d ∈ A, d ∈ pairElements A nstar ∧ x + d = 2 * y ∧
      ∃ a ∈ A, a ∈ pairElements A nstar ∧ y + a = 2 * x ∧
        a + d = nstar := by
  exact uniqueExtra_maximal_missingReflection_exact_pairEndpoints
    hmax h_exception hxExtra hxy hyN
      (unique_extra_of_extraDefect_le_one hxExtra hdef)

/-- Moving right on a fixed reflection axis preserves the high inequality:
if `x + y = z + yz = nstar`, `x < z`, and `2y < x`, then `2yz < z`. -/
theorem high_reflection_mono_right
    {nstar x y z yz : ℕ}
    (hxy : x + y = nstar) (hzy : z + yz = nstar)
    (hxz : x < z) (hhigh : 2 * y < x) :
    2 * yz < z := by
  omega

/-- Moving right on a fixed reflection axis keeps the reflection in the same
ambient interval, provided it stays positive. -/
theorem reflection_ground_mono_right
    {N nstar x y z yz : ℕ}
    (hxy : x + y = nstar) (hzy : z + yz = nstar)
    (hxz : x < z) (hyN : y ∈ ground N) (hyz_pos : 1 ≤ yz) :
    yz ∈ ground N := by
  rw [mem_ground] at hyN ⊢
  omega

/-- A finite set cannot have a strict successor above each of its elements. -/
theorem extraElements_empty_of_every_extra_has_larger
    {A : Finset ℕ} {nstar : ℕ}
    (hstep :
      ∀ x ∈ extraElements A nstar,
        ∃ z ∈ extraElements A nstar, x < z) :
    extraElements A nstar = ∅ := by
  classical
  by_contra hne
  have hE : (extraElements A nstar).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  let m := (extraElements A nstar).max' hE
  have hm : m ∈ extraElements A nstar :=
    (extraElements A nstar).max'_mem hE
  obtain ⟨z, hz, hmz⟩ := hstep m hm
  have hz_le : z ≤ m := (extraElements A nstar).le_max' z hz
  omega

/-- If all extras are high relative to their missing reflections, then any
specified reflection of an extra is high. -/
theorem high_of_allExtrasHigh
    {A : Finset ℕ} {nstar x y : ℕ}
    (hAllHigh :
      ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) :
    2 * y < x := by
  obtain ⟨yz, hyz, hyz_high⟩ := hAllHigh x hxExtra
  omega

/-- If every extra is high on the exception axis, then a high extra's missing
reflection cannot be blocked by a self-shadow. -/
theorem allExtrasHigh_no_selfShadow
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hAllHigh :
      ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (hhigh : 2 * y < x) :
    ¬ ∃ b ∈ A, ∃ c ∈ A, b + c = 2 * y := by
  intro hself
  have hxExtra_unpacked : x ∈ A ∧ x ∉ pairElements A nstar := by
    rw [mem_extraElements] at hxExtra
    exact hxExtra
  rcases hself with ⟨b, hbA, c, hcA, hbc⟩
  have hendpoint :=
    selfShadow_forces_extra_endpoint hA h_exception hxExtra_unpacked.1
      hxExtra_unpacked.2 hxy hyA hbA hcA hbc
  rcases hendpoint with hbExtra | hcExtra
  · have hbExtraElem : b ∈ extraElements A nstar := by
      rw [mem_extraElements]
      exact ⟨hbA, hbExtra⟩
    obtain ⟨yb, hbyb, hyb_high⟩ := hAllHigh b hbExtraElem
    omega
  · have hcExtraElem : c ∈ extraElements A nstar := by
      rw [mem_extraElements]
      exact ⟨hcA, hcExtra⟩
    obtain ⟨yc, hcyc, hyc_high⟩ := hAllHigh c hcExtraElem
    omega

/-- Under the all-extras-high hypothesis, a translate shadow for a high extra
cannot have a paired anchor. -/
theorem allExtrasHigh_no_pairedAnchor_translateShadow
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hAllHigh :
      ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (hhigh : 2 * y < x)
    (haPE : a ∈ pairElements A nstar)
    (hT : TranslateShadow A nstar y a b c) :
    False := by
  have hxExtra_unpacked : x ∈ A ∧ x ∉ pairElements A nstar := by
    rw [mem_extraElements] at hxExtra
    exact hxExtra
  rcases hT with ⟨haA, hbA, hcA, hbc, hsum, hne⟩
  have hendpoints :=
    translateShadow_pairedAnchor_forces_oldPair_endpoints_extra hA h_exception
      hxExtra_unpacked.1 hxExtra_unpacked.2 hxy hyA haPE
      ⟨haA, hbA, hcA, hbc, hsum, hne⟩
  have hbExtraElem : b ∈ extraElements A nstar := by
    rw [mem_extraElements]
    exact ⟨hbA, hendpoints.1⟩
  have hcExtraElem : c ∈ extraElements A nstar := by
    rw [mem_extraElements]
    exact ⟨hcA, hendpoints.2⟩
  obtain ⟨yb, hbyb, hyb_high⟩ := hAllHigh b hbExtraElem
  obtain ⟨yc, hcyc, hyc_high⟩ := hAllHigh c hcExtraElem
  have ha_le : a ≤ nstar := le_nstar_of_mem_pairElements haPE
  omega

/-- Under the all-extras-high hypothesis, a translate shadow whose anchor is
itself extra must have at least one paired endpoint.  Thus the remaining
unpaired-anchor shadows are mixed old pairs, not all-extra triples. -/
theorem allExtrasHigh_translateShadow_extraAnchor_has_paired_endpoint
    {A : Finset ℕ} {nstar x y a b c : ℕ}
    (hAllHigh :
      ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar)
    (haExtra : a ∈ extraElements A nstar)
    (hT : TranslateShadow A nstar y a b c) :
    b ∈ pairElements A nstar ∨ c ∈ pairElements A nstar := by
  rcases hT with ⟨_haA, hbA, hcA, _hbc, hsum, _hne⟩
  have hhigh : 2 * y < x :=
    high_of_allExtrasHigh hAllHigh hxExtra hxy
  by_contra hnone
  rw [not_or] at hnone
  have hbExtraElem : b ∈ extraElements A nstar := by
    rw [mem_extraElements]
    exact ⟨hbA, hnone.1⟩
  have hcExtraElem : c ∈ extraElements A nstar := by
    rw [mem_extraElements]
    exact ⟨hcA, hnone.2⟩
  obtain ⟨ya, haya, _hya_high⟩ := hAllHigh a haExtra
  obtain ⟨yb, hbyb, hyb_high⟩ := hAllHigh b hbExtraElem
  obtain ⟨yc, hcyc, hyc_high⟩ := hAllHigh c hcExtraElem
  omega

/-- Therefore, under the all-extras-high hypothesis, maximality forces every
in-range missing reflection of an extra to have an unpaired-anchor translate
shadow.  This isolates the remaining obstruction as an unpaired-anchor graph
problem. -/
theorem allExtrasHigh_maximal_missingReflection_has_unpaired_translateShadow
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hAllHigh :
      ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) :
    ∃ a ∈ A, a ∉ pairElements A nstar ∧
      ∃ b : ℕ, ∃ c : ℕ, TranslateShadow A nstar y a b c := by
  have hxExtra_unpacked : x ∈ A ∧ x ∉ pairElements A nstar := by
    rw [mem_extraElements] at hxExtra
    exact hxExtra
  have hyA : y ∉ A :=
    reflection_not_mem_of_extra hxExtra_unpacked.1 hxExtra_unpacked.2 hxy
  have hhigh : 2 * y < x :=
    high_of_allExtrasHigh hAllHigh hxExtra hxy
  have hNoSelf : ¬ ∃ b ∈ A, ∃ c ∈ A, b + c = 2 * y :=
    allExtrasHigh_no_selfShadow hmax.1.1 h_exception hAllHigh hxExtra hxy hyA hhigh
  obtain ⟨a, haA, b, c, hT⟩ :=
    maximal_missing_point_has_translateShadow hmax h_exception hyN hyA hNoSelf
  by_cases haPE : a ∈ pairElements A nstar
  · exact (allExtrasHigh_no_pairedAnchor_translateShadow hmax.1.1 h_exception
      hAllHigh hxExtra hxy hyA hhigh haPE hT).elim
  · exact ⟨a, haA, haPE, b, c, hT⟩

/-- Sharpened all-high residual form: the forced translate shadow has an extra
anchor and at least one paired endpoint. -/
theorem allExtrasHigh_maximal_missingReflection_has_mixed_translateShadow
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hAllHigh :
      ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) :
    ∃ a ∈ extraElements A nstar, ∃ b : ℕ, ∃ c : ℕ,
      TranslateShadow A nstar y a b c ∧
        (b ∈ pairElements A nstar ∨ c ∈ pairElements A nstar) := by
  obtain ⟨a, haA, haNotPE, b, c, hT⟩ :=
    allExtrasHigh_maximal_missingReflection_has_unpaired_translateShadow
      hmax h_exception hAllHigh hxExtra hxy hyN
  have haExtra : a ∈ extraElements A nstar := by
    rw [mem_extraElements]
    exact ⟨haA, haNotPE⟩
  have hendpoint :=
    allExtrasHigh_translateShadow_extraAnchor_has_paired_endpoint
      hAllHigh hxExtra hxy haExtra hT
  exact ⟨a, haExtra, b, c, hT, hendpoint⟩

/-- The all-extras-high regime has no in-range missing reflection for any
extra.  Maximality forces an unpaired-anchor translate shadow; all-high
arithmetic says such a shadow must have a paired endpoint, while R3 reflection
says translate-shadow endpoints for missing reflections are never paired. -/
theorem allExtrasHigh_maximal_missingReflection_false
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hAllHigh :
      ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) :
    False := by
  have hxExtra_unpacked : x ∈ A ∧ x ∉ pairElements A nstar := by
    rw [mem_extraElements] at hxExtra
    exact hxExtra
  have hyA : y ∉ A :=
    reflection_not_mem_of_extra hxExtra_unpacked.1 hxExtra_unpacked.2 hxy
  obtain ⟨a, _haExtra, b, c, hT, hpaired⟩ :=
    allExtrasHigh_maximal_missingReflection_has_mixed_translateShadow
      hmax h_exception hAllHigh
      (by rw [mem_extraElements]; exact hxExtra_unpacked) hxy hyN
  have hendpoints :=
    translateShadow_forces_oldPair_endpoints_extra hmax.1.1 h_exception
      hxExtra_unpacked.1 hxy hyA hT
  rcases hpaired with hbPE | hcPE
  · exact hendpoints.1 hbPE
  · exact hendpoints.2 hcPE

/-- Contrapositive packaging of
`allExtrasHigh_maximal_missingReflection_false`: an in-range missing reflection
of an extra prevents all extras from being high. -/
theorem not_allExtrasHigh_of_maximal_missingReflection
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) :
    ¬ ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z := by
  intro hAllHigh
  exact allExtrasHigh_maximal_missingReflection_false
    hmax h_exception hAllHigh hxExtra hxy hyN

/-- Concrete witness form: maximality forces some extra to be non-high on the
exception axis.  If the extra has an axis-reflection, it lies in the low/middle
region `z ≤ 2yz`; otherwise this theorem records the axis-overflow escape. -/
theorem exists_extra_not_high_of_maximal_missingReflection
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) :
    ∃ z ∈ extraElements A nstar,
      ∀ yz, z + yz = nstar → z ≤ 2 * yz := by
  classical
  by_contra hnone
  push Not at hnone
  have hAllHigh :
      ∀ z ∈ extraElements A nstar,
        ∃ yz, z + yz = nstar ∧ 2 * yz < z := by
    intro z hz
    obtain ⟨yz, hyz, hhigh⟩ := hnone z hz
    exact ⟨yz, hyz, hhigh⟩
  exact not_allExtrasHigh_of_maximal_missingReflection
    hmax h_exception hxExtra hxy hyN hAllHigh

/-- If every extra lies on or below the exception axis, then the previous
witness can be chosen with an actual low/middle reflection. -/
theorem exists_middle_extra_of_maximal_missingReflection
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hAxisBound : ∀ z ∈ extraElements A nstar, z ≤ nstar) :
    ∃ z ∈ extraElements A nstar, ∃ yz,
      z + yz = nstar ∧ z ≤ 2 * yz := by
  obtain ⟨z, hzExtra, hz_not_high⟩ :=
    exists_extra_not_high_of_maximal_missingReflection
      hmax h_exception hxExtra hxy hyN
  have hz_le : z ≤ nstar := hAxisBound z hzExtra
  refine ⟨z, hzExtra, nstar - z, ?_, ?_⟩
  · omega
  · exact hz_not_high (nstar - z) (by omega)

/-- In the high region `2y < x`, a self-shadow blocker descends to a smaller
extra. -/
theorem selfShadow_highExtra_descends
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (hhigh : 2 * y < x)
    (hself : ∃ b ∈ A, ∃ c ∈ A, b + c = 2 * y) :
    ∃ z ∈ A, z ∉ pairElements A nstar ∧ z < x := by
  rcases hself with ⟨b, hbA, c, hcA, hbc⟩
  have h_endpoint :=
    selfShadow_forces_extra_endpoint hA h_exception hxA hxExtra hxy hyA hbA hcA hbc
  rcases h_endpoint with hbExtra | hcExtra
  · refine ⟨b, hbA, hbExtra, ?_⟩
    omega
  · refine ⟨c, hcA, hcExtra, ?_⟩
    omega

/-- A least extra in the high region has no self-shadow blocker. -/
theorem leastExtra_no_high_selfShadow
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (hleast : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z)
    (hhigh : 2 * y < x) :
    ¬ ∃ b ∈ A, ∃ c ∈ A, b + c = 2 * y := by
  intro hself
  obtain ⟨z, hzA, hzExtra, hz_lt⟩ :=
    selfShadow_highExtra_descends hA h_exception hxA hxExtra hxy hyA hhigh hself
  exact (not_lt_of_ge (hleast z hzA hzExtra)) hz_lt

/-- A least high extra cannot appear inside a translate shadow with paired
anchor.  Such a shadow would produce a self-shadow, already ruled out by the
descent lemma. -/
theorem leastHighExtra_translateShadow_pairedAnchor_avoids_x
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (hleast : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z)
    (hhigh : 2 * y < x)
    (haPE : a ∈ pairElements A nstar)
    (hT : TranslateShadow A nstar y a b c) :
    b ≠ x ∧ c ≠ x := by
  have hNoSelf : ¬ ∃ d ∈ A, ∃ e ∈ A, d + e = 2 * y :=
    leastExtra_no_high_selfShadow hA h_exception hxA hxExtra hxy hyA hleast hhigh
  constructor
  · intro hbx
    exact hNoSelf
      (translateShadow_contains_x_with_pairedAnchor_gives_selfShadow
        hxy haPE hT (Or.inl hbx))
  · intro hcx
    exact hNoSelf
      (translateShadow_contains_x_with_pairedAnchor_gives_selfShadow
        hxy haPE hT (Or.inr hcx))

/-- With a paired anchor, a translate shadow for a least high extra must ascend:
one of the old-pair endpoints is a strictly larger extra. -/
theorem leastHighExtra_translateShadow_pairedAnchor_ascends
    {A : Finset ℕ} (hA : AlmostSidonFinset A)
    {nstar x y a b c : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyA : y ∉ A)
    (hleast : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z)
    (hhigh : 2 * y < x)
    (haPE : a ∈ pairElements A nstar)
    (hT : TranslateShadow A nstar y a b c) :
    ∃ z ∈ A, z ∉ pairElements A nstar ∧ x < z ∧ (z = b ∨ z = c) := by
  rcases hT with ⟨haA, hbA, hcA, hbc, hsum, hne⟩
  have havoid :=
    leastHighExtra_translateShadow_pairedAnchor_avoids_x hA h_exception
      hxA hxExtra hxy hyA hleast hhigh haPE ⟨haA, hbA, hcA, hbc, hsum, hne⟩
  have h_participant :=
    translateShadow_forces_extra_participant hA h_exception hxA hxy hyA
      ⟨haA, hbA, hcA, hbc, hsum, hne⟩
  rcases h_participant with haExtra | hbExtra | hcExtra
  · exact (haExtra haPE).elim
  · have hx_lt_b : x < b := lt_of_le_of_ne (hleast b hbA hbExtra) (Ne.symm havoid.1)
    exact ⟨b, hbA, hbExtra, hx_lt_b, Or.inl rfl⟩
  · have hx_lt_c : x < c := lt_of_le_of_ne (hleast c hcA hcExtra) (Ne.symm havoid.2)
    exact ⟨c, hcA, hcExtra, hx_lt_c, Or.inr rfl⟩

/-- In a maximal set, a least extra in the high region must be blocked by a
translate shadow.  The previous lemma rules out the self-shadow branch, and
maximality supplies the remaining translate branch. -/
theorem leastHighExtra_has_translateShadow
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hleast : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z)
    (hhigh : 2 * y < x) :
    ∃ a ∈ A, ∃ b : ℕ, ∃ c : ℕ, TranslateShadow A nstar y a b c := by
  have hNoSelf : ¬ ∃ b ∈ A, ∃ c ∈ A, b + c = 2 * y :=
    leastExtra_no_high_selfShadow hmax.1.1 h_exception hxA hxExtra hxy hyA hleast hhigh
  exact maximal_missing_point_has_translateShadow hmax h_exception hyN hyA hNoSelf

/-- A least high extra has a translate shadow with an extra participant. -/
theorem leastHighExtra_has_translateShadow_with_large_extra_participant
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hleast : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z)
    (hhigh : 2 * y < x) :
    ∃ a ∈ A, ∃ b : ℕ, ∃ c : ℕ,
      TranslateShadow A nstar y a b c ∧
        ∃ z ∈ A, z ∉ pairElements A nstar ∧ x ≤ z ∧
          (z = a ∨ z = b ∨ z = c) := by
  obtain ⟨a, ha, b, c, hT⟩ :=
    leastHighExtra_has_translateShadow hmax h_exception hxA hxExtra hxy hyN hyA hleast hhigh
  have hz :=
    translateShadow_has_large_extra_participant_of_leastExtra hmax.1.1 h_exception
      hxA hxy hyA hleast hT
  exact ⟨a, ha, b, c, hT, hz⟩

/-- Dichotomy for a least high extra: its forced translate shadow either touches
`x` itself, or it contains a strictly larger extra participant. -/
theorem leastHighExtra_translateShadow_touches_or_ascends
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hleast : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z)
    (hhigh : 2 * y < x) :
    ∃ a ∈ A, ∃ b : ℕ, ∃ c : ℕ,
      TranslateShadow A nstar y a b c ∧
        ((a = x ∨ b = x ∨ c = x) ∨
          ∃ z ∈ A, z ∉ pairElements A nstar ∧ x < z ∧
            (z = a ∨ z = b ∨ z = c)) := by
  obtain ⟨a, ha, b, c, hT, z, hzA, hzExtra, hx_le_z, hz_part⟩ :=
    leastHighExtra_has_translateShadow_with_large_extra_participant
      hmax h_exception hxA hxExtra hxy hyN hyA hleast hhigh
  by_cases hzx : z = x
  · have htouch : a = x ∨ b = x ∨ c = x := by
      rcases hz_part with hza | hzb | hzc
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    exact ⟨a, ha, b, c, hT, Or.inl htouch⟩
  · have hx_lt_z : x < z := lt_of_le_of_ne hx_le_z (Ne.symm hzx)
    exact ⟨a, ha, b, c, hT,
      Or.inr ⟨z, hzA, hzExtra, hx_lt_z, hz_part⟩⟩

/-- A least extra in the high region cannot be the largest extra: maximality
forces some strictly larger extra.

The forced translate shadow has either an unpaired anchor, which is itself a
larger extra since `a = x` would make `y + a = nstar`, or a paired anchor, in
which case the old-pair endpoint ascends by
`leastHighExtra_translateShadow_pairedAnchor_ascends`. -/
theorem leastHighExtra_forces_larger_extra
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxA : x ∈ A) (hxExtra : x ∉ pairElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hleast : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z)
    (hhigh : 2 * y < x) :
    ∃ z ∈ A, z ∉ pairElements A nstar ∧ x < z := by
  obtain ⟨a, haA, b, c, hT⟩ :=
    leastHighExtra_has_translateShadow hmax h_exception hxA hxExtra hxy hyN hyA hleast hhigh
  by_cases haPE : a ∈ pairElements A nstar
  · obtain ⟨z, hzA, hzExtra, hx_lt_z, _hz_part⟩ :=
      leastHighExtra_translateShadow_pairedAnchor_ascends hmax.1.1 h_exception
        hxA hxExtra hxy hyA hleast hhigh haPE hT
    exact ⟨z, hzA, hzExtra, hx_lt_z⟩
  · rcases hT with ⟨_haA, _hbA, _hcA, _hbc, _hsum, hne⟩
    have hax : a ≠ x := by
      intro hax
      exact hne (by omega)
    have hx_lt_a : x < a := lt_of_le_of_ne (hleast a haA haPE) (Ne.symm hax)
    exact ⟨a, haA, haPE, hx_lt_a⟩

/-- Finset form of `leastHighExtra_forces_larger_extra`: a least high extra
forces a strictly larger element of `extraElements`. -/
theorem leastHighExtra_forces_larger_extraElement
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hleast : ∀ z ∈ extraElements A nstar, x ≤ z)
    (hhigh : 2 * y < x) :
    ∃ z ∈ extraElements A nstar, x < z := by
  rw [mem_extraElements] at hxExtra
  have hleast' : ∀ z ∈ A, z ∉ pairElements A nstar → x ≤ z := by
    intro z hzA hzExtra
    exact hleast z (by rw [mem_extraElements]; exact ⟨hzA, hzExtra⟩)
  obtain ⟨z, hzA, hzExtra, hx_lt_z⟩ :=
    leastHighExtra_forces_larger_extra hmax h_exception hxExtra.1 hxExtra.2
      hxy hyN hyA hleast' hhigh
  exact ⟨z, by rw [mem_extraElements]; exact ⟨hzA, hzExtra⟩, hx_lt_z⟩

/-- Minimum-extra form: if the least extra is high and its reflection is in
range, then there is a larger extra. -/
theorem minExtra_high_forces_larger_extraElement
    {A : Finset ℕ} {N nstar y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hE : (extraElements A nstar).Nonempty) :
    let x := (extraElements A nstar).min' hE
    x + y = nstar → y ∈ ground N → 2 * y < x →
      ∃ z ∈ extraElements A nstar, x < z := by
  intro x hxy hyN hhigh
  have hxExtra : x ∈ extraElements A nstar := (extraElements A nstar).min'_mem hE
  have hxExtra_unpacked : x ∈ A ∧ x ∉ pairElements A nstar := by
    rw [mem_extraElements] at hxExtra
    exact hxExtra
  have hyA : y ∉ A :=
    reflection_not_mem_of_extra hxExtra_unpacked.1 hxExtra_unpacked.2 hxy
  have hleast : ∀ z ∈ extraElements A nstar, x ≤ z := by
    intro z hz
    exact (extraElements A nstar).min'_le z hz
  exact leastHighExtra_forces_larger_extraElement hmax h_exception hxExtra
    hxy hyN hyA hleast hhigh

/-- A least high extra cannot also be an upper bound for all extras. -/
theorem leastHighExtra_not_greatestExtra
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hleast : ∀ z ∈ extraElements A nstar, x ≤ z)
    (hgreatest : ∀ z ∈ extraElements A nstar, z ≤ x)
    (hhigh : 2 * y < x) :
    False := by
  obtain ⟨z, hzExtra, hx_lt_z⟩ :=
    leastHighExtra_forces_larger_extraElement hmax h_exception hxExtra hxy hyN hyA
      hleast hhigh
  exact (not_lt_of_ge (hgreatest z hzExtra)) hx_lt_z

/-- In particular, a high missing reflection cannot be the unique extra. -/
theorem uniqueExtra_not_high_missingReflection
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hunique : ∀ z ∈ extraElements A nstar, z = x)
    (hhigh : 2 * y < x) :
    False := by
  apply leastHighExtra_not_greatestExtra hmax h_exception hxExtra hxy hyN hyA
  · intro z hz
    have hz_eq : z = x := hunique z hz
    omega
  · intro z hz
    have hz_eq : z = x := hunique z hz
    omega
  · exact hhigh

/-- Cardinality form: if there is at most one extra, no extra can have an
in-range missing reflection in the high region. -/
theorem extraElements_card_le_one_not_high_missingReflection
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N) (hyA : y ∉ A)
    (hcard : (extraElements A nstar).card ≤ 1)
    (hhigh : 2 * y < x) :
    False := by
  have hdef : extraDefect A nstar ≤ 1 := by
    simpa [extraDefect] using hcard
  have hunique : ∀ z ∈ extraElements A nstar, z = x :=
    unique_extra_of_extraDefect_le_one hxExtra hdef
  exact uniqueExtra_not_high_missingReflection hmax h_exception hxExtra hxy hyN hyA
    hunique hhigh

/-! ## R4 saturation closes the extra set

The preceding local lemmas analyze what an unpaired element would have to do
under maximality.  The R4 saturation hypothesis is stronger: its counting
identity already forces every element of `A` to appear in an `nstar`-pair, so
the extra set is empty before any shadow analysis is needed. -/

/-- The R4 saturation deficit.  Without a self-pair, saturation means
`2 * r_A(nstar) = A.card`; with a self-pair, it means
`2 * r_A(nstar) = A.card + 1`.  This definition records the corresponding
finite deficit as a natural number. -/
def r4SaturationDefect (A : Finset ℕ) (nstar : ℕ) : ℕ :=
  if HasSelfPair A nstar then
    A.card + 1 - 2 * (sumReprsFinset A nstar).card
  else
    A.card - 2 * (sumReprsFinset A nstar).card

/-- No-self-pair form: the extra defect plus twice the `nstar` multiplicity
is exactly `A.card`. -/
theorem extraDefect_add_twice_sumReprs_card_no_self
    (A : Finset ℕ) (nstar : ℕ)
    (h_no_self : ¬ HasSelfPair A nstar) :
    extraDefect A nstar + 2 * (sumReprsFinset A nstar).card = A.card := by
  have h_extra := extraDefect_add_pairElements_card A nstar
  have h_pair : (pairElements A nstar).card =
      2 * (sumReprsFinset A nstar).card :=
    pairElements_card_no_self_pair A nstar h_no_self
  omega

/-- Self-pair form: the extra defect plus twice the `nstar` multiplicity is
`A.card + 1`, because the self-pair contributes one paired element but one
representation. -/
theorem extraDefect_add_twice_sumReprs_card_self
    (A : Finset ℕ) (nstar : ℕ)
    (h_self : HasSelfPair A nstar) :
    extraDefect A nstar + 2 * (sumReprsFinset A nstar).card = A.card + 1 := by
  rcases h_self with ⟨c, hc, h2c⟩
  have h_extra := extraDefect_add_pairElements_card A nstar
  have h_pair : (pairElements A nstar).card + 1 =
      2 * (sumReprsFinset A nstar).card :=
    pairElements_card_with_self_pair A nstar c hc h2c
  omega

/-- In the no-self-pair branch, the R4 saturation deficit is the extra
defect. -/
theorem extraDefect_eq_r4SaturationDefect_no_self
    (A : Finset ℕ) (nstar : ℕ)
    (h_no_self : ¬ HasSelfPair A nstar) :
    extraDefect A nstar =
      A.card - 2 * (sumReprsFinset A nstar).card := by
  have h := extraDefect_add_twice_sumReprs_card_no_self A nstar h_no_self
  omega

/-- In the self-pair branch, the R4 saturation deficit is the extra defect. -/
theorem extraDefect_eq_r4SaturationDefect_self
    (A : Finset ℕ) (nstar : ℕ)
    (h_self : HasSelfPair A nstar) :
    extraDefect A nstar =
      A.card + 1 - 2 * (sumReprsFinset A nstar).card := by
  have h := extraDefect_add_twice_sumReprs_card_self A nstar h_self
  omega

/-- The two notions of defect coincide: the number of unpaired elements is
exactly the finite deficit from R4 half-multiplicity saturation. -/
theorem extraDefect_eq_r4SaturationDefect (A : Finset ℕ) {nstar : ℕ} :
    extraDefect A nstar = r4SaturationDefect A nstar := by
  by_cases h_self : HasSelfPair A nstar
  · rw [r4SaturationDefect, if_pos h_self]
    exact extraDefect_eq_r4SaturationDefect_self A nstar h_self
  · rw [r4SaturationDefect, if_neg h_self]
    exact extraDefect_eq_r4SaturationDefect_no_self A nstar h_self

/-- Zero R4 defect recovers the R4 maximum-multiplicity alternatives. -/
theorem r4_saturation_of_r4SaturationDefect_zero
    (A : Finset ℕ) {nstar : ℕ}
    (hdef : r4SaturationDefect A nstar = 0) :
    (¬ HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card) ∨
      (HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card + 1) := by
  have hExtra0 : extraDefect A nstar = 0 := by
    rw [extraDefect_eq_r4SaturationDefect A]
    exact hdef
  by_cases h_self : HasSelfPair A nstar
  · right
    refine ⟨h_self, ?_⟩
    have h := extraDefect_add_twice_sumReprs_card_self A nstar h_self
    omega
  · left
    refine ⟨h_self, ?_⟩
    have h := extraDefect_add_twice_sumReprs_card_no_self A nstar h_self
    omega

/-- Near-saturation defect-one form of endpoint rigidity.  If the R4
saturation defect is at most one, then any specified extra with an in-range
missing reflection has the exact unique-extra endpoint shape. -/
theorem r4SaturationDefect_le_one_maximal_missingReflection_exact_pairEndpoints
    {A : Finset ℕ} {N nstar x y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hxExtra : x ∈ extraElements A nstar)
    (hxy : x + y = nstar) (hyN : y ∈ ground N)
    (hdef : r4SaturationDefect A nstar ≤ 1) :
    ∃ d ∈ A, d ∈ pairElements A nstar ∧ x + d = 2 * y ∧
      ∃ a ∈ A, a ∈ pairElements A nstar ∧ y + a = 2 * x ∧
        a + d = nstar := by
  apply extraDefect_le_one_maximal_missingReflection_exact_pairEndpoints
    hmax h_exception hxExtra hxy hyN
  rwa [extraDefect_eq_r4SaturationDefect A]

/-- Under the R4 maximum-multiplicity alternatives, the paired elements are
exactly the ambient set. -/
theorem pairElements_eq_of_r4_saturation
    (A : Finset ℕ) {nstar : ℕ}
    (h_max_mult :
      (¬ HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card) ∨
      (HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card + 1)) :
    pairElements A nstar = A := by
  classical
  have h_pe_sub : pairElements A nstar ⊆ A := pairElements_subset A nstar
  rcases h_max_mult with ⟨h_no_self, h_mm⟩ | ⟨⟨c, hc, h2c⟩, h_mm⟩
  · have h_pe_card : (pairElements A nstar).card =
        2 * (sumReprsFinset A nstar).card :=
      pairElements_card_no_self_pair A nstar h_no_self
    exact Finset.eq_of_subset_of_card_le h_pe_sub (by omega)
  · have h_pe_card : (pairElements A nstar).card + 1 =
        2 * (sumReprsFinset A nstar).card :=
      pairElements_card_with_self_pair A nstar c hc h2c
    exact Finset.eq_of_subset_of_card_le h_pe_sub (by omega)

/-- If the paired elements already exhaust `A`, then there are no extras. -/
theorem extraElements_empty_of_pairElements_eq
    {A : Finset ℕ} {nstar : ℕ}
    (h_pair : pairElements A nstar = A) :
    extraElements A nstar = ∅ := by
  ext x
  simp [extraElements, h_pair]

/-- R4 saturation rules out extras outright.  This is the formal endpoint for
the saturation branch of the maximality program. -/
theorem extraElements_empty_of_r4_saturation
    (A : Finset ℕ) {nstar : ℕ}
    (h_max_mult :
      (¬ HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card) ∨
      (HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card + 1)) :
    extraElements A nstar = ∅ := by
  exact extraElements_empty_of_pairElements_eq
    (pairElements_eq_of_r4_saturation A h_max_mult)

/-- Zero R4 saturation defect rules out extras.  This is the defect-language
version of `extraElements_empty_of_r4_saturation`. -/
theorem extraElements_empty_of_r4SaturationDefect_zero
    (A : Finset ℕ) {nstar : ℕ}
    (hdef : r4SaturationDefect A nstar = 0) :
    extraElements A nstar = ∅ := by
  exact extraElements_empty_of_r4_saturation A
    (r4_saturation_of_r4SaturationDefect_zero A hdef)

/-- The R4 saturation defect vanishes exactly when there are no extras. -/
theorem extraElements_empty_iff_r4SaturationDefect_zero
    (A : Finset ℕ) {nstar : ℕ} :
    extraElements A nstar = ∅ ↔ r4SaturationDefect A nstar = 0 := by
  constructor
  · intro hempty
    have hExtra0 : extraDefect A nstar = 0 := by
      simp [extraDefect, hempty]
    rwa [← extraDefect_eq_r4SaturationDefect A]
  · intro hdef
    exact extraElements_empty_of_r4SaturationDefect_zero A hdef

/-- Conditional stability form for cardinality extremizers: once the
Erdős-Freud/R4 saturation defect is zero, a cardinality-maximal almost-Sidon
set has no extras.  The cardinality-extremal hypothesis is included so this
statement can be used directly in the finite extremizer pipeline. -/
theorem cardinalityMaximal_extraElements_empty_of_r4SaturationDefect_zero
    {A : Finset ℕ} {N nstar : ℕ}
    (_hopt : IsCardinalityMaximalAlmostSidonInInterval A N)
    (_h_exception : HasTwoSumReprs A nstar)
    (hdef : r4SaturationDefect A nstar = 0) :
    extraElements A nstar = ∅ := by
  exact extraElements_empty_of_r4SaturationDefect_zero A hdef

end AlmostSidonSets
