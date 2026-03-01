/-
# Star Neighborhoods for Triple-Free Sets

For each a ≥ 1, define the "star neighborhood" S_a = {2a, 3a, 4a, 6a, 12a}.
This set contains THREE unit fraction triples:
  - (2a, 3a, 6a):  1/(2a) = 1/(3a) + 1/(6a)
  - (3a, 4a, 12a): 1/(3a) = 1/(4a) + 1/(12a)
  - (4a, 6a, 12a): 1/(4a) = 1/(6a) + 1/(12a)

Removing any single element from S_a leaves at least one triple intact.
Therefore any triple-free set must omit at least 2 elements from each star,
keeping at most 3 of the 5.

For distinct d₁, d₂ coprime to 6, the stars S_{d₁} and S_{d₂} are disjoint.
Combined with the hitting-set bound, this gives
  f₃₀₂(N) ≤ N − 2·|{d ≤ N/12 : gcd(d,6) = 1}|.
-/
import Erdos.UnitFractionTriples.UpperBound

namespace UnitFractionTriples

/-! ### Three triples in the star S_a = {2a, 3a, 4a, 6a, 12a} -/

/-- The triple (3a, 4a, 12a) is a unit fraction triple for all a ≥ 1:
    1/(3a) = 1/(4a) + 1/(12a), equivalently 3a·(4a + 12a) = 48a² = 4a·12a. -/
theorem triple_3a_4a_12a (a : ℕ) (ha : 0 < a) :
    IsUnitFractionTriple (3 * a) (4 * a) (12 * a) := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [triple_iff_div (by omega) (by omega) (by omega)]
  ring

/-- The triple (4a, 6a, 12a) is a unit fraction triple for all a ≥ 1:
    1/(4a) = 1/(6a) + 1/(12a), equivalently 4a·(6a + 12a) = 72a² = 6a·12a. -/
theorem triple_4a_6a_12a (a : ℕ) (ha : 0 < a) :
    IsUnitFractionTriple (4 * a) (6 * a) (12 * a) := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [triple_iff_div (by omega) (by omega) (by omega)]
  ring

/-! ### Hitting-set bound: triple-free sets keep ≤ 3 from each star

The key insight: removing any single element from {2a, 3a, 4a, 6a, 12a}
leaves at least one complete triple:
- Remove 2a  → (3a, 4a, 12a) and (4a, 6a, 12a) survive
- Remove 3a  → (4a, 6a, 12a) survives
- Remove 4a  → (2a, 3a, 6a) survives
- Remove 6a  → (3a, 4a, 12a) survives
- Remove 12a → (2a, 3a, 6a) survives

So any 4 of the 5 elements contain a triple, meaning a triple-free set
keeps at most 3. -/

/-- A triple-free set cannot contain {2a, 3a, 4a, 6a} (since it contains {2a, 3a, 6a}). -/
private theorem star_not_2346 {A : Finset ℕ} (hA : TripleFree A) {a : ℕ} (ha : 0 < a)
    (h2 : 2 * a ∈ A) (h3 : 3 * a ∈ A) (h6 : 6 * a ∈ A) : False :=
  triple_free_excludes_one hA ha h2 h3 h6

/-- A triple-free set cannot contain {3a, 4a, 12a}. -/
private theorem star_not_3_4_12 {A : Finset ℕ} (hA : TripleFree A) {a : ℕ} (ha : 0 < a)
    (h3 : 3 * a ∈ A) (h4 : 4 * a ∈ A) (h12 : 12 * a ∈ A) : False :=
  hA (3 * a) h3 (4 * a) h4 (12 * a) h12 (by omega) (by omega) (by omega)
    (triple_3a_4a_12a a ha)

/-- A triple-free set cannot contain {4a, 6a, 12a}. -/
private theorem star_not_4_6_12 {A : Finset ℕ} (hA : TripleFree A) {a : ℕ} (ha : 0 < a)
    (h4 : 4 * a ∈ A) (h6 : 6 * a ∈ A) (h12 : 12 * a ∈ A) : False :=
  hA (4 * a) h4 (6 * a) h6 (12 * a) h12 (by omega) (by omega) (by omega)
    (triple_4a_6a_12a a ha)

/-- **Hitting-set theorem (qualitative).** A triple-free set cannot contain
    4 or more elements of the star {2a, 3a, 4a, 6a, 12a}.

    Proof by contradiction: assume all 5 membership predicates, then for each
    of the 5 possible missing elements, one of the three triples survives. -/
theorem star_miss_two {A : Finset ℕ} (hA : TripleFree A) {a : ℕ} (ha : 0 < a)
    (_h2 : 2 * a ∈ A) (h3 : 3 * a ∈ A) (_h4 : 4 * a ∈ A) (h6 : 6 * a ∈ A) : False :=
  star_not_2346 hA ha _h2 h3 h6

/-- A triple-free set cannot contain {2a, 3a, 4a, 12a}. -/
theorem star_not_2_3_4_12 {A : Finset ℕ} (hA : TripleFree A) {a : ℕ} (ha : 0 < a)
    (_h2 : 2 * a ∈ A) (h3 : 3 * a ∈ A) (h4 : 4 * a ∈ A) (h12 : 12 * a ∈ A) : False :=
  star_not_3_4_12 hA ha h3 h4 h12

/-- A triple-free set cannot contain {2a, 4a, 6a, 12a}. -/
theorem star_not_2_4_6_12 {A : Finset ℕ} (hA : TripleFree A) {a : ℕ} (ha : 0 < a)
    (_h2 : 2 * a ∈ A) (h4 : 4 * a ∈ A) (h6 : 6 * a ∈ A) (h12 : 12 * a ∈ A) : False :=
  star_not_4_6_12 hA ha h4 h6 h12

/-- A triple-free set cannot contain {2a, 3a, 6a, 12a}. -/
theorem star_not_2_3_6_12 {A : Finset ℕ} (hA : TripleFree A) {a : ℕ} (ha : 0 < a)
    (h2 : 2 * a ∈ A) (h3 : 3 * a ∈ A) (h6 : 6 * a ∈ A) (_h12 : 12 * a ∈ A) : False :=
  star_not_2346 hA ha h2 h3 h6

/-- A triple-free set cannot contain {3a, 4a, 6a, 12a}. -/
theorem star_not_3_4_6_12 {A : Finset ℕ} (hA : TripleFree A) {a : ℕ} (ha : 0 < a)
    (_h3 : 3 * a ∈ A) (h4 : 4 * a ∈ A) (h6 : 6 * a ∈ A) (h12 : 12 * a ∈ A) : False :=
  star_not_4_6_12 hA ha h4 h6 h12

/-! ### Disjointness of 5-element stars for distinct d coprime to 6 -/

/-- k coprime to 6 implies 2 ∤ k. -/
private theorem not_dvd_two_of_coprime6 {k : ℕ} (hk : Nat.Coprime k 6) : ¬(2 ∣ k) := by
  intro ⟨j, hj⟩
  have : 2 ∣ Nat.gcd k 6 := Nat.dvd_gcd ⟨j, hj⟩ ⟨3, by ring⟩
  rw [hk] at this; omega

/-- k coprime to 6 implies 3 ∤ k. -/
private theorem not_dvd_three_of_coprime6 {k : ℕ} (hk : Nat.Coprime k 6) : ¬(3 ∣ k) := by
  intro ⟨j, hj⟩
  have : 3 ∣ Nat.gcd k 6 := Nat.dvd_gcd ⟨j, hj⟩ ⟨2, by ring⟩
  rw [hk] at this; omega

/-- For distinct d₁, d₂ both coprime to 6, the 5-element stars
    {2d₁, 3d₁, 4d₁, 6d₁, 12d₁} and {2d₂, 3d₂, 4d₂, 6d₂, 12d₂} are disjoint.

    We check all 25 cross-equalities. Same-multiplier equalities give d₁ = d₂.
    Cross-multiplier equalities c₁·d₁ = c₂·d₂ force 2 ∣ dᵢ or 3 ∣ dᵢ,
    contradicting coprimality to 6.

    "Simple" cases: one multiplier divides the other (e.g. 2d₁ = 4d₂ → d₁ = 2d₂).
    "Complex" cases: use Nat.Prime.dvd_mul (e.g. 2d₁ = 3d₂ → 3∣2d₁ → 3∣d₁). -/
theorem stars_disjoint_coprime6 {d₁ d₂ : ℕ} (hne : d₁ ≠ d₂)
    (h1 : Nat.Coprime d₁ 6) (h2 : Nat.Coprime d₂ 6) :
    Disjoint ({2 * d₁, 3 * d₁, 4 * d₁, 6 * d₁, 12 * d₁} : Finset ℕ)
             {2 * d₂, 3 * d₂, 4 * d₂, 6 * d₂, 12 * d₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  rcases hx₁ with rfl | rfl | rfl | rfl | rfl <;> rcases hx₂ with h | h | h | h | h
  -- Row 1: 2d₁ vs {2d₂, 3d₂, 4d₂, 6d₂, 12d₂}
  · exact hne (by omega)
  · -- 2d₁ = 3d₂ → 3∣2d₁ → 3∣d₁
    exact not_dvd_three_of_coprime6 h1
      (((Nat.Prime.dvd_mul Nat.prime_three).mp ⟨d₂, by omega⟩).resolve_left (by decide))
  · exact not_dvd_two_of_coprime6 h1 ⟨d₂, by omega⟩
  · exact not_dvd_three_of_coprime6 h1 ⟨d₂, by omega⟩
  · exact not_dvd_two_of_coprime6 h1 ⟨3 * d₂, by omega⟩
  -- Row 2: 3d₁ vs {2d₂, 3d₂, 4d₂, 6d₂, 12d₂}
  · -- 3d₁ = 2d₂ → 2∣3d₁ → 2∣d₁
    exact not_dvd_two_of_coprime6 h1
      (((Nat.Prime.dvd_mul Nat.prime_two).mp ⟨d₂, by omega⟩).resolve_left (by decide))
  · exact hne (by omega)
  · -- 3d₁ = 4d₂ → 2∣3d₁ → 2∣d₁
    have h2d : 2 ∣ 3 * d₁ := ⟨2 * d₂, by omega⟩
    exact not_dvd_two_of_coprime6 h1
      (((Nat.Prime.dvd_mul Nat.prime_two).mp h2d).resolve_left (by decide))
  · exact not_dvd_two_of_coprime6 h1 ⟨d₂, by omega⟩
  · exact not_dvd_two_of_coprime6 h1 ⟨2 * d₂, by omega⟩
  -- Row 3: 4d₁ vs {2d₂, 3d₂, 4d₂, 6d₂, 12d₂}
  · exact not_dvd_two_of_coprime6 h2 ⟨d₁, by omega⟩
  · -- 4d₁ = 3d₂ → 3∣4d₁ → 3∣d₁
    exact not_dvd_three_of_coprime6 h1
      (((Nat.Prime.dvd_mul Nat.prime_three).mp ⟨d₂, by omega⟩).resolve_left (by decide))
  · exact hne (by omega)
  · -- 4d₁ = 6d₂ → 3∣4d₁ → 3∣d₁
    have h3d : 3 ∣ 4 * d₁ := ⟨2 * d₂, by omega⟩
    exact not_dvd_three_of_coprime6 h1
      (((Nat.Prime.dvd_mul Nat.prime_three).mp h3d).resolve_left (by decide))
  · exact not_dvd_three_of_coprime6 h1 ⟨d₂, by omega⟩
  -- Row 4: 6d₁ vs {2d₂, 3d₂, 4d₂, 6d₂, 12d₂}
  · exact not_dvd_three_of_coprime6 h2 ⟨d₁, by omega⟩
  · exact not_dvd_two_of_coprime6 h2 ⟨d₁, by omega⟩
  · -- 6d₁ = 4d₂ → 2∣3d₁ → 2∣d₁ (from 6d₁ = 4d₂ → 3d₁ = 2d₂)
    have h2d : 2 ∣ 3 * d₁ := ⟨d₂, by omega⟩
    exact not_dvd_two_of_coprime6 h1
      (((Nat.Prime.dvd_mul Nat.prime_two).mp h2d).resolve_left (by decide))
  · exact hne (by omega)
  · exact not_dvd_two_of_coprime6 h1 ⟨d₂, by omega⟩
  -- Row 5: 12d₁ vs {2d₂, 3d₂, 4d₂, 6d₂, 12d₂}
  · exact not_dvd_two_of_coprime6 h2 ⟨3 * d₁, by omega⟩
  · exact not_dvd_two_of_coprime6 h2 ⟨2 * d₁, by omega⟩
  · exact not_dvd_three_of_coprime6 h2 ⟨d₁, by omega⟩
  · exact not_dvd_two_of_coprime6 h2 ⟨d₁, by omega⟩
  · exact hne (by omega)

/-! ### Counting: star cardinality, subset, and intersection bounds -/

/-- The star {2d, 3d, 4d, 6d, 12d} has exactly 5 elements for d > 0. -/
theorem star_card_eq_five {d : ℕ} (hd : 0 < d) :
    ({2*d, 3*d, 4*d, 6*d, 12*d} : Finset ℕ).card = 5 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

/-- The star {2d, 3d, 4d, 6d, 12d} ⊆ {1, …, N} when 12d ≤ N and d > 0. -/
theorem star_subset_Icc {d N : ℕ} (hd : 0 < d) (h12 : 12 * d ≤ N) :
    ({2*d, 3*d, 4*d, 6*d, 12*d} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega

/-- If two distinct elements of a finset S are not in A, then (S ∩ A).card + 2 ≤ S.card. -/
private lemma card_inter_le_of_two_not_mem {S A : Finset ℕ} {x y : ℕ}
    (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y) (hxA : x ∉ A) (hyA : y ∉ A) :
    (S ∩ A).card + 2 ≤ S.card := by
  have hdisj : Disjoint (S ∩ A) ({x, y} : Finset ℕ) := by
    rw [Finset.disjoint_right]
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp [hxA]
    · simp [hyA]
  have hpair : ({x, y} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy])]
    simp
  have hsub : S ∩ A ∪ {x, y} ⊆ S :=
    Finset.union_subset Finset.inter_subset_left (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption)
  calc (S ∩ A).card + 2
      = (S ∩ A).card + ({x, y} : Finset ℕ).card := by rw [hpair]
    _ = (S ∩ A ∪ {x, y}).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ S.card := Finset.card_le_card hsub

/-- **Hitting-set bound (quantitative).** A triple-free set keeps at most 3
    elements from the star {2d, 3d, 4d, 6d, 12d}.

    Proof: we find two distinct star elements not in A using the triple
    structure, then apply `card_inter_le_of_two_not_mem`. -/
theorem star_inter_card_le_three {A : Finset ℕ} (hA : TripleFree A)
    {d : ℕ} (hd : 0 < d) :
    (({2*d, 3*d, 4*d, 6*d, 12*d} : Finset ℕ) ∩ A).card ≤ 3 := by
  set S := ({2*d, 3*d, 4*d, 6*d, 12*d} : Finset ℕ) with hS_def
  -- It suffices to find two distinct star elements not in A
  suffices ∃ x y, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ x ∉ A ∧ y ∉ A by
    obtain ⟨x, y, hxS, hyS, hxy, hxA, hyA⟩ := this
    have h1 := card_inter_le_of_two_not_mem hxS hyS hxy hxA hyA
    have h2 : S.card = 5 := star_card_eq_five hd
    omega
  -- Case analysis on the three triples in the star.
  -- T1 = {2d,3d,6d}: at least one not in A.
  -- For each missing element, find a second via T2 or T3.
  by_cases h2 : 2 * d ∈ A
  · by_cases h3 : 3 * d ∈ A
    · by_cases h6 : 6 * d ∈ A
      · -- 2d, 3d, 6d all in A → contradiction from T1
        exact absurd (star_not_2346 hA hd h2 h3 h6) id
      · -- 6d ∉ A; use T2: ¬(3d ∧ 4d ∧ 12d ∈ A)
        by_cases h4 : 4 * d ∈ A
        · exact ⟨6*d, 12*d, by simp [hS_def], by simp [hS_def], by omega, h6,
            fun h12 => star_not_3_4_12 hA hd h3 h4 h12⟩
        · exact ⟨4*d, 6*d, by simp [hS_def], by simp [hS_def], by omega, h4, h6⟩
    · by_cases h6 : 6 * d ∈ A
      · -- 3d ∉ A; use T3: ¬(4d ∧ 6d ∧ 12d ∈ A)
        by_cases h4 : 4 * d ∈ A
        · exact ⟨3*d, 12*d, by simp [hS_def], by simp [hS_def], by omega, h3,
            fun h12 => star_not_4_6_12 hA hd h4 h6 h12⟩
        · exact ⟨3*d, 4*d, by simp [hS_def], by simp [hS_def], by omega, h3, h4⟩
      · -- 3d, 6d both not in A
        exact ⟨3*d, 6*d, by simp [hS_def], by simp [hS_def], by omega, h3, h6⟩
  · by_cases h3 : 3 * d ∈ A
    · by_cases h6 : 6 * d ∈ A
      · -- 2d ∉ A; use T2: ¬(3d ∧ 4d ∧ 12d ∈ A)
        by_cases h4 : 4 * d ∈ A
        · exact ⟨2*d, 12*d, by simp [hS_def], by simp [hS_def], by omega, h2,
            fun h12 => star_not_3_4_12 hA hd h3 h4 h12⟩
        · exact ⟨2*d, 4*d, by simp [hS_def], by simp [hS_def], by omega, h2, h4⟩
      · -- 2d, 6d both not in A
        exact ⟨2*d, 6*d, by simp [hS_def], by simp [hS_def], by omega, h2, h6⟩
    · -- 2d, 3d both not in A
      exact ⟨2*d, 3*d, by simp [hS_def], by simp [hS_def], by omega, h2, h3⟩

/-! ### The star counting argument: f₃₀₂(N) ≤ N − 2|D| -/

/-- **Star upper bound.** For D = {d ∈ [1, N/12] : gcd(d,6) = 1}, each star
    S_d = {2d, 3d, 4d, 6d, 12d} is a 5-element subset of {1,…,N} and the stars
    are pairwise disjoint. A triple-free A keeps ≤ 3 of 5 from each star, so
    A.card + 2·|D| ≤ N. -/
theorem triple_free_star_upper_bound (N : ℕ) (A : Finset ℕ)
    (hA : TripleFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + 2 * ((Finset.Icc 1 (N / 12)).filter (Nat.Coprime · 6)).card ≤ N := by
  set D := (Finset.Icc 1 (N / 12)).filter (Nat.Coprime · 6) with hD_def
  -- Star function
  let star : ℕ → Finset ℕ := fun d => {2*d, 3*d, 4*d, 6*d, 12*d}
  -- Helper: extract properties from D membership
  have hD_mem : ∀ d ∈ D, 0 < d ∧ Nat.Coprime d 6 ∧ 12 * d ≤ N := by
    intro d hd
    simp only [hD_def, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨by omega, hd.2, by omega⟩
  -- Step 1: Stars are pairwise disjoint on D
  have hpwd : (↑D : Set ℕ).PairwiseDisjoint star := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact stars_disjoint_coprime6 hne
      (hD_mem d₁ (Finset.mem_coe.mp hd₁)).2.1
      (hD_mem d₂ (Finset.mem_coe.mp hd₂)).2.1
  -- Step 2: Union of stars ⊆ Icc 1 N
  have hUsub : D.biUnion star ⊆ Finset.Icc 1 N :=
    Finset.biUnion_subset.mpr fun d hd =>
      star_subset_Icc (hD_mem d hd).1 (hD_mem d hd).2.2
  -- Step 3: |⋃ stars| = 5 · |D|
  have hUcard : (D.biUnion star).card = 5 * D.card := by
    rw [Finset.card_biUnion hpwd,
        Finset.sum_const_nat (fun d hd => star_card_eq_five (hD_mem d hd).1)]
    ring
  -- Step 4: |A ∩ ⋃stars| ≤ 3 · |D|
  have hUAcard : (D.biUnion star ∩ A).card ≤ 3 * D.card := by
    rw [Finset.biUnion_inter]
    have hpwd' : (↑D : Set ℕ).PairwiseDisjoint (fun d => star d ∩ A) := by
      intro d₁ hd₁ d₂ hd₂ hne
      exact (hpwd hd₁ hd₂ hne).mono Finset.inter_subset_left Finset.inter_subset_left
    calc (D.biUnion (fun d => star d ∩ A)).card
        = ∑ d ∈ D, (star d ∩ A).card := Finset.card_biUnion hpwd'
      _ ≤ ∑ d ∈ D, 3 := Finset.sum_le_sum (fun d hd =>
          star_inter_card_le_three hA (hD_mem d hd).1)
      _ = D.card * 3 := Finset.sum_const_nat (fun _ _ => rfl)
      _ = 3 * D.card := by ring
  -- Step 5: A ⊆ (⋃stars ∩ A) ∪ (Icc \ ⋃stars), giving the card bound
  have hAle : A.card ≤ (D.biUnion star ∩ A).card +
      (Finset.Icc 1 N \ D.biUnion star).card :=
    calc A.card
        ≤ (D.biUnion star ∩ A ∪ (Finset.Icc 1 N \ D.biUnion star)).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ D.biUnion star
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  -- Step 6: |Icc \ ⋃stars| + |⋃stars| = N
  have hsdiff : (Finset.Icc 1 N \ D.biUnion star).card +
      (D.biUnion star).card = (Finset.Icc 1 N).card :=
    Finset.card_sdiff_add_card_eq_card hUsub
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  -- Combine: A.card + 2·|D| ≤ 3·|D| + (N - 5·|D|) + 2·|D| = N
  omega

/-! ### Phase 2: Combined full-star + partial-triple bound -/

/-- The partial triple {2d, 3d, 6d} has exactly 3 elements for d > 0. -/
private theorem triple_card_eq_three {d : ℕ} (hd : 0 < d) :
    ({2*d, 3*d, 6*d} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

/-- A triple-free set keeps at most 2 elements from {2d, 3d, 6d}. -/
theorem triple_inter_card_le_two {A : Finset ℕ} (hA : TripleFree A)
    {d : ℕ} (hd : 0 < d) :
    (({2*d, 3*d, 6*d} : Finset ℕ) ∩ A).card ≤ 2 := by
  -- It suffices to find one element of {2d,3d,6d} not in A
  suffices h : ∃ x ∈ ({2*d, 3*d, 6*d} : Finset ℕ), x ∉ A by
    obtain ⟨x, hxT, hxA⟩ := h
    calc (({2*d, 3*d, 6*d} : Finset ℕ) ∩ A).card
        ≤ (({2*d, 3*d, 6*d} : Finset ℕ).erase x).card :=
          Finset.card_le_card fun a ha =>
            Finset.mem_erase.mpr ⟨fun h => by subst h; exact hxA (Finset.mem_inter.mp ha).2,
              (Finset.mem_inter.mp ha).1⟩
      _ = ({2*d, 3*d, 6*d} : Finset ℕ).card - 1 := Finset.card_erase_of_mem hxT
      _ = 2 := by rw [triple_card_eq_three hd]
  -- By contradiction: if all three in A, triple_free_excludes_one gives False
  by_contra h; push_neg at h
  exact triple_free_excludes_one hA hd (h _ (by simp)) (h _ (by simp)) (h _ (by simp))

/-- The partial triple {2d, 3d, 6d} ⊆ {1, …, N} when 6d ≤ N and d > 0. -/
private theorem triple_subset_Icc {d N : ℕ} (hd : 0 < d) (h6 : 6 * d ≤ N) :
    ({2*d, 3*d, 6*d} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl <;> omega

/-- The partial triple is a subset of the full star. -/
private theorem triple_subset_star (d : ℕ) :
    ({2*d, 3*d, 6*d} : Finset ℕ) ⊆ {2*d, 3*d, 4*d, 6*d, 12*d} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl <;> simp

/-- **Combined upper bound.** Using full stars for d ≤ N/12 and partial triples
    for N/12 < d ≤ N/6, both coprime to 6:
    A.card + 2·|D₁| + |D₂| ≤ N, giving f₃₀₂(N) ≤ 11N/12 + O(1). -/
theorem triple_free_combined_upper_bound (N : ℕ) (A : Finset ℕ)
    (hA : TripleFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + 2 * ((Finset.Icc 1 (N / 12)).filter (Nat.Coprime · 6)).card
           + ((Finset.Icc (N / 12 + 1) (N / 6)).filter (Nat.Coprime · 6)).card ≤ N := by
  set D₁ := (Finset.Icc 1 (N / 12)).filter (Nat.Coprime · 6) with hD₁_def
  set D₂ := (Finset.Icc (N / 12 + 1) (N / 6)).filter (Nat.Coprime · 6) with hD₂_def
  let star : ℕ → Finset ℕ := fun d => {2*d, 3*d, 4*d, 6*d, 12*d}
  let triple : ℕ → Finset ℕ := fun d => {2*d, 3*d, 6*d}
  -- Properties of D₁ and D₂ members
  have hD₁_mem : ∀ d ∈ D₁, 0 < d ∧ Nat.Coprime d 6 ∧ 12 * d ≤ N := by
    intro d hd; simp only [hD₁_def, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨by omega, hd.2, by omega⟩
  have hD₂_mem : ∀ d ∈ D₂, 0 < d ∧ Nat.Coprime d 6 ∧ 6 * d ≤ N := by
    intro d hd; simp only [hD₂_def, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨by omega, hd.2, by omega⟩
  -- Pairwise disjointness of full stars on D₁
  have hpwd₁ : (↑D₁ : Set ℕ).PairwiseDisjoint star := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact stars_disjoint_coprime6 hne
      (hD₁_mem d₁ (Finset.mem_coe.mp hd₁)).2.1
      (hD₁_mem d₂ (Finset.mem_coe.mp hd₂)).2.1
  -- Pairwise disjointness of partial triples on D₂
  have hpwd₂ : (↑D₂ : Set ℕ).PairwiseDisjoint triple := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact triples_disjoint_coprime6 hne
      (hD₂_mem d₁ (Finset.mem_coe.mp hd₁)).2.1
      (hD₂_mem d₂ (Finset.mem_coe.mp hd₂)).2.1
  -- U₁ = full star union, U₂ = partial triple union
  set U₁ := D₁.biUnion star with hU₁_def
  set U₂ := D₂.biUnion triple with hU₂_def
  -- U₁ ⊆ Icc 1 N
  have hU₁sub : U₁ ⊆ Finset.Icc 1 N :=
    Finset.biUnion_subset.mpr fun d hd =>
      star_subset_Icc (hD₁_mem d hd).1 (hD₁_mem d hd).2.2
  -- U₂ ⊆ Icc 1 N
  have hU₂sub : U₂ ⊆ Finset.Icc 1 N :=
    Finset.biUnion_subset.mpr fun d hd =>
      triple_subset_Icc (hD₂_mem d hd).1 (hD₂_mem d hd).2.2
  -- Disjoint U₁ U₂
  have hU_disj : Disjoint U₁ U₂ := by
    rw [hU₁_def, hU₂_def, Finset.disjoint_biUnion_left]
    intro d₁ hd₁
    rw [Finset.disjoint_biUnion_right]
    intro d₂ hd₂
    have hne : d₁ ≠ d₂ := by
      intro heq; subst heq
      simp only [hD₁_def, hD₂_def, Finset.mem_filter, Finset.mem_Icc] at hd₁ hd₂; omega
    exact (stars_disjoint_coprime6 hne (hD₁_mem d₁ hd₁).2.1
      (hD₂_mem d₂ hd₂).2.1).mono_right (triple_subset_star d₂)
  -- |U₁| = 5|D₁|
  have hU₁card : U₁.card = 5 * D₁.card := by
    rw [hU₁_def, Finset.card_biUnion hpwd₁,
        Finset.sum_const_nat (fun d hd => star_card_eq_five (hD₁_mem d hd).1)]
    ring
  -- |U₂| = 3|D₂|
  have hU₂card : U₂.card = 3 * D₂.card := by
    rw [hU₂_def, Finset.card_biUnion hpwd₂,
        Finset.sum_const_nat (fun d hd => triple_card_eq_three (hD₂_mem d hd).1)]
    ring
  -- |U₁ ∪ U₂| = |U₁| + |U₂|
  have hU_card : (U₁ ∪ U₂).card = U₁.card + U₂.card :=
    Finset.card_union_of_disjoint hU_disj
  -- U₁ ∪ U₂ ⊆ Icc 1 N
  have hUsub : U₁ ∪ U₂ ⊆ Finset.Icc 1 N :=
    Finset.union_subset hU₁sub hU₂sub
  -- |U₁ ∩ A| ≤ 3|D₁|
  have hU₁A : (U₁ ∩ A).card ≤ 3 * D₁.card := by
    rw [show U₁ = D₁.biUnion star from rfl, Finset.biUnion_inter]
    have hpwd₁' : (↑D₁ : Set ℕ).PairwiseDisjoint (fun d => star d ∩ A) := by
      intro d₁ hd₁ d₂ hd₂ hne
      exact (hpwd₁ hd₁ hd₂ hne).mono Finset.inter_subset_left Finset.inter_subset_left
    calc (D₁.biUnion (fun d => star d ∩ A)).card
        = ∑ d ∈ D₁, (star d ∩ A).card := Finset.card_biUnion hpwd₁'
      _ ≤ ∑ d ∈ D₁, 3 := Finset.sum_le_sum (fun d hd =>
          star_inter_card_le_three hA (hD₁_mem d hd).1)
      _ = D₁.card * 3 := Finset.sum_const_nat (fun _ _ => rfl)
      _ = 3 * D₁.card := by ring
  -- |U₂ ∩ A| ≤ 2|D₂|
  have hU₂A : (U₂ ∩ A).card ≤ 2 * D₂.card := by
    rw [show U₂ = D₂.biUnion triple from rfl, Finset.biUnion_inter]
    have hpwd₂' : (↑D₂ : Set ℕ).PairwiseDisjoint (fun d => triple d ∩ A) := by
      intro d₁ hd₁ d₂ hd₂ hne
      exact (hpwd₂ hd₁ hd₂ hne).mono Finset.inter_subset_left Finset.inter_subset_left
    calc (D₂.biUnion (fun d => triple d ∩ A)).card
        = ∑ d ∈ D₂, (triple d ∩ A).card := Finset.card_biUnion hpwd₂'
      _ ≤ ∑ d ∈ D₂, 2 := Finset.sum_le_sum (fun d hd =>
          triple_inter_card_le_two hA (hD₂_mem d hd).1)
      _ = D₂.card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
      _ = 2 * D₂.card := by ring
  -- |(U₁ ∪ U₂) ∩ A| ≤ 3|D₁| + 2|D₂|
  have hUA : ((U₁ ∪ U₂) ∩ A).card ≤ 3 * D₁.card + 2 * D₂.card :=
    calc ((U₁ ∪ U₂) ∩ A).card
        ≤ (U₁ ∩ A).card + (U₂ ∩ A).card := by
          rw [Finset.union_inter_distrib_right]
          exact Finset.card_union_le _ _
      _ ≤ 3 * D₁.card + 2 * D₂.card := Nat.add_le_add hU₁A hU₂A
  -- A.card ≤ |(U₁∪U₂) ∩ A| + |Icc \ (U₁∪U₂)|
  have hAle : A.card ≤ ((U₁ ∪ U₂) ∩ A).card +
      (Finset.Icc 1 N \ (U₁ ∪ U₂)).card :=
    calc A.card
        ≤ ((U₁ ∪ U₂) ∩ A ∪ (Finset.Icc 1 N \ (U₁ ∪ U₂))).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ U₁ ∪ U₂
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  -- |Icc \ (U₁∪U₂)| + |U₁∪U₂| = N
  have hsdiff : (Finset.Icc 1 N \ (U₁ ∪ U₂)).card + (U₁ ∪ U₂).card =
      (Finset.Icc 1 N).card := Finset.card_sdiff_add_card_eq_card hUsub
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  -- Combine with omega
  omega

end UnitFractionTriples
