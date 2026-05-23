/-
# Lindström's Constant-Form Bound for Sidon Subsets of Intervals

For every Sidon subset `A ⊆ {α+1, ..., α+L}`, the classical Lindström
(1969) counting bound gives

  `|A|·(|A|-1) ≤ 2·L`,

equivalently `|A| ≤ (1 + √(8L+1))/2 ≤ √(2L) + 1`.

The proof is a clean injection: the off-diagonal pairs `(a, b) ∈ A × A`
with `a > b` map injectively (by the Sidon property) into the positive
differences `{1, ..., L}`. There are `|A|·(|A|-1)/2` such pairs, hence
`|A|·(|A|-1)/2 ≤ L`.

This is the **constant** form of the bound, sufficient for any
asymptotic application requiring `|A| ≤ c·√L` with a fixed constant
`c ≥ √2`. The asymptotic refinement `|A| ≤ (1+ε)·√L` for all `ε > 0`
(`SidonIntervalAsymptotic`) needs a second-moment Cauchy–Schwarz
argument we do not formalise here.

## Main results

* `Sidon_card_sq_sub_card_le_two_mul`: the integer-form Lindström
  bound `|A|·(|A|-1) ≤ 2·L`.
* `Sidon_card_le_sqrt_two_mul_L_succ`: the rational corollary
  `|A| ≤ √(2L) + 1`.
-/
import Erdos.AlmostSidonSets.Statement

namespace AlmostSidonSets.UpperBound

open SidonSumsets

/-- Strictly off-diagonal ordered pairs `(a, b) ∈ A × A` with `a > b`. -/
private def offDiagPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun p => p.2 < p.1)

private lemma mem_offDiagPairs_iff {A : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ offDiagPairs A ↔ p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 < p.1 := by
  unfold offDiagPairs
  rw [Finset.mem_filter, Finset.mem_product]
  tauto

/-- The off-diagonal ordered-pair count is `(|A|² − |A|) / 2`, in the
form `2 · |offDiag| = |A|² − |A|`. The proof pairs each `(a, b)` with
its swap `(b, a)`. -/
private lemma two_mul_card_offDiagPairs (A : Finset ℕ) :
    2 * (offDiagPairs A).card = A.card * A.card - A.card := by
  classical
  set L : Finset (ℕ × ℕ) := offDiagPairs A
  set R : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 < p.2)
  set D : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 = p.2)
  -- L and R have the same cardinality, via the swap.
  have hRimage : R = L.image Prod.swap := by
    ext ⟨a, b⟩
    constructor
    · intro hab
      simp only [R, Finset.mem_filter, Finset.mem_product] at hab
      refine Finset.mem_image.mpr ⟨(b, a), ?_, rfl⟩
      rw [mem_offDiagPairs_iff]
      exact ⟨hab.1.2, hab.1.1, hab.2⟩
    · intro hab
      rcases Finset.mem_image.mp hab with ⟨⟨x, y⟩, hxy, heq⟩
      rw [mem_offDiagPairs_iff] at hxy
      have h1 : y = a := by simpa using congrArg Prod.fst heq
      have h2 : x = b := by simpa using congrArg Prod.snd heq
      subst h1; subst h2
      simp only [R, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hxy.2.1, hxy.1⟩, hxy.2.2⟩
  have hcardR : R.card = L.card := by
    rw [hRimage]
    refine Finset.card_image_of_injective _ ?_
    intro p q hpq
    have := congrArg Prod.swap hpq
    simpa using this
  -- L ∪ R ∪ D partitions A ×ˢ A.
  have hLR_disj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro p hL hR
    simp only [L, offDiagPairs, R, Finset.mem_filter] at hL hR
    omega
  have hLRD_disj : Disjoint (L ∪ R) D := by
    rw [Finset.disjoint_left]
    intro p hLR hD
    simp only [L, offDiagPairs, R, D, Finset.mem_filter,
      Finset.mem_union] at hLR hD
    rcases hLR with hL | hR
    · omega
    · omega
  have hcoverLR : L ∪ R ∪ D = A ×ˢ A := by
    ext ⟨a, b⟩
    simp only [L, offDiagPairs, R, D, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;>
        exact h1
    · intro hp
      rcases lt_trichotomy a b with h | h | h
      · exact Or.inl (Or.inr ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h⟩
      · exact Or.inl (Or.inl ⟨hp, h⟩)
  -- Cardinality of D = |A|: pair p ∈ D iff p = (a, a) for some a ∈ A.
  have hcardD : D.card = A.card := by
    have himage : D = A.image (fun a => (a, a)) := by
      ext ⟨a, b⟩
      simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, _⟩, hab⟩
        exact ⟨a, ha, by subst hab; rfl⟩
      · rintro ⟨c, hc, heq⟩
        have h1 : c = a := by simpa using congrArg Prod.fst heq
        have h2 : c = b := by simpa using congrArg Prod.snd heq
        subst h1; subst h2; exact ⟨⟨hc, hc⟩, rfl⟩
    rw [himage]
    refine Finset.card_image_of_injective _ ?_
    intro a b hab
    simpa using congrArg Prod.fst hab
  -- Cardinality of A ×ˢ A = |A|².
  have hcardAA : (A ×ˢ A).card = A.card * A.card := Finset.card_product _ _
  -- Now assemble.
  have hcardLR : (L ∪ R).card = L.card + R.card :=
    Finset.card_union_of_disjoint hLR_disj
  have hcardLRD : (L ∪ R ∪ D).card = (L ∪ R).card + D.card :=
    Finset.card_union_of_disjoint hLRD_disj
  rw [hcoverLR, hcardAA] at hcardLRD
  rw [hcardLR, hcardR, hcardD] at hcardLRD
  -- hcardLRD : L.card + L.card + A.card = A.card * A.card
  omega

/-- For Sidon `A ⊆ Finset.Icc (α + 1) (α + L)`, the positive-difference
map `(a, b) ↦ a - b` is injective on `offDiagPairs A`. -/
private lemma sidon_diff_injOn {A : Finset ℕ} (hSidon : IsSidonFinset A) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2) ↑(offDiagPairs A) := by
  rintro ⟨pa, pb⟩ hp ⟨qa, qb⟩ hq hdiff
  have hp' := mem_offDiagPairs_iff.mp hp
  have hq' := mem_offDiagPairs_iff.mp hq
  obtain ⟨hpa, hpb, hpgt⟩ := hp'
  obtain ⟨hqa, hqb, hqgt⟩ := hq'
  -- hdiff : pa - pb = qa - qb (after unfolding the lambda).
  simp only at hdiff
  -- Translate to the Sidon equation pa + qb = qa + pb using hpgt, hqgt.
  have hsum : pa + qb = qa + pb := by omega
  -- Apply Sidon via two ordered-pair cases.
  -- We apply IsSidon on sorted-pair sums; the order of the elements depends
  -- on which case we are in.  In every case the resulting equalities pin
  -- down pa = qa and pb = qb.
  rcases le_total pb qa with hle | hle
  · rcases le_total qb pa with hle2 | hle2
    · have hsum' : pb + qa = qb + pa := by omega
      obtain ⟨heq1, heq2⟩ :=
        hSidon (a₁ := pb) (a₂ := qa) (b₁ := qb) (b₂ := pa)
          hpb hqa hqb hpa hle hle2 hsum'
      -- heq1 : pb = qb, heq2 : qa = pa.
      ext
      · exact heq2.symm
      · exact heq1
    · -- pa ≤ qb: use (pb, qa) and (pa, qb).
      have hsum' : pb + qa = pa + qb := by omega
      obtain ⟨heq1, heq2⟩ :=
        hSidon (a₁ := pb) (a₂ := qa) (b₁ := pa) (b₂ := qb)
          hpb hqa hpa hqb hle hle2 hsum'
      -- heq1 : pb = pa.  But pb < pa contradicts pb = pa.
      exfalso; omega
  · -- qa ≤ pb.  Sub-case on pa vs qb.
    rcases le_total qb pa with hle2 | hle2
    · have hsum' : qa + pb = qb + pa := by omega
      obtain ⟨heq1, heq2⟩ :=
        hSidon (a₁ := qa) (a₂ := pb) (b₁ := qb) (b₂ := pa)
          hqa hpb hqb hpa hle hle2 hsum'
      -- heq1 : qa = qb.  But qb < qa contradicts qa = qb.
      exfalso; omega
    · -- pa ≤ qb: use (qa, pb) and (pa, qb).
      have hsum' : qa + pb = pa + qb := by omega
      obtain ⟨heq1, heq2⟩ :=
        hSidon (a₁ := qa) (a₂ := pb) (b₁ := pa) (b₂ := qb)
          hqa hpb hpa hqb hle hle2 hsum'
      -- heq1 : qa = pa, heq2 : pb = qb.
      ext
      · exact heq1.symm
      · exact heq2

/-- The image of `offDiagPairs A` under `(a, b) ↦ a - b` lies in
`Finset.Icc 1 L` when `A ⊆ Finset.Icc (α + 1) (α + L)`. -/
private lemma diff_mem_Icc {A : Finset ℕ} {α L : ℕ}
    (hA : ∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L)
    {p : ℕ × ℕ} (hp : p ∈ offDiagPairs A) :
    p.1 - p.2 ∈ Finset.Icc 1 L := by
  rcases mem_offDiagPairs_iff.mp hp with ⟨h1, h2, hgt⟩
  have hb1 := hA p.1 h1
  have hb2 := hA p.2 h2
  rw [Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · omega
  · omega

/-- **Lindström's constant-form bound (integer version).** For Sidon
`A ⊆ [α+1, α+L]`, we have `|A|·(|A|-1) ≤ 2L`. -/
theorem Sidon_card_sq_sub_card_le_two_mul
    {A : Finset ℕ} {α L : ℕ}
    (hA : ∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L)
    (hSidon : IsSidonFinset A) :
    A.card * A.card - A.card ≤ 2 * L := by
  classical
  -- Image of off-diagonal pairs under difference lies in Icc 1 L.
  have hmap : ((offDiagPairs A).image (fun p : ℕ × ℕ => p.1 - p.2)) ⊆
      Finset.Icc 1 L := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, heq⟩
    rw [← heq]
    exact diff_mem_Icc hA hp
  -- The map is injective on offDiagPairs, so the image has the same cardinality.
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2) ↑(offDiagPairs A) :=
    sidon_diff_injOn hSidon
  have hcard_image :
      ((offDiagPairs A).image (fun p : ℕ × ℕ => p.1 - p.2)).card =
        (offDiagPairs A).card := by
    rw [Finset.card_image_of_injOn hinj]
  -- Card Icc 1 L = L.
  have hcardIcc : (Finset.Icc 1 L).card = L := by
    rw [Nat.card_Icc]; omega
  -- Combine: |offDiagPairs A| ≤ L.
  have hbound : (offDiagPairs A).card ≤ L := by
    have := Finset.card_le_card hmap
    rw [hcard_image, hcardIcc] at this
    exact this
  -- Use 2 · |offDiagPairs A| = |A|² − |A|.
  have h2 := two_mul_card_offDiagPairs A
  omega

/-- **Lindström's constant-form bound (real version).** For Sidon
`A ⊆ [α+1, α+L]`, we have `|A| ≤ √(2L) + 1`. -/
theorem Sidon_card_le_sqrt_two_mul_L_succ
    {A : Finset ℕ} {α L : ℕ}
    (hA : ∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L)
    (hSidon : IsSidonFinset A) :
    (A.card : ℝ) ≤ Real.sqrt (2 * L) + 1 := by
  have hint := Sidon_card_sq_sub_card_le_two_mul hA hSidon
  -- From |A|² − |A| ≤ 2L and |A| ≥ 0, conclude |A| ≤ √(2L) + 1.
  have hineq : (A.card : ℝ) * A.card - A.card ≤ 2 * L := by
    have hcast : ((A.card * A.card - A.card : ℕ) : ℝ) ≤ ((2 * L : ℕ) : ℝ) := by
      exact_mod_cast hint
    have hle : A.card ≤ A.card * A.card := by
      cases hA0 : A.card with
      | zero => simp
      | succ n =>
        have : n + 1 ≤ (n + 1) * (n + 1) := by
          have h : 0 < n + 1 := Nat.succ_pos n
          calc n + 1 = 1 * (n + 1) := by ring
            _ ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right _ h
        exact this
    -- Cast the Nat subtraction to ℝ via the inequality |A| ≤ |A|².
    have hsub_eq : ((A.card * A.card - A.card : ℕ) : ℝ) =
        (A.card : ℝ) * A.card - A.card := by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [hsub_eq] at hcast
    have h2L : ((2 * L : ℕ) : ℝ) = 2 * L := by push_cast; ring
    rw [h2L] at hcast
    exact hcast
  -- From |A|² ≤ |A| + 2L, derive |A| ≤ √(2L) + 1.
  -- The key inequality: (|A| - 1)² = |A|² − 2|A| + 1 ≤ 2L − |A| + 1 ≤ 2L + 1.
  -- But we want |A| ≤ √(2L) + 1, i.e. |A| − 1 ≤ √(2L), i.e. (|A| − 1)² ≤ 2L
  -- (when |A| ≥ 1).  However (|A| − 1)² = |A|² − 2|A| + 1.
  -- From hineq: |A|² ≤ 2L + |A|. So |A|² − 2|A| + 1 ≤ 2L − |A| + 1 ≤ 2L (if |A| ≥ 1).
  -- Combine with |A| ≥ 0 ⇒ (|A| − 1)² ≤ 2L ⇒ |A| − 1 ≤ √(2L).
  by_cases hAcard : A.card = 0
  · rw [hAcard]
    have : (0 : ℝ) ≤ Real.sqrt (2 * L) := Real.sqrt_nonneg _
    push_cast
    linarith
  · have hge : (1 : ℝ) ≤ A.card := by
      have : 1 ≤ A.card := Nat.one_le_iff_ne_zero.mpr hAcard
      exact_mod_cast this
    -- (|A| − 1)² ≤ 2L:
    have hsq : ((A.card : ℝ) - 1) ^ 2 ≤ 2 * L := by
      have h0 : ((A.card : ℝ) - 1) ^ 2 = (A.card : ℝ) * A.card - 2 * A.card + 1 := by
        ring
      rw [h0]
      linarith
    -- |A| − 1 ≤ √(2L):
    have h2L_nn : (0 : ℝ) ≤ 2 * L := by positivity
    have hA1_nn : (0 : ℝ) ≤ (A.card : ℝ) - 1 := by linarith
    have hsqrt : (A.card : ℝ) - 1 ≤ Real.sqrt (2 * L) := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hA1_nn] at this
    linarith

end AlmostSidonSets.UpperBound
