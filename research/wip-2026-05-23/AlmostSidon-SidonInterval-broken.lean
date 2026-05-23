/-
# Lindström's Cardinality Bound for Sidon Subsets of Intervals

For every Sidon subset `A ⊆ {α+1, ..., α+L}`, the classical Lindström
(1969) bound says

  `|A|² ≤ |A| + 2L`,

which yields `|A| ≤ √(2L) + 1`.

The proof is a clean counting argument: any two distinct ordered pairs
`(a, b)` and `(a', b')` with `a > b` and `a' > b'` in `A` must yield
distinct positive differences `a - b ≠ a' - b'`. Otherwise `a + b' =
a' + b`, and the Sidon property forces `(a, b) = (a', b')` (after sorting).

The number of ordered pairs `(a, b)` with `a > b` in `A` is exactly
`|A|·(|A|-1)/2`, and each such difference lies in `{1, ..., L-1}`.
Hence `|A|·(|A|-1)/2 ≤ L-1 ≤ L`, i.e. `|A|² - |A| ≤ 2L`.

This unconditional constant-form bound is the easy half of the
Erdős–Turán asymptotic `(1+ε)√L`; the asymptotic refinement requires
a second-moment argument we do not need here. The √(2L) bound is
strong enough to give an unconditional `2·√N` upper bound for strong
almost-Sidon sets (see `Sqrt2Bound.lean`), which is the easy version
of Erdős–Freud's conjectured `(2/√3)·√N` bound.
-/
import Erdos.AlmostSidonSets.Statement
import Erdos.AlmostSidonSets.Structure

namespace AlmostSidonSets.UpperBound

open Real
open AlmostSidonSets SidonSumsets

/-! ### The ordered positive-difference injection

We use the off-diagonal set of pairs `{(a, b) ∈ A × A : a > b}`, which
has cardinality exactly `|A|·(|A|-1)/2`, and inject it into the set of
positive differences `{1, ..., L-1}` via `(a, b) ↦ a - b`. -/

/-- The set of strictly off-diagonal pairs `(a, b) ∈ A × A` with `a > b`. -/
private def offDiagPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun p => p.2 < p.1)

@[simp] private theorem mem_offDiagPairs {A : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ offDiagPairs A ↔ p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 < p.1 := by
  simp [offDiagPairs, and_assoc]

/-- Cardinality of the off-diagonal pair set: `|A|·(|A|-1)/2`. We use the
  symmetric pairing across the diagonal: there are `|A|² - |A|` ordered
  pairs with `a ≠ b`, half of which have `a > b`. -/
private theorem card_offDiagPairs (A : Finset ℕ) :
    2 * (offDiagPairs A).card = A.card * A.card - A.card := by
  classical
  -- Strategy: pair each (a, b) with (b, a) via the swap.
  -- {a < b pairs} ⊕ {a > b pairs} ⊕ {diagonal} = A ×ˢ A.
  -- The swap σ(a,b) = (b,a) sends offDiag to its "reverse" disjointly.
  set L := offDiagPairs A
  set R : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 < p.2)
  -- L and R have the same cardinality via the swap.
  have hswap : R = L.image Prod.swap := by
    ext ⟨a, b⟩
    simp only [Finset.mem_image, mem_offDiagPairs, Finset.mem_filter,
      Finset.mem_product, Prod.swap]
    constructor
    · rintro ⟨ha, hb, hlt⟩
      refine ⟨(b, a), ?_, rfl⟩
      exact ⟨hb, ha, hlt⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy, hlt⟩, hxy⟩
      have h1 : y = a := by simpa using congrArg Prod.fst hxy
      have h2 : x = b := by simpa using congrArg Prod.snd hxy
      subst h1; subst h2
      exact ⟨hy, hx, hlt⟩
  have hcardR : R.card = L.card := by
    rw [hswap]
    refine Finset.card_image_of_injective _ ?_
    intro p q hpq
    simpa [Prod.swap] using congrArg Prod.swap hpq
  -- L ∪ R ∪ diag(A) = A ×ˢ A, disjointly.
  set D : Finset (ℕ × ℕ) := A.image fun a => (a, a)
  have hcardD : D.card = A.card := by
    refine Finset.card_image_of_injective _ ?_
    intro a b hab
    simpa using congrArg Prod.fst hab
  have hdisjLR : Disjoint L R := by
    refine Finset.disjoint_left.mpr ?_
    intro p hpL hpR
    rw [mem_offDiagPairs] at hpL
    simp only [Finset.mem_filter, Finset.mem_product] at hpR
    omega
  have hdisjLD : Disjoint L D := by
    refine Finset.disjoint_left.mpr ?_
    intro p hpL hpD
    rw [mem_offDiagPairs] at hpL
    simp only [Finset.mem_image] at hpD
    obtain ⟨a, _, ha⟩ := hpD
    have h1 : p.1 = a := by simpa using congrArg Prod.fst ha
    have h2 : p.2 = a := by simpa using congrArg Prod.snd ha
    omega
  have hdisjRD : Disjoint R D := by
    refine Finset.disjoint_left.mpr ?_
    intro p hpR hpD
    simp only [Finset.mem_filter, Finset.mem_product] at hpR
    simp only [Finset.mem_image] at hpD
    obtain ⟨a, _, ha⟩ := hpD
    have h1 : p.1 = a := by simpa using congrArg Prod.fst ha
    have h2 : p.2 = a := by simpa using congrArg Prod.snd ha
    omega
  have hunion : L ∪ R ∪ D = A ×ˢ A := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, mem_offDiagPairs, Finset.mem_filter,
      Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ((⟨ha, hb, _⟩ | ⟨⟨ha, hb⟩, _⟩) | ⟨x, hx, hxy⟩)
      · exact ⟨ha, hb⟩
      · exact ⟨ha, hb⟩
      · have h1 : x = a := by simpa using congrArg Prod.fst hxy
        have h2 : x = b := by simpa using congrArg Prod.snd hxy
        subst h1
        subst h2
        exact ⟨hx, hx⟩
    · rintro ⟨ha, hb⟩
      rcases lt_trichotomy a b with hab | hab | hab
      · left; right; exact ⟨⟨ha, hb⟩, hab⟩
      · right; refine ⟨a, ha, ?_⟩
        simp [hab]
      · left; left; exact ⟨ha, hb, hab⟩
  -- Cardinality: |L| + |R| + |D| = |A|².
  have hcardLRD : L.card + R.card + D.card = A.card * A.card := by
    have h1 : (L ∪ R).card = L.card + R.card :=
      Finset.card_union_of_disjoint hdisjLR
    have hdisjLRD : Disjoint (L ∪ R) D :=
      Finset.disjoint_union_left.mpr ⟨hdisjLD, hdisjRD⟩
    have h2 : ((L ∪ R) ∪ D).card = (L ∪ R).card + D.card :=
      Finset.card_union_of_disjoint hdisjLRD
    have h3 : (A ×ˢ A).card = A.card * A.card := by
      simp [Finset.card_product]
    rw [← hunion, h2, h1] at h3
    omega
  -- Conclude.
  rw [hcardR, hcardD] at hcardLRD
  have : 2 * L.card + A.card = A.card * A.card := by linarith
  omega

/-! ### The Sidon injection: ordered differences are distinct -/

/-- **The key Sidon injection lemma**: for a Sidon set `A`, the map
`(a, b) ↦ a - b` is injective on the off-diagonal pairs with `a > b`. -/
theorem Sidon_diff_injective {A : Finset ℕ} (hSidon : IsSidonFinset A) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2) (offDiagPairs A : Set (ℕ × ℕ)) := by
  intro p hp q hq hpq
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
    Finset.mem_product] at hp hq
  obtain ⟨⟨ha, hb⟩, hlt⟩ := hp
  obtain ⟨⟨hc, hd⟩, hlt'⟩ := hq
  -- p = (a, b), q = (c, d), b < a, d < c, a - b = c - d.
  set a := p.1; set b := p.2; set c := q.1; set d := q.2
  -- From a - b = c - d (in ℕ) with b < a, d < c, get a + d = b + c.
  have hadd : a + d = b + c := by
    have : a = b + (a - b) := by omega
    have hac : c = d + (c - d) := by omega
    omega
  -- Apply Sidon. WLOG sort the pairs.
  -- Sidon needs sorted pairs. We have a + d = b + c. Want (a, d) = (b, c) sorted.
  -- Case a ≤ c: sort {a, d} and {b, c}.
  -- Apply Sidon to the multisets {a, d} = {b, c} (sorted).
  -- We use the IsSidon property which sorts pairs.
  unfold IsSidonFinset IsSidon at hSidon
  -- We have b < a and d < c. So sorted pairs: (b, a) wait that's wrong, we need (smaller, larger).
  -- a + d = b + c.  Sort (a, d) and (b, c).
  -- min(a, d), max(a, d) vs min(b, c), max(b, c).
  -- Strategy: use Sidon on pairs (a, d) and (b, c). a + d = b + c.
  -- Sidon (sorted) gives min(a, d) = min(b, c), max(a, d) = max(b, c).
  rcases le_total a d with hle1 | hle1 <;> rcases le_total b c with hle2 | hle2
  · -- a ≤ d, b ≤ c. Sidon: (a, d) and (b, c) sorted.
    have hABm : a ∈ A := ha
    have hCDm : d ∈ A := hd
    have hBBm : b ∈ A := hb
    have hCCm : c ∈ A := hc
    have ⟨hab, hcd⟩ := hSidon (a := a) (a₂ := d) (b₁ := b) (b₂ := c)
      hABm hCDm hBBm hCCm hle1 hle2 hadd
    -- a = b and d = c. But b < a contradicts a = b unless... omega.
    omega
  · -- a ≤ d, c ≤ b. Sidon: (a, d) sorted, (c, b) sorted, a + d = c + b.
    have hABm : a ∈ A := ha
    have hCDm : d ∈ A := hd
    have hBBm : c ∈ A := hc
    have hCCm : b ∈ A := hb
    have hadd' : a + d = c + b := by omega
    have ⟨hab, hcd⟩ := hSidon (a := a) (a₂ := d) (b₁ := c) (b₂ := b)
      hABm hCDm hBBm hCCm hle1 hle2 hadd'
    omega
  · -- d ≤ a, b ≤ c. Sidon: (d, a) sorted, (b, c) sorted, d + a = b + c.
    have hABm : d ∈ A := hd
    have hCDm : a ∈ A := ha
    have hBBm : b ∈ A := hb
    have hCCm : c ∈ A := hc
    have hadd' : d + a = b + c := by omega
    have ⟨hab, hcd⟩ := hSidon (a := d) (a₂ := a) (b₁ := b) (b₂ := c)
      hABm hCDm hBBm hCCm hle1 hle2 hadd'
    omega
  · -- d ≤ a, c ≤ b. Sidon: (d, a) sorted, (c, b) sorted, d + a = c + b.
    have hABm : d ∈ A := hd
    have hCDm : a ∈ A := ha
    have hBBm : c ∈ A := hb
    have hCCm : b ∈ A := hc
    have hadd' : d + a = c + b := by omega
    have ⟨hab, hcd⟩ := hSidon (a := d) (a₂ := a) (b₁ := c) (b₂ := b)
      hABm hCDm hBBm hCCm hle1 hle2 hadd'
    omega

/-- The image of the difference map on off-diagonal pairs lies in `Icc 1 (L-1)`,
provided `A ⊆ Icc (α+1) (α+L)`. -/
private theorem diff_mem_Icc {A : Finset ℕ} {α L : ℕ}
    (hA : ∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L) {p : ℕ × ℕ}
    (hp : p ∈ offDiagPairs A) :
    p.1 - p.2 ∈ Finset.Icc 1 L := by
  rw [mem_offDiagPairs] at hp
  obtain ⟨h1, h2, hlt⟩ := hp
  have ⟨ha1, ha2⟩ := hA p.1 h1
  have ⟨hb1, hb2⟩ := hA p.2 h2
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · omega
  · omega

/-! ### Lindström's bound -/

/-- **Lindström's bound (counted form)**: for a Sidon subset `A` of an
interval of length `L`, `|A|² ≤ |A| + 2·L`. -/
theorem Sidon_card_sq_le {A : Finset ℕ} {α L : ℕ}
    (hA : ∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L) (hSidon : IsSidonFinset A) :
    A.card * A.card ≤ A.card + 2 * L := by
  classical
  -- Cardinality count: |offDiag| ≤ |Icc 1 L| = L via the injection.
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2)
      (offDiagPairs A : Set (ℕ × ℕ)) := Sidon_diff_injective hSidon
  have hmap : ∀ p ∈ offDiagPairs A, p.1 - p.2 ∈ Finset.Icc 1 L := by
    intro p hp
    exact diff_mem_Icc hA hp
  have hcard_le : (offDiagPairs A).card ≤ (Finset.Icc 1 L).card := by
    have := Finset.card_le_card_of_injOn (s := offDiagPairs A) (t := Finset.Icc 1 L)
      (f := fun p : ℕ × ℕ => p.1 - p.2) hmap hinj
    exact this
  have hIcc : (Finset.Icc 1 L).card = L := by
    rw [Nat.card_Icc]; omega
  rw [hIcc] at hcard_le
  -- 2·|offDiag| = |A|² - |A|, so |A|² - |A| ≤ 2L, i.e., |A|² ≤ |A| + 2L.
  have hcd := card_offDiagPairs A
  -- hcd : 2 * (offDiagPairs A).card = A.card * A.card - A.card
  have hAcard_le : A.card ≤ A.card * A.card := by
    rcases Nat.eq_zero_or_pos A.card with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  omega

/-- The Lindström bound in `≤ √(2L) + 1` form, in `ℝ`.

From `k² ≤ k + 2L`, we get `(k - 1/2)² ≤ 2L + 1/4`, so `k ≤ 1/2 + √(2L + 1/4) ≤ √(2L) + 1`. -/
theorem Sidon_card_le_sqrt {A : Finset ℕ} {α L : ℕ}
    (hA : ∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L) (hSidon : IsSidonFinset A) :
    (A.card : ℝ) ≤ Real.sqrt (2 * L) + 1 := by
  classical
  have hsq := Sidon_card_sq_le hA hSidon
  -- (A.card : ℝ) * (A.card : ℝ) ≤ (A.card : ℝ) + 2 * L.
  have hsqR : (A.card : ℝ) * (A.card : ℝ) ≤ (A.card : ℝ) + 2 * (L : ℝ) := by
    have : ((A.card * A.card : ℕ) : ℝ) ≤ ((A.card + 2 * L : ℕ) : ℝ) := by
      exact_mod_cast hsq
    push_cast at this
    linarith
  -- Set k = A.card. We have k² ≤ k + 2L, so (k - 1)² ≤ k² ≤ ... actually let's go directly.
  -- (k - 1)·k ≤ 2L, so (k - 1)·k ≤ 2L. If k ≥ 1, then (k - 1)² ≤ (k - 1)k ≤ 2L,
  -- so k - 1 ≤ √(2L), i.e., k ≤ √(2L) + 1.
  set k : ℝ := (A.card : ℝ) with hk
  have hk_nn : 0 ≤ k := by exact_mod_cast Nat.zero_le _
  have hL_nn : (0 : ℝ) ≤ 2 * L := by positivity
  -- Case k ≤ 1: then k ≤ √(2L) + 1 trivially since √(2L) ≥ 0.
  by_cases hk_le : k ≤ 1
  · have : (0 : ℝ) ≤ Real.sqrt (2 * L) := Real.sqrt_nonneg _
    linarith
  · push_neg at hk_le
    have hk_ge_1 : 1 ≤ k := le_of_lt hk_le
    -- (k - 1) * k ≤ k² - k ≤ 2L from hsqR.
    have hkm1k : (k - 1) * k ≤ 2 * L := by nlinarith
    -- (k - 1)² ≤ (k - 1) * k since k ≥ 1 implies k - 1 ≥ 0 and k - 1 ≤ k.
    have hkm1_nn : 0 ≤ k - 1 := by linarith
    have hkm1_sq : (k - 1) ^ 2 ≤ 2 * L := by
      have hsq_le : (k - 1) ^ 2 ≤ (k - 1) * k := by
        have : (k - 1) * (k - 1) ≤ (k - 1) * k := by
          apply mul_le_mul_of_nonneg_left _ hkm1_nn
          linarith
        nlinarith
      linarith
    -- Take square roots.
    have : k - 1 ≤ Real.sqrt (2 * L) := by
      have h1 : Real.sqrt ((k - 1) ^ 2) ≤ Real.sqrt (2 * L) :=
        Real.sqrt_le_sqrt hkm1_sq
      have h2 : Real.sqrt ((k - 1) ^ 2) = k - 1 := by
        rw [Real.sqrt_sq hkm1_nn]
      linarith
    linarith

/-- Reformulation with `√2 · √L` separated out: `|A| ≤ √2·√L + 1`. -/
theorem Sidon_card_le_sqrt2_mul_sqrt {A : Finset ℕ} {α L : ℕ}
    (hA : ∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L) (hSidon : IsSidonFinset A) :
    (A.card : ℝ) ≤ Real.sqrt 2 * Real.sqrt L + 1 := by
  have h := Sidon_card_le_sqrt hA hSidon
  have hsplit : Real.sqrt (2 * L) = Real.sqrt 2 * Real.sqrt L := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsplit] at h
  exact h

/-! ### Packaging as an unconditional Sidon-interval bound

We package the Lindström bound in the same shape as the asymptotic
`SidonIntervalAsymptotic` hypothesis used in `Sqrt2BoundConditional.lean`,
but with the constant `√2` in place of `1 + ε`. This is the
*unconditional* Lindström bound. -/

/-- The unconditional Lindström bound shape, matching the structure of
`SidonIntervalAsymptotic` but with constant `√2 + 1·L^{-1/2}`. -/
theorem SidonInterval_constant_bound :
    ∀ ⦃α L : ℕ⦄,
      ∀ (A : Finset ℕ), (∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L) → IsSidonFinset A →
        (A.card : ℝ) ≤ Real.sqrt 2 * Real.sqrt L + 1 :=
  fun _ _ A hA hSidon => Sidon_card_le_sqrt2_mul_sqrt hA hSidon

end AlmostSidonSets.UpperBound
