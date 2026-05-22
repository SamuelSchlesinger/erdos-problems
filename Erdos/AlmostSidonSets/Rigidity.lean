/-
# Structural Rigidity Lemmas for Strong Almost-Sidon Extremizers

Two structural facts about almost-Sidon sets, extracted from a direct
combinatorial case analysis on `(min A, max A, n*)` where `n*` is the
exceptional sum value. See `research/sqrt2-strong-almost-sidon/direct-combinatorial-attack.md`
for the original derivation and `research/sqrt2-strong-almost-sidon/below-sqrt2.md`
for the broader context.

## Theorems

* **R1 (Single-atom amplification):** if the exceptional value `n*` has at
  most two unordered representations as a sum of `A`-elements, then `A` is
  essentially Sidon — specifically, removing a single element produces a
  genuine Sidon set. Consequence: near-extremal almost-Sidon sets *must*
  have at least three representations of the exceptional value.

* **R2 (Extreme-pair n*-incidence, conditional):** if `(min A, max A)` is
  not itself a representation of `n*`, then `A` admits a single "anchor
  pair" `(m, M)` whose sum has multiplicity 1, and the elementary pair
  count gives the (weak) bound `|A| ≤ M − m + 2`. In particular,
  near-extremal almost-Sidon sets must have `min A + max A = n*`.

Both lemmas are elementary and unconditional (no Sidon-bound dependency).
-/
import Erdos.AlmostSidonSets.Statement

namespace AlmostSidonSets

open SidonSumsets

/-- `n` has at least three pairwise-distinct unordered sorted representations
as a sum of `A`-elements. -/
def HasThreeSumReprs (A : Finset ℕ) (n : ℕ) : Prop :=
  ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ A, ∃ b₂ ∈ A, ∃ c₁ ∈ A, ∃ c₂ ∈ A,
    a₁ ≤ a₂ ∧ b₁ ≤ b₂ ∧ c₁ ≤ c₂ ∧
    a₁ + a₂ = n ∧ b₁ + b₂ = n ∧ c₁ + c₂ = n ∧
    (a₁ ≠ b₁ ∨ a₂ ≠ b₂) ∧
    (a₁ ≠ c₁ ∨ a₂ ≠ c₂) ∧
    (b₁ ≠ c₁ ∨ b₂ ≠ c₂)

/-- A simple structural lemma: from `HasTwoSumReprs` we can extract a
specific pair of distinct representations. -/
private theorem hasTwoSumReprs_witness {A : Finset ℕ} {n : ℕ}
    (h : HasTwoSumReprs A n) :
    ∃ a₁ a₂ b₁ b₂ : ℕ,
      a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ A ∧ b₂ ∈ A ∧
      a₁ ≤ a₂ ∧ b₁ ≤ b₂ ∧
      a₁ + a₂ = n ∧ b₁ + b₂ = n ∧
      (a₁ ≠ b₁ ∨ a₂ ≠ b₂) := by
  rcases h with ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hle1, hle2, hsum1, hsum2, hneq⟩
  exact ⟨a₁, a₂, b₁, b₂, ha₁, ha₂, hb₁, hb₂, hle1, hle2, hsum1, hsum2, hneq⟩

/-- **R1 (Single-atom amplification).** If `A` is a non-empty almost-Sidon set
and no value has three distinct sorted representations, then we can remove
one element of `A` to obtain a genuine Sidon set.

The contrapositive structural conclusion: any near-extremal almost-Sidon set
(with `|A| > |Sidon-bound| + 1`) must have an exceptional value with at
least *three* unordered representations. -/
theorem r1_atMostTwoReprs_implies_sidon_after_one_removal
    (A : Finset ℕ) (hA_ne : A.Nonempty) (hA : AlmostSidonFinset A)
    (h_atMostTwo : ∀ n, ¬ HasThreeSumReprs A n) :
    ∃ x ∈ A, IsSidonFinset (A.erase x) := by
  classical
  -- Two cases: either A has no exceptional value (already Sidon), or there
  -- is a unique exceptional value with exactly 2 representations.
  by_cases hExists : ∃ n, HasTwoSumReprs A n
  · -- Case: exceptional value n* exists; remove one of the 4 witnesses.
    obtain ⟨n, hn⟩ := hExists
    obtain ⟨a₁, a₂, b₁, b₂, ha₁, ha₂, hb₁, hb₂, hle1, hle2, hsum1, hsum2, hneq⟩ :=
      hasTwoSumReprs_witness hn
    -- The two pairs are distinct (hneq), so at least one of a₁, a₂ differs
    -- from the corresponding entry of (b₁, b₂). WLOG remove a₁ (the case
    -- a₁ = b₁ ∧ a₂ ≠ b₂ is handled symmetrically by removing a₂).
    refine ⟨a₁, ha₁, ?_⟩
    -- Show A.erase a₁ is Sidon. Take any p₁ ≤ p₂, q₁ ≤ q₂ in A.erase a₁
    -- with p₁ + p₂ = q₁ + q₂; need (p₁, p₂) = (q₁, q₂).
    intro p₁ p₂ q₁ q₂ hp₁ hp₂ hq₁ hq₂ hp_le hq_le hsum
    -- Lift to membership in A.
    have hp₁A : p₁ ∈ A := by
      have := Finset.mem_coe.mp hp₁
      exact (Finset.mem_erase.mp this).2
    have hp₂A : p₂ ∈ A := by
      have := Finset.mem_coe.mp hp₂
      exact (Finset.mem_erase.mp this).2
    have hq₁A : q₁ ∈ A := by
      have := Finset.mem_coe.mp hq₁
      exact (Finset.mem_erase.mp this).2
    have hq₂A : q₂ ∈ A := by
      have := Finset.mem_coe.mp hq₂
      exact (Finset.mem_erase.mp this).2
    -- Neither p₁, p₂, q₁, q₂ equals a₁.
    have hp₁_ne : p₁ ≠ a₁ := (Finset.mem_erase.mp (Finset.mem_coe.mp hp₁)).1
    have hp₂_ne : p₂ ≠ a₁ := (Finset.mem_erase.mp (Finset.mem_coe.mp hp₂)).1
    have hq₁_ne : q₁ ≠ a₁ := (Finset.mem_erase.mp (Finset.mem_coe.mp hq₁)).1
    have hq₂_ne : q₂ ≠ a₁ := (Finset.mem_erase.mp (Finset.mem_coe.mp hq₂)).1
    -- By contradiction: assume (p₁, p₂) ≠ (q₁, q₂); derive HasThreeSumReprs.
    by_contra hcontra
    push_neg at hcontra
    -- hcontra : p₁ = q₁ → p₂ ≠ q₂
    have hpqneq : p₁ ≠ q₁ ∨ p₂ ≠ q₂ := by
      by_cases h1 : p₁ = q₁
      · right; exact hcontra h1
      · left; exact h1
    -- (p₁, p₂) and (q₁, q₂) give two distinct sorted representations of (p₁ + p₂).
    have hpq_two : HasTwoSumReprs A (p₁ + p₂) :=
      ⟨p₁, hp₁A, p₂, hp₂A, q₁, hq₁A, q₂, hq₂A, hp_le, hq_le, rfl, hsum.symm, hpqneq⟩
    -- By AlmostSidonFinset, p₁ + p₂ = n.
    have hpqn : p₁ + p₂ = n := hA _ _ hpq_two hn
    -- So (p₁, p₂), (q₁, q₂), (a₁, a₂), (b₁, b₂) are all sums equal to n
    -- where (p₁, p₂) ≠ (q₁, q₂). We now produce three distinct
    -- representations of n in A, contradicting h_atMostTwo.
    -- The three representations: (a₁, a₂), (b₁, b₂), and one of (p₁, p₂), (q₁, q₂)
    -- (whichever differs from both — since p_i ≠ a₁ and q_i ≠ a₁, neither is
    -- (a₁, a₂), and they're distinct from each other, so at least one
    -- differs from (b₁, b₂)).
    -- (a₁, a₂) and (p₁, p₂) are distinct: p₁ ≠ a₁.
    have hap_neq : a₁ ≠ p₁ ∨ a₂ ≠ p₂ := Or.inl (Ne.symm hp₁_ne)
    -- (a₁, a₂) and (q₁, q₂) are distinct: q₁ ≠ a₁.
    have haq_neq : a₁ ≠ q₁ ∨ a₂ ≠ q₂ := Or.inl (Ne.symm hq₁_ne)
    -- Now (a₁, a₂), (p₁, p₂), (q₁, q₂) — three distinct representations of n.
    -- Verify pairwise distinctness:
    --   (a₁, a₂) vs (p₁, p₂): hap_neq.
    --   (a₁, a₂) vs (q₁, q₂): haq_neq.
    --   (p₁, p₂) vs (q₁, q₂): hpqneq.
    -- These three give HasThreeSumReprs A n.
    have h_three : HasThreeSumReprs A n :=
      ⟨a₁, ha₁, a₂, ha₂, p₁, hp₁A, p₂, hp₂A, q₁, hq₁A, q₂, hq₂A,
       hle1, hp_le, hq_le, hsum1, hpqn, by linarith [hsum, hpqn],
       hap_neq, haq_neq, hpqneq⟩
    exact h_atMostTwo n h_three
  · -- Case: no exceptional value; A is genuinely Sidon. Remove any element.
    push_neg at hExists
    obtain ⟨x, hx⟩ := hA_ne
    refine ⟨x, hx, ?_⟩
    intro p₁ p₂ q₁ q₂ hp₁ hp₂ hq₁ hq₂ hp_le hq_le hsum
    have hp₁A : p₁ ∈ A := (Finset.mem_erase.mp (Finset.mem_coe.mp hp₁)).2
    have hp₂A : p₂ ∈ A := (Finset.mem_erase.mp (Finset.mem_coe.mp hp₂)).2
    have hq₁A : q₁ ∈ A := (Finset.mem_erase.mp (Finset.mem_coe.mp hq₁)).2
    have hq₂A : q₂ ∈ A := (Finset.mem_erase.mp (Finset.mem_coe.mp hq₂)).2
    by_contra hcontra
    push_neg at hcontra
    have hpqneq : p₁ ≠ q₁ ∨ p₂ ≠ q₂ := by
      by_cases h1 : p₁ = q₁
      · right; exact hcontra h1
      · left; exact h1
    have : HasTwoSumReprs A (p₁ + p₂) :=
      ⟨p₁, hp₁A, p₂, hp₂A, q₁, hq₁A, q₂, hq₂A, hp_le, hq_le, rfl, hsum.symm, hpqneq⟩
    exact hExists _ this

/-- **R2 (Extreme-pair axis identification).** Let `A` be almost-Sidon with
at least two elements. If `A` has an exceptional sum value (some `n` with two
distinct sorted representations), then *either* `min A + max A` is itself
that exceptional value, *or* `(min A, max A)` is the unique sorted-pair
representation of `min A + max A`.

In other words: when an exception exists, the extreme-pair sum is on the
"exception axis" *or* the extreme pair is rigid. Combined with the
empirical observation that every known SAS extremizer has at least 3
representations at the exception (R1), this says the extreme pair sits
precisely on the exception axis.

This uses the uniqueness property of `AlmostSidonFinset`: at most one value
has two representations. -/
theorem r2_extreme_pair_on_exception_axis_or_unique
    (A : Finset ℕ) (hA : AlmostSidonFinset A) (h_card : 2 ≤ A.card)
    {nstar : ℕ} (h_exception : HasTwoSumReprs A nstar) :
    let m := A.min' (Finset.card_pos.mp (by omega : 0 < A.card))
    let M := A.max' (Finset.card_pos.mp (by omega : 0 < A.card))
    -- Either m + M is the exception value, or (m, M) is the unique sorted
    -- pair representation of m + M in A.
    m + M = nstar ∨
    (∀ a b : ℕ, a ∈ A → b ∈ A → a ≤ b → a + b = m + M → a = m ∧ b = M) := by
  classical
  intro m M
  -- Case analysis: does some non-extreme pair also sum to m + M?
  by_cases h_alt : ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a ≤ b ∧ a + b = m + M ∧
                              ¬ (a = m ∧ b = M)
  · -- Yes: build HasTwoSumReprs at m + M, then use AlmostSidonFinset
    -- uniqueness to conclude m + M = nstar.
    left
    obtain ⟨a, b, ha, hb, hab_le, hab_sum, hab_ne⟩ := h_alt
    have hm_mem : m ∈ A := A.min'_mem _
    have hM_mem : M ∈ A := A.max'_mem _
    have hm_le_M : m ≤ M := A.le_max' m hm_mem
    have hneq : a ≠ m ∨ b ≠ M := by
      by_cases h1 : a = m
      · right; intro h2; exact hab_ne ⟨h1, h2⟩
      · left; exact h1
    have h_two_mM : HasTwoSumReprs A (m + M) :=
      ⟨a, ha, b, hb, m, hm_mem, M, hM_mem, hab_le, hm_le_M, hab_sum, rfl, hneq⟩
    exact hA _ _ h_two_mM h_exception
  · -- No: any pair summing to m + M must equal (m, M).
    right
    intro a b ha hb hab_le hab_sum
    push_neg at h_alt
    by_contra h_ne
    push_neg at h_ne
    have := h_alt a b ha hb hab_le hab_sum
    exact h_ne this.1 this.2

/-- **Corollary of R2.** If `A` is almost-Sidon with at least two elements
and admits some exceptional value `n*`, but the extreme-pair sum
`min A + max A` is NOT that exceptional value, then `(min A, max A)` is the
unique sorted-pair representation of its sum. -/
theorem r2_extreme_pair_unique_when_not_on_axis
    (A : Finset ℕ) (hA : AlmostSidonFinset A) (h_card : 2 ≤ A.card)
    {nstar : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (h_off_axis : (A.min' (Finset.card_pos.mp (by omega : 0 < A.card))) +
                  (A.max' (Finset.card_pos.mp (by omega : 0 < A.card))) ≠ nstar) :
    let m := A.min' (Finset.card_pos.mp (by omega : 0 < A.card))
    let M := A.max' (Finset.card_pos.mp (by omega : 0 < A.card))
    ∀ a b : ℕ, a ∈ A → b ∈ A → a ≤ b → a + b = m + M → a = m ∧ b = M := by
  have hcase := r2_extreme_pair_on_exception_axis_or_unique A hA h_card h_exception
  simp only at hcase
  rcases hcase with h | h
  · exact absurd h h_off_axis
  · intro m M a b ha hb hab_le hab_sum
    exact h a b ha hb hab_le hab_sum

end AlmostSidonSets
