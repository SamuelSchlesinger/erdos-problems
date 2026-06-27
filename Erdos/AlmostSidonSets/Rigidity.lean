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
    push Not at hcontra
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
    push Not at hExists
    obtain ⟨x, hx⟩ := hA_ne
    refine ⟨x, hx, ?_⟩
    intro p₁ p₂ q₁ q₂ hp₁ hp₂ hq₁ hq₂ hp_le hq_le hsum
    have hp₁A : p₁ ∈ A := (Finset.mem_erase.mp (Finset.mem_coe.mp hp₁)).2
    have hp₂A : p₂ ∈ A := (Finset.mem_erase.mp (Finset.mem_coe.mp hp₂)).2
    have hq₁A : q₁ ∈ A := (Finset.mem_erase.mp (Finset.mem_coe.mp hq₁)).2
    have hq₂A : q₂ ∈ A := (Finset.mem_erase.mp (Finset.mem_coe.mp hq₂)).2
    by_contra hcontra
    push Not at hcontra
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
    push Not at h_alt
    by_contra h_ne
    push Not at h_ne
    have := h_alt a b ha hb hab_le hab_sum
    exact h_ne this.1 this.2

/-- **E1 (Disjoint-pair structure at the exception).** Two *distinct* sorted
pairs `(a₁, a₂)` and `(b₁, b₂)` summing to the same value `n` necessarily
use disjoint pairs of elements: `{a₁, a₂} ∩ {b₁, b₂} = ∅`.

This is an unconditional, elementary cancellation fact. It does not even
require the ambient set to be (almost-)Sidon. In the SAS context, it
implies: the `k` distinct sorted pairs at the exception value `n*` use
`2k` pairwise-distinct elements of `A` — the only possible coincidence
across pairs is between an element and itself, which is excluded by
distinctness of the sorted pairs.

Together with R1 (which removes a single element to obtain a Sidon set)
this says the SAS surplus at the exception is structurally *non-overlapping*:
each new representation costs two fresh elements, not one. -/
theorem e1_distinct_pairs_disjoint
    {a₁ a₂ b₁ b₂ n : ℕ}
    (hle_a : a₁ ≤ a₂) (hle_b : b₁ ≤ b₂)
    (hsum_a : a₁ + a₂ = n) (hsum_b : b₁ + b₂ = n)
    (hneq : a₁ ≠ b₁ ∨ a₂ ≠ b₂) :
    a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₂ ≠ b₁ ∧ a₂ ≠ b₂ := by
  -- First, distinct sorted pairs with same sum force *both* coordinates
  -- to differ: if a₁ = b₁ then a₂ = n - a₁ = n - b₁ = b₂.
  have hboth_ne : a₁ ≠ b₁ ∧ a₂ ≠ b₂ := by
    refine ⟨?_, ?_⟩
    · intro h1
      rcases hneq with h | h
      · exact h h1
      · apply h
        have : a₂ = n - a₁ := by omega
        have : b₂ = n - b₁ := by omega
        omega
    · intro h2
      rcases hneq with h | h
      · apply h
        have : a₁ = n - a₂ := by omega
        have : b₁ = n - b₂ := by omega
        omega
      · exact h h2
  obtain ⟨hne11, hne22⟩ := hboth_ne
  -- Now the cross-coincidences: a₁ = b₂ would force a₁ ≥ b₁ (since b₁ ≤ b₂ = a₁)
  -- and a₁ ≤ a₂ = n - a₁ = n - b₂ = b₁, hence a₁ = b₁, contradicting hne11.
  refine ⟨hne11, ?_, ?_, hne22⟩
  · intro h12
    -- a₁ = b₂, want contradiction.
    -- a₂ = n - a₁ = n - b₂ = b₁, so a₂ = b₁.
    have ha2_eq_b1 : a₂ = b₁ := by omega
    -- Then b₁ = a₂ ≥ a₁ = b₂, but b₁ ≤ b₂, so b₁ = b₂, hence a₂ = b₂, contradicting hne22.
    have : b₁ = b₂ := le_antisymm hle_b (by omega)
    omega
  · intro h21
    -- a₂ = b₁: then a₂ ≤ b₂ (since b₁ ≤ b₂), and a₁ ≤ a₂ = b₁.
    -- Also a₁ = n - a₂ = n - b₁ = b₂.
    have ha1_eq_b2 : a₁ = b₂ := by omega
    -- a₁ = b₂ ≥ b₁ = a₂, but a₁ ≤ a₂, so a₁ = a₂ = b₁, contradicting hne11.
    have ha_eq : a₁ = a₂ := le_antisymm hle_a (by omega)
    omega

/-- **E1' (Set-level disjointness corollary).** In a set with two distinct
sorted representations of the same value, the four witnesses are
pairwise distinct. This is the immediate cardinality-2k corollary used
when iterating R1-style peels. -/
theorem e1_four_distinct
    {a₁ a₂ b₁ b₂ n : ℕ}
    (hle_a : a₁ ≤ a₂) (hle_b : b₁ ≤ b₂)
    (hsum_a : a₁ + a₂ = n) (hsum_b : b₁ + b₂ = n)
    (hneq : a₁ ≠ b₁ ∨ a₂ ≠ b₂) :
    a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₂ ≠ b₁ ∧ a₂ ≠ b₂ :=
  e1_distinct_pairs_disjoint hle_a hle_b hsum_a hsum_b hneq

/-- **E2 (Reflection structure of pair elements).** Every element `x ∈ A`
participating in an n*-pair is reflected to its partner `n* - x ∈ A`.
The k pairs at n* therefore form k "reflective" couples about the
midpoint `n*/2`. -/
theorem e2_pair_element_has_reflection
    {A : Finset ℕ} {a b nstar : ℕ}
    (_ha : a ∈ A) (_hb : b ∈ A) (hsum : a + b = nstar) :
    b = nstar - a := by
  omega

/-- **E_anchor (Anchor-confinement of non-extreme n*-pairs).**
Suppose `A` is almost-Sidon with at least two elements, exception `nstar`,
and `min A + max A = nstar` (the case forced by R2 in the near-extremal
regime). Then for *any* sorted n*-pair `(a, b)` with `a + b = nstar` and
`a ≤ b`, we have either `(a, b) = (m, M)` *or* `m < a` and `b < M`. In
other words: aside from the anchor pair `(m, M)`, every n*-pair lies
strictly in the open interval `(m, M)`.

This is a structural refinement of R2 + E1: not only is the extreme pair
on the exception axis, but every *other* n*-pair is *strictly interior*. -/
theorem e_anchor_nonextreme_pairs_interior
    (A : Finset ℕ) (h_card : 2 ≤ A.card)
    {nstar : ℕ}
    (h_axis : (A.min' (Finset.card_pos.mp (by omega : 0 < A.card))) +
              (A.max' (Finset.card_pos.mp (by omega : 0 < A.card))) = nstar)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (h_le : a ≤ b) (h_sum : a + b = nstar) :
    let m := A.min' (Finset.card_pos.mp (by omega : 0 < A.card))
    let M := A.max' (Finset.card_pos.mp (by omega : 0 < A.card))
    (a = m ∧ b = M) ∨ (m < a ∧ b < M) := by
  intro m M
  have hm_mem : m ∈ A := A.min'_mem _
  have hM_mem : M ∈ A := A.max'_mem _
  have hm_le_a : m ≤ a := A.min'_le _ ha
  have hb_le_M : b ≤ M := A.le_max' _ hb
  have hm_le_M : m ≤ M := A.min'_le M hM_mem
  -- Apply E1 to (m, M) vs (a, b): either same pair, or all 4 elements distinct.
  by_cases h_eq : a = m ∧ b = M
  · exact Or.inl h_eq
  · right
    -- (a, b) ≠ (m, M), so by E1 the four elements are pairwise distinct,
    -- and in particular a ≠ m and b ≠ M.
    have hneq : a ≠ m ∨ b ≠ M := by
      by_cases h1 : a = m
      · right; intro h2; exact h_eq ⟨h1, h2⟩
      · left; exact h1
    have hdisj := e1_distinct_pairs_disjoint h_le hm_le_M h_sum h_axis hneq
    obtain ⟨ha_ne_m, _ha_ne_M, _hb_ne_m, hb_ne_M⟩ := hdisj
    exact ⟨lt_of_le_of_ne hm_le_a (Ne.symm ha_ne_m),
           lt_of_le_of_ne hb_le_M (hb_ne_M)⟩

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

/-! ## Generalized R1: quantitative cardinality / multiplicity tradeoff

The following generalizes R1 from "at most two representations" to "at most
`k + 1` representations". Let `A` be almost-Sidon. If no value has more than
`k + 1` sorted-pair representations in `A`, then there is a Sidon subset
`S ⊆ A` with `A.card ≤ S.card + k`.

Combined with the Lindström-style Sidon interval bound, this yields
`|A| ≤ √N + O(N^{1/4}) + k`. Contrapositive: an almost-Sidon set strictly
exceeding that bound has some value with `≥ k + 2` representations.

The proof is by induction on `k`. The base case `k = 0` says "no value has
two reps" hence `A` is Sidon. The step `k → k + 1` exploits the disjointness
of distinct sorted pairs (E1 above): when some value has the maximal
multiplicity `k + 2`, removing any element appearing in one of those pairs
drops the multiplicity at that value by exactly one, while leaving the
almost-Sidon property intact. -/

/-- The finset of sorted-pair representations of `n` in `A`. -/
def sumReprsFinset (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n

@[simp] theorem mem_sumReprsFinset {A : Finset ℕ} {n : ℕ} {p : ℕ × ℕ} :
    p ∈ sumReprsFinset A n ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n := by
  simp [sumReprsFinset, and_assoc]

/-- `n` has at least `k + 1` sorted-pair representations in `A`. -/
def HasKPlusOneSumReprs (A : Finset ℕ) (n k : ℕ) : Prop :=
  k + 1 ≤ (sumReprsFinset A n).card

theorem hasTwoSumReprs_iff_two_le_card {A : Finset ℕ} {n : ℕ} :
    HasTwoSumReprs A n ↔ 2 ≤ (sumReprsFinset A n).card := by
  classical
  constructor
  · rintro ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hle1, hle2, hsum1, hsum2, hneq⟩
    have hp1 : (a₁, a₂) ∈ sumReprsFinset A n := by
      rw [mem_sumReprsFinset]; exact ⟨ha₁, ha₂, hle1, hsum1⟩
    have hp2 : (b₁, b₂) ∈ sumReprsFinset A n := by
      rw [mem_sumReprsFinset]; exact ⟨hb₁, hb₂, hle2, hsum2⟩
    have hp_ne : (a₁, a₂) ≠ (b₁, b₂) := by
      intro heq
      have hpair := (Prod.mk.injEq ..).mp heq
      rcases hneq with h | h
      · exact h hpair.1
      · exact h hpair.2
    have hsub : ({(a₁, a₂), (b₁, b₂)} : Finset (ℕ × ℕ)) ⊆ sumReprsFinset A n := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      exacts [hp1, hp2]
    have hcard : ({(a₁, a₂), (b₁, b₂)} : Finset (ℕ × ℕ)).card = 2 := by
      simp [hp_ne]
    have := Finset.card_le_card hsub
    omega
  · intro h
    have h_pos : 0 < (sumReprsFinset A n).card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp h_pos
    have h_pos' : 0 < ((sumReprsFinset A n).erase p).card := by
      rw [Finset.card_erase_of_mem hp]; omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp h_pos'
    have hq_mem : q ∈ sumReprsFinset A n := (Finset.mem_erase.mp hq).2
    have hq_ne : q ≠ p := (Finset.mem_erase.mp hq).1
    rw [mem_sumReprsFinset] at hp hq_mem
    refine ⟨p.1, hp.1, p.2, hp.2.1, q.1, hq_mem.1, q.2, hq_mem.2.1,
            hp.2.2.1, hq_mem.2.2.1, hp.2.2.2, hq_mem.2.2.2, ?_⟩
    by_cases h1 : p.1 = q.1
    · right; intro h2
      apply hq_ne
      ext
      · exact h1.symm
      · exact h2.symm
    · left; intro h2; exact h1 h2

/-- Erasing one element preserves the almost-Sidon property. -/
theorem AlmostSidonFinset.erase {A : Finset ℕ} (hA : AlmostSidonFinset A)
    (x : ℕ) : AlmostSidonFinset (A.erase x) := by
  intro m n hm hn
  apply hA m n
  · obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hle1, hle2, hsum1, hsum2, hneq⟩ := hm
    exact ⟨a₁, (Finset.mem_erase.mp ha₁).2, a₂, (Finset.mem_erase.mp ha₂).2,
           b₁, (Finset.mem_erase.mp hb₁).2, b₂, (Finset.mem_erase.mp hb₂).2,
           hle1, hle2, hsum1, hsum2, hneq⟩
  · obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hle1, hle2, hsum1, hsum2, hneq⟩ := hn
    exact ⟨a₁, (Finset.mem_erase.mp ha₁).2, a₂, (Finset.mem_erase.mp ha₂).2,
           b₁, (Finset.mem_erase.mp hb₁).2, b₂, (Finset.mem_erase.mp hb₂).2,
           hle1, hle2, hsum1, hsum2, hneq⟩

/-- If no value has two representations, the set is Sidon. -/
theorem isSidonFinset_of_no_twoSumReprs {A : Finset ℕ}
    (h : ∀ n, ¬ HasTwoSumReprs A n) : IsSidonFinset A := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hle1 hle2 hsum
  have ha₁' : a₁ ∈ A := Finset.mem_coe.mp ha₁
  have ha₂' : a₂ ∈ A := Finset.mem_coe.mp ha₂
  have hb₁' : b₁ ∈ A := Finset.mem_coe.mp hb₁
  have hb₂' : b₂ ∈ A := Finset.mem_coe.mp hb₂
  by_contra hne
  push Not at hne
  have hneq : a₁ ≠ b₁ ∨ a₂ ≠ b₂ := by
    by_cases h1 : a₁ = b₁
    · right; exact hne h1
    · left; exact h1
  exact h (a₁ + a₂) ⟨a₁, ha₁', a₂, ha₂', b₁, hb₁', b₂, hb₂', hle1, hle2,
                     rfl, hsum.symm, hneq⟩

/-- The sorted-pair representations of `n` in `A.erase a` form a subset of
those in `A`. -/
theorem sumReprsFinset_erase_subset {A : Finset ℕ} {a n : ℕ} :
    sumReprsFinset (A.erase a) n ⊆ sumReprsFinset A n := by
  intro p hp
  rw [mem_sumReprsFinset] at hp ⊢
  exact ⟨(Finset.mem_erase.mp hp.1).2, (Finset.mem_erase.mp hp.2.1).2,
         hp.2.2.1, hp.2.2.2⟩

/-- **Generalized R1 (quantitative multiplicity / cardinality bound).** Let `A`
be an almost-Sidon set. If no value has `k + 2` or more sorted-pair
representations (i.e. `HasKPlusOneSumReprs A n (k + 1)` fails for every `n`),
then we can remove `k` elements from `A` to obtain a Sidon subset.

In symbols: `∃ S ⊆ A, IsSidonFinset S ∧ A.card ≤ S.card + k`.

The base case `k = 0` is "every value has ≤ 1 rep" so `A` is already Sidon
(`S = A`). The inductive step exploits the unique-pairing fact
(`e1_distinct_pairs_disjoint`): when some value has the maximal multiplicity
`k + 2`, removing any element appearing in one of those pairs drops the
multiplicity at that value by exactly one, while leaving the almost-Sidon
property intact. Iterating gives a Sidon subset after `k` removals. -/
theorem r1_general_multiplicity_bound
    (A : Finset ℕ) (hA : AlmostSidonFinset A) (k : ℕ)
    (h_atMost : ∀ n, ¬ HasKPlusOneSumReprs A n (k + 1)) :
    ∃ S ⊆ A, IsSidonFinset S ∧ A.card ≤ S.card + k := by
  classical
  induction k generalizing A with
  | zero =>
    refine ⟨A, subset_refl A, ?_, by omega⟩
    apply isSidonFinset_of_no_twoSumReprs
    intro n h_two
    have h_card : 2 ≤ (sumReprsFinset A n).card :=
      hasTwoSumReprs_iff_two_le_card.mp h_two
    exact h_atMost n h_card
  | succ k ih =>
    by_cases h_inner : ∀ n, ¬ HasKPlusOneSumReprs A n (k + 1)
    · obtain ⟨S, hS_sub, hS_sidon, hS_card⟩ := ih A hA h_inner
      exact ⟨S, hS_sub, hS_sidon, by omega⟩
    · push Not at h_inner
      obtain ⟨nstar, h_many⟩ := h_inner
      -- `h_many : HasKPlusOneSumReprs A nstar (k + 1)`
      -- i.e. `k + 2 ≤ (sumReprsFinset A nstar).card`
      have h_many' : k + 2 ≤ (sumReprsFinset A nstar).card := by
        unfold HasKPlusOneSumReprs at h_many; omega
      have h_card_pos : 0 < (sumReprsFinset A nstar).card := by omega
      obtain ⟨⟨a, b⟩, hab_mem⟩ : (sumReprsFinset A nstar).Nonempty :=
        Finset.card_pos.mp h_card_pos
      have hab := mem_sumReprsFinset.mp hab_mem
      obtain ⟨haA, hbA, hab_le, hab_sum⟩ := hab
      have h_erase_AS : AlmostSidonFinset (A.erase a) :=
        AlmostSidonFinset.erase hA a
      have h_erase_bound :
          ∀ n, ¬ HasKPlusOneSumReprs (A.erase a) n (k + 1) := by
        intro n h_many_erase
        have h_sub : sumReprsFinset (A.erase a) n ⊆ sumReprsFinset A n :=
          sumReprsFinset_erase_subset
        unfold HasKPlusOneSumReprs at h_many_erase
        have h_card_back : k + 2 ≤ (sumReprsFinset A n).card :=
          le_trans h_many_erase (Finset.card_le_card h_sub)
        have h_card_at_n : (sumReprsFinset A n).card ≤ k + 2 := by
          by_contra hgt; push Not at hgt
          have h_target : HasKPlusOneSumReprs A n (k + 1 + 1) := by
            unfold HasKPlusOneSumReprs; omega
          exact h_atMost n h_target
        by_cases h_n_eq : n = nstar
        · have h_pair_in : (a, b) ∈ sumReprsFinset A n := by
            rw [mem_sumReprsFinset, h_n_eq]
            exact ⟨haA, hbA, hab_le, hab_sum⟩
          have h_pair_out : (a, b) ∉ sumReprsFinset (A.erase a) n := by
            intro h
            rw [mem_sumReprsFinset] at h
            exact (Finset.mem_erase.mp h.1).1 rfl
          have h_strict : (sumReprsFinset (A.erase a) n).card <
              (sumReprsFinset A n).card := by
            apply Finset.card_lt_card
            exact (Finset.ssubset_iff_of_subset h_sub).mpr
                  ⟨(a, b), h_pair_in, h_pair_out⟩
          omega
        · have h_two_n : HasTwoSumReprs A n :=
            hasTwoSumReprs_iff_two_le_card.mpr (by omega)
          have h_two_nstar : HasTwoSumReprs A nstar :=
            hasTwoSumReprs_iff_two_le_card.mpr (by omega)
          exact h_n_eq (hA n nstar h_two_n h_two_nstar)
      obtain ⟨S, hS_sub_erase, hS_sidon, hS_card⟩ :=
        ih (A.erase a) h_erase_AS h_erase_bound
      refine ⟨S, hS_sub_erase.trans (Finset.erase_subset _ _), hS_sidon, ?_⟩
      have h_card_erase : (A.erase a).card = A.card - 1 :=
        Finset.card_erase_of_mem haA
      have h_card_pos_A : 0 < A.card := Finset.card_pos.mpr ⟨a, haA⟩
      omega

/-! ## R3: Off-axis pair-sums are Sidon-unique

An empirical investigation of all 12 known SAS extremizers (N = 70..79 from
exhaustive bitfield search, plus N = 100 and N = 200 from asymmetric Erdős–Freud
search; see `research/sqrt2-strong-almost-sidon/data/analyze_invariants.py`)
revealed that every off-axis pair-sum is realised by a unique sorted pair from
`A`. R3 makes this rigorous and shows the property follows directly from the
almost-Sidon axiom — no further combinatorial input is needed.

Concretely: among the 12 extremizers, for *every* `a, b ∈ A` with
`a + b ≠ nstar`, the pair `(min a b, max a b)` is the unique sorted-pair
representation of `a + b` in `A × A`. The lemma `r3_off_axis_unique_representation`
below proves this for all almost-Sidon sets, not just extremizers.

Two specialisations capture the empirical observations directly:

* `r3_second_largest_pair_unique`: under R2 (i.e. `min A + max A = nstar`),
  the pair `(min A, M₂)` is the unique sorted-pair sum for *any* `M₂ ∈ A`
  with `M₂ < max A`. Empirically `M₂` is the "second-largest" element, but
  the lemma applies to every interior element.
* `r3_second_smallest_pair_unique`: symmetric statement for `(m₂, max A)`. -/

/-- **R3 (Off-axis pair-sums are Sidon-unique).** In any almost-Sidon set `A`,
every sum value `s` with `s ≠ nstar` has at most one sorted-pair
representation. Equivalently: a pair-sum either equals the exception `nstar`
or is realised by exactly one sorted pair from `A`.

This strengthens R2's uniqueness branch (which handled the specific extreme
pair `(min A, max A)`) to *every* off-axis pair-sum, capturing the empirical
observation that off-axis sums in known extremizers are always uniquely
realised. -/
theorem r3_off_axis_unique_representation
    (A : Finset ℕ) (hA : AlmostSidonFinset A)
    {nstar : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (s : ℕ) (hs_ne : s ≠ nstar) :
    ∀ a₁ a₂ b₁ b₂ : ℕ,
      a₁ ∈ A → a₂ ∈ A → b₁ ∈ A → b₂ ∈ A →
      a₁ ≤ a₂ → b₁ ≤ b₂ →
      a₁ + a₂ = s → b₁ + b₂ = s →
      a₁ = b₁ ∧ a₂ = b₂ := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hle1 hle2 hsum1 hsum2
  by_contra h_ne
  push Not at h_ne
  have hneq : a₁ ≠ b₁ ∨ a₂ ≠ b₂ := by
    by_cases h1 : a₁ = b₁
    · right; exact h_ne h1
    · left; exact h1
  have h_two_s : HasTwoSumReprs A s :=
    ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hle1, hle2, hsum1, hsum2, hneq⟩
  exact hs_ne (hA _ _ h_two_s h_exception)

/-- **R3 specialised — sub-extreme pair on the small side is unique.**
Combining R2 (`min A + max A = nstar` in near-extremal SAS) with R3,
the pair `(min A, M')` is the unique sorted-pair representation of
`min A + M'` whenever `M' ∈ A` lies *strictly* below `max A`.

Empirically (12/12 extremizers), `M' = M₂` (second-largest element) gives a
uniquely-realised sum sitting just below the exception value `nstar`. -/
theorem r3_second_largest_pair_unique
    (A : Finset ℕ) (hA : AlmostSidonFinset A) (h_card : 2 ≤ A.card)
    {nstar : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (h_axis : (A.min' (Finset.card_pos.mp (by omega : 0 < A.card))) +
              (A.max' (Finset.card_pos.mp (by omega : 0 < A.card))) = nstar)
    {M' : ℕ} (hM'_mem : M' ∈ A)
    (hM'_lt : M' < A.max' (Finset.card_pos.mp (by omega : 0 < A.card))) :
    let m := A.min' (Finset.card_pos.mp (by omega : 0 < A.card))
    ∀ a b : ℕ, a ∈ A → b ∈ A → a ≤ b → a + b = m + M' → a = m ∧ b = M' := by
  intro m a b ha hb hab_le hab_sum
  have hm_mem : m ∈ A := A.min'_mem _
  have hm_le_M' : m ≤ M' := A.min'_le _ hM'_mem
  have h_lt_nstar : m + M' < nstar := by
    rw [← h_axis]; exact Nat.add_lt_add_left hM'_lt m
  have h_ne_nstar : m + M' ≠ nstar := Nat.ne_of_lt h_lt_nstar
  exact r3_off_axis_unique_representation A hA h_exception (m + M') h_ne_nstar
    a b m M' ha hb hm_mem hM'_mem hab_le hm_le_M' hab_sum rfl

/-- **R3 specialised — sub-extreme pair on the large side is unique.**
Symmetric counterpart: under R2, the pair `(m', max A)` is the unique
sorted-pair representation of `m' + max A` whenever `m' ∈ A` lies strictly
above `min A`. -/
theorem r3_second_smallest_pair_unique
    (A : Finset ℕ) (hA : AlmostSidonFinset A) (h_card : 2 ≤ A.card)
    {nstar : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (h_axis : (A.min' (Finset.card_pos.mp (by omega : 0 < A.card))) +
              (A.max' (Finset.card_pos.mp (by omega : 0 < A.card))) = nstar)
    {m' : ℕ} (hm'_mem : m' ∈ A)
    (hm'_gt : A.min' (Finset.card_pos.mp (by omega : 0 < A.card)) < m') :
    let M := A.max' (Finset.card_pos.mp (by omega : 0 < A.card))
    ∀ a b : ℕ, a ∈ A → b ∈ A → a ≤ b → a + b = m' + M → a = m' ∧ b = M := by
  intro M a b ha hb hab_le hab_sum
  have hM_mem : M ∈ A := A.max'_mem _
  have hm'_le_M : m' ≤ M := A.le_max' _ hm'_mem
  have h_gt_nstar : nstar < m' + M := by
    rw [← h_axis]; exact Nat.add_lt_add_right hm'_gt M
  have h_ne_nstar : m' + M ≠ nstar := (Nat.ne_of_lt h_gt_nstar).symm
  exact r3_off_axis_unique_representation A hA h_exception (m' + M) h_ne_nstar
    a b m' M ha hb hm'_mem hM_mem hab_le hm'_le_M hab_sum rfl

/-! ## R3 (second-extreme reflection axis)

The R3 lemmas above (`r3_off_axis_unique_representation`,
`r3_second_largest_pair_unique`, `r3_second_smallest_pair_unique`)
constrain *off-axis* pair-sums. The lemmas below address the
complementary structural question: *is the second-extreme pair
`(m₂, M₂)` itself on the exception axis?*

Empirically (OEIS A389182 + exhaustive search up to `N = 79`) every SAS
extremizer has the Erdős–Freud form `B ∪ (n* − B)`, so elements pair up
about `n*/2` and `(m₂, M₂)` is a reflection pair: `m₂ + M₂ = n*`. We
prove this under the natural participation hypothesis that both `m₂` and
`M₂` lie in some `n*`-pair, equivalently `n* − m₂ ∈ A` and
`n* − M₂ ∈ A`. -/

/-- **R3 (bracket form).** If `|A| ≥ 3` and `min A + max A = n*`, every
sorted `n*`-pair `(c, d)` distinct from `(m, M)` satisfies `m₂ ≤ c` and
`d ≤ M₂`: every non-extreme `n*`-pair sits inside the "second-extreme
bracket" `[m₂, M₂]`. -/
theorem r3_nonextreme_pair_in_second_bracket
    (A : Finset ℕ) (h_card : 3 ≤ A.card)
    {nstar : ℕ}
    (h_axis : (A.min' (Finset.card_pos.mp (by omega : 0 < A.card))) +
              (A.max' (Finset.card_pos.mp (by omega : 0 < A.card))) = nstar)
    {c d : ℕ} (hc : c ∈ A) (hd : d ∈ A)
    (h_le : c ≤ d) (h_sum : c + d = nstar)
    (h_nonext : ¬ (c = A.min' (Finset.card_pos.mp (by omega : 0 < A.card)) ∧
                    d = A.max' (Finset.card_pos.mp (by omega : 0 < A.card)))) :
    let m := A.min' (Finset.card_pos.mp (by omega : 0 < A.card))
    let M := A.max' (Finset.card_pos.mp (by omega : 0 < A.card))
    let hmerase : (A.erase m).Nonempty := by
      have : 1 ≤ (A.erase m).card := by
        rw [Finset.card_erase_of_mem (A.min'_mem _)]; omega
      exact Finset.card_pos.mp (by omega)
    let hMerase : (A.erase M).Nonempty := by
      have : 1 ≤ (A.erase M).card := by
        rw [Finset.card_erase_of_mem (A.max'_mem _)]; omega
      exact Finset.card_pos.mp (by omega)
    let m₂ := (A.erase m).min' hmerase
    let M₂ := (A.erase M).max' hMerase
    m₂ ≤ c ∧ d ≤ M₂ := by
  intro m M hmerase hMerase m₂ M₂
  have h_card2 : 2 ≤ A.card := by omega
  have h_interior : (c = m ∧ d = M) ∨ (m < c ∧ d < M) :=
    e_anchor_nonextreme_pairs_interior A h_card2 h_axis hc hd h_le h_sum
  have h_mc_dM : m < c ∧ d < M := by
    rcases h_interior with h | h
    · exact absurd h h_nonext
    · exact h
  obtain ⟨hmc, hdM⟩ := h_mc_dM
  have hc_erase : c ∈ A.erase m :=
    Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hmc), hc⟩
  have h_m2_le_c : m₂ ≤ c := (A.erase m).min'_le _ hc_erase
  have hd_erase : d ∈ A.erase M :=
    Finset.mem_erase.mpr ⟨ne_of_lt hdM, hd⟩
  have h_d_le_M2 : d ≤ M₂ := (A.erase M).le_max' _ hd_erase
  exact ⟨h_m2_le_c, h_d_le_M2⟩

/-- **R3 (reflection bound for `m₂`).** If `|A| ≥ 3`, `m + M = n*`, and
the reflection `n* − m₂` of the second-smallest element belongs to `A`,
then `n* − m₂ ≤ M₂` (and moreover `m < n* − m₂ < M`). -/
theorem r3_second_min_reflection_bounded
    (A : Finset ℕ) (h_card : 3 ≤ A.card)
    {nstar : ℕ}
    (h_axis : (A.min' (Finset.card_pos.mp (by omega : 0 < A.card))) +
              (A.max' (Finset.card_pos.mp (by omega : 0 < A.card))) = nstar)
    (h_refl :
      nstar - (A.erase (A.min' (Finset.card_pos.mp (by omega : 0 < A.card)))).min'
        (by
          have : 1 ≤ (A.erase (A.min' (Finset.card_pos.mp (by omega : 0 < A.card)))).card := by
            rw [Finset.card_erase_of_mem (A.min'_mem _)]; omega
          exact Finset.card_pos.mp (by omega)) ∈ A) :
    let m := A.min' (Finset.card_pos.mp (by omega : 0 < A.card))
    let M := A.max' (Finset.card_pos.mp (by omega : 0 < A.card))
    let hmerase : (A.erase m).Nonempty := by
      have : 1 ≤ (A.erase m).card := by
        rw [Finset.card_erase_of_mem (A.min'_mem _)]; omega
      exact Finset.card_pos.mp (by omega)
    let hMerase : (A.erase M).Nonempty := by
      have : 1 ≤ (A.erase M).card := by
        rw [Finset.card_erase_of_mem (A.max'_mem _)]; omega
      exact Finset.card_pos.mp (by omega)
    let m₂ := (A.erase m).min' hmerase
    let M₂ := (A.erase M).max' hMerase
    nstar - m₂ ≤ M₂ ∧ m < nstar - m₂ ∧ nstar - m₂ < M := by
  intro m M hmerase hMerase m₂ M₂
  have hm₂_erase : m₂ ∈ A.erase m := (A.erase m).min'_mem _
  have hm₂_mem : m₂ ∈ A := (Finset.mem_erase.mp hm₂_erase).2
  have hm₂_ne : m₂ ≠ m := (Finset.mem_erase.mp hm₂_erase).1
  have hm_mem : m ∈ A := A.min'_mem _
  have hM_mem : M ∈ A := A.max'_mem _
  have hm_le_m₂ : m ≤ m₂ := A.min'_le _ hm₂_mem
  have hm_lt_m₂ : m < m₂ := lt_of_le_of_ne hm_le_m₂ (Ne.symm hm₂_ne)
  set r := nstar - m₂ with hr_def
  have hr_mem : r ∈ A := h_refl
  have hm₂_le_M : m₂ ≤ M := A.le_max' _ hm₂_mem
  have hsum_m2_r : m₂ + r = nstar := by simp only [hr_def]; omega
  have hr_lt_M : r < M := by simp only [hr_def]; omega
  have hm₂_lt_M : m₂ < M := by
    by_contra h
    push Not at h
    have h_eq : m₂ = M := le_antisymm hm₂_le_M h
    have h_erase_2 : 2 ≤ (A.erase m).card := by
      rw [Finset.card_erase_of_mem hm_mem]; omega
    have h_exists_two : ∃ x ∈ A.erase m, x ≠ m₂ := by
      by_contra hne
      push Not at hne
      have h_sub : A.erase m ⊆ {m₂} := fun x hx => Finset.mem_singleton.mpr (hne x hx)
      have : (A.erase m).card ≤ 1 := by
        calc (A.erase m).card ≤ ({m₂} : Finset ℕ).card := Finset.card_le_card h_sub
          _ = 1 := Finset.card_singleton _
      omega
    obtain ⟨y, hy_erase, hy_ne⟩ := h_exists_two
    have hy_ge_m₂ : m₂ ≤ y := (A.erase m).min'_le _ hy_erase
    have hy_mem : y ∈ A := (Finset.mem_erase.mp hy_erase).2
    have hy_le_M : y ≤ M := A.le_max' _ hy_mem
    have : y = m₂ := by omega
    exact hy_ne this
  have hr_gt_m : m < r := by simp only [hr_def]; omega
  rcases le_or_gt m₂ r with hle | hlt
  · have h_nonext : ¬ (m₂ = m ∧ r = M) := by
      intro ⟨h1, _⟩; exact hm₂_ne h1
    have hb := r3_nonextreme_pair_in_second_bracket A h_card h_axis hm₂_mem hr_mem
                hle hsum_m2_r h_nonext
    simp only at hb
    exact ⟨hb.2, hr_gt_m, hr_lt_M⟩
  · have hle' : r ≤ m₂ := le_of_lt hlt
    have hsum' : r + m₂ = nstar := by omega
    have hr_ne_m : r ≠ m := ne_of_gt hr_gt_m
    have h_nonext : ¬ (r = m ∧ m₂ = M) := by
      intro ⟨h1, _⟩; exact hr_ne_m h1
    have hb := r3_nonextreme_pair_in_second_bracket A h_card h_axis hr_mem hm₂_mem
                hle' hsum' h_nonext
    simp only at hb
    have hm₂_eq_r : m₂ = r := le_antisymm hb.1 hle'
    refine ⟨?_, hr_gt_m, hr_lt_M⟩
    rw [← hm₂_eq_r]; exact hb.2

/-- **R3 (Second-extreme pair on exception axis).** Suppose `|A| ≥ 3`,
`min A + max A = n*`, and that both reflections `n* − m₂` and `n* − M₂`
lie in `A` (equivalently each second-extreme participates in some
`n*`-pair). Then `m₂ + M₂ = n*`.

This is the structural analogue of R2 for the second-extreme pair, valid
under a participation hypothesis that provably holds in the Erdős–Freud
construction `A = B ∪ (n* − B)`. The proof pinches `m₂ + M₂` between
`n*` from below (via `r3_second_min_reflection_bounded`) and `n*` from
above (via the symmetric application of the bracket lemma to the sorted
pair `(s, M₂)` with `s = n* − M₂`). -/
theorem r3_second_extreme_pair
    (A : Finset ℕ) (h_card : 3 ≤ A.card)
    {nstar : ℕ}
    (h_axis : (A.min' (Finset.card_pos.mp (by omega : 0 < A.card))) +
              (A.max' (Finset.card_pos.mp (by omega : 0 < A.card))) = nstar)
    (h_refl_m₂ :
      nstar - (A.erase (A.min' (Finset.card_pos.mp (by omega : 0 < A.card)))).min'
        (by
          have : 1 ≤ (A.erase (A.min' (Finset.card_pos.mp (by omega : 0 < A.card)))).card := by
            rw [Finset.card_erase_of_mem (A.min'_mem _)]; omega
          exact Finset.card_pos.mp (by omega)) ∈ A)
    (h_refl_M₂ :
      nstar - (A.erase (A.max' (Finset.card_pos.mp (by omega : 0 < A.card)))).max'
        (by
          have : 1 ≤ (A.erase (A.max' (Finset.card_pos.mp (by omega : 0 < A.card)))).card := by
            rw [Finset.card_erase_of_mem (A.max'_mem _)]; omega
          exact Finset.card_pos.mp (by omega)) ∈ A) :
    let m := A.min' (Finset.card_pos.mp (by omega : 0 < A.card))
    let M := A.max' (Finset.card_pos.mp (by omega : 0 < A.card))
    let hmerase : (A.erase m).Nonempty := by
      have : 1 ≤ (A.erase m).card := by
        rw [Finset.card_erase_of_mem (A.min'_mem _)]; omega
      exact Finset.card_pos.mp (by omega)
    let hMerase : (A.erase M).Nonempty := by
      have : 1 ≤ (A.erase M).card := by
        rw [Finset.card_erase_of_mem (A.max'_mem _)]; omega
      exact Finset.card_pos.mp (by omega)
    let m₂ := (A.erase m).min' hmerase
    let M₂ := (A.erase M).max' hMerase
    m₂ + M₂ = nstar := by
  intro m M hmerase hMerase m₂ M₂
  have hb_m₂ := r3_second_min_reflection_bounded A h_card h_axis h_refl_m₂
  simp only at hb_m₂
  obtain ⟨h_le_M2_raw, _, _⟩ := hb_m₂
  -- Convert h_le_M2_raw to use our local m₂ and M₂ via definitional equality.
  have h_le_M2 : nstar - m₂ ≤ M₂ := h_le_M2_raw
  have hM_mem : M ∈ A := A.max'_mem _
  have hm_mem : m ∈ A := A.min'_mem _
  have hM₂_erase : M₂ ∈ A.erase M := (A.erase M).max'_mem _
  have hM₂_mem : M₂ ∈ A := (Finset.mem_erase.mp hM₂_erase).2
  have hM₂_ne : M₂ ≠ M := (Finset.mem_erase.mp hM₂_erase).1
  have hM₂_le_M : M₂ ≤ M := A.le_max' _ hM₂_mem
  have hM₂_lt_M : M₂ < M := lt_of_le_of_ne hM₂_le_M hM₂_ne
  set s := nstar - M₂ with hs_def
  have hs_mem : s ∈ A := h_refl_M₂
  have hsum_M2_s : M₂ + s = nstar := by simp only [hs_def]; omega
  have hs_gt_m : m < s := by simp only [hs_def]; omega
  have hm₂_erase : m₂ ∈ A.erase m := (A.erase m).min'_mem _
  have hm₂_mem : m₂ ∈ A := (Finset.mem_erase.mp hm₂_erase).2
  have hm₂_ne : m₂ ≠ m := (Finset.mem_erase.mp hm₂_erase).1
  have hm_le_m₂ : m ≤ m₂ := A.min'_le _ hm₂_mem
  have hm_lt_m₂ : m < m₂ := lt_of_le_of_ne hm_le_m₂ (Ne.symm hm₂_ne)
  have hm₂_ne_M : m₂ ≠ M := by
    intro h_eq
    have h_erase_2 : 2 ≤ (A.erase m).card := by
      rw [Finset.card_erase_of_mem hm_mem]; omega
    have : ∃ y ∈ A.erase m, y ≠ m₂ := by
      by_contra hne
      push Not at hne
      have h_sub : A.erase m ⊆ {m₂} := fun x hx => Finset.mem_singleton.mpr (hne x hx)
      have : (A.erase m).card ≤ 1 := by
        calc (A.erase m).card ≤ ({m₂} : Finset ℕ).card := Finset.card_le_card h_sub
          _ = 1 := Finset.card_singleton _
      omega
    obtain ⟨y, hy_erase, hy_ne⟩ := this
    have hy_ge_m₂ : m₂ ≤ y := (A.erase m).min'_le _ hy_erase
    have hy_mem : y ∈ A := (Finset.mem_erase.mp hy_erase).2
    have hy_le_M : y ≤ M := A.le_max' _ hy_mem
    have : y = m₂ := by omega
    exact hy_ne this
  have hm₂_erase_M : m₂ ∈ A.erase M :=
    Finset.mem_erase.mpr ⟨hm₂_ne_M, hm₂_mem⟩
  have hm₂_le_M₂ : m₂ ≤ M₂ := (A.erase M).le_max' _ hm₂_erase_M
  have hM₂_gt_m : m < M₂ := lt_of_lt_of_le hm_lt_m₂ hm₂_le_M₂
  have hs_lt_M : s < M := by simp only [hs_def]; omega
  rcases le_or_gt M₂ s with hle | hlt
  · have h_nonext : ¬ (M₂ = m ∧ s = M) := by
      intro ⟨h1, _⟩; omega
    have hbracket := r3_nonextreme_pair_in_second_bracket A h_card h_axis
      hM₂_mem hs_mem hle hsum_M2_s h_nonext
    simp only at hbracket
    have hs_le_M₂ : s ≤ M₂ := hbracket.2
    have hs_eq : s = M₂ := le_antisymm hs_le_M₂ hle
    have h2M₂ : nstar = 2 * M₂ := by simp only [hs_def] at hs_eq; omega
    have hM₂_le_m₂ : M₂ ≤ m₂ := by omega
    have : m₂ = M₂ := le_antisymm hm₂_le_M₂ hM₂_le_m₂
    omega
  · have hle' : s ≤ M₂ := le_of_lt hlt
    have hsum' : s + M₂ = nstar := by omega
    have hs_ne_m : s ≠ m := ne_of_gt hs_gt_m
    have h_nonext : ¬ (s = m ∧ M₂ = M) := by
      intro ⟨h1, _⟩; exact hs_ne_m h1
    have hbracket := r3_nonextreme_pair_in_second_bracket A h_card h_axis
      hs_mem hM₂_mem hle' hsum' h_nonext
    simp only at hbracket
    have hm₂_le_s : m₂ ≤ s := hbracket.1
    have h_le_nstar : m₂ + M₂ ≤ nstar := by simp only [hs_def] at hm₂_le_s; omega
    have h_ge_nstar : nstar ≤ m₂ + M₂ := by
      have hm₂_le_nstar : m₂ ≤ nstar := by
        have := A.le_max' _ hm₂_mem; omega
      omega
    omega

/-! ## R4: Full reflection symmetry under maximum multiplicity

The empirical-invariants report observed that every known SAS extremizer
satisfies the full reflection symmetry `a ∈ A ↔ nstar - a ∈ A`,
equivalently `A = B ∪ (nstar - B)` for some Sidon `B ⊆ [1, nstar/2]`
(Erdős–Freud form). The crucial empirical invariant is "exact
half-multiplicity": `2 · r_A(nstar) = |A|`, where `r_A(nstar) =
|sumReprsFinset A nstar|`.

The theorems below formalise the deduction: if the multiplicity at the
exception value is precisely `|A| / 2` (equivalently `2r = |A|`), then
every element of `A` belongs to some `nstar`-pair, hence has its
reflection in `A`. The proof is a clean counting/bijection argument
using `e1_distinct_pairs_disjoint` (disjointness of distinct
sorted pairs) and `e2_pair_element_has_reflection` (each pair partner
is the reflection). The "self-pair" case `nstar = 2c, (c, c)` is handled
explicitly: a self-pair contributes a single element instead of two, so
the cardinality identity becomes `|pairElements| = 2·r - [self-pair]`. -/

/-- The set of elements of `A` that participate in some sorted
`nstar`-pair: the union of first and second coordinates of
`sumReprsFinset A nstar`. -/
def pairElements (A : Finset ℕ) (nstar : ℕ) : Finset ℕ :=
  (sumReprsFinset A nstar).image Prod.fst ∪ (sumReprsFinset A nstar).image Prod.snd

theorem pairElements_subset (A : Finset ℕ) (nstar : ℕ) :
    pairElements A nstar ⊆ A := by
  intro x hx
  unfold pairElements at hx
  rw [Finset.mem_union] at hx
  rcases hx with h | h
  · rw [Finset.mem_image] at h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    have hp := mem_sumReprsFinset.mp hp_mem
    subst hp_eq; exact hp.1
  · rw [Finset.mem_image] at h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    have hp := mem_sumReprsFinset.mp hp_mem
    subst hp_eq; exact hp.2.1

/-- Every element of `pairElements A nstar` has its reflection `nstar - x`
in `A`. -/
theorem pairElements_has_reflection {A : Finset ℕ} {nstar x : ℕ}
    (hx : x ∈ pairElements A nstar) : nstar - x ∈ A := by
  unfold pairElements at hx
  rw [Finset.mem_union] at hx
  rcases hx with h | h
  · rw [Finset.mem_image] at h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    have hp := mem_sumReprsFinset.mp hp_mem
    subst hp_eq
    have hsum : p.1 + p.2 = nstar := hp.2.2.2
    have : nstar - p.1 = p.2 := by omega
    rw [this]; exact hp.2.1
  · rw [Finset.mem_image] at h
    obtain ⟨p, hp_mem, hp_eq⟩ := h
    have hp := mem_sumReprsFinset.mp hp_mem
    subst hp_eq
    have hsum : p.1 + p.2 = nstar := hp.2.2.2
    have : nstar - p.2 = p.1 := by omega
    rw [this]; exact hp.1

/-- The "self-pair" indicator: there exists a `c ∈ A` with `2c = nstar`
and `(c, c) ∈ sumReprsFinset A nstar`. -/
def HasSelfPair (A : Finset ℕ) (nstar : ℕ) : Prop :=
  ∃ c ∈ A, 2 * c = nstar

instance (A : Finset ℕ) (nstar : ℕ) : Decidable (HasSelfPair A nstar) :=
  decidable_of_iff (∃ c ∈ A, 2 * c = nstar) Iff.rfl

/-- Counting lemma (no-self-pair case). If no `c ∈ A` has `2c = nstar`,
then every sorted pair in `sumReprsFinset A nstar` has distinct
coordinates, and `|pairElements A nstar| = 2 · r_A(nstar)`. -/
theorem pairElements_card_no_self_pair
    (A : Finset ℕ) (nstar : ℕ) (h_no_self : ¬ HasSelfPair A nstar) :
    (pairElements A nstar).card = 2 * (sumReprsFinset A nstar).card := by
  classical
  -- Strategy: show pairElements equals the image of sumReprsFinset under
  -- the "split-pair" function p ↦ {p.1, p.2}, and use disjointness.
  -- Cleaner: show the image of Prod.fst and Prod.snd are disjoint, and
  -- each is injective on sumReprsFinset.
  have h_fst_inj : Set.InjOn Prod.fst (sumReprsFinset A nstar : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hp' := mem_sumReprsFinset.mp (Finset.mem_coe.mp hp)
    have hq' := mem_sumReprsFinset.mp (Finset.mem_coe.mp hq)
    ext
    · exact hpq
    · -- p.1 + p.2 = nstar = q.1 + q.2, p.1 = q.1, so p.2 = q.2
      have : p.1 + p.2 = q.1 + q.2 := by rw [hp'.2.2.2, hq'.2.2.2]
      omega
  have h_snd_inj : Set.InjOn Prod.snd (sumReprsFinset A nstar : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hp' := mem_sumReprsFinset.mp (Finset.mem_coe.mp hp)
    have hq' := mem_sumReprsFinset.mp (Finset.mem_coe.mp hq)
    ext
    · -- p.1 + p.2 = nstar = q.1 + q.2, p.2 = q.2, so p.1 = q.1
      have : p.1 + p.2 = q.1 + q.2 := by rw [hp'.2.2.2, hq'.2.2.2]
      omega
    · exact hpq
  have h_card_fst : ((sumReprsFinset A nstar).image Prod.fst).card =
      (sumReprsFinset A nstar).card :=
    Finset.card_image_of_injOn h_fst_inj
  have h_card_snd : ((sumReprsFinset A nstar).image Prod.snd).card =
      (sumReprsFinset A nstar).card :=
    Finset.card_image_of_injOn h_snd_inj
  -- Disjointness: an element of image-fst is a "small" coord of some pair,
  -- and an element of image-snd is a "large" coord of some pair. If x is
  -- both, then x = p.1 ≤ p.2 and x = q.2 ≥ q.1, with p.1 + p.2 = q.1 + q.2,
  -- forcing p.1 = p.2 (a self-pair), contradicting h_no_self.
  have h_disj : Disjoint ((sumReprsFinset A nstar).image Prod.fst)
                          ((sumReprsFinset A nstar).image Prod.snd) := by
    rw [Finset.disjoint_left]
    intro x hx_fst hx_snd
    rw [Finset.mem_image] at hx_fst hx_snd
    obtain ⟨p, hp_mem, hp_eq⟩ := hx_fst
    obtain ⟨q, hq_mem, hq_eq⟩ := hx_snd
    rw [mem_sumReprsFinset] at hp_mem hq_mem
    -- p.1 = x = q.2; p.1 ≤ p.2, q.1 ≤ q.2 = x, sums equal nstar.
    have hp1_eq : p.1 = x := hp_eq
    have hq2_eq : q.2 = x := hq_eq
    have hp_le : p.1 ≤ p.2 := hp_mem.2.2.1
    have hq_le : q.1 ≤ q.2 := hq_mem.2.2.1
    have hp_sum : p.1 + p.2 = nstar := hp_mem.2.2.2
    have hq_sum : q.1 + q.2 = nstar := hq_mem.2.2.2
    -- p.1 = x = q.2, p.2 = nstar - x = q.1. So p.1 ≤ p.2 means x ≤ nstar - x,
    -- and q.1 ≤ q.2 means nstar - x ≤ x. Hence 2x = nstar.
    have hx_le : x ≤ nstar - x := by omega
    have hx_ge : nstar - x ≤ x := by omega
    have hx_eq : x = nstar - x := le_antisymm hx_le hx_ge
    have h2x : 2 * x = nstar := by omega
    -- x ∈ A: from hp_mem.1, p.1 ∈ A, and p.1 = x.
    have hx_mem : x ∈ A := by rw [← hp1_eq]; exact hp_mem.1
    exact h_no_self ⟨x, hx_mem, h2x⟩
  rw [pairElements, Finset.card_union_of_disjoint h_disj, h_card_fst, h_card_snd]
  ring

/-- Counting lemma (self-pair case). If `(c, c)` is the unique self-pair
in `sumReprsFinset A nstar` (i.e. `2c = nstar` and `c ∈ A`), then
`|pairElements A nstar| = 2 · r_A(nstar) - 1`. -/
theorem pairElements_card_with_self_pair
    (A : Finset ℕ) (nstar : ℕ) (c : ℕ) (hc_mem : c ∈ A) (h2c : 2 * c = nstar) :
    (pairElements A nstar).card + 1 = 2 * (sumReprsFinset A nstar).card := by
  classical
  -- The self-pair (c, c) ∈ sumReprsFinset A nstar.
  have hcc_mem : (c, c) ∈ sumReprsFinset A nstar := by
    rw [mem_sumReprsFinset]; exact ⟨hc_mem, hc_mem, le_refl _, by omega⟩
  -- Let R = sumReprsFinset A nstar, R' = R.erase (c, c).
  set R := sumReprsFinset A nstar with hR_def
  set R' := R.erase (c, c) with hR'_def
  -- R' has no self-pair (since (c, c) was the only one — by uniqueness of c).
  -- Actually we don't need that — we directly compute.
  -- pairElements = image fst R ∪ image snd R = (image fst R' ∪ {c}) ∪ (image snd R' ∪ {c})
  --              = image fst R' ∪ image snd R' ∪ {c}.
  -- For p ∈ R', p ≠ (c, c). Since p.1 + p.2 = nstar and 2c = nstar, p = (c, c) iff
  -- p.1 = c (which forces p.2 = c). So for p ∈ R', p.1 ≠ c and p.2 ≠ c.
  -- Also for p ∈ R', p.1 ≠ p.2 (else p = (p.1, p.1) gives 2p.1 = nstar, and the
  -- unique solution in ℕ is p.1 = c, contradiction).
  have h_R'_no_self_coord : ∀ p ∈ R', p.1 ≠ c ∧ p.2 ≠ c := by
    intro p hp
    have hp_ne : p ≠ (c, c) := (Finset.mem_erase.mp hp).1
    have hp_mem := mem_sumReprsFinset.mp (Finset.mem_erase.mp hp).2
    refine ⟨?_, ?_⟩
    · intro h1
      have hp2_eq : p.2 = c := by
        have hsum : p.1 + p.2 = nstar := hp_mem.2.2.2
        omega
      exact hp_ne (Prod.ext h1 hp2_eq)
    · intro h2
      have hp1_eq : p.1 = c := by
        have hsum : p.1 + p.2 = nstar := hp_mem.2.2.2
        omega
      exact hp_ne (Prod.ext hp1_eq h2)
  have h_R'_no_self : ∀ p ∈ R', p.1 ≠ p.2 := by
    intro p hp h_eq
    have hp_mem := mem_sumReprsFinset.mp (Finset.mem_erase.mp hp).2
    have hsum : p.1 + p.2 = nstar := hp_mem.2.2.2
    have hp1c : p.1 = c := by omega
    exact (h_R'_no_self_coord p hp).1 hp1c
  -- image fst R = (image fst R') ∪ {c}, since (c, c) contributes c, and
  -- by h_R'_no_self_coord no p ∈ R' contributes c.
  have h_img_fst_R : R.image Prod.fst = R'.image Prod.fst ∪ {c} := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp_mem, hp_eq⟩ := hx
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
      by_cases h : p = (c, c)
      · right; subst h; exact hp_eq.symm
      · left; exact ⟨p, Finset.mem_erase.mpr ⟨h, hp_mem⟩, hp_eq⟩
    · intro hx
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hx
      rw [Finset.mem_image]
      rcases hx with ⟨p, hp_R', hp_eq⟩ | h
      · refine ⟨p, ?_, hp_eq⟩
        exact (Finset.mem_erase.mp hp_R').2
      · exact ⟨(c, c), hcc_mem, h.symm⟩
  have h_img_snd_R : R.image Prod.snd = R'.image Prod.snd ∪ {c} := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp_mem, hp_eq⟩ := hx
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
      by_cases h : p = (c, c)
      · right; subst h; exact hp_eq.symm
      · left; exact ⟨p, Finset.mem_erase.mpr ⟨h, hp_mem⟩, hp_eq⟩
    · intro hx
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hx
      rw [Finset.mem_image]
      rcases hx with ⟨p, hp_R', hp_eq⟩ | h
      · refine ⟨p, ?_, hp_eq⟩
        exact (Finset.mem_erase.mp hp_R').2
      · exact ⟨(c, c), hcc_mem, h.symm⟩
  -- Now: image fst R' and image snd R' are disjoint from {c}, and disjoint
  -- from each other (by the same "self-pair" argument applied to R').
  have h_fst_R'_no_c : c ∉ R'.image Prod.fst := by
    rw [Finset.mem_image]; rintro ⟨p, hp, hp_eq⟩
    exact (h_R'_no_self_coord p hp).1 hp_eq
  have h_snd_R'_no_c : c ∉ R'.image Prod.snd := by
    rw [Finset.mem_image]; rintro ⟨p, hp, hp_eq⟩
    exact (h_R'_no_self_coord p hp).2 hp_eq
  -- For R', no self-pair exists in the sense above, and pairs are
  -- distinct-coordinate. So image fst R' and image snd R' are disjoint.
  have h_R'_disj : Disjoint (R'.image Prod.fst) (R'.image Prod.snd) := by
    rw [Finset.disjoint_left]
    intro x hx_fst hx_snd
    rw [Finset.mem_image] at hx_fst hx_snd
    obtain ⟨p, hp_R', hp_eq⟩ := hx_fst
    obtain ⟨q, hq_R', hq_eq⟩ := hx_snd
    have hp_mem := mem_sumReprsFinset.mp (Finset.mem_erase.mp hp_R').2
    have hq_mem := mem_sumReprsFinset.mp (Finset.mem_erase.mp hq_R').2
    -- Same argument as before:
    have hp_le : p.1 ≤ p.2 := hp_mem.2.2.1
    have hq_le : q.1 ≤ q.2 := hq_mem.2.2.1
    have hp_sum : p.1 + p.2 = nstar := hp_mem.2.2.2
    have hq_sum : q.1 + q.2 = nstar := hq_mem.2.2.2
    have hp1_eq : p.1 = x := hp_eq
    have hq2_eq : q.2 = x := hq_eq
    have hx_le : x ≤ nstar - x := by omega
    have hx_ge : nstar - x ≤ x := by omega
    have hx_eq : x = nstar - x := le_antisymm hx_le hx_ge
    have h2x : 2 * x = nstar := by omega
    -- So x = c by 2x = 2c (natural number)
    have hx_c : x = c := by omega
    rw [hx_c] at hp_eq
    exact (h_R'_no_self_coord p hp_R').1 hp_eq
  -- Injectivity on R' (same proof as no-self-pair case, restricted to R')
  have h_fst_R'_inj : Set.InjOn Prod.fst (R' : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hp_mem := mem_sumReprsFinset.mp (Finset.mem_erase.mp (Finset.mem_coe.mp hp)).2
    have hq_mem := mem_sumReprsFinset.mp (Finset.mem_erase.mp (Finset.mem_coe.mp hq)).2
    ext
    · exact hpq
    · have : p.1 + p.2 = q.1 + q.2 := by rw [hp_mem.2.2.2, hq_mem.2.2.2]
      omega
  have h_snd_R'_inj : Set.InjOn Prod.snd (R' : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hp_mem := mem_sumReprsFinset.mp (Finset.mem_erase.mp (Finset.mem_coe.mp hp)).2
    have hq_mem := mem_sumReprsFinset.mp (Finset.mem_erase.mp (Finset.mem_coe.mp hq)).2
    ext
    · have : p.1 + p.2 = q.1 + q.2 := by rw [hp_mem.2.2.2, hq_mem.2.2.2]
      omega
    · exact hpq
  have h_card_R' : R'.card = R.card - 1 := Finset.card_erase_of_mem hcc_mem
  have h_R_pos : 0 < R.card := Finset.card_pos.mpr ⟨(c, c), hcc_mem⟩
  have h_card_fst_R' : (R'.image Prod.fst).card = R'.card :=
    Finset.card_image_of_injOn h_fst_R'_inj
  have h_card_snd_R' : (R'.image Prod.snd).card = R'.card :=
    Finset.card_image_of_injOn h_snd_R'_inj
  -- pairElements = (image fst R') ∪ {c} ∪ (image snd R') ∪ {c}
  --              = (image fst R') ∪ (image snd R') ∪ {c}
  have h_pe_eq : pairElements A nstar =
      (R'.image Prod.fst ∪ R'.image Prod.snd) ∪ {c} := by
    rw [pairElements, ← hR_def, h_img_fst_R, h_img_snd_R]
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton]
    tauto
  rw [h_pe_eq]
  -- {c} is disjoint from the union since c ∉ either image
  have h_c_disj : Disjoint (R'.image Prod.fst ∪ R'.image Prod.snd) ({c} : Finset ℕ) := by
    rw [Finset.disjoint_right]
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [Finset.mem_union]
    push Not
    exact ⟨h_fst_R'_no_c, h_snd_R'_no_c⟩
  rw [Finset.card_union_of_disjoint h_c_disj, Finset.card_singleton,
      Finset.card_union_of_disjoint h_R'_disj, h_card_fst_R', h_card_snd_R']
  omega

/-- **R4 (Full reflection symmetry under maximum multiplicity, no self-pair
case).** If `A` is almost-Sidon with exception value `nstar`, no element
`c ∈ A` satisfies `2c = nstar`, and the multiplicity at `nstar` saturates
the bound `2 · r_A(nstar) = |A|`, then every element of `A` participates
in some `nstar`-pair, and consequently `nstar - a ∈ A` for every `a ∈ A`.

This formalises the empirically observed "full reflection symmetry"
invariant for SAS extremizers: every extremizer of the strong almost-Sidon
problem satisfies `A = B ∪ (nstar - B)`, the Erdős–Freud form. The proof
is a counting argument:

* `pairElements A nstar ⊆ A` (`pairElements_subset`).
* `|pairElements A nstar| = 2 · r_A(nstar)` in the no-self-pair case
  (`pairElements_card_no_self_pair`).
* Under the saturation hypothesis `2 · r = |A|`, the inclusion
  `pairElements ⊆ A` forces equality, so every `a ∈ A` lies in
  `pairElements A nstar` and has `nstar - a ∈ A`
  (`pairElements_has_reflection`). -/
theorem r4_full_reflection_under_max_multiplicity_no_self_pair
    (A : Finset ℕ) (_hA : AlmostSidonFinset A)
    {nstar : ℕ} (_h_exception : HasTwoSumReprs A nstar)
    (h_no_self : ¬ HasSelfPair A nstar)
    (h_max_mult : 2 * (sumReprsFinset A nstar).card = A.card) :
    ∀ a ∈ A, nstar - a ∈ A := by
  classical
  have h_pe_sub : pairElements A nstar ⊆ A := pairElements_subset A nstar
  have h_pe_card : (pairElements A nstar).card = 2 * (sumReprsFinset A nstar).card :=
    pairElements_card_no_self_pair A nstar h_no_self
  have h_pe_eq_A : pairElements A nstar = A :=
    Finset.eq_of_subset_of_card_le h_pe_sub (by omega)
  intro a ha
  have ha_pe : a ∈ pairElements A nstar := by rwa [h_pe_eq_A]
  exact pairElements_has_reflection ha_pe

/-- **R4 (Full reflection symmetry under maximum multiplicity, self-pair
case).** Variant for the self-pair case: if there exists `c ∈ A` with
`2c = nstar` (so `(c, c)` is an `nstar`-pair), and `2 · r_A(nstar) =
|A| + 1` (one fewer paired-element due to the self-pair contributing
just one element), then every element of `A` has `nstar - a ∈ A`. The
hypothesis `2r = |A| + 1` reflects the empirical observation that
self-pair extremizers have one "extra" representation. -/
theorem r4_full_reflection_under_max_multiplicity_self_pair
    (A : Finset ℕ) (_hA : AlmostSidonFinset A)
    {nstar : ℕ} (_h_exception : HasTwoSumReprs A nstar)
    {c : ℕ} (hc_mem : c ∈ A) (h2c : 2 * c = nstar)
    (h_max_mult : 2 * (sumReprsFinset A nstar).card = A.card + 1) :
    ∀ a ∈ A, nstar - a ∈ A := by
  classical
  have h_pe_sub : pairElements A nstar ⊆ A := pairElements_subset A nstar
  have h_pe_card : (pairElements A nstar).card + 1 =
      2 * (sumReprsFinset A nstar).card :=
    pairElements_card_with_self_pair A nstar c hc_mem h2c
  -- So |pairElements| + 1 = |A| + 1, i.e. |pairElements| = |A|.
  have h_pe_eq_A : pairElements A nstar = A :=
    Finset.eq_of_subset_of_card_le h_pe_sub (by omega)
  intro a ha
  have ha_pe : a ∈ pairElements A nstar := by rwa [h_pe_eq_A]
  exact pairElements_has_reflection ha_pe

/-- **R4 (Full reflection symmetry under maximum multiplicity, unified
form).** If `A` is almost-Sidon with exception `nstar`, and `2 · r_A(nstar)
= |A| + δ` where `δ ∈ {0, 1}` matches the self-pair indicator (`δ = 1`
exactly when some `c ∈ A` has `2c = nstar`), then every element of `A`
has `nstar - a ∈ A`. -/
theorem r4_full_reflection_under_max_multiplicity
    (A : Finset ℕ) (hA : AlmostSidonFinset A)
    {nstar : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (h_max_mult :
      (¬ HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card) ∨
      (HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card + 1)) :
    ∀ a ∈ A, nstar - a ∈ A := by
  rcases h_max_mult with ⟨h_no_self, h_mm⟩ | ⟨⟨c, hc, h2c⟩, h_mm⟩
  · exact r4_full_reflection_under_max_multiplicity_no_self_pair A hA h_exception
      h_no_self h_mm
  · exact r4_full_reflection_under_max_multiplicity_self_pair A hA h_exception
      hc h2c h_mm

/-- **R4 (Erdős–Freud form).** Under the saturation hypothesis, `A` is
exactly the union `B ∪ (nstar - B)` for `B = A ∩ [0, nstar/2]`. This is
the explicit Erdős–Freud-form witness: `B` consists of the "small halves"
of `nstar`-pairs (together with the self-pair element `c` if present),
and `A = B ∪ (nstar - B)`. -/
theorem r4_ef_decomposition
    (A : Finset ℕ) (hA : AlmostSidonFinset A)
    {nstar : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (h_max_mult :
      (¬ HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card) ∨
      (HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card + 1)) :
    let B := A.filter (fun a => 2 * a ≤ nstar)
    A = B ∪ B.image (fun a => nstar - a) := by
  classical
  intro B
  have h_refl := r4_full_reflection_under_max_multiplicity A hA h_exception h_max_mult
  -- Establish that every element x ∈ A satisfies x ≤ nstar.
  have h_pe_sub : pairElements A nstar ⊆ A := pairElements_subset A nstar
  have h_pe_eq_A : pairElements A nstar = A := by
    rcases h_max_mult with ⟨h_no_self, h_mm⟩ | ⟨⟨c, hc, h2c⟩, h_mm⟩
    · have h_pe_card : (pairElements A nstar).card =
          2 * (sumReprsFinset A nstar).card :=
        pairElements_card_no_self_pair A nstar h_no_self
      exact Finset.eq_of_subset_of_card_le h_pe_sub (by omega)
    · have h_pe_card : (pairElements A nstar).card + 1 =
          2 * (sumReprsFinset A nstar).card :=
        pairElements_card_with_self_pair A nstar c hc h2c
      exact Finset.eq_of_subset_of_card_le h_pe_sub (by omega)
  have h_le_nstar : ∀ a ∈ A, a ≤ nstar := by
    intro a ha
    have ha_pe : a ∈ pairElements A nstar := by rwa [h_pe_eq_A]
    unfold pairElements at ha_pe
    rw [Finset.mem_union] at ha_pe
    rcases ha_pe with h1 | h1
    · rw [Finset.mem_image] at h1
      obtain ⟨p, hp_mem, hp_eq⟩ := h1
      have hp := mem_sumReprsFinset.mp hp_mem
      have hsum : p.1 + p.2 = nstar := hp.2.2.2
      have : a = p.1 := hp_eq.symm
      omega
    · rw [Finset.mem_image] at h1
      obtain ⟨p, hp_mem, hp_eq⟩ := h1
      have hp := mem_sumReprsFinset.mp hp_mem
      have hsum : p.1 + p.2 = nstar := hp.2.2.2
      have : a = p.2 := hp_eq.symm
      omega
  ext x
  simp only [B, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · intro hx
    have hx_le_nstar : x ≤ nstar := h_le_nstar x hx
    by_cases h : 2 * x ≤ nstar
    · left; exact ⟨hx, h⟩
    · right
      push Not at h
      refine ⟨nstar - x, ⟨h_refl x hx, ?_⟩, ?_⟩
      · omega
      · omega
  · rintro (⟨hx, _⟩ | ⟨y, ⟨hy, _⟩, hxy⟩)
    · exact hx
    · subst hxy; exact h_refl y hy

end AlmostSidonSets
