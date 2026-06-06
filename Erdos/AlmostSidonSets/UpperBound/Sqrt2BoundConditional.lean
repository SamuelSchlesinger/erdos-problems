/-
# Strong Almost-Sidon Upper Bound: `|A| ≤ (√2 + ε)·√N`, Conditional Version

This file proves the `√2·√N` upper bound for strong almost-Sidon sets in
`{1, ..., N}` *assuming* an asymptotic Erdős–Turán/Lindström bound for Sidon
sets in an interval. The unconditional Sidon-interval bound is proved
separately in `SidonInterval.lean` and combined with this theorem in
`Sqrt2Bound.lean`.

The proof strategy: if `A` is strong almost-Sidon with an exceptional sum
value `n*`, split `A` at `⌊n*/2⌋`. By `AlmostSidonSets.Structure`, both
halves `A_-` and `A_+` are genuinely Sidon and partition `A`. Apply the
Sidon-interval bound to each half, then use the Cauchy–Schwarz bound
`√x + √(N - x) ≤ √(2N)` from `SplitOptimization.lean`.
-/
import Erdos.AlmostSidonSets.Statement
import Erdos.AlmostSidonSets.Structure
import Erdos.AlmostSidonSets.UpperBound.SplitOptimization

namespace AlmostSidonSets.UpperBound

open Real
open AlmostSidonSets SidonSumsets

/-- The shape of the asymptotic Sidon-interval bound we assume.

For every `ε > 0` there is a length threshold `L₀` such that every Sidon
subset of an interval of length `L ≥ L₀` has cardinality at most
`(1 + ε)·√L`. This is the asymptotic Erdős–Turán/Lindström statement.
The interval is allowed to be shifted (parameter `α`) because the Sidon
condition is translation-invariant. -/
def SidonIntervalAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ ⦃α L : ℕ⦄, L₀ ≤ L →
    ∀ (A : Finset ℕ), (∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L) → IsSidonFinset A →
      (A.card : ℝ) ≤ (1 + ε) * Real.sqrt L

/-- Trivial bound: a finite set of naturals contained in the interval
`[α+1, α+L]` has cardinality at most `L`. -/
private theorem card_le_of_subset_interval {A : Finset ℕ} {α L : ℕ}
    (hA : ∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L) :
    A.card ≤ L := by
  classical
  have hsub : A ⊆ Finset.Icc (α + 1) (α + L) := by
    intro a ha
    rcases hA a ha with ⟨h1, h2⟩
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hcard : A.card ≤ (Finset.Icc (α + 1) (α + L)).card :=
    Finset.card_le_card hsub
  have hIcc : (Finset.Icc (α + 1) (α + L)).card = L := by
    rw [Nat.card_Icc]; omega
  rw [hIcc] at hcard
  exact hcard

/-- Uniform Sidon-interval bound: combining the asymptotic Sidon-interval bound
with the trivial cardinality bound. For any Sidon `A ⊆ [α+1, α+L]`,

  `|A| ≤ (1 + ε)·√L + L₀`

where `L₀` is the threshold provided by the asymptotic bound. -/
private theorem sidon_uniform_bound
    (hSI : SidonIntervalAsymptotic) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ ⦃α L : ℕ⦄,
      ∀ (A : Finset ℕ), (∀ a ∈ A, α + 1 ≤ a ∧ a ≤ α + L) → IsSidonFinset A →
        (A.card : ℝ) ≤ (1 + ε) * Real.sqrt L + L₀ := by
  obtain ⟨L₀, hL₀⟩ := hSI ε hε
  refine ⟨L₀, ?_⟩
  intro α L A hA hSidon
  by_cases hL : L₀ ≤ L
  · have := hL₀ hL A hA hSidon
    have : (A.card : ℝ) ≤ (1 + ε) * Real.sqrt L := this
    have hL₀nn : (0 : ℝ) ≤ L₀ := Nat.cast_nonneg _
    linarith
  · have hLlt : L < L₀ := lt_of_not_ge hL
    have hcard : A.card ≤ L := card_le_of_subset_interval hA
    have hcardR : (A.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hcard
    have hLL₀ : (L : ℝ) ≤ (L₀ : ℝ) := by exact_mod_cast hLlt.le
    have hsqrt_nn : 0 ≤ (1 + ε) * Real.sqrt L := by
      have : 0 ≤ 1 + ε := by linarith
      positivity
    linarith

/-- A useful packaging: the midpoint split partitions `A`'s cardinality. -/
private theorem split_card_eq {A : Finset ℕ} (n : ℕ) :
    (lowerPart n A).card + (upperPart n A).card = A.card :=
  card_lowerPart_add_card_upperPart n A

/-- Helper: every element of `lowerPart n A` lies in `{1, ..., ⌊n/2⌋}`,
provided every element of `A` lies in `{1, ..., N}`. -/
private theorem lowerPart_mem_interval {A : Finset ℕ} {n N : ℕ}
    (hA : ∀ a ∈ A, a ∈ ground N) (a : ℕ) (ha : a ∈ lowerPart n A) :
    1 ≤ a ∧ a ≤ n / 2 := by
  have ha' := mem_lowerPart.mp ha
  have hA' := hA a ha'.1
  have h1 : 1 ≤ a := (mem_ground.mp hA').1
  have h2 : 2 * a ≤ n := ha'.2
  have hadiv : a ≤ n / 2 := by
    have : a ≤ n / 2 := Nat.le_div_iff_mul_le (by decide : (0:ℕ) < 2)
      |>.mpr (by linarith)
    exact this
  exact ⟨h1, hadiv⟩

/-- Helper: every element of `upperPart n A` lies in `(⌊n/2⌋, N]`,
provided every element of `A` lies in `{1, ..., N}`. -/
private theorem upperPart_mem_interval {A : Finset ℕ} {n N : ℕ}
    (hA : ∀ a ∈ A, a ∈ ground N) (a : ℕ) (ha : a ∈ upperPart n A) :
    n / 2 + 1 ≤ a ∧ a ≤ N := by
  have ha' := mem_upperPart.mp ha
  have hA' := hA a ha'.1
  have h2 : n < 2 * a := ha'.2
  have hN : a ≤ N := (mem_ground.mp hA').2
  have hge : n / 2 + 1 ≤ a := by
    have hdiv : n / 2 < a := by omega
    omega
  exact ⟨hge, hN⟩

/-- The main conditional theorem.

Assuming the asymptotic Sidon-interval bound `SidonIntervalAsymptotic`,
every strong almost-Sidon set `A ⊆ {1, ..., N}` satisfies
`|A| ≤ (√2 + ε) · √N` for `N` large enough (depending on `ε`).

This is the headline structural result; the unconditional version is in
`Sqrt2Bound.lean`, obtained by combining this with `SidonInterval.lean`. -/
theorem strong_almostSidon_card_le_sqrt2_sqrt_of_sidon_interval
    (hSI : SidonIntervalAsymptotic) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ ⦃N : ℕ⦄, N₀ ≤ N →
      ∀ A : Finset ℕ, AlmostSidonInInterval A N →
        (A.card : ℝ) ≤ (Real.sqrt 2 + ε) * Real.sqrt N := by
  intro ε hε
  -- Strategy: pick ε' small so that (1 + ε')·√2 + (slack)·N^{-1/2} ≤ √2 + ε.
  -- Concretely, set ε' = ε / (2·√2) and choose N₀ so that 2·L₀ ≤ (ε/2)·√N.
  set εprime : ℝ := ε / (2 * Real.sqrt 2) with hεprime
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := by
    have : (0 : ℝ) < 2 := by norm_num
    exact Real.sqrt_pos.mpr this
  have hεprime_pos : 0 < εprime := by
    rw [hεprime]; positivity
  obtain ⟨L₀, hL₀⟩ := sidon_uniform_bound hSI hεprime_pos
  -- Pick N₀ ≥ max(2L₀, (8 L₀ / ε)² + 1) so that
  --   (1+ε')·√(2N) + 2L₀ ≤ (√2 + ε)·√N for all N ≥ N₀.
  -- Equivalently, 2L₀ ≤ (ε/2)·√N, i.e., √N ≥ 4L₀/ε.
  set N₀ : ℕ := Nat.ceil ((4 * (L₀ : ℝ) / ε) ^ 2) + 1 with hN₀
  refine ⟨N₀, ?_⟩
  intro N hN A hA
  obtain ⟨hAlmost, hSubset⟩ := hA
  have hNpos : 0 < N := by
    have : (0:ℕ) < N₀ := by
      rw [hN₀]; omega
    omega
  have hNnn : (0 : ℝ) ≤ N := by exact_mod_cast Nat.zero_le N
  have hsqrtN_nn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  -- Lower bound: √N ≥ 4 L₀ / ε.
  have hsqrtN_ge : (4 * (L₀ : ℝ)) / ε ≤ Real.sqrt N := by
    have hNR_ge : ((N₀ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN₀_ge : ((4 * (L₀ : ℝ) / ε) ^ 2) ≤ ((N₀ : ℝ) : ℝ) := by
      have hceil : ((4 * (L₀ : ℝ) / ε) ^ 2) ≤
          (Nat.ceil ((4 * (L₀ : ℝ) / ε) ^ 2) : ℝ) :=
        Nat.le_ceil _
      have : ((N₀ : ℕ) : ℝ) = (Nat.ceil ((4 * (L₀ : ℝ) / ε) ^ 2) : ℝ) + 1 := by
        rw [hN₀]; push_cast; ring
      linarith
    have hsq_le_N : ((4 * (L₀ : ℝ) / ε) ^ 2) ≤ (N : ℝ) := by linarith
    have h_base_nn : 0 ≤ 4 * (L₀ : ℝ) / ε := by
      have hε_pos : 0 < ε := hε
      have : 0 ≤ 4 * (L₀ : ℝ) := by positivity
      positivity
    -- From x² ≤ N (with x ≥ 0), deduce x ≤ √N.
    have h_sqrt_sq_le : Real.sqrt ((4 * (L₀ : ℝ) / ε) ^ 2) ≤ Real.sqrt N :=
      Real.sqrt_le_sqrt hsq_le_N
    have h_sqrt_sq_eq : Real.sqrt ((4 * (L₀ : ℝ) / ε) ^ 2) = 4 * (L₀ : ℝ) / ε := by
      rw [Real.sqrt_sq h_base_nn]
    linarith
  -- 2·L₀ ≤ (ε/2) · √N.
  have h2L₀_le : (2 * (L₀ : ℝ)) ≤ (ε / 2) * Real.sqrt N := by
    have : (4 * (L₀ : ℝ)) / ε ≤ Real.sqrt N := hsqrtN_ge
    have hε_pos : 0 < ε := hε
    have h_mul : (4 * (L₀ : ℝ)) ≤ ε * Real.sqrt N := by
      have := mul_le_mul_of_nonneg_left this (le_of_lt hε_pos)
      have hsimp : ε * ((4 * (L₀ : ℝ)) / ε) = 4 * (L₀ : ℝ) := by
        field_simp
      linarith
    linarith
  -- Case split on existence of an exceptional value.
  by_cases hExists : ∃ n, HasTwoSumReprs A n
  · -- Case 1: A has an exceptional value n*.
    obtain ⟨n, hn⟩ := hExists
    have hExc : ExceptionalAt A n := exceptionalAt_of_hasTwoSumReprs hAlmost hn
    -- Both halves are Sidon and partition A.
    have hLowSidon : IsSidonFinset (lowerPart n A) :=
      exceptionalAt_lowerPart_isSidon hExc
    have hUppSidon : IsSidonFinset (upperPart n A) :=
      exceptionalAt_upperPart_isSidon hExc
    have hLowInt : ∀ a ∈ (lowerPart n A), 0 + 1 ≤ a ∧ a ≤ 0 + (n / 2) := by
      intro a ha
      have := lowerPart_mem_interval hSubset a ha
      omega
    have hUppInt : ∀ a ∈ (upperPart n A), (n / 2) + 1 ≤ a ∧ a ≤ (n / 2) + (N - n / 2) := by
      intro a ha
      have ⟨h1, h2⟩ := upperPart_mem_interval hSubset a ha
      refine ⟨h1, ?_⟩
      have : n / 2 ≤ N := by
        have hmem := mem_ground.mp (hSubset a (mem_upperPart.mp ha).1)
        have hn2 : 2 * a ≤ 2 * N := by linarith [hmem.2]
        have hlt : n / 2 < a := by
          have := (mem_upperPart.mp ha).2
          omega
        omega
      omega
    have hLowBd := hL₀ (lowerPart n A) hLowInt hLowSidon
    have hUppBd := hL₀ (upperPart n A) hUppInt hUppSidon
    -- Sum and apply Cauchy–Schwarz.
    have hsum_card : ((lowerPart n A).card : ℝ) + ((upperPart n A).card : ℝ)
                    = (A.card : ℝ) := by
      have := card_lowerPart_add_card_upperPart n A
      exact_mod_cast this
    have hk_n2 : ((n / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
      -- n / 2 ≤ N follows from elements of A in [1,N] and any pair sums to ≤ 2N.
      -- More directly: lowerPart n A ⊆ {1,...,n/2} ⊆ {1,...,N} if A is in [1,N].
      -- Simpler approach: bound n directly. Since hExc gives some pair summing to n,
      -- and pair members ≤ N, n ≤ 2N, so n/2 ≤ N.
      rcases hn with ⟨a₁, ha₁, a₂, ha₂, _, _, _, _, _, _, hsum, _, _⟩
      have h1 : a₁ ≤ N := (mem_ground.mp (hSubset a₁ ha₁)).2
      have h2 : a₂ ≤ N := (mem_ground.mp (hSubset a₂ ha₂)).2
      have : n ≤ 2 * N := by omega
      have hdiv : n / 2 ≤ N := by omega
      exact_mod_cast hdiv
    have hN_sub_nn : (0 : ℝ) ≤ (N : ℝ) - ((n / 2 : ℕ) : ℝ) := by linarith
    have hn2_nn : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    have hN_minus_eq : (((N - n / 2 : ℕ)) : ℝ) = (N : ℝ) - ((n / 2 : ℕ) : ℝ) := by
      have hle : n / 2 ≤ N := by exact_mod_cast hk_n2
      rw [Nat.cast_sub hle]
    -- Now combine.
    have hcombined :
        (A.card : ℝ) ≤
          (1 + εprime) * (Real.sqrt (n / 2 : ℕ) + Real.sqrt (N - n / 2 : ℕ)) +
            2 * (L₀ : ℝ) := by
      calc (A.card : ℝ)
          = ((lowerPart n A).card : ℝ) + ((upperPart n A).card : ℝ) := by
              rw [← hsum_card]
        _ ≤ ((1 + εprime) * Real.sqrt (n / 2 : ℕ) + L₀)
            + ((1 + εprime) * Real.sqrt (N - n / 2 : ℕ) + L₀) :=
              add_le_add hLowBd hUppBd
        _ = (1 + εprime) * (Real.sqrt (n / 2 : ℕ) + Real.sqrt (N - n / 2 : ℕ))
              + 2 * (L₀ : ℝ) := by ring
    -- Apply Cauchy–Schwarz.
    have hCS : Real.sqrt (n / 2 : ℕ) + Real.sqrt (N - n / 2 : ℕ)
              ≤ Real.sqrt (2 * N) := by
      have h1 := sqrt_add_sqrt_complement_le (x := ((n / 2 : ℕ) : ℝ))
        (N := (N : ℝ)) hn2_nn (by exact_mod_cast hk_n2)
      rw [hN_minus_eq]
      exact h1
    -- √(2N) = √2 · √N.
    have hsqrt2N : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt N := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    have h_one_plus_pos : 0 ≤ 1 + εprime := by linarith
    have hcombined' : (A.card : ℝ)
        ≤ (1 + εprime) * (Real.sqrt 2 * Real.sqrt N) + 2 * (L₀ : ℝ) := by
      have := mul_le_mul_of_nonneg_left hCS h_one_plus_pos
      rw [hsqrt2N] at this
      linarith
    -- Bound (1 + εprime) · √2 · √N ≤ (√2 + ε/2) · √N.
    have hεprime_bd : (1 + εprime) * Real.sqrt 2 ≤ Real.sqrt 2 + ε / 2 := by
      have hε2 : εprime * Real.sqrt 2 = ε / 2 := by
        rw [hεprime]
        have hne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
        field_simp
      linarith
    have hkey : (1 + εprime) * (Real.sqrt 2 * Real.sqrt N)
              ≤ (Real.sqrt 2 + ε / 2) * Real.sqrt N := by
      have := mul_le_mul_of_nonneg_right hεprime_bd hsqrtN_nn
      have hreassoc : (1 + εprime) * (Real.sqrt 2 * Real.sqrt N)
                    = ((1 + εprime) * Real.sqrt 2) * Real.sqrt N := by ring
      rw [hreassoc]
      exact this
    -- Finally, 2 L₀ ≤ (ε/2) · √N.
    calc (A.card : ℝ)
        ≤ (1 + εprime) * (Real.sqrt 2 * Real.sqrt N) + 2 * (L₀ : ℝ) := hcombined'
      _ ≤ (Real.sqrt 2 + ε / 2) * Real.sqrt N + (ε / 2) * Real.sqrt N := by linarith
      _ = (Real.sqrt 2 + ε) * Real.sqrt N := by ring
  · -- Case 2: no exceptional value. Then A is genuinely Sidon.
    push Not at hExists
    have hSidon : IsSidonFinset A := by
      intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hle12 hle12' hsum
      by_contra hne
      have h_neq : a₁ ≠ b₁ ∨ a₂ ≠ b₂ := by
        by_cases h1 : a₁ = b₁
        · right; intro h2; exact hne ⟨h1, h2⟩
        · left; exact h1
      have hrepr : HasTwoSumReprs A (a₁ + a₂) := by
        refine ⟨a₁, ?_, a₂, ?_, b₁, ?_, b₂, ?_, hle12, hle12', rfl, hsum.symm, h_neq⟩ <;>
          exact Finset.mem_coe.mp ‹_›
      exact hExists _ hrepr
    -- Apply Sidon-interval bound to A on [1, N].
    have hAInt : ∀ a ∈ A, 0 + 1 ≤ a ∧ a ≤ 0 + N := by
      intro a ha
      have := hSubset a ha
      have ⟨h1, h2⟩ := mem_ground.mp this
      omega
    have hBd := hL₀ A hAInt hSidon
    -- (1 + ε') · √N + L₀ ≤ (√2 + ε) · √N.
    -- We have (1 + ε') · √N ≤ √2 · √N (since 1 + ε' ≤ √2 for small ε').
    -- Combined with L₀ ≤ (ε/2) · √N (which follows from h2L₀_le since L₀ ≤ 2L₀).
    have hL₀_le : (L₀ : ℝ) ≤ (ε / 2) * Real.sqrt N := by
      have : (L₀ : ℝ) ≤ 2 * (L₀ : ℝ) := by
        have : (0:ℝ) ≤ (L₀ : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have hsqrt2_ge_one : 1 ≤ Real.sqrt 2 := by
      have : (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      rw [this]
      exact Real.sqrt_le_sqrt (by norm_num)
    -- We need (1 + ε') · √N + L₀ ≤ (√2 + ε) · √N.
    -- Rewriting: need ε' · √N + L₀ ≤ (√2 - 1 + ε) · √N.
    -- Since ε' = ε/(2√2) > 0 and √2 - 1 + ε > 0, plus L₀ bound, this works.
    -- More directly, use that (1 + ε') ≤ √2 when ε' ≤ √2 - 1.
    -- ε' = ε/(2√2). Suffices ε/(2√2) ≤ √2 - 1, i.e., ε ≤ 2√2(√2 - 1) = 4 - 2√2 ≈ 1.17.
    -- For arbitrary ε > 0 this may fail. Use a different bound.
    -- Just bound (1 + ε') · √N ≤ √2 · √N + ε' · √N, then use ε' · √N + L₀ ≤ ε · √N.
    have hbound1 : (1 + εprime) * Real.sqrt N
                 ≤ Real.sqrt 2 * Real.sqrt N + εprime * Real.sqrt N := by
      have : (1 + εprime) * Real.sqrt N
           = Real.sqrt N + εprime * Real.sqrt N := by ring
      rw [this]
      have : Real.sqrt N ≤ Real.sqrt 2 * Real.sqrt N := by
        have h1mul : 1 * Real.sqrt N ≤ Real.sqrt 2 * Real.sqrt N :=
          mul_le_mul_of_nonneg_right hsqrt2_ge_one hsqrtN_nn
        linarith
      linarith
    have hbound2 : εprime * Real.sqrt N ≤ ε / 2 * Real.sqrt N := by
      have : εprime ≤ ε / 2 := by
        rw [hεprime]
        have : ε / (2 * Real.sqrt 2) ≤ ε / 2 := by
          apply div_le_div_of_nonneg_left (le_of_lt hε) (by norm_num : (0:ℝ) < 2)
          have : 2 ≤ 2 * Real.sqrt 2 := by
            have : 1 ≤ Real.sqrt 2 := hsqrt2_ge_one
            linarith
          exact this
        exact this
      exact mul_le_mul_of_nonneg_right this hsqrtN_nn
    calc (A.card : ℝ)
        ≤ (1 + εprime) * Real.sqrt N + L₀ := hBd
      _ ≤ Real.sqrt 2 * Real.sqrt N + εprime * Real.sqrt N + L₀ := by linarith
      _ ≤ Real.sqrt 2 * Real.sqrt N + (ε / 2) * Real.sqrt N + (ε / 2) * Real.sqrt N := by
            linarith
      _ = (Real.sqrt 2 + ε) * Real.sqrt N := by ring

end AlmostSidonSets.UpperBound
