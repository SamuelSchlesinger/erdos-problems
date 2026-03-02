/-
# Upper Half is NOT Pair-Free

Unlike Problems #302 and #301 (where the upper half (N/2, N] is always
triple-free and sum-free respectively), the upper half can contain unit
fraction pairs for infinitely many N.

The pair (10m, 15m) satisfies 1/(10m) + 1/(15m) = 1/(6m), and for any m ≥ 1
both elements lie in (15m/2, 15m]. For N = 15 (m = 1), this gives the pair
(10, 15) in {8, 9, …, 15}.

**Structural significance**: this shows the "magnitude obstruction" that
gives density-1/2 lower bounds for #302 and #301 fails for #327. The
pair-free density problem fundamentally cannot use the upper-half strategy.

Reference: https://www.erdosproblems.com/327
-/
import Erdos.UnitFractionPairs.Classification

namespace UnitFractionPairs

/-- (10m, 15m) is a unit fraction pair for all m: (10m + 15m) = 25m divides
    10m · 15m = 150m², with quotient 6m. -/
theorem pair_10m_15m' (m : ℕ) : IsUnitFractionPair (10 * m) (15 * m) :=
  ⟨6 * m, by ring⟩

/-- **The upper half is NOT pair-free for N = 15.**

    The pair (10, 15) lies in {8, 9, …, 15} and satisfies
    (10 + 15) = 25 ∣ 150 = 10 · 15, so 1/10 + 1/15 = 1/6.

    This contrasts sharply with Problems #302 and #301, where the upper
    half (N/2, N] is always triple-free and sum-free respectively
    (`upper_half_triple_free`, `upper_half_sum_free`). -/
theorem upper_half_not_pair_free :
    ¬PairFree (Finset.Icc (15 / 2 + 1) 15) := by
  intro hpf
  have h10 : (10 : ℕ) ∈ Finset.Icc (15 / 2 + 1) 15 := by
    simp only [Finset.mem_Icc]; omega
  have h15 : (15 : ℕ) ∈ Finset.Icc (15 / 2 + 1) 15 := by
    simp only [Finset.mem_Icc]; omega
  exact hpf 10 h10 15 h15 (by omega) ⟨6, by norm_num⟩

/-- **For every m ≥ 1, the upper half of N = 15m is not pair-free.**

    The pair (10m, 15m) lies in (15m/2, 15m] and satisfies
    1/(10m) + 1/(15m) = 1/(6m).

    Since N = 15m → ∞ as m → ∞, this gives infinitely many N for
    which the upper-half construction fails. -/
theorem upper_half_not_pair_free_15m {m : ℕ} (hm : 1 ≤ m) :
    ¬PairFree (Finset.Icc (15 * m / 2 + 1) (15 * m)) := by
  intro hpf
  have h10m : 10 * m ∈ Finset.Icc (15 * m / 2 + 1) (15 * m) := by
    simp only [Finset.mem_Icc]; omega
  have h15m : 15 * m ∈ Finset.Icc (15 * m / 2 + 1) (15 * m) := by
    simp only [Finset.mem_Icc]; omega
  exact hpf (10 * m) h10m (15 * m) h15m (by omega) ⟨6 * m, by ring⟩

/-- **The upper-half strategy fails for #327 infinitely often.**

    For every bound M, there exists N ≥ M such that the upper half
    (N/2, N] ∩ ℕ is not pair-free.

    This is the formal witness that Problem #327 cannot achieve density 1/2
    via the magnitude obstruction. Compare with `upper_half_triple_free`
    (Problem #302) and `upper_half_sum_free` (Problem #301), which work
    for ALL N. -/
theorem upper_half_not_pair_free_infinitely :
    ∀ M : ℕ, ∃ N, M ≤ N ∧ ¬PairFree (Finset.Icc (N / 2 + 1) N) := by
  intro M
  refine ⟨15 * (M / 15 + 1), ?_, ?_⟩
  · omega
  · exact upper_half_not_pair_free_15m (by omega)

end UnitFractionPairs
