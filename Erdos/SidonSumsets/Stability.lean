/-
# Value-Truncation Stability for Isolated Sums

The key observation is that sumset information below a value cutoff `N` is
completely determined by the part of the set lying in `[0, N]`. Therefore an
isolated sum detected strictly below `N` survives in every larger truncation and
in the full sumset.

Reference: https://www.erdosproblems.com/152
-/
import Erdos.SidonSumsets.Statement

namespace SidonSumsets

/-- Below the cutoff `N`, value truncation does not change the sumset. -/
theorem mem_sumset_truncateByValue_iff_of_le {A : Set ℕ} {N s : ℕ} (hs : s ≤ N) :
    s ∈ sumset (truncateByValue A N) ↔ s ∈ sumset A := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha.1, b, hb.1, rfl⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    have haN : a ≤ N := by omega
    have hbN : b ≤ N := by omega
    exact ⟨a, ⟨ha, haN⟩, b, ⟨hb, hbN⟩, hab⟩

/-- Isolated sums below the cutoff are identical in the truncation and in the
full sumset. -/
theorem isolated_iff_isolated_truncateByValue_of_lt {A : Set ℕ} {N s : ℕ} (hs : s < N) :
    Isolated (sumset (truncateByValue A N)) s ↔ Isolated (sumset A) s := by
  have hs_le : s ≤ N := by omega
  have hs_pred : s - 1 ≤ N := by omega
  have hs_succ : s + 1 ≤ N := by omega
  constructor
  · rintro ⟨hsum, hpred, hsucc⟩
    refine ⟨(mem_sumset_truncateByValue_iff_of_le hs_le).mp hsum, ?_, ?_⟩
    · intro hpred_full
      exact hpred ((mem_sumset_truncateByValue_iff_of_le hs_pred).mpr hpred_full)
    · intro hsucc_full
      exact hsucc ((mem_sumset_truncateByValue_iff_of_le hs_succ).mpr hsucc_full)
  · rintro ⟨hsum, hpred, hsucc⟩
    refine ⟨(mem_sumset_truncateByValue_iff_of_le hs_le).mpr hsum, ?_, ?_⟩
    · intro hpred_trunc
      exact hpred ((mem_sumset_truncateByValue_iff_of_le hs_pred).mp hpred_trunc)
    · intro hsucc_trunc
      exact hsucc ((mem_sumset_truncateByValue_iff_of_le hs_succ).mp hsucc_trunc)

/-- Once an isolated sum appears strictly below a value cutoff, it persists in
every larger truncation. -/
theorem isolated_stable_under_larger_truncations {A : Set ℕ} {N M s : ℕ}
    (hs : s < N) (hNM : N ≤ M) :
    Isolated (sumset (truncateByValue A N)) s ↔
      Isolated (sumset (truncateByValue A M)) s := by
  have hsM : s < M := lt_of_lt_of_le hs hNM
  rw [isolated_iff_isolated_truncateByValue_of_lt hs,
    isolated_iff_isolated_truncateByValue_of_lt hsM]

/-- Lower isolated sums are genuine isolated sums of the full sumset. -/
theorem lowerIsolated_subset_full {A : Set ℕ} {N s : ℕ} (hs : s ∈ lowerIsolated A N) :
    Isolated (sumset A) s := by
  exact (isolated_iff_isolated_truncateByValue_of_lt hs.1).mp hs.2

/-- The lower-isolated witness set grows monotonically with the value cutoff. -/
theorem lowerIsolated_mono {A : Set ℕ} {N M : ℕ} (hNM : N ≤ M) :
    lowerIsolated A N ⊆ lowerIsolated A M := by
  intro s hs
  have hsM : s < M := lt_of_lt_of_le hs.1 hNM
  exact ⟨hsM, (isolated_stable_under_larger_truncations hs.1 hNM).mp hs.2⟩

/-- A set of naturals with arbitrarily large elements is infinite. -/
theorem infinite_of_forall_ge_exists_mem {S : Set ℕ}
    (hS : ∀ K : ℕ, ∃ s ∈ S, K ≤ s) :
    S.Infinite := by
  by_contra hInf
  have hFinite : S.Finite := Set.not_infinite.mp hInf
  rcases hFinite.bddAbove with ⟨u, hu⟩
  rcases hS (u + 1) with ⟨s, hs, hus⟩
  exact Nat.not_succ_le_self u (le_trans hus (hu hs))

/-- The value-truncation strategy implies the infinite Sidon conjecture. -/
theorem infinite_isolated_of_arbitrarily_large_lowerIsolated {A : Set ℕ}
    (hA : ∀ K : ℕ, ∃ N s, K ≤ s ∧ s ∈ lowerIsolated A N) :
    {s : ℕ | Isolated (sumset A) s}.Infinite := by
  apply infinite_of_forall_ge_exists_mem
  intro K
  rcases hA K with ⟨N, s, hsK, hs⟩
  exact ⟨s, lowerIsolated_subset_full hs, hsK⟩

/-- Any proof that infinite Sidon sets admit arbitrarily large lower-isolated
witnesses automatically proves the infinite conjecture. -/
theorem infiniteConjecture_of_lowerIsolated_strategy
    (h :
      ∀ A : Set ℕ,
        A.Infinite →
          IsSidon A →
            ∀ K : ℕ, ∃ N s, K ≤ s ∧ s ∈ lowerIsolated A N) :
    infiniteConjecture := by
  intro A hInf hSidon
  exact infinite_isolated_of_arbitrarily_large_lowerIsolated (h A hInf hSidon)

end SidonSumsets
