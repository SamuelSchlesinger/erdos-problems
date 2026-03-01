/-
# Upper Half is Sum-Free

The set (N/2, N] ∩ ℕ is sum-free: no element's reciprocal equals the sum
of reciprocals of a nonempty subset of other elements.

This gives f₃₀₁(N) ≥ ⌊N/2⌋ for Erdős Problem 301.

The proof splits by the size k of the witness subset:
- k = 1: 1/a = 1/b forces a = b, contradicting distinctness.
- k ≥ 2: Σ_{b ∈ S} 1/b ≥ k/N ≥ 2/N. But 1/a ≤ 1/(N/2+1) < 2/N
  (since a ≥ N/2+1). Contradiction.
-/
import Erdos.UnitFractionSets.Statement

namespace UnitFractionSets

/-- **The upper half (N/2, N] is sum-free.**

    For any N, the set {N/2+1, …, N} contains no a and nonempty S ⊆ A \ {a}
    with 1/a = Σ_{b ∈ S} 1/b.

    This gives f₃₀₁(N) ≥ ⌊N/2⌋ for Erdős Problem 301. -/
theorem upper_half_sum_free (N : ℕ) :
    SumFree (Finset.Icc (N / 2 + 1) N) := by
  intro a ha S hSsub hSne hsum
  simp only [Finset.mem_Icc] at ha
  -- S ⊆ Icc (N/2+1) N
  have hSicc : S ⊆ Finset.Icc (N / 2 + 1) N := fun x hx =>
    Finset.mem_of_mem_erase (hSsub hx)
  have hS_bounds : ∀ b ∈ S, N / 2 + 1 ≤ b ∧ b ≤ N := by
    intro b hb; exact Finset.mem_Icc.mp (hSicc hb)
  -- Case: |S| = 1
  by_cases h1 : S.card = 1
  · obtain ⟨b, hbS⟩ := Finset.card_eq_one.mp h1
    rw [hbS, Finset.sum_singleton] at hsum
    have hapos : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
    have hbmem := hS_bounds b (hbS ▸ Finset.mem_singleton_self b)
    have hbpos : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
    have hab : a = b := by
      have h := hsum
      field_simp at h
      exact_mod_cast h.symm
    have hbA := hSsub (hbS ▸ Finset.mem_singleton_self b)
    rw [Finset.mem_erase] at hbA
    exact hbA.1 hab.symm
  -- Case: |S| ≥ 2: derive contradiction from 1/a < Σ 1/b
  · have hcard : 2 ≤ S.card := by
      have := Finset.Nonempty.card_pos hSne; omega
    -- Key inequality: 2*a > N (since a ≥ N/2+1), so 1/a < 2/N
    -- But Σ 1/b ≥ 2/N (each b ≤ N gives 1/b ≥ 1/N, and |S| ≥ 2)
    -- Combined: 1/a < 2/N ≤ Σ 1/b, contradicting 1/a = Σ 1/b
    have haN : N < 2 * a := by omega
    have hNpos : (0 : ℚ) < N := by exact_mod_cast (show 0 < N by omega)
    have hapos : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
    -- 1/a < 2/N
    have ha_ub : (1 : ℚ) / a < 2 / N := by
      rw [div_lt_div_iff₀ hapos hNpos]
      have : 1 * N < 2 * a := by omega
      exact_mod_cast this
    -- Σ 1/b ≥ 2/N
    have hsum_lb : (2 : ℚ) / N ≤ ∑ b ∈ S, (1 / b : ℚ) := by
      -- Each 1/b ≥ 1/N since b ≤ N
      have hterm : ∀ b ∈ S, (1 / N : ℚ) ≤ 1 / b := by
        intro b hb
        have ⟨_, hbN⟩ := hS_bounds b hb
        have hbpos : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
        exact div_le_div_of_nonneg_left (by positivity : (0 : ℚ) ≤ 1) hbpos
          (by exact_mod_cast hbN : (b : ℚ) ≤ N)
      calc (2 : ℚ) / N
          = 2 * (1 / N) := by ring
        _ ≤ S.card * (1 / N) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcard
        _ = ∑ _b ∈ S, (1 / N : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ b ∈ S, (1 / b : ℚ) := Finset.sum_le_sum hterm
    linarith

end UnitFractionSets
