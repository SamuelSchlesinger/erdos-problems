/-
# Upper Bound on Pair-Free Sets

For every odd k, the pair (3k, 6k) satisfies 1/(3k) + 1/(6k) = 1/(2k),
so any pair-free subset of {1, …, N} must exclude at least one of {3k, 6k}.
For distinct odd k₁, k₂ with 6k ≤ N, the pairs {3k₁, 6k₁} and {3k₂, 6k₂}
are disjoint (3·odd ≠ 6·odd by parity), giving
  f₃₂₇(N) ≤ N − |{k ≤ N/6 : k odd}|.

Since the density of odd integers is 1/2, this yields
  f₃₂₇(N) ≤ (11/12 + o(1))N.
-/
import Erdos.UnitFractionPairs.Classification

namespace UnitFractionPairs

/-! ### Disjointness of pairs for distinct odd k -/

/-- For distinct odd k₁, k₂, the pairs {3k₁, 6k₁} and {3k₂, 6k₂} are disjoint.

    The four cross-equalities:
    - 3k₁ = 3k₂ ⟹ k₁ = k₂ (contra)
    - 6k₁ = 6k₂ ⟹ k₁ = k₂ (contra)
    - 3k₁ = 6k₂ ⟹ k₁ = 2k₂, so k₁ even (contra since k₁ odd)
    - 6k₁ = 3k₂ ⟹ 2k₁ = k₂, so k₂ even (contra since k₂ odd) -/
theorem pairs_disjoint_odd {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂)
    (h1 : ¬Even k₁) (h2 : ¬Even k₂) :
    Disjoint ({3 * k₁, 6 * k₁} : Finset ℕ) {3 * k₂, 6 * k₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h
  -- 3k₁ = 3k₂
  · exact hne (by omega)
  -- 3k₁ = 6k₂ means k₁ = 2k₂, contradicts k₁ odd
  · exact h1 ⟨k₂, by omega⟩
  -- 6k₁ = 3k₂ means k₂ = 2k₁, contradicts k₂ odd
  · exact h2 ⟨k₁, by omega⟩
  -- 6k₁ = 6k₂
  · exact hne (by omega)

/-- A pair-free set cannot contain both 3k and 6k for any k ≥ 1.
    This is immediate from pair_3m_6m. -/
theorem pair_free_excludes {A : Finset ℕ} (hA : PairFree A) {k : ℕ}
    (hk : 0 < k) (h3 : 3 * k ∈ A) (h6 : 6 * k ∈ A) : False :=
  pair_free_not_3k_6k hA hk h3 h6

end UnitFractionPairs
