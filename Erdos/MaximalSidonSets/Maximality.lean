/- 
# Maximality Forces Elementary Obstructions

For a Sidon set `A ⊆ {1, ..., N}`, maximality means that no outside point `x`
can be adjoined while preserving the Sidon property. Expanding the failure of
Sidon after inserting `x` yields an equal-sum collision involving `x`. A short
case split shows that every such collision produces either

- a midpoint obstruction `a + b = 2x`, or
- a sum-difference obstruction `x + c = a + b`.

This connects the formal maximality definition to the elementary obstruction
cover used in the cubic counting argument.
-/
import Erdos.MaximalSidonSets.Existence
import Erdos.MaximalSidonSets.ElementaryBound

namespace MaximalSidonSets

/-- A singleton is Sidon. -/
theorem isSidonFinset_singleton (x : ℕ) : IsSidonFinset ({x} : Finset ℕ) := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ _ _ _
  have ha₁' : a₁ = x := by simpa using ha₁
  have ha₂' : a₂ = x := by simpa using ha₂
  have hb₁' : b₁ = x := by simpa using hb₁
  have hb₂' : b₂ = x := by simpa using hb₂
  subst a₁
  subst a₂
  subst b₁
  subst b₂
  exact ⟨rfl, rfl⟩

/-- Genuine maximality implies the elementary obstruction-cover property. -/
theorem obstructionCoveredInInterval_of_maximal {A : Finset ℕ} {N : ℕ}
    (hmax : IsMaximalSidonInInterval A N) :
    ObstructionCoveredInInterval A N := by
  refine ⟨hmax.1, ?_⟩
  intro x hx hxa
  have hnot : ¬ IsSidonFinset (insert x A) := hmax.2 x hx hxa
  have hSidonA : IsSidonFinset A := hmax.1.1
  unfold IsSidonFinset SidonSumsets.IsSidon at hnot hSidonA
  push_neg at hnot
  rcases hnot with ⟨a₁, a₂, b₁, b₂, ha₁, ha₂, hb₁, hb₂, ha₁₂, hb₁₂, hsum, hneq⟩
  have hnot_mem_of_eq {y : ℕ} (hyA : y ∈ A) (hyx : y = x) : False := by
    exact hxa (hyx ▸ hyA)
  rcases (show a₁ = x ∨ a₁ ∈ A by simpa using ha₁) with ha₁x | ha₁A
  · rcases (show a₂ = x ∨ a₂ ∈ A by simpa using ha₂) with ha₂x | ha₂A
    · rcases (show b₁ = x ∨ b₁ ∈ A by simpa using hb₁) with hb₁x | hb₁A
      · rcases (show b₂ = x ∨ b₂ ∈ A by simpa using hb₂) with hb₂x | hb₂A
        · exfalso
          exact (hneq (ha₁x.trans hb₁x.symm)) (ha₂x.trans hb₂x.symm)
        · exfalso
          exact hnot_mem_of_eq hb₂A (by omega)
      · rcases (show b₂ = x ∨ b₂ ∈ A by simpa using hb₂) with hb₂x | hb₂A
        · exfalso
          exact hnot_mem_of_eq hb₁A (by omega)
        · exact Finset.mem_union.mpr <| Or.inl <|
            mem_midpointCandidates_of_eq hb₁A hb₂A (by omega)
    · rcases (show b₁ = x ∨ b₁ ∈ A by simpa using hb₁) with hb₁x | hb₁A
      · rcases (show b₂ = x ∨ b₂ ∈ A by simpa using hb₂) with hb₂x | hb₂A
        · exfalso
          exact hnot_mem_of_eq ha₂A (by omega)
        · exfalso
          have ha₂b₂ : a₂ = b₂ := by omega
          exact (hneq (ha₁x.trans hb₁x.symm)) ha₂b₂
      · rcases (show b₂ = x ∨ b₂ ∈ A by simpa using hb₂) with hb₂x | hb₂A
        · exfalso
          exact hnot_mem_of_eq ha₂A (by omega)
        · exact Finset.mem_union.mpr <| Or.inr <|
            mem_sumDiffCandidates_of_eq hb₁A hb₂A ha₂A (by omega)
  · rcases (show a₂ = x ∨ a₂ ∈ A by simpa using ha₂) with ha₂x | ha₂A
    · rcases (show b₁ = x ∨ b₁ ∈ A by simpa using hb₁) with hb₁x | hb₁A
      · rcases (show b₂ = x ∨ b₂ ∈ A by simpa using hb₂) with hb₂x | hb₂A
        · exfalso
          exact hnot_mem_of_eq ha₁A (by omega)
        · exfalso
          exact hnot_mem_of_eq ha₁A (by omega)
      · rcases (show b₂ = x ∨ b₂ ∈ A by simpa using hb₂) with hb₂x | hb₂A
        · exfalso
          have ha₁b₁ : a₁ = b₁ := by omega
          exact (hneq ha₁b₁) (ha₂x.trans hb₂x.symm)
        · exact Finset.mem_union.mpr <| Or.inr <|
            mem_sumDiffCandidates_of_eq hb₁A hb₂A ha₁A (by omega)
    · rcases (show b₁ = x ∨ b₁ ∈ A by simpa using hb₁) with hb₁x | hb₁A
      · rcases (show b₂ = x ∨ b₂ ∈ A by simpa using hb₂) with hb₂x | hb₂A
        · exact Finset.mem_union.mpr <| Or.inl <|
            mem_midpointCandidates_of_eq ha₁A ha₂A (by omega)
        · exact Finset.mem_union.mpr <| Or.inr <|
            mem_sumDiffCandidates_of_eq ha₁A ha₂A hb₂A (by omega)
      · rcases (show b₂ = x ∨ b₂ ∈ A by simpa using hb₂) with hb₂x | hb₂A
        · exact Finset.mem_union.mpr <| Or.inr <|
            mem_sumDiffCandidates_of_eq ha₁A ha₂A hb₁A (by omega)
        · exfalso
          have hpair : a₁ = b₁ ∧ a₂ = b₂ :=
            hSidonA ha₁A ha₂A hb₁A hb₂A ha₁₂ hb₁₂ hsum
          exact (hneq hpair.1) hpair.2

/-- Every maximal Sidon subset of `{1, ..., N}` satisfies the standard coarse
cubic counting lower bound. -/
theorem cubic_counting_bound_of_maximal {A : Finset ℕ} {N : ℕ}
    (hmax : IsMaximalSidonInInterval A N) :
    N ≤ A.card + A.card ^ 2 + A.card ^ 3 := by
  exact cubic_counting_bound_of_obstructionCover
    (obstructionCoveredInInterval_of_maximal hmax)

/-- A maximal Sidon subset of a nonempty interval must itself be nonempty. -/
theorem one_le_card_of_maximal {A : Finset ℕ} {N : ℕ}
    (hN : 1 ≤ N) (hmax : IsMaximalSidonInInterval A N) :
    1 ≤ A.card := by
  by_contra hcard
  have hA0 : A.card = 0 := by omega
  have hA : A = ∅ := Finset.card_eq_zero.mp hA0
  have h1ground : 1 ∈ ground N := by simp [ground, hN]
  have hnot : ¬ IsSidonFinset (insert 1 A) := hmax.2 1 h1ground (by simp [hA])
  have hs : IsSidonFinset (insert 1 A) := by
    simpa [hA] using isSidonFinset_singleton 1
  exact hnot hs

/-- Standard compressed form of the easy lower bound for maximal Sidon sets. -/
theorem three_mul_cube_bound_of_maximal {A : Finset ℕ} {N : ℕ}
    (hN : 1 ≤ N) (hmax : IsMaximalSidonInInterval A N) :
    N ≤ 3 * A.card ^ 3 := by
  have hcard1 : 1 ≤ A.card := one_le_card_of_maximal hN hmax
  have hk2 : A.card ≤ A.card ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left A.card hcard1
  have hk3 : A.card ^ 2 ≤ A.card ^ 3 := by
    have hk3' : A.card ^ 2 ≤ A.card * (A.card ^ 2) := by
      simpa using Nat.mul_le_mul_right (A.card ^ 2) hcard1
    simpa [pow_succ, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk3'
  have hk : A.card ≤ A.card ^ 3 := le_trans hk2 hk3
  have hcount : N ≤ A.card + A.card ^ 2 + A.card ^ 3 :=
    cubic_counting_bound_of_maximal hmax
  omega

/-- Threshold form of the cubic lower bound: if `3 k^3 < N`, then every maximal
Sidon subset of `{1, ..., N}` has more than `k` elements. -/
theorem lt_card_of_three_mul_cube_lt {A : Finset ℕ} {N k : ℕ}
    (hN : 1 ≤ N) (hmax : IsMaximalSidonInInterval A N) (hk : 3 * k ^ 3 < N) :
    k < A.card := by
  by_contra hcard
  have hcard' : A.card ≤ k := Nat.le_of_not_gt hcard
  have hpow : A.card ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left hcard' 3
  have hbound : N ≤ 3 * k ^ 3 := by
    exact le_trans (three_mul_cube_bound_of_maximal hN hmax) (Nat.mul_le_mul_left 3 hpow)
  omega

/-- Equivalent non-strict packaging of the same threshold statement. -/
theorem succ_le_card_of_three_mul_cube_lt {A : Finset ℕ} {N k : ℕ}
    (hN : 1 ≤ N) (hmax : IsMaximalSidonInInterval A N) (hk : 3 * k ^ 3 < N) :
    k + 1 ≤ A.card := by
  exact Nat.succ_le_of_lt (lt_card_of_three_mul_cube_lt hN hmax hk)

/-- Packaged existence theorem: every nonempty interval admits a maximal Sidon
subset satisfying the coarse `N^{1/3}` lower bound. -/
theorem exists_maximalSidonInInterval_with_three_mul_cube_bound {N : ℕ}
    (hN : 1 ≤ N) :
    ∃ A : Finset ℕ, IsMaximalSidonInInterval A N ∧ N ≤ 3 * A.card ^ 3 := by
  rcases exists_maximalSidonInInterval N with ⟨A, hA⟩
  exact ⟨A, hA, three_mul_cube_bound_of_maximal hN hA⟩

end MaximalSidonSets
