import Erdos.PracticalNumbers.Statement

/-
# Elementary Facts About Practical Numbers

This file records the first complete facts for Erdős problem `#18`: the
unbounded and bounded representation predicates are related in the expected
way, larger cardinality bounds preserve bounded representations and `hBound`,
and the first two practical numbers are practical.
-/
namespace PracticalNumbers

/-- A bounded representation is, in particular, an ordinary divisor
representation. -/
theorem DivisorRepresentation.of_bounded {m k n : ℕ}
    (h : BoundedDivisorRepresentation m k n) :
    DivisorRepresentation m n := by
  rcases h with ⟨S, hS, _hcard, hsum⟩
  exact ⟨S, hS, hsum⟩

/-- Any ordinary divisor representation becomes bounded once the bound is at
least the number of chosen divisors. -/
theorem DivisorRepresentation.to_bounded {m n : ℕ}
    (h : DivisorRepresentation m n) :
    ∃ k : ℕ, BoundedDivisorRepresentation m k n := by
  rcases h with ⟨S, hS, hsum⟩
  exact ⟨S.card, S, hS, le_rfl, hsum⟩

/-- Enlarging the allowed number of divisors preserves a bounded
representation. -/
theorem BoundedDivisorRepresentation.mono_bound {m k l n : ℕ}
    (hkl : k ≤ l) (h : BoundedDivisorRepresentation m k n) :
    BoundedDivisorRepresentation m l n := by
  rcases h with ⟨S, hS, hcard, hsum⟩
  exact ⟨S, hS, hcard.trans hkl, hsum⟩

/-- Practical numbers are positive by definition. -/
theorem IsPractical.pos {m : ℕ} (hm : IsPractical m) :
    0 < m :=
  hm.1

/-- Every practical number has representations for all targets in its defining
range. -/
theorem IsPractical.representation {m n : ℕ} (hm : IsPractical m)
    (hn1 : 1 ≤ n) (hnm : n ≤ m) :
    DivisorRepresentation m n :=
  hm.2 n hn1 hnm

/-- A uniform `h`-bound supplies bounded representations for every target in
the defining range. -/
theorem hBound.representation {m k n : ℕ} (hm : hBound m k)
    (hn1 : 1 ≤ n) (hnm : n ≤ m) :
    BoundedDivisorRepresentation m k n :=
  hm.2 n hn1 hnm

/-- Increasing the divisor-count allowance preserves an `h`-bound. -/
theorem hBound.mono {m k l : ℕ} (hkl : k ≤ l) (hm : hBound m k) :
    hBound m l := by
  refine ⟨hm.1, ?_⟩
  intro n hn1 hnm
  exact (hm.representation hn1 hnm).mono_bound hkl

/-- The number `1` is practical: there are no integers `n` satisfying
`1 ≤ n ≤ 1` except `1`, represented by the divisor `1`. -/
theorem isPractical_one : IsPractical 1 := by
  refine ⟨by norm_num, ?_⟩
  intro n hn1 hnle
  have hn : n = 1 := by omega
  subst n
  refine ⟨({1} : Finset ℕ), ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_singleton] at hd
    subst d
    exact Nat.one_mem_divisors.mpr (by norm_num)
  · simp

/-- For `1`, one divisor always suffices. -/
theorem hBound_one_one : hBound 1 1 := by
  refine ⟨isPractical_one, ?_⟩
  intro n hn1 hnle
  have hn : n = 1 := by omega
  subst n
  refine ⟨({1} : Finset ℕ), ?_, ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_singleton] at hd
    subst d
    exact Nat.one_mem_divisors.mpr (by norm_num)
  · simp
  · simp

/-- The least uniform divisor-count bound for `1` is `1`. -/
theorem hValue_one_one : hValue 1 1 := by
  refine ⟨hBound_one_one, ?_⟩
  intro j hj
  by_contra hlt
  have hrep : BoundedDivisorRepresentation 1 j 1 :=
    hj.representation (by norm_num) (by norm_num)
  rcases hrep with ⟨S, _hS, hcard, hsum⟩
  have hSempty : S = ∅ := by
    exact Finset.card_eq_zero.mp (by omega)
  rw [hSempty] at hsum
  simp at hsum

/-- The number `2` is practical: the only target is `1`, represented by the
divisor `1`. -/
theorem isPractical_two : IsPractical 2 := by
  refine ⟨by norm_num, ?_⟩
  intro n hn1 hnle
  have hn : n = 1 ∨ n = 2 := by omega
  rcases hn with rfl | rfl
  · refine ⟨({1} : Finset ℕ), ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.one_mem_divisors.mpr (by norm_num)
    · simp
  · refine ⟨({2} : Finset ℕ), ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.mem_divisors.mpr ⟨dvd_rfl, by norm_num⟩
    · simp

/-- For `2`, one divisor always suffices. -/
theorem hBound_two_one : hBound 2 1 := by
  refine ⟨isPractical_two, ?_⟩
  intro n hn1 hnle
  have hn : n = 1 ∨ n = 2 := by omega
  rcases hn with rfl | rfl
  · refine ⟨({1} : Finset ℕ), ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.one_mem_divisors.mpr (by norm_num)
    · simp
    · simp
  · refine ⟨({2} : Finset ℕ), ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.mem_divisors.mpr ⟨dvd_rfl, by norm_num⟩
    · simp
    · simp

/-- The least uniform divisor-count bound for `2` is `1`. -/
theorem hValue_two_one : hValue 2 1 := by
  refine ⟨hBound_two_one, ?_⟩
  intro j hj
  by_contra hlt
  have hrep : BoundedDivisorRepresentation 2 j 1 :=
    hj.representation (by norm_num) (by norm_num)
  rcases hrep with ⟨S, _hS, hcard, hsum⟩
  have hSempty : S = ∅ := by
    exact Finset.card_eq_zero.mp (by omega)
  rw [hSempty] at hsum
  simp at hsum

/-- The divisors of `4` are `{1, 2, 4}`. -/
private lemma divisors_four : Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) := by
  decide

/-- The divisors of `3` are `{1, 3}`. -/
private lemma divisors_three : Nat.divisors 3 = ({1, 3} : Finset ℕ) := by
  decide

/-- The divisors of `5` are `{1, 5}`. -/
private lemma divisors_five : Nat.divisors 5 = ({1, 5} : Finset ℕ) := by
  decide

/-- The number `4` is practical: every `1 ≤ n ≤ 4` is a sum of distinct divisors
of `4`. The representations are `1 = 1`, `2 = 2`, `3 = 1 + 2`, `4 = 4`. -/
theorem isPractical_four : IsPractical 4 := by
  refine ⟨by norm_num, ?_⟩
  intro n hn1 hnle
  have hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hn with rfl | rfl | rfl | rfl
  · refine ⟨({1} : Finset ℕ), ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.one_mem_divisors.mpr (by norm_num)
    · simp
  · refine ⟨({2} : Finset ℕ), ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.mem_divisors.mpr ⟨by decide, by norm_num⟩
    · simp
  · refine ⟨({1, 2} : Finset ℕ), ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact Nat.one_mem_divisors.mpr (by norm_num)
      · exact Nat.mem_divisors.mpr ⟨by decide, by norm_num⟩
    · decide
  · refine ⟨({4} : Finset ℕ), ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.mem_divisors.mpr ⟨dvd_rfl, by norm_num⟩
    · simp

/-- For `4`, two divisors always suffice in the defining range. The maximum is
attained at `n = 3 = 1 + 2`; every other target uses a single divisor. -/
theorem hBound_four_two : hBound 4 2 := by
  refine ⟨isPractical_four, ?_⟩
  intro n hn1 hnle
  have hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hn with rfl | rfl | rfl | rfl
  · refine ⟨({1} : Finset ℕ), ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.one_mem_divisors.mpr (by norm_num)
    · simp
    · simp
  · refine ⟨({2} : Finset ℕ), ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.mem_divisors.mpr ⟨by decide, by norm_num⟩
    · simp
    · simp
  · refine ⟨({1, 2} : Finset ℕ), ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact Nat.one_mem_divisors.mpr (by norm_num)
      · exact Nat.mem_divisors.mpr ⟨by decide, by norm_num⟩
    · decide
    · decide
  · refine ⟨({4} : Finset ℕ), ?_, ?_, ?_⟩
    · intro d hd
      rw [Finset.mem_singleton] at hd
      subst d
      exact Nat.mem_divisors.mpr ⟨dvd_rfl, by norm_num⟩
    · simp
    · simp

/-- Helper: every subset of `{a, b}` (as a `Finset ℕ`) is one of the four
canonical subsets `∅`, `{a}`, `{b}`, `{a, b}`. -/
private lemma subset_pair_cases {a b : ℕ} (hab : a ≠ b) {S : Finset ℕ}
    (hS : S ⊆ ({a, b} : Finset ℕ)) :
    S = ∅ ∨ S = {a} ∨ S = {b} ∨ S = ({a, b} : Finset ℕ) := by
  classical
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · right; right; right
      apply Finset.Subset.antisymm hS
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · right; left
      apply Finset.Subset.antisymm
      · intro x hxS
        rw [Finset.mem_singleton]
        have hx2 : x ∈ ({a, b} : Finset ℕ) := hS hxS
        rw [Finset.mem_insert, Finset.mem_singleton] at hx2
        rcases hx2 with rfl | rfl
        · rfl
        · exact absurd hxS hb
      · intro x hx
        rw [Finset.mem_singleton] at hx
        subst x
        exact ha
  · by_cases hb : b ∈ S
    · right; right; left
      apply Finset.Subset.antisymm
      · intro x hxS
        rw [Finset.mem_singleton]
        have hx2 : x ∈ ({a, b} : Finset ℕ) := hS hxS
        rw [Finset.mem_insert, Finset.mem_singleton] at hx2
        rcases hx2 with rfl | rfl
        · exact absurd hxS ha
        · rfl
      · intro x hx
        rw [Finset.mem_singleton] at hx
        subst x
        exact hb
    · left
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hxS
      have hx2 : x ∈ ({a, b} : Finset ℕ) := hS hxS
      rw [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with rfl | rfl
      · exact ha hxS
      · exact hb hxS

/-- The number `3` is **not** practical: the divisors of `3` are `{1, 3}`, so
the achievable subset sums are `0, 1, 3, 4`. The target `n = 2` is unreachable. -/
theorem not_isPractical_three : ¬ IsPractical 3 := by
  intro hp
  have hrep : DivisorRepresentation 3 2 :=
    hp.representation (by norm_num) (by norm_num)
  rcases hrep with ⟨S, hS, hsum⟩
  rw [divisors_three] at hS
  have hcases := subset_pair_cases (a := 1) (b := 3) (by norm_num) hS
  rcases hcases with h | h | h | h <;> rw [h] at hsum <;> simp at hsum

/-- The number `5` is **not** practical: the divisors of `5` are `{1, 5}`, so
the achievable subset sums are `0, 1, 5, 6`. The targets `n = 2, 3, 4` are all
unreachable; we use `n = 2` to derive the contradiction. -/
theorem not_isPractical_five : ¬ IsPractical 5 := by
  intro hp
  have hrep : DivisorRepresentation 5 2 :=
    hp.representation (by norm_num) (by norm_num)
  rcases hrep with ⟨S, hS, hsum⟩
  rw [divisors_five] at hS
  have hcases := subset_pair_cases (a := 1) (b := 5) (by norm_num) hS
  rcases hcases with h | h | h | h <;> rw [h] at hsum <;> simp at hsum

end PracticalNumbers
