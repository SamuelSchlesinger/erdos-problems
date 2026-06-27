import Erdos.TotientValueRatio.Statement

/-!
# Elementary Facts About `V` and `V'`

The first basic relation in Erdős problem `#417` is the trivial inequality
`V'(x) ≤ V(x)`: every totient value produced by some argument `m ≤ x` is, in
particular, a totient value at most `x`.
-/
namespace TotientValueRatio

/-- The value `1 = φ(1)` is always counted by `V'(x)` once `x ≥ 1`. -/
theorem one_mem_totientImageUpTo {x : ℕ} (hx : 1 ≤ x) :
    1 ∈ totientImageUpTo x := by
  refine Finset.mem_image.mpr ?_
  refine ⟨1, ?_, Nat.totient_one⟩
  simp [hx]

/-- Hence `V'(x)` is positive for every `x ≥ 1`. -/
theorem vPrime_pos {x : ℕ} (hx : 1 ≤ x) : 0 < VPrime x := by
  unfold VPrime
  exact Finset.card_pos.mpr ⟨1, one_mem_totientImageUpTo hx⟩

/-- There are no positive arguments in `[1, 0]`, so `V'(0) = 0`. -/
@[simp]
theorem vPrime_zero : VPrime 0 = 0 := by
  simp [VPrime, totientImageUpTo]

/-- The only totient value produced by arguments in `[1, 1]` is `φ(1) = 1`. -/
@[simp]
theorem vPrime_one : VPrime 1 = 1 := by
  simp [VPrime, totientImageUpTo]

/-- Enlarging the argument range can only add totient values. -/
theorem monotone_totientImageUpTo : Monotone totientImageUpTo := by
  intro x y hxy n hn
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  rcases Finset.mem_Icc.mp hm with ⟨h1m, hmx⟩
  exact Finset.mem_image.mpr
    ⟨m, Finset.mem_Icc.mpr ⟨h1m, le_trans hmx hxy⟩, rfl⟩

/-- Raising the cutoff can only add totient values below the cutoff. -/
theorem monotone_totientValuesAtMost : Monotone totientValuesAtMost := by
  classical
  intro x y hxy n hn
  unfold totientValuesAtMost at hn ⊢
  rw [Finset.mem_filter] at hn ⊢
  refine ⟨?_, hn.2⟩
  rw [Finset.mem_range] at hn ⊢
  exact lt_of_lt_of_le hn.1 (Nat.succ_le_succ hxy)

/-- The Erdős quantity `V'` is monotone. -/
theorem monotone_vPrime : Monotone VPrime := by
  intro x y hxy
  unfold VPrime
  exact Finset.card_le_card (monotone_totientImageUpTo hxy)

/-- The Erdős quantity `V` is monotone. -/
theorem monotone_v : Monotone V := by
  classical
  intro x y hxy
  unfold V
  exact Finset.card_le_card (monotone_totientValuesAtMost hxy)

/-- Every totient value arising from an argument `m ≤ x` is a totient value at
most `x`. -/
theorem totientImageUpTo_subset_totientValuesAtMost (x : ℕ) :
    totientImageUpTo x ⊆ totientValuesAtMost x := by
  classical
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  unfold totientValuesAtMost
  rw [Finset.mem_filter]
  refine ⟨?_, ⟨m, rfl⟩⟩
  rw [Finset.mem_range]
  have hmx : m ≤ x := (Finset.mem_Icc.mp hm).2
  exact Nat.lt_succ_of_le (le_trans (Nat.totient_le m) hmx)

/-- The trivial inequality noted on the Erdős problems page. -/
theorem vPrime_le_v (x : ℕ) : VPrime x ≤ V x := by
  classical
  unfold VPrime V
  exact Finset.card_le_card (totientImageUpTo_subset_totientValuesAtMost x)

/-- In particular `V(x)` is also positive once `x ≥ 1`. -/
theorem v_pos {x : ℕ} (hx : 1 ≤ x) : 0 < V x := lt_of_lt_of_le (vPrime_pos hx) (vPrime_le_v x)

/-!
## A structural constraint on the values counted by `V`

The set whose cardinality is `V(x)` consists of the totient values `≤ x`.  A
basic but useful structural fact is that this set is extremely sparse among the
odd numbers: apart from `1 = φ(1) = φ(2)`, *no* odd number is ever a totient
value.  Indeed `φ(m)` is even for every `m > 2`, while `φ(0) = 0`,
`φ(1) = φ(2) = 1`.

Consequently `V(x)` counts only the value `1` together with even numbers `≤ x`,
which already caps `V(x)` by roughly `x/2 + 1`.  This is a genuine density
constraint on the quantity studied in Erdős problem `#417` (it does not by itself
resolve the convergence question, which concerns the comparison with `V'`). -/

/-- **The only odd value taken by Euler's totient is `1`.** If `n` is odd and
`n ≠ 1`, then no `m` satisfies `φ(m) = n`.

The proof is a four–way case split on the argument `m`:
`φ(0) = 0` is not odd, `φ(1) = φ(2) = 1` contradicts `n ≠ 1`, and `φ(m)` is even
for every `m > 2` (so again not odd). -/
theorem no_odd_totient {n : ℕ} (hodd : Odd n) (h1 : n ≠ 1) :
    ¬ ∃ m : ℕ, Nat.totient m = n := by
  rintro ⟨m, rfl⟩
  -- Split into the small arguments `m ∈ {0,1,2}` and the generic case `m ≥ 3`.
  rcases Nat.lt_or_ge m 3 with hm | hm
  · -- `m < 3`: check `m = 0, 1, 2` explicitly.
    interval_cases m
    · -- `m = 0`: `φ 0 = 0` is not odd.
      rw [Nat.totient_zero] at hodd
      exact (by decide : ¬ Odd 0) hodd
    · -- `m = 1`: `φ 1 = 1`, contradicting `n ≠ 1`.
      exact h1 Nat.totient_one
    · -- `m = 2`: `φ 2 = 1`, contradicting `n ≠ 1`.
      exact h1 Nat.totient_two
  · -- `m ≥ 3`: `φ m` is even, hence not odd.
    exact (Nat.not_odd_iff_even.mpr (Nat.totient_even (by omega))) hodd

/-- **Problem-relevant corollary.** Odd numbers greater than `1` are never
counted by `V`, since they never occur as totient values.  Hence every value
counted by `V(x)` is either `1` or even — a structural constraint on the set
whose cardinality is `V(x)` in Erdős problem `#417`. -/
theorem not_mem_totientValuesAtMost_of_odd {x n : ℕ}
    (hodd : Odd n) (h1 : n ≠ 1) :
    n ∉ totientValuesAtMost x := by
  classical
  unfold totientValuesAtMost
  rw [Finset.mem_filter]
  rintro ⟨-, hex⟩
  exact no_odd_totient hodd h1 hex

end TotientValueRatio
