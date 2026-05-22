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
theorem v_pos {x : ℕ} (hx : 1 ≤ x) : 0 < V x := by
  exact lt_of_lt_of_le (vPrime_pos hx) (vPrime_le_v x)

end TotientValueRatio
