/-
# Egyptian Fraction Bridge (#470 ↔ #301)

The divisor complement map d ↦ n/d converts between subset-sum
characterizations and unit-fraction-sum characterizations:

  n is pseudoperfect ⟺ ∃ nonempty T ⊆ divisors(n) \ {1} with ∑ 1/t = 1

This bridges the weird-numbers module with the unit-fraction universe.
-/
import Erdos.WeirdNumbers.Statement
import Erdos.UnitFractionSets.Statement

namespace WeirdNumbers

open Finset

/-! ### Divisor complement helpers

The map d ↦ n/d sends proper divisors to divisors > 1 and vice versa.
These are the building blocks for both directions of the bridge. -/

/-- If a and b both divide n ≠ 0 and n/a = n/b, then a = b. -/
private lemma div_left_cancel {n a b : ℕ} (hn : n ≠ 0)
    (ha : a ∣ n) (hb : b ∣ n) (hab : n / a = n / b) : a = b := by
  have ha' := Nat.div_mul_cancel ha   -- n / a * a = n
  have hb' := Nat.div_mul_cancel hb   -- n / b * b = n
  have ha_ne : a ≠ 0 := fun h => hn (by subst h; simpa using ha)
  have hna_pos : 0 < n / a :=
    Nat.div_pos (Nat.le_of_dvd (by omega) ha) (by omega)
  apply Nat.eq_of_mul_eq_mul_left hna_pos
  -- Goal: n / a * a = n / a * b
  -- We know n / a * a = n (from ha') and n / a * b = n (from hb', hab)
  have step : n / a * b = n := by
    conv_lhs => rw [hab]
    exact hb'
  linarith

/-- d ↦ n/d is injective on divisors of n. -/
private lemma div_left_injOn (hn : n ≠ 0) :
    Set.InjOn (n / ·) (n.divisors : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Nat.mem_divisors] at ha hb
  exact div_left_cancel hn ha.1 hb.1 hab

/-- A proper divisor d of n maps to a divisor n/d that is > 1.
    Since d < n, we have n/d ≥ 2. -/
private lemma div_properDivisor_mem {n d : ℕ} (hn : 0 < n)
    (hd : d ∈ n.properDivisors) : n / d ∈ n.divisors ∧ 1 < n / d := by
  rw [Nat.mem_properDivisors] at hd
  constructor
  · -- n/d divides n (since d divides n), and n ≠ 0
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd.1, by omega⟩
  · -- d < n and d ∣ n, so n/d > 1.
    -- Write n = d * k. Then n/d = k, and d < d*k forces k > 1.
    obtain ⟨k, hk⟩ := hd.1
    have hd_ne : d ≠ 0 := by intro h; subst h; simp at hk; omega
    have hk_eq : n / d = k := by
      rw [hk]; exact Nat.mul_div_cancel_left k (by omega)
    rw [hk_eq]
    -- From d < n = d * k with d > 0: k > 1
    nlinarith [hd.2]

/-- A divisor t > 1 of n maps to a proper divisor n/t.
    Since t > 1, we have n/t < n. -/
private lemma div_divisor_gt_one_mem {n t : ℕ} (hn : 0 < n)
    (ht : t ∈ n.divisors) (h1 : 1 < t) : n / t ∈ n.properDivisors := by
  rw [Nat.mem_divisors] at ht
  rw [Nat.mem_properDivisors]
  exact ⟨Nat.div_dvd_of_dvd ht.1, Nat.div_lt_self hn h1⟩

/-! ### Forward direction: pseudoperfect → unit-fraction sum

If S ⊆ properDivisors(n) sums to n, then T = {n/d : d ∈ S} is a set
of divisors > 1 whose reciprocals sum to 1.

The key calculation: 1/(n/d) = d/n in ℚ, so ∑ 1/(n/d) = (∑ d)/n = n/n = 1. -/

private theorem pseudoperfect_to_unit_sum {n : ℕ} (hn : 0 < n)
    {S : Finset ℕ} (hSsub : S ⊆ n.properDivisors)
    (hSne : S.Nonempty) (hSsum : S.sum id = n) :
    ∃ T ⊆ n.divisors, (1 : ℕ) ∉ T ∧ T.Nonempty ∧
      ∑ t ∈ T, (1 / (t : ℚ)) = 1 := by
  -- Build T = {n/d : d ∈ S}
  set T := S.image (n / ·) with hT_def
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · -- T ⊆ n.divisors
    intro t ht
    rw [mem_image] at ht
    obtain ⟨d, hd, rfl⟩ := ht
    exact (div_properDivisor_mem hn (hSsub hd)).1
  · -- 1 ∉ T: if n/d = 1 for some d ∈ S, then d = n, but d < n
    intro h1
    rw [mem_image] at h1
    obtain ⟨d, hd, hnd⟩ := h1
    have hpd := Nat.mem_properDivisors.mp (hSsub hd)
    have hmul := Nat.div_mul_cancel hpd.1  -- n / d * d = n
    -- n/d = 1 means 1 * d = n, i.e., d = n, contradicting d < n
    rw [hnd, one_mul] at hmul
    omega
  · -- T.Nonempty
    exact hSne.image _
  · -- ∑ t ∈ T, 1/t = 1
    -- Rewrite sum over T = S.image(n/·) as sum over S
    have hinj : ∀ a ∈ S, ∀ b ∈ S, n / a = n / b → a = b := by
      intro a ha b hb hab
      have ha' := Nat.mem_properDivisors.mp (hSsub ha)
      have hb' := Nat.mem_properDivisors.mp (hSsub hb)
      exact div_left_cancel (by omega) ha'.1 hb'.1 hab
    rw [hT_def, sum_image hinj]
    -- Goal: ∑ d ∈ S, 1 / ↑(n / d) = 1
    -- Pointwise: 1/↑(n/d) = ↑d/↑n via Nat.cast_div then field simplification
    have hcast : ∀ d ∈ S, (1 : ℚ) / (↑(n / d) : ℚ) = (↑d : ℚ) / (↑n : ℚ) := by
      intro d hd
      have hpd := Nat.mem_properDivisors.mp (hSsub hd)
      have hd_ne : (d : ℚ) ≠ 0 := by
        have : d ≠ 0 := by intro h; subst h; simp at hpd; omega
        exact_mod_cast this
      have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [Nat.cast_div hpd.1 hd_ne]
      field_simp
    rw [sum_congr rfl hcast]
    -- Goal: ∑ d ∈ S, ↑d / ↑n = 1
    rw [← sum_div]
    -- Goal: (∑ d ∈ S, ↑d) / ↑n = 1
    have hsum_cast : (∑ d ∈ S, (↑d : ℚ)) = (↑n : ℚ) := by
      have h : (↑(S.sum id) : ℚ) = ∑ d ∈ S, (↑d : ℚ) := by push_cast; rfl
      rw [hSsum] at h; exact h.symm
    rw [hsum_cast]
    exact div_self (by exact_mod_cast (show n ≠ 0 by omega))

/-! ### Backward direction: unit-fraction sum → pseudoperfect

If T ⊆ divisors(n) with all elements > 1 and ∑ 1/t = 1, then
S = {n/t : t ∈ T} ⊆ properDivisors(n) sums to n.

The key: cast S.sum to ℚ, where it becomes n · ∑ 1/t = n · 1 = n. -/

private theorem unit_sum_to_pseudoperfect {n : ℕ} (hn : 0 < n)
    {T : Finset ℕ} (hTsub : T ⊆ n.divisors) (h1 : (1 : ℕ) ∉ T)
    (_hTne : T.Nonempty) (hTsum : ∑ t ∈ T, (1 / (t : ℚ)) = 1) :
    Pseudoperfect n := by
  -- Build S = {n/t : t ∈ T}
  set S := T.image (n / ·)
  -- Each t ∈ T is a divisor > 1 (since 1 ∉ T and t ∈ n.divisors means t ≥ 1)
  have ht_gt : ∀ t ∈ T, 1 < t := by
    intro t ht
    have htd := Nat.mem_divisors.mp (hTsub ht)
    have ht_pos : 0 < t := Nat.pos_of_dvd_of_pos htd.1 hn
    by_contra h; push_neg at h
    -- t ≤ 1 and t > 0 means t = 1, contradicting 1 ∉ T
    interval_cases t; exact h1 ht
  -- S ⊆ n.properDivisors
  have hS_sub : S ⊆ n.properDivisors := by
    intro s hs
    rw [mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact div_divisor_gt_one_mem hn (hTsub ht) (ht_gt t ht)
  -- Injectivity of n/· on T (for sum_image)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, n / a = n / b → a = b := by
    intro a ha b hb hab
    have ha' := Nat.mem_divisors.mp (hTsub ha)
    have hb' := Nat.mem_divisors.mp (hTsub hb)
    exact div_left_cancel (by omega) ha'.1 hb'.1 hab
  -- S.sum id = n: cast to ℚ and use the reciprocal sum
  have hS_sum : S.sum id = n := by
    -- It suffices to show the equation in ℚ (since both sides are in ℕ)
    have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    suffices h : (↑(S.sum id) : ℚ) = ↑n from by exact_mod_cast h
    -- Expand S.sum via sum_image: S = T.image(n/·), so S.sum = ∑ t∈T, n/t
    have h1 : (↑(S.sum id) : ℚ) = ∑ t ∈ T, (↑(n / t) : ℚ) := by
      rw [Finset.sum_image hinj]; push_cast; rfl
    rw [h1]
    -- Cast each n/t to ↑n / ↑t using Nat.cast_div
    have h2 : ∀ t ∈ T, (↑(n / t) : ℚ) = (↑n : ℚ) / (↑t : ℚ) := by
      intro t ht
      have htd := Nat.mem_divisors.mp (hTsub ht)
      have ht_ne : (t : ℚ) ≠ 0 := by
        have : t ≠ 0 := by intro h; subst h; simp at htd
        exact_mod_cast this
      exact Nat.cast_div htd.1 ht_ne
    rw [sum_congr rfl h2]
    -- ∑ n/t = n · ∑ 1/t = n · 1 = n
    -- Rewrite n/t as n * (1/t), then factor out n
    simp_rw [div_eq_mul_inv]
    rw [← Finset.mul_sum]
    -- Now use hTsum: ∑ 1/t = 1
    simp_rw [one_div] at hTsum
    rw [hTsum, mul_one]
  exact ⟨S, mem_powerset.mpr hS_sub, hS_sum⟩

/-! ### Main theorem and corollary -/

/-- **Egyptian fraction bridge.** A positive integer n is pseudoperfect if and
    only if some nonempty subset of its divisors (excluding 1) has reciprocals
    summing to 1.

    This connects the subset-sum world (Problem #470, weird numbers) with the
    unit-fraction world (Problems #301/#302). -/
theorem pseudoperfect_iff_unit_sum {n : ℕ} (hn : 0 < n) :
    Pseudoperfect n ↔
      ∃ T ⊆ n.divisors, (1 : ℕ) ∉ T ∧ T.Nonempty ∧
        ∑ t ∈ T, (1 / (t : ℚ)) = 1 := by
  constructor
  · -- Forward: pseudoperfect → unit sum
    intro ⟨S, hSmem, hSsum⟩
    rw [mem_powerset] at hSmem
    -- S must be nonempty: its sum is n > 0
    have hSne : S.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty.mp h] at hSsum
      simp at hSsum; omega
    exact pseudoperfect_to_unit_sum hn hSmem hSne hSsum
  · -- Backward: unit sum → pseudoperfect
    intro ⟨T, hTsub, h1, hTne, hTsum⟩
    exact unit_sum_to_pseudoperfect hn hTsub h1 hTne hTsum

/-- **Pseudoperfect numbers have divisor sets that are not SumFree.**

    If n > 1 is pseudoperfect, take a = 1 ∈ divisors(n). The bridge gives
    T ⊆ divisors(n) \ {1} with ∑ 1/t = 1 = 1/a, violating SumFree. -/
theorem pseudoperfect_divisors_not_sumFree {n : ℕ} (hn : 1 < n)
    (hp : Pseudoperfect n) : ¬UnitFractionSets.SumFree n.divisors := by
  -- Get T from the bridge
  have hn_pos : 0 < n := by omega
  obtain ⟨T, hTsub, h1, hTne, hTsum⟩ := (pseudoperfect_iff_unit_sum hn_pos).mp hp
  -- Unfold SumFree and exhibit the violation with a = 1
  intro hsf
  -- 1 ∈ n.divisors (since 1 divides everything and n ≠ 0)
  have h1_mem : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  -- T ⊆ n.divisors.erase 1 (since 1 ∉ T and T ⊆ n.divisors)
  have hT_erase : T ⊆ n.divisors.erase 1 := by
    intro t ht
    rw [mem_erase]
    exact ⟨fun h => h1 (h ▸ ht), hTsub ht⟩
  -- SumFree says 1/1 ≠ ∑ 1/t for any nonempty T ⊆ divisors\{1}
  have := hsf 1 h1_mem T hT_erase hTne
  -- But 1/1 = 1 = ∑ 1/t, contradiction
  simp only [Nat.cast_one, one_div, inv_one, ne_eq] at this
  simp only [one_div] at hTsum
  exact this hTsum.symm

end WeirdNumbers
