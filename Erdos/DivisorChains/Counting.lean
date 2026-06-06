import Erdos.DivisorChains.Statement

/-!
# Counting integers with two coprime divisors

This is the only number-theoretic input to the upper bound for Erdős #696.

A chain step `d → e` forces `gcd d e = 1` (`ChainStep.coprime`), so the integers
`n ≤ x` that admit the step `d → e` as part of a chain (i.e. `d ∣ n` and `e ∣ n`)
are exactly the multiples of `d * e` in `(0, x]`, of which there are
`⌊x / (d e)⌋ ≤ x / (d e)`.  Summing `1/(de)` over "bad" short steps is what makes
the exceptional set have density zero; that summation is carried out elsewhere.
-/

namespace DivisorChains

open Finset

/-- For coprime `d, e`, the integers in `(0, x]` divisible by both are exactly
the multiples of `d * e`, so there are `x / (d * e)` of them. -/
theorem card_filter_dvd_pair {d e x : ℕ} (hcop : Nat.Coprime d e) :
    #{n ∈ Finset.Ioc 0 x | d ∣ n ∧ e ∣ n} = x / (d * e) := by
  have hpred : ∀ n, (d ∣ n ∧ e ∣ n) ↔ d * e ∣ n := by
    intro n
    constructor
    · rintro ⟨hd, he⟩; exact hcop.mul_dvd_of_dvd_of_dvd hd he
    · intro hn; exact ⟨(dvd_mul_right d e).trans hn, (dvd_mul_left e d).trans hn⟩
  rw [← Nat.Ioc_filter_dvd_card_eq_div x (d * e)]
  congr 1
  exact Finset.filter_congr (fun n _ => hpred n)

/-- Real-valued form: the number of `n ∈ (0, x]` with two coprime divisors `d, e`
is at most `x / (d * e)`. -/
theorem card_filter_dvd_pair_le_real {d e x : ℕ} (hcop : Nat.Coprime d e) :
    (#{n ∈ Finset.Ioc 0 x | d ∣ n ∧ e ∣ n} : ℝ) ≤ (x : ℝ) / (d * e) := by
  rw [card_filter_dvd_pair hcop]
  calc ((x / (d * e) : ℕ) : ℝ) ≤ ((x : ℝ) / (d * e : ℕ)) := Nat.cast_div_le
    _ = (x : ℝ) / (d * e) := by push_cast; ring

end DivisorChains
