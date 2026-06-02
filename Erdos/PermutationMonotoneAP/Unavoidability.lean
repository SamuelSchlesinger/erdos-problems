import Erdos.PermutationMonotoneAP.Statement

/-!
# Erdős #196, impossibility direction: scale-controlled monotone 3-APs

This file begins the **impossibility (YES) direction** of Erdős #196 — the attempt to show
that *every* permutation of `ℕ` contains a monotone 4-term AP. The roadmap there is a ladder:

* **(a)** [proved] every permutation of `ℕ` has a monotone 3-AP — Davis–Entringer–Graham–Simmons
  (`Statement.hasMonotoneAP_three`). The seed.
* **(b)** [this file] every permutation of `ℕ` has monotone 3-APs whose common difference is
  divisible by an *arbitrary* prescribed `M` — in particular by `2^k` for every `k`. This is the
  hinge that lets an impossibility argument **escalate the 2-adic scale**: a monotone 4-AP that
  extends such a 3-AP inherits its difference, so high-`v₂(d)` 3-APs are exactly the seeds
  needed to defeat Adenwalla's bounded-valuation avoiders.
* **(c)** [open — the crux] among those high-scale 3-APs, at least one has an *un-tuckable*
  completion (forcing an actual monotone 4-AP). This is the genuine content of #196-YES.

The proof of (b) is a one-line idea: **run the DEGS argument inside a single residue class.**
Fix `M`. Let `a = f 0` and look only at values `≡ a (mod M)`. Let `b` be the first such value
(in position order) exceeding `a`; its reflection `m = 2b − a` is again `≡ a (mod M)` and, by the
same prefix counting as DEGS, occurs later than `b`. So `(a, b, m)` is a monotone 3-AP, and
because `a, b` share a residue class mod `M`, its difference `b − a` is divisible by `M`.

`hasMonotoneAP_three` is the special case `M = 1`.
-/

namespace PermutationMonotoneAP

open Function

/-- **Scale-controlled DEGS (sub-lemma (b)).** For every permutation `f` of `ℕ` and every
`M ≥ 1`, the sequence `f 0, f 1, …` contains a monotone 3-term AP whose common difference is a
nonzero multiple of `M`. Taking `M = 2^k` gives monotone 3-APs of arbitrarily high 2-adic
valuation. The case `M = 1` is the Davis–Entringer–Graham–Simmons base case `hasMonotoneAP_three`.

Proof: the DEGS argument restricted to the residue class of `f 0` modulo `M`. With `a = f 0`,
take `b = f k` where `k` is the least position carrying a value `> a` that is `≡ a (mod M)`; then
`m = 2 b − a ≡ a (mod M)` exceeds `b` and, since every earlier position holds either a value
`≤ a` (in the class) or a value in another class, cannot occur before position `k`. Hence
`(a, b, m)` is an increasing monotone 3-AP at positions `0 < k < f⁻¹ m`, with difference
`b − a` divisible by `M`. -/
theorem hasMonotoneAP_three_dvd (f : ℕ ≃ ℕ) (M : ℕ) (hM : 0 < M) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      ∃ a d : ℤ, (M : ℤ) ∣ d ∧ d ≠ 0 ∧ ∀ j < 3, (f (p j) : ℤ) = a + (j : ℤ) * d := by
  classical
  -- some later position carries a value exceeding `f 0` and congruent to it mod `M`
  have hne : ∃ n, f 0 < f n ∧ f n % M = f 0 % M := by
    refine ⟨f.symm (f 0 + M), ?_, ?_⟩
    · rw [Equiv.apply_symm_apply]; omega
    · rw [Equiv.apply_symm_apply, Nat.add_mod_right]
  set k := Nat.find hne with hk_def
  have hspec : f 0 < f k ∧ f k % M = f 0 % M := Nat.find_spec hne
  obtain ⟨hk, hkmod⟩ := hspec
  have hmin : ∀ j, j < k → ¬ (f 0 < f j ∧ f j % M = f 0 % M) :=
    fun j hj => Nat.find_min hne hj
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; exact absurd hk (lt_irrefl _)
    · exact h
  set b := f k with hb
  -- `b` and `f 0` share a residue class mod `M`
  have hmb : Nat.ModEq M b (f 0) := hkmod
  set m := 2 * b - f 0 with hm
  set p₂ := f.symm m with hp₂
  have hfp₂ : f p₂ = m := by rw [hp₂, Equiv.apply_symm_apply]
  -- the reflection `m` is again `≡ f 0 (mod M)`
  have hmmod : m % M = f 0 % M := by
    have h1 : (m + f 0) ≡ (f 0 + f 0) [MOD M] := by
      have e1 : m + f 0 = 2 * b := by omega
      have e2 : f 0 + f 0 = 2 * f 0 := (two_mul (f 0)).symm
      rw [e1, e2]; exact hmb.mul_left 2
    exact Nat.ModEq.add_right_cancel' (f 0) h1
  -- `m` occurs after position `k`
  have hk_lt_p₂ : k < p₂ := by
    by_contra hle
    rw [not_lt] at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hmin' := hmin p₂ hlt
      rw [hfp₂] at hmin'
      exact hmin' ⟨by omega, hmmod⟩
    · rw [heq] at hfp₂; rw [← hb] at hfp₂; omega
  -- the integer cast of `m`
  have hcast : (m : ℤ) = 2 * (b : ℤ) - (f 0 : ℤ) := by
    rw [hm, Nat.cast_sub (by omega : f 0 ≤ 2 * b)]; push_cast; ring
  refine ⟨fun j => match j with | 0 => 0 | 1 => k | (n + 2) => p₂ + n, ?_,
          (f 0 : ℤ), (b : ℤ) - (f 0 : ℤ), ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => exact hkpos
    | 1 => exact hk_lt_p₂
    | (n + 2) => simp only; omega
  · -- `M ∣ b − f 0`: `b ≡ f 0 (mod M)`
    have hdvdnat : M ∣ b - f 0 := (Nat.modEq_iff_dvd' (le_of_lt hk)).mp hmb.symm
    rw [← Nat.cast_sub (le_of_lt hk)]; exact_mod_cast hdvdnat
  · -- `b − f 0 ≠ 0` since `f 0 < b`
    have : (f 0 : ℤ) < (b : ℤ) := by exact_mod_cast hk
    omega
  · intro j hj
    interval_cases j
    · simp
    · dsimp only; rw [← hb]; push_cast; ring
    · simp only [Nat.add_zero]; rw [hfp₂, hcast]; push_cast; ring

/-- **Monotone 3-APs of arbitrarily high 2-adic valuation.** For every permutation `f` of `ℕ`
and every `k`, the sequence contains a monotone 3-term AP whose common difference is a nonzero
multiple of `2^k`. This is sub-lemma (b) of the #196 impossibility ladder in the form used to
escalate the dyadic scale (each scale `k` is the regime Adenwalla's avoiders defend only up to). -/
theorem hasMonotoneAP_three_pow_two (f : ℕ ≃ ℕ) (k : ℕ) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      ∃ a d : ℤ, (2 : ℤ) ^ k ∣ d ∧ d ≠ 0 ∧ ∀ j < 3, (f (p j) : ℤ) = a + (j : ℤ) * d := by
  obtain ⟨p, hp, a, d, hdvd, hd0, hap⟩ := hasMonotoneAP_three_dvd f (2 ^ k) (by positivity)
  exact ⟨p, hp, a, d, by exact_mod_cast hdvd, hd0, hap⟩

end PermutationMonotoneAP
