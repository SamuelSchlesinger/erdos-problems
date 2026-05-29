import Mathlib

/-!
# Erdős Problems 195, 196, 197: Monotone Arithmetic Progressions in Permutations

A *permutation of `ℕ`* is a bijection `f : ℕ ≃ ℕ`, viewed as the sequence
`f 0, f 1, f 2, …`. A **monotone `k`-term arithmetic progression** in such a
sequence is a choice of strictly increasing positions `p 0 < p 1 < ⋯` whose
values `f (p 0), …, f (p (k-1))` form a `k`-term arithmetic progression
(equivalently an increasing or decreasing AP appears as a subsequence).

* **#195** (Erdős): for permutations of `ℤ`, what is the largest `k` such that
  every permutation contains a monotone `k`-term AP? Known to be `3` or `4`.
* **#196** (Erdős): must every permutation of `ℕ` contain a monotone 4-term AP?
* **#197** (Erdős–Graham): can `ℕ` be partitioned into two sets, each of which
  can be enumerated to avoid monotone 3-term APs?

The base case is a classical observation of Davis, Entringer, Graham and Simmons
(1977): *every* permutation of `ℕ` contains a monotone 3-term AP. We formalize
this here (`hasMonotoneAP_three`), giving the first formal treatment of this
circle of problems.

References:
- https://www.erdosproblems.com/195, /196, /197
- Davis, Entringer, Graham, Simmons, *On permutations containing no long
  arithmetic progressions*, Acta Arith. 34 (1977), 81–90.
- LeSaulnier, Vijay, *On permutations avoiding arithmetic progressions*,
  arXiv:1004.1740.
-/

namespace PermutationMonotoneAP

/-- The sequence `f : ℕ → ℕ` contains a **monotone `k`-term arithmetic
progression**: there is a strictly increasing sequence of positions `p` whose
first `k` values `f (p 0), …, f (p (k-1))` form a `k`-term arithmetic
progression with integer common difference `d` (the sign of `d` encodes
increasing vs. decreasing). -/
def HasMonotoneAP (f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ p : ℕ → ℕ, StrictMono p ∧ ∃ a d : ℤ, ∀ j < k, (f (p j) : ℤ) = a + (j : ℤ) * d

/-- A set `S ⊆ ℕ` is **`k`-free** if it can be enumerated (as a bijection
`ℕ ≃ S`) so that the resulting sequence avoids monotone `k`-term APs. -/
def IsFree (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ e : ℕ ≃ S, ¬ HasMonotoneAP (fun n => (e n : ℕ)) k

/-- **Erdős Problem 196.** Must every permutation of `ℕ` contain a monotone
4-term AP? -/
def Erdos196 : Prop := ∀ f : ℕ ≃ ℕ, HasMonotoneAP (fun n => f n) 4

/-- **Erdős Problem 197** (Erdős–Graham). Can `ℕ` be partitioned into two sets,
each of which is 3-free (can be enumerated avoiding monotone 3-term APs)? -/
def Erdos197 : Prop :=
  ∃ A B : Set ℕ, (∀ n, n ∈ A ↔ n ∉ B) ∧ IsFree A 3 ∧ IsFree B 3

/-- **Davis–Entringer–Graham–Simmons (1977).** Every permutation of `ℕ`
contains a monotone 3-term arithmetic progression.

Proof: Let `a = f 0`, and let `k` be the least index with `f k > a` (it exists
since `f` is surjective). Then `m := 2 (f k) - a > f k > a`, and `m` cannot
occur at any position `≤ k`: positions `< k` carry values `≤ a < m`, and
position `k` carries `f k ≠ m`. Hence `m` occurs after position `k`, so
`(a, f k, m)` is an increasing 3-term AP at the strictly increasing positions
`0 < k < f.symm m`. -/
theorem hasMonotoneAP_three (f : ℕ ≃ ℕ) : HasMonotoneAP (fun n => f n) 3 := by
  classical
  -- some position has value exceeding `f 0`
  have hne : ∃ n, f 0 < f n := ⟨f.symm (f 0 + 1), by rw [Equiv.apply_symm_apply]; omega⟩
  set k := Nat.find hne with hk_def
  have hk : f 0 < f k := Nat.find_spec hne
  have hmin : ∀ j, j < k → f j ≤ f 0 := by
    intro j hj; have := Nat.find_min hne hj; omega
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; exact absurd hk (lt_irrefl _)
    · exact h
  set b := f k with hb
  set m := 2 * b - f 0 with hm
  set p₂ := f.symm m with hp₂
  have hfp₂ : f p₂ = m := by rw [hp₂, Equiv.apply_symm_apply]
  -- `m` occurs after position `k`
  have hk_lt_p₂ : k < p₂ := by
    by_contra hle
    rw [not_lt] at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have := hmin p₂ hlt; omega
    · rw [heq] at hfp₂; omega
  -- the integer cast of `m`
  have hcast : (m : ℤ) = 2 * (b : ℤ) - (f 0 : ℤ) := by
    rw [hm, Nat.cast_sub (by omega : f 0 ≤ 2 * b)]; push_cast; ring
  -- the strictly increasing positions 0, k, p₂, then increasing forever
  refine ⟨fun j => match j with | 0 => 0 | 1 => k | (n + 2) => p₂ + n, ?_,
          (f 0 : ℤ), (b : ℤ) - (f 0 : ℤ), ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => exact hkpos
    | 1 => exact hk_lt_p₂
    | (n + 2) => simp only; omega
  · intro j hj
    interval_cases j
    · simp
    · dsimp only; rw [← hb]; push_cast; ring
    · simp only [Nat.add_zero]; rw [hfp₂, hcast]; push_cast; ring

end PermutationMonotoneAP
