import Erdos.IntervalDivisibility.Statement

/-
# Elementary Facts About Short Intervals with Prescribed Divisibility

This file records the simplest explicit constructions for problem `#710`.
For `n ≥ 2`, the interval `(n, n + n²)` already contains distinct integers
`a₁, …, aₙ` with `k ∣ a_k`, namely

* `a₁ = n + 1`
* `a_k = nk` for `2 ≤ k ≤ n`.

This yields the elementary quadratic upper bound `f(n) ≤ n²`.
-/
namespace IntervalDivisibility

/-- Explicit witnesses for the interval `(n, n + n²)`. -/
def quadraticWitness (n : ℕ) (i : Fin n) : ℕ :=
  if i.1 = 0 then n + 1 else (i.1 + 1) * n

theorem quadraticWitness_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (quadraticWitness n) := by
  intro i j hij
  apply Fin.ext
  by_cases hi : i.1 = 0 <;> by_cases hj : j.1 = 0
  · omega
  · exfalso
    have hj2 : 2 ≤ j.1 + 1 := by omega
    have hmul : 2 * n ≤ (j.1 + 1) * n := by
      simpa [two_mul] using Nat.mul_le_mul_right n hj2
    have hlt : n + 1 < (j.1 + 1) * n := by
      have hn2 : n + 1 < 2 * n := by omega
      exact lt_of_lt_of_le hn2 hmul
    have heq : n + 1 = (j.1 + 1) * n := by
      simpa [quadraticWitness, hi, hj] using hij
    exact (ne_of_lt hlt) heq
  · exfalso
    have hi2 : 2 ≤ i.1 + 1 := by omega
    have hmul : 2 * n ≤ (i.1 + 1) * n := by
      simpa [two_mul] using Nat.mul_le_mul_right n hi2
    have hlt : n + 1 < (i.1 + 1) * n := by
      have hn2 : n + 1 < 2 * n := by omega
      exact lt_of_lt_of_le hn2 hmul
    have heq : n + 1 = (i.1 + 1) * n := by
      simpa [quadraticWitness, hi, hj] using hij.symm
    exact (ne_of_lt hlt) heq
  · have heq : (i.1 + 1) * n = (j.1 + 1) * n := by
      simpa [quadraticWitness, hi, hj] using hij
    have hnpos : 0 < n := by omega
    have heq' : n * (i.1 + 1) = n * (j.1 + 1) := by
      simpa [Nat.mul_comm] using heq
    have hcancel : i.1 + 1 = j.1 + 1 := Nat.mul_left_cancel hnpos heq'
    omega

theorem quadraticWitness_bounds {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    n < quadraticWitness n i ∧ quadraticWitness n i < n + n ^ 2 := by
  by_cases hi : i.1 = 0
  · have hq : quadraticWitness n i = n + 1 := by simp [quadraticWitness, hi]
    constructor
    · rw [hq]
      omega
    · have hlt : n + 1 < n + n := by omega
      have hn1 : 1 ≤ n := by omega
      have hle : n + n ≤ n + n ^ 2 := by
        have hmul : n ≤ n ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul_left n hn1
        exact Nat.add_le_add_left hmul n
      rw [hq]
      exact lt_of_lt_of_le hlt hle
  · have hi2 : 2 ≤ i.1 + 1 := by omega
    have hi_le : i.1 + 1 ≤ n := Nat.succ_le_of_lt i.2
    have hq : quadraticWitness n i = (i.1 + 1) * n := by simp [quadraticWitness, hi]
    constructor
    · rw [hq]
      have hnpos : 0 < n := by omega
      have hn2 : n < 2 * n := by
        rw [two_mul]
        exact Nat.lt_add_of_pos_right hnpos
      have hmul : 2 * n ≤ (i.1 + 1) * n := by
        simpa [two_mul] using Nat.mul_le_mul_right n hi2
      exact lt_of_lt_of_le hn2 hmul
    · rw [hq]
      have hmul : (i.1 + 1) * n ≤ n * n := by
        exact Nat.mul_le_mul_right n hi_le
      have hs_lt : n * n < n + n * n := by
        have hs_lt' : n * n < n * n + n := Nat.lt_add_of_pos_right (show 0 < n by omega)
        simpa [Nat.add_comm] using hs_lt'
      have hs_eq : n ^ 2 = n * n := by rw [pow_two]
      rw [hs_eq]
      exact lt_of_le_of_lt hmul hs_lt

theorem quadraticWitness_dvd {n : ℕ} (i : Fin n) :
    (i.1 + 1) ∣ quadraticWitness n i := by
  by_cases hi : i.1 = 0
  · simp [quadraticWitness, hi]
  · simp [quadraticWitness, hi]

theorem validConfiguration_quadratic {n : ℕ} (hn : 2 ≤ n) :
    ValidConfiguration n (n ^ 2) := by
  refine ⟨quadraticWitness n, quadraticWitness_injective hn, ?_, quadraticWitness_dvd⟩
  intro i
  exact quadraticWitness_bounds hn i

theorem validConfiguration_one :
    ValidConfiguration 1 2 := by
  refine ⟨fun _ => 2, ?_, ?_, ?_⟩
  · intro i j _
    exact Subsingleton.elim _ _
  · intro i
    fin_cases i
    constructor <;> decide
  · intro i
    fin_cases i
    simp

/-- Any explicit valid configuration yields an upper bound for `f(n)`. -/
theorem fValue_le_of_validConfiguration {n m : ℕ}
    (h : ValidConfiguration n m) :
    fValue n ≤ m := by
  exact Nat.sInf_le h

theorem fValue_one_le_two :
    fValue 1 ≤ 2 := by
  exact fValue_le_of_validConfiguration validConfiguration_one

/-- Elementary quadratic upper bound coming from the explicit configuration
`a₁ = n + 1` and `a_k = nk` for `2 ≤ k ≤ n`. -/
theorem fValue_le_sq {n : ℕ} (hn : 2 ≤ n) :
    fValue n ≤ n ^ 2 := by
  exact fValue_le_of_validConfiguration (validConfiguration_quadratic hn)

/-- For every `n ≥ 1` there is at least one valid configuration, so the set of
admissible interval lengths is nonempty. (For `n = 1` use the interval `(1, 3)`;
for `n ≥ 2` use the explicit quadratic construction `a₁ = n + 1`, `a_k = nk`.)
This is exactly what is needed to guarantee that `fValue n`, defined as an
infimum, is *attained* and hence is itself an admissible length rather than the
junk value `0` produced by `sInf ∅`. -/
theorem validConfiguration_nonempty {n : ℕ} (hn : 1 ≤ n) :
    {m : ℕ | ValidConfiguration n m}.Nonempty := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- `n = 1`
    have hn1 : n = 1 := by omega
    subst hn1
    exact ⟨2, validConfiguration_one⟩
  · -- `n ≥ 2`
    exact ⟨n ^ 2, validConfiguration_quadratic h2⟩

/-- Lower bound coming from the last divisibility constraint.

In any valid configuration on `(n, n + m)` (with `n ≥ 1`) the witness `a_{n-1}`
attached to the index `n - 1` must satisfy `n ∣ a_{n-1}` and `n < a_{n-1}`. A
multiple of `n` that is strictly larger than `n` is at least `2n`, so
`2n ≤ a_{n-1} < n + m`, which forces `n < m`. -/
theorem lt_of_validConfiguration {n m : ℕ} (hn : 1 ≤ n)
    (h : ValidConfiguration n m) : n < m := by
  obtain ⟨a, _hinj, hbound, hdvd⟩ := h
  -- The last index `n - 1 : Fin n` (valid because `n ≥ 1`).
  have hlt : n - 1 < n := by omega
  let i : Fin n := ⟨n - 1, hlt⟩
  -- The underlying value of this index is `n - 1`.
  have hival : i.1 = n - 1 := rfl
  -- Its divisibility condition is `(n - 1) + 1 = n` divides `a i`.
  have hidx : i.1 + 1 = n := by rw [hival]; omega
  have hdvdn : n ∣ a i := by
    have := hdvd i
    rwa [hidx] at this
  -- Interval bounds on `a i`.
  obtain ⟨hgt, hlt'⟩ := hbound i
  -- Write `a i = n * c`.
  obtain ⟨c, hc⟩ := hdvdn
  -- From `n < a i = n * c` and `n ≥ 1` we get `2 ≤ c`.
  have hncn : n * 1 < n * c := by rw [Nat.mul_one, ← hc]; exact hgt
  have h1c : 1 < c := Nat.lt_of_mul_lt_mul_left hncn
  have hc2 : 2 ≤ c := h1c
  -- Hence `2 * n ≤ a i`.
  have h2n : 2 * n ≤ a i := by
    rw [hc]
    calc 2 * n = n * 2 := by ring
      _ ≤ n * c := Nat.mul_le_mul_left n hc2
  -- Combine with `a i < n + m`.
  omega

/-- **Main lower bound for problem #710.** For every `n ≥ 1` we have

`n < fValue n`,

i.e. the shortest admissible interval has length strictly greater than `n`.

The hypothesis `n ≥ 1` is essential: for `n = 0` the divisibility constraints
are vacuous (`Fin 0` is empty), so `ValidConfiguration 0 m` holds for *every*
`m`, whence `fValue 0 = sInf {m | True} = 0` and the strict bound `0 < 0` is
false. For `n ≥ 1`, `validConfiguration_nonempty` guarantees the infimum is
attained, and `lt_of_validConfiguration` applied to that attaining length gives
the bound. -/
theorem lt_fValue {n : ℕ} (hn : 1 ≤ n) : n < fValue n := by
  -- The infimum is attained at some valid length `m₀ = fValue n`.
  have hmem : fValue n ∈ {m : ℕ | ValidConfiguration n m} :=
    Nat.sInf_mem (validConfiguration_nonempty hn)
  -- That length is itself a valid configuration length, so the bound applies.
  exact lt_of_validConfiguration hn hmem

end IntervalDivisibility
