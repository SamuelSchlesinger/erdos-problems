/-
# Erdős Problem 710: Short Intervals with Prescribed Divisibility

Let `f(n)` be minimal such that the open interval `(n, n + f(n))` contains
distinct integers `a₁, …, aₙ` with `k ∣ a_k` for every `1 ≤ k ≤ n`.

The problem asks for an asymptotic formula for `f(n)`.

Reference: https://www.erdosproblems.com/710
-/
import Mathlib

namespace IntervalDivisibility

/-- `ValidConfiguration n m` means that the open interval `(n, n + m)` contains
pairwise distinct witnesses `a₁, …, aₙ` with `k ∣ a_k` for every
`1 ≤ k ≤ n`. We index by `Fin n`, so the `i`th divisibility condition is
`(i + 1) ∣ a_i`. -/
def ValidConfiguration (n m : ℕ) : Prop :=
  ∃ a : Fin n → ℕ,
    Function.Injective a ∧
    (∀ i : Fin n, n < a i ∧ a i < n + m) ∧
    ∀ i : Fin n, (i.1 + 1) ∣ a i

/-- The extremal quantity from problem `#710`. -/
noncomputable def fValue (n : ℕ) : ℕ :=
  sInf {m : ℕ | ValidConfiguration n m}

end IntervalDivisibility
