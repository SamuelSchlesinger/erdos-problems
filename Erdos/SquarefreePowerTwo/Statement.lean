/- 
# Erdős Problem 11: Squarefree Numbers Plus Powers of Two

Problem `#11` asks whether every sufficiently large odd integer is the sum of
a squarefree number and a power of `2`. The problem page also records the
variant in which the hypothesis "odd" is replaced by "not divisible by `4`".

Reference: https://www.erdosproblems.com/11
-/
import Mathlib

namespace SquarefreePowerTwo

/-- `n` has a squarefree-plus-power-of-two representation if
`n = q + 2 ^ k` for some squarefree natural number `q`.

The exponent `k : ℕ` allows the power `2 ^ 0 = 1`, matching the usual natural
number formalization of powers of two. -/
def HasSquarefreePowerTwoRepresentation (n : ℕ) : Prop :=
  ∃ q k : ℕ, Squarefree q ∧ n = q + 2 ^ k

/-- All odd integers at least `N` have a squarefree-plus-power-of-two
representation. This is the bounded form of the main assertion. -/
def OddRepresentableFrom (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → Odd n → HasSquarefreePowerTwoRepresentation n

/-- Erdős problem `#11`: all sufficiently large odd integers are representable
as a squarefree number plus a power of `2`. -/
def EventuallyOddRepresentable : Prop :=
  ∃ N : ℕ, OddRepresentableFrom N

/-- All integers at least `N` that are not divisible by `4` have a
squarefree-plus-power-of-two representation. This packages the variant
mentioned on the problem page. -/
def NotDivisibleByFourRepresentableFrom (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → ¬ 4 ∣ n → HasSquarefreePowerTwoRepresentation n

/-- The "not divisible by `4`" eventual variant mentioned on the problem page. -/
def EventuallyNotDivisibleByFourRepresentable : Prop :=
  ∃ N : ℕ, NotDivisibleByFourRepresentableFrom N

/-- The main Erdős `#11` statement. -/
def Erdos11 : Prop :=
  EventuallyOddRepresentable

/-- A combined package containing the main statement and the `4 ∤ n` variant,
so later files can refer to both formulations together when useful. -/
def Erdos11Package : Prop :=
  EventuallyOddRepresentable ∧ EventuallyNotDivisibleByFourRepresentable

end SquarefreePowerTwo
