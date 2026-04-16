/- 
# Erdős Problem 472: Ulam's Prime Recurrence

Start from a finite increasing seed of primes `q₁ < ⋯ < q_m`. For each later
index, define `q_{n+1}` to be the smallest prime of the form `q_n + q_i - 1`
coming from an earlier term `q_i`.

Erdős problem `#472` asks whether there exists an initial seed for which this
process never gets stuck, equivalently produces arbitrarily long valid finite
prefixes.

Reference: https://www.erdosproblems.com/472
-/
import Mathlib

namespace UlamPrimeRecurrence

/-- A valid initial seed is a nonempty strictly increasing list of primes. -/
def PrimeSeed (s : List ℕ) : Prop :=
  s ≠ [] ∧ s.Pairwise (· < ·) ∧ ∀ q ∈ s, Nat.Prime q

/-- The current last term of a finite prefix, with default `0` for the empty
list. All substantive uses below impose nonemptiness separately. -/
def lastTerm (s : List ℕ) : ℕ :=
  s.getLastD 0

/-- The candidate values of the form `q_n + q_i - 1` obtained from a finite
prefix `s = [q₁, …, q_n]`. We package them as a `Finset`, so duplicates are
discarded automatically. -/
def admissibleValues (s : List ℕ) : Finset ℕ :=
  s.toFinset.image fun q => lastTerm s + q - 1

/-- `q` is the next Ulam-prime term after the prefix `s` if `s` is nonempty and
`q` is the smallest prime among the admissible values `q_n + q_i - 1`. -/
def NextPrime (s : List ℕ) (q : ℕ) : Prop :=
  s ≠ [] ∧ q ∈ admissibleValues s ∧ Nat.Prime q ∧
    ∀ r, r ∈ admissibleValues s → Nat.Prime r → q ≤ r

/-- The valid finite prefixes generated from a fixed seed by repeatedly
appending the prescribed next prime. -/
inductive UlamPrimePrefixes (seed : List ℕ) : List ℕ → Prop
  | base : PrimeSeed seed → UlamPrimePrefixes seed seed
  | step {s : List ℕ} {q : ℕ} :
      UlamPrimePrefixes seed s →
      NextPrime s q →
      UlamPrimePrefixes seed (s ++ [q])

/-- Erdős problem `#472`: some finite prime seed generates arbitrarily long
valid prefixes, hence an infinite Ulam-prime recurrence. -/
def Erdos472Conjecture : Prop :=
  ∃ seed : List ℕ, PrimeSeed seed ∧
    ∀ N : ℕ, ∃ s : List ℕ, UlamPrimePrefixes seed s ∧ N ≤ s.length

end UlamPrimeRecurrence
