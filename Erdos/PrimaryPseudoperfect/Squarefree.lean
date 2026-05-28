import Erdos.PrimaryPseudoperfect.Statement
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-
# Squarefree Reformulation of Primary Pseudoperfect Numbers

The defining identity for problem `#313` is usually phrased in the
literature as

  `m ≥ 2` is **squarefree** and  `∑_{p ∣ m, p prime} 1/p + 1/m = 1`.

Our `Statement.lean` instead packages a primary pseudoperfect number via a
witness `Finset` of primes `P` whose product is `m` and whose reciprocal sum
equals `1 − 1/m`.

This file proves the two definitions are equivalent. Given a witness `P`:

* `Nat.Finset.squarefree_prod_of_pairwise_isCoprime` (with distinct primes
  being coprime via `Nat.coprime_primes`) gives squarefreeness of `m`;
* the equality `P = m.primeFactors` follows from
  `Nat.prod_primeFactors_invOn_squarefree`.

Conversely, given a squarefree `m ≥ 2` with the sum identity, the
`primeFactors` set is a witness.

Reference: https://www.erdosproblems.com/313
-/
namespace PrimaryPseudoperfect

open scoped BigOperators

/-- **Structural lemma.** A `Finset` of primes whose product equals `m`
forces `m` to be squarefree, and the `Finset` to be exactly the set of prime
divisors of `m`. -/
theorem squarefree_and_eq_primeFactors_of_prod_eq {m : ℕ} {P : Finset ℕ}
    (_hm : 1 ≤ m) (hprimes : ∀ p ∈ P, Nat.Prime p)
    (hprod : (∏ p ∈ P, p) = m) :
    Squarefree m ∧ P = m.primeFactors := by
  -- (1) Squarefreeness: each prime is squarefree, and distinct primes are
  -- pairwise `IsRelPrime` (since they are coprime in `ℕ`).
  have hSF_prod : Squarefree (∏ p ∈ P, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro p hp q hq hpq
      have hcop : p.Coprime q :=
        (Nat.coprime_primes (hprimes p hp) (hprimes q hq)).mpr hpq
      exact Nat.coprime_iff_isRelPrime.mp hcop
    · intro p hp
      exact (hprimes p hp).squarefree
  have hSF : Squarefree m := by simpa [hprod] using hSF_prod
  refine ⟨hSF, ?_⟩
  -- (2) Identify `P` with `m.primeFactors` using the bijection
  -- `s ↦ ∏ p ∈ s, p` between prime-Finsets and squarefree naturals.
  have hsupp : (∏ p ∈ P, p).factorization.support = P :=
    Nat.prod_primeFactors_invOn_squarefree.1 hprimes
  have hsupp' : m.factorization.support = P := by simpa [hprod] using hsupp
  have hsf := Nat.support_factorization m
  -- `hsf : m.factorization.support = m.primeFactors`, `hsupp' : ... = P`.
  rw [hsupp'] at hsf
  exact hsf

/-- The prime-reciprocal witness reciprocal-sum equation rewritten over
`m.primeFactors`. -/
theorem witness_sum_eq_primeFactors_sum {m : ℕ} {P : Finset ℕ}
    (hm : 1 ≤ m) (hW : PrimeReciprocalWitness m P) :
    (∑ p ∈ m.primeFactors, (1 / (p : ℚ))) = 1 - 1 / (m : ℚ) := by
  rcases hW with ⟨hprimes, hprod, hsum⟩
  obtain ⟨_, hPF⟩ := squarefree_and_eq_primeFactors_of_prod_eq hm hprimes hprod
  rw [← hPF]
  exact hsum

/-- **Squarefree reformulation, forward direction.** A primary pseudoperfect
number is squarefree and satisfies the standard prime-divisor identity. -/
theorem squarefree_form_of_primaryPseudoperfect {m : ℕ}
    (hm : IsPrimaryPseudoperfect m) :
    Squarefree m ∧
      (∑ p ∈ m.primeFactors, (1 / (p : ℚ))) + 1 / (m : ℚ) = 1 := by
  rcases hm with ⟨hm2, P, hW⟩
  have hm1 : 1 ≤ m := by omega
  rcases hW with ⟨hprimes, hprod, hsum⟩
  obtain ⟨hSF, hPF⟩ :=
    squarefree_and_eq_primeFactors_of_prod_eq hm1 hprimes hprod
  refine ⟨hSF, ?_⟩
  have hm_ne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← hPF, hsum]
  field_simp [hm_ne]
  ring

/-- **Squarefree reformulation, backward direction.** A squarefree `m ≥ 2`
satisfying `∑_{p | m} 1/p + 1/m = 1` is primary pseudoperfect with witness
`m.primeFactors`. -/
theorem primaryPseudoperfect_of_squarefree_form {m : ℕ}
    (hm : 2 ≤ m) (hSF : Squarefree m)
    (hsum : (∑ p ∈ m.primeFactors, (1 / (p : ℚ))) + 1 / (m : ℚ) = 1) :
    IsPrimaryPseudoperfect m := by
  refine ⟨hm, m.primeFactors, ?_, ?_, ?_⟩
  · intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  · exact Nat.prod_primeFactors_of_squarefree hSF
  · have hm_ne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    linarith

/-- **Main equivalence.** Our witness-based definition of primary
pseudoperfect numbers is equivalent to the literature definition:
`m ≥ 2 ∧ Squarefree m ∧ ∑_{p ∣ m} 1/p + 1/m = 1`. -/
theorem isPrimaryPseudoperfect_iff_squarefree_form (m : ℕ) :
    IsPrimaryPseudoperfect m ↔
      2 ≤ m ∧ Squarefree m ∧
        (∑ p ∈ m.primeFactors, (1 / (p : ℚ))) + 1 / (m : ℚ) = 1 := by
  refine ⟨?_, ?_⟩
  · intro hm
    refine ⟨hm.1, ?_⟩
    exact squarefree_form_of_primaryPseudoperfect hm
  · rintro ⟨hm2, hSF, hsum⟩
    exact primaryPseudoperfect_of_squarefree_form hm2 hSF hsum

/-- Every primary pseudoperfect number is squarefree. -/
theorem squarefree_of_primaryPseudoperfect {m : ℕ}
    (hm : IsPrimaryPseudoperfect m) : Squarefree m :=
  (squarefree_form_of_primaryPseudoperfect hm).1

end PrimaryPseudoperfect
