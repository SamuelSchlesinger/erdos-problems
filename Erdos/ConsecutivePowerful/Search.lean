/- 
# Finite Search Infrastructure for Consecutive Powerful Triples

The Erdős Problems site marks problem #364 as *verifiable*: one can rule out
initial ranges by exhaustive search. This file makes that computational view
available inside Lean by giving a finite-factorization characterization of
`Powerful`.
-/
import Erdos.ConsecutivePowerful.Modular

namespace ConsecutivePowerful

/-- A positive natural number is powerful iff every prime in its finite
    factorization support appears with exponent at least `2`. -/
theorem powerful_iff_factorization_ge_two {n : ℕ} :
    Powerful n ↔ 0 < n ∧ ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p := by
  constructor
  · intro hn
    refine ⟨hn.1, ?_⟩
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hsquare : p ^ 2 ∣ n := hn.2 p hp' hpdvd
    exact (hp'.pow_dvd_iff_le_factorization hn.1.ne').mp hsquare
  · rintro ⟨hn, hfac⟩
    refine ⟨hn, ?_⟩
    intro p hp hpdvd
    have hmem : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hn.ne'⟩
    exact (hp.pow_dvd_iff_le_factorization hn.ne').mpr (hfac p hmem)

instance : DecidablePred Powerful := by
  intro n
  rw [powerful_iff_factorization_ge_two]
  infer_instance

instance : DecidablePred ConsecutivePowerfulTriple := by
  intro n
  unfold ConsecutivePowerfulTriple
  infer_instance

set_option linter.style.nativeDecide false

/-- **Residue-class search certificate.**

Exhaustive search on the three admissible residue classes modulo `36`
shows there is no candidate start below `1000000`. -/
theorem no_candidate_consecutive_powerful_triples_below_1000000 :
    (∀ k < 27778, ¬ConsecutivePowerfulTriple (36 * k + 7)) ∧
    (∀ k < 27778, ¬ConsecutivePowerfulTriple (36 * k + 27)) ∧
    (∀ k < 27778, ¬ConsecutivePowerfulTriple (36 * k + 35)) := by
  native_decide

/-- **Certified finite search, strengthened by modular pruning.**

There is no triple of consecutive powerful numbers starting below `1000000`. -/
theorem no_consecutive_powerful_triple_below_1000000 :
    ∀ n < 1000000, ¬ConsecutivePowerfulTriple n := by
  intro n hn htriple
  rcases no_candidate_consecutive_powerful_triples_below_1000000 with ⟨h7, h27, h35⟩
  have hmod : n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 :=
    consecutive_powerful_triple_mod_thirtysix htriple
  have hdiv : n = n % 36 + 36 * (n / 36) := by
    exact (Nat.mod_add_div n 36).symm
  rcases hmod with h7mod | h27mod | h35mod
  · have hk : n / 36 < 27778 := by omega
    have hn_eq : n = 36 * (n / 36) + 7 := by omega
    exact (h7 (n / 36) hk) (hn_eq ▸ htriple)
  · have hk : n / 36 < 27778 := by omega
    have hn_eq : n = 36 * (n / 36) + 27 := by omega
    exact (h27 (n / 36) hk) (hn_eq ▸ htriple)
  · have hk : n / 36 < 27778 := by omega
    have hn_eq : n = 36 * (n / 36) + 35 := by omega
    exact (h35 (n / 36) hk) (hn_eq ▸ htriple)

end ConsecutivePowerful
