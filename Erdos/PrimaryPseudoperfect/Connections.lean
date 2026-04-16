/- 
# Primary Pseudoperfect Connections

Primary pseudoperfect numbers sit at the intersection of prime-reciprocal
identities and the pseudoperfect/weird-number framework already developed in
the repository.

For `m > 2`, the defining identity

`∑_{p ∈ P} 1/p = 1 - 1/m`

can be upgraded to a genuine unit-fraction representation of `1` by adjoining
the divisor `m` itself:

`∑_{p ∈ P} 1/p + 1/m = 1`.

The Egyptian-fraction bridge then implies that `m` is pseudoperfect.
-/
import Erdos.PrimaryPseudoperfect.Statement
import Erdos.WeirdNumbers.EgyptianBridge

namespace PrimaryPseudoperfect

open scoped BigOperators
open WeirdNumbers

/-- Any prime occurring in a witness divides the ambient integer `m`. -/
theorem prime_dvd_of_witness {m : ℕ} {P : Finset ℕ} {p : ℕ}
    (hW : PrimeReciprocalWitness m P) (hp : p ∈ P) : p ∣ m := by
  rcases hW with ⟨_, hprod, _⟩
  rw [← hprod]
  exact Finset.dvd_prod_of_mem (fun x => x) hp

/-- If the ambient integer `m` itself occurs in a witness set, then we are in
the trivial case `m = 2`. -/
theorem eq_two_of_mem_witness {m : ℕ} {P : Finset ℕ}
    (hW : PrimeReciprocalWitness m P) (hmP : m ∈ P) : m = 2 := by
  rcases hW with ⟨hprime, hprod, hsum⟩
  have hmprime : Nat.Prime m := hprime m hmP
  have hmpos : 0 < m := hmprime.pos
  have hmul : (∏ x ∈ P.erase m, x) * m = m := by
    calc
      (∏ x ∈ P.erase m, x) * m = ∏ x ∈ P, x := by
        simpa using (Finset.prod_erase_mul P (fun x => x) hmP)
      _ = m := hprod
  have hrest : ∏ x ∈ P.erase m, x = 1 := by
    apply Nat.eq_of_mul_eq_mul_right hmpos
    simpa using hmul
  have hEraseEmpty : P.erase m = ∅ := by
    by_contra hne
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hq_dvd : q ∣ ∏ x ∈ P.erase m, x := Finset.dvd_prod_of_mem (fun x => x) hq
    have hq_prime : Nat.Prime q := hprime q (Finset.mem_of_mem_erase hq)
    rw [hrest] at hq_dvd
    exact hq_prime.not_dvd_one hq_dvd
  have hPsingleton : P = {m} := by
    rw [← Finset.insert_erase hmP, hEraseEmpty]
    simp
  have hsum_single : ∑ p ∈ P, (1 / (p : ℚ)) = 1 / (m : ℚ) := by
    rw [hPsingleton]
    norm_num
  have hEqQ : (1 / (m : ℚ)) = 1 - 1 / (m : ℚ) := by
    rw [hsum_single] at hsum
    exact hsum
  have hm_ne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm_two : (m : ℚ) = 2 := by
    field_simp [hm_ne] at hEqQ
    linarith
  exact_mod_cast hm_two

/-- For `m > 2`, the ambient integer itself is not one of the witnessing
primes. -/
theorem not_mem_witness_of_two_lt {m : ℕ} {P : Finset ℕ}
    (hm : 2 < m) (hW : PrimeReciprocalWitness m P) : m ∉ P := by
  intro hmP
  have hm_two := eq_two_of_mem_witness hW hmP
  omega

/-- For `m > 2`, adjoining `m` to a prime-reciprocal witness produces a
divisor-set Egyptian-fraction representation of `1`. -/
theorem witness_to_unit_sum {m : ℕ} {P : Finset ℕ}
    (hm : 2 < m) (hW : PrimeReciprocalWitness m P) :
    ∃ T ⊆ m.divisors, (1 : ℕ) ∉ T ∧ T.Nonempty ∧
      ∑ t ∈ T, (1 / (t : ℚ)) = 1 := by
  rcases hW with ⟨hprime, hprod, hsum⟩
  let T : Finset ℕ := insert m P
  have hm_notin : m ∉ P := not_mem_witness_of_two_lt hm ⟨hprime, hprod, hsum⟩
  refine ⟨T, ?_, ?_, by simp [T], ?_⟩
  · intro t ht
    rcases Finset.mem_insert.mp ht with rfl | hp
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨prime_dvd_of_witness ⟨hprime, hprod, hsum⟩ hp, by omega⟩
  · intro h1
    rcases Finset.mem_insert.mp h1 with hm1 | h1P
    · omega
    · exact (hprime 1 h1P).ne_one rfl
  · calc
      ∑ t ∈ T, (1 / (t : ℚ))
        = (1 / (m : ℚ)) + ∑ p ∈ P, (1 / (p : ℚ)) := by
            simp [T, hm_notin]
      _ = (1 / (m : ℚ)) + (1 - 1 / (m : ℚ)) := by rw [hsum]
      _ = 1 := by
            have hm_ne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            field_simp [hm_ne]
            ring

/-- Every primary pseudoperfect number `m > 2` is pseudoperfect. -/
theorem primaryPseudoperfect_pseudoperfect {m : ℕ}
    (hm : IsPrimaryPseudoperfect m) (hgt : 2 < m) : Pseudoperfect m := by
  rcases hm with ⟨_, P, hP⟩
  exact (pseudoperfect_iff_unit_sum (by omega)).mpr (witness_to_unit_sum hgt hP)

/-- A primary pseudoperfect number is either the trivial example `2` or a
genuine pseudoperfect number. -/
theorem primaryPseudoperfect_two_or_pseudoperfect {m : ℕ}
    (hm : IsPrimaryPseudoperfect m) : m = 2 ∨ Pseudoperfect m := by
  rcases hm with ⟨hm2, P, hP⟩
  rcases lt_or_eq_of_le hm2 with hgt | rfl
  · exact Or.inr (primaryPseudoperfect_pseudoperfect ⟨hm2, P, hP⟩ hgt)
  · exact Or.inl rfl

/-- Every nontrivial primary pseudoperfect number has a divisor set which is
not sum-free. -/
theorem primaryPseudoperfect_divisors_not_sumFree {m : ℕ}
    (hm : IsPrimaryPseudoperfect m) (hgt : 2 < m) :
    ¬UnitFractionSets.SumFree m.divisors := by
  have hm1 : 1 < m := by omega
  exact pseudoperfect_divisors_not_sumFree hm1
    (primaryPseudoperfect_pseudoperfect hm hgt)

/-- Primary pseudoperfect numbers are never weird. -/
theorem primaryPseudoperfect_not_weird {m : ℕ}
    (hm : IsPrimaryPseudoperfect m) : ¬Weird m := by
  rcases primaryPseudoperfect_two_or_pseudoperfect hm with rfl | hp
  · exact prime_not_weird (by decide : Nat.Prime 2)
  · intro hw
    exact hw.2 hp

end PrimaryPseudoperfect
