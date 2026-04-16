/- 
# Primary Pseudoperfect Examples and Extension Lemma

The classical examples

`2, 6, 42, 1806`

arise from a simple extension rule: whenever `m` is primary pseudoperfect and
`m + 1` is prime, adjoining the new prime `m + 1` produces a witness for
`m * (m + 1)`.
-/
import Erdos.PrimaryPseudoperfect.Connections

namespace PrimaryPseudoperfect

open scoped BigOperators

/-- The trivial primary pseudoperfect witness `1/2 = 1 - 1/2`. -/
theorem two_witness : PrimeReciprocalWitness 2 ({2} : Finset ℕ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp at hp
    simpa [hp] using (by decide : Nat.Prime 2)
  · norm_num
  · norm_num

/-- If `m` has a prime-reciprocal witness and `m + 1` is prime, then
`m * (m + 1)` also has a witness obtained by adjoining the new prime. -/
theorem succ_prime_extension {m : ℕ} {P : Finset ℕ}
    (hm : 2 ≤ m) (hW : PrimeReciprocalWitness m P) (hprime : Nat.Prime (m + 1)) :
    PrimeReciprocalWitness (m * (m + 1)) (insert (m + 1) P) := by
  rcases hW with ⟨hprimes, hprod, hsum⟩
  have hnotin : m + 1 ∉ P := by
    intro hm1P
    have hdiv_prod : m + 1 ∣ ∏ p ∈ P, p :=
      Finset.dvd_prod_of_mem (s := P) (a := m + 1) (f := fun x : ℕ => x) hm1P
    have hdiv : m + 1 ∣ m := by simpa [hprod] using hdiv_prod
    have hm_pos : 0 < m := by omega
    have hm1_le : m + 1 ≤ m := Nat.le_of_dvd hm_pos hdiv
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hpP
    · exact hprime
    · exact hprimes p hpP
  · rw [Finset.prod_insert hnotin, hprod]
    ring
  · rw [Finset.sum_insert hnotin, hsum]
    have hm_ne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm1_ne : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfrac :
        (1 / ((m + 1 : ℕ) : ℚ)) = (1 / (m : ℚ)) - 1 / ((m * (m + 1) : ℕ) : ℚ) := by
      rw [Nat.cast_mul]
      field_simp [hm_ne, hm1_ne]
      norm_num
    calc
      (1 / ((m + 1 : ℕ) : ℚ)) + (1 - 1 / (m : ℚ))
        = ((1 / (m : ℚ)) - 1 / ((m * (m + 1) : ℕ) : ℚ)) + (1 - 1 / (m : ℚ)) := by
            rw [hfrac]
      _ = 1 - 1 / ((m * (m + 1) : ℕ) : ℚ) := by ring

/-- `2` is primary pseudoperfect. -/
theorem primaryPseudoperfect_two : IsPrimaryPseudoperfect 2 := by
  exact ⟨by omega, {2}, two_witness⟩

/-- The witness `{2, 3}` gives the primary pseudoperfect number `6`. -/
theorem six_witness : PrimeReciprocalWitness 6 ({2, 3} : Finset ℕ) := by
  have hP : insert 3 ({2} : Finset ℕ) = ({2, 3} : Finset ℕ) := by
    ext x
    simp [or_comm]
  simpa [hP] using succ_prime_extension (m := 2) (P := ({2} : Finset ℕ))
    (by omega) two_witness (by decide : Nat.Prime 3)

/-- `6` is primary pseudoperfect. -/
theorem primaryPseudoperfect_six : IsPrimaryPseudoperfect 6 := by
  exact ⟨by omega, {2, 3}, six_witness⟩

/-- The witness `{2, 3, 7}` gives the primary pseudoperfect number `42`. -/
theorem fortyTwo_witness : PrimeReciprocalWitness 42 ({2, 3, 7} : Finset ℕ) := by
  have hP : insert 7 ({2, 3} : Finset ℕ) = ({2, 3, 7} : Finset ℕ) := by
    ext x
    simp [or_assoc, or_comm]
  simpa [hP] using
    succ_prime_extension (m := 6) (P := ({2, 3} : Finset ℕ))
      (by omega) six_witness (by decide : Nat.Prime 7)

/-- `42` is primary pseudoperfect. -/
theorem primaryPseudoperfect_fortyTwo : IsPrimaryPseudoperfect 42 := by
  exact ⟨by omega, {2, 3, 7}, fortyTwo_witness⟩

/-- The witness `{2, 3, 7, 43}` gives the primary pseudoperfect number `1806`. -/
theorem eighteenOhSix_witness : PrimeReciprocalWitness 1806 ({2, 3, 7, 43} : Finset ℕ) := by
  have hP : insert 43 ({2, 3, 7} : Finset ℕ) = ({2, 3, 7, 43} : Finset ℕ) := by
    ext x
    simp [or_assoc, or_comm]
  simpa [hP] using
    succ_prime_extension (m := 42) (P := ({2, 3, 7} : Finset ℕ))
      (by omega) fortyTwo_witness (by decide : Nat.Prime 43)

/-- `1806` is primary pseudoperfect. -/
theorem primaryPseudoperfect_eighteenOhSix : IsPrimaryPseudoperfect 1806 := by
  exact ⟨by omega, {2, 3, 7, 43}, eighteenOhSix_witness⟩

/-- Every displayed example beyond `2` is pseudoperfect. -/
theorem pseudoperfect_six : WeirdNumbers.Pseudoperfect 6 :=
  primaryPseudoperfect_pseudoperfect primaryPseudoperfect_six (by omega)

/-- Every displayed example beyond `2` is pseudoperfect. -/
theorem pseudoperfect_fortyTwo : WeirdNumbers.Pseudoperfect 42 :=
  primaryPseudoperfect_pseudoperfect primaryPseudoperfect_fortyTwo (by omega)

/-- Every displayed example beyond `2` is pseudoperfect. -/
theorem pseudoperfect_eighteenOhSix : WeirdNumbers.Pseudoperfect 1806 :=
  primaryPseudoperfect_pseudoperfect primaryPseudoperfect_eighteenOhSix (by omega)

end PrimaryPseudoperfect
