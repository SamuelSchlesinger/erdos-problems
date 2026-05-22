import Erdos.UlamPrimeRecurrence.Statement

/- 
# Elementary Facts About Ulam's Prime Recurrence

This file records the first concrete infrastructure for problem `#472`. We
prove uniqueness of the prescribed next prime, describe admissible values in a
finite prefix, and extend the example from the problem page:

`3, 5, 7, 11, 13, 17, 19, 23`.
-/
namespace UlamPrimeRecurrence

theorem mem_admissibleValues_iff {s : List ℕ} {x : ℕ} :
    x ∈ admissibleValues s ↔ ∃ q ∈ s, x = lastTerm s + q - 1 := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    exact ⟨q, by simpa using hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact Finset.mem_image.mpr ⟨q, by simpa using hq, rfl⟩

/-- The minimal admissible prime is unique whenever it exists. -/
theorem nextPrime_unique {s : List ℕ} {p q : ℕ}
    (hp : NextPrime s p) (hq : NextPrime s q) :
    p = q := by
  apply le_antisymm
  · exact hp.2.2.2 q hq.2.1 hq.2.2.1
  · exact hq.2.2.2 p hp.2.1 hp.2.2.1

/-- The seed `[3, 5]` is a legitimate starting seed of primes. -/
theorem threeFive_isPrimeSeed : PrimeSeed [3, 5] := by
  refine ⟨by decide, by simp, ?_⟩
  intro q hq
  have hq' : q = 3 ∨ q = 5 := by
    simpa using hq
  rcases hq' with rfl | rfl <;> norm_num

theorem admissibleValues_threeFive :
    admissibleValues [3, 5] = ({7, 9} : Finset ℕ) := by
  norm_num [admissibleValues, lastTerm]

theorem nextPrime_threeFive : NextPrime [3, 5] 7 := by
  refine ⟨by decide, ?_, by norm_num, ?_⟩
  · norm_num [admissibleValues, lastTerm]
  · intro r hr hprime
    have hr' : r = 7 ∨ r = 9 := by
      simpa [admissibleValues, lastTerm] using hr
    rcases hr' with rfl | rfl
    · omega
    · exfalso
      norm_num at hprime

theorem admissibleValues_threeFiveSeven :
    admissibleValues [3, 5, 7] = ({9, 11, 13} : Finset ℕ) := by
  norm_num [admissibleValues, lastTerm]

theorem nextPrime_threeFiveSeven : NextPrime [3, 5, 7] 11 := by
  refine ⟨by decide, ?_, by norm_num, ?_⟩
  · norm_num [admissibleValues, lastTerm]
  · intro r hr hprime
    have hr' : r = 9 ∨ r = 11 ∨ r = 13 := by
      simpa [admissibleValues, lastTerm] using hr
    rcases hr' with rfl | rfl | rfl
    · exfalso
      norm_num at hprime
    · omega
    · omega

theorem admissibleValues_threeFiveSevenEleven :
    admissibleValues [3, 5, 7, 11] = ({13, 15, 17, 21} : Finset ℕ) := by
  norm_num [admissibleValues, lastTerm]

theorem nextPrime_threeFiveSevenEleven : NextPrime [3, 5, 7, 11] 13 := by
  refine ⟨by decide, ?_, by norm_num, ?_⟩
  · norm_num [admissibleValues, lastTerm]
  · intro r hr hprime
    have hr' : r = 13 ∨ r = 15 ∨ r = 17 ∨ r = 21 := by
      simpa [admissibleValues, lastTerm] using hr
    rcases hr' with rfl | rfl | rfl | rfl
    · omega
    · exfalso
      norm_num at hprime
    · omega
    · exfalso
      norm_num at hprime

theorem admissibleValues_threeFiveSevenElevenThirteen :
    admissibleValues [3, 5, 7, 11, 13] = ({15, 17, 19, 23, 25} : Finset ℕ) := by
  norm_num [admissibleValues, lastTerm]

theorem nextPrime_threeFiveSevenElevenThirteen :
    NextPrime [3, 5, 7, 11, 13] 17 := by
  refine ⟨by decide, ?_, by norm_num, ?_⟩
  · norm_num [admissibleValues, lastTerm]
  · intro r hr hprime
    have hr' : r = 15 ∨ r = 17 ∨ r = 19 ∨ r = 23 ∨ r = 25 := by
      simpa [admissibleValues, lastTerm] using hr
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · exfalso
      norm_num at hprime
    · omega
    · omega
    · omega
    · exfalso
      norm_num at hprime

/-- After the prefix ending in `17`, the admissible values are obtained by
adding each earlier term to `17` and subtracting `1`. -/
theorem admissibleValues_threeFiveSevenElevenThirteenSeventeen :
    admissibleValues [3, 5, 7, 11, 13, 17] =
      ({19, 21, 23, 27, 29, 33} : Finset ℕ) := by
  norm_num [admissibleValues, lastTerm]

/-- The next Ulam-prime term after `3, 5, 7, 11, 13, 17` is `19`. -/
theorem nextPrime_threeFiveSevenElevenThirteenSeventeen :
    NextPrime [3, 5, 7, 11, 13, 17] 19 := by
  refine ⟨by decide, ?_, by norm_num, ?_⟩
  · norm_num [admissibleValues, lastTerm]
  · intro r hr hprime
    have hr' : r = 19 ∨ r = 21 ∨ r = 23 ∨ r = 27 ∨ r = 29 ∨ r = 33 := by
      simpa [admissibleValues, lastTerm] using hr
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · exfalso
      norm_num at hprime
    · omega
    · exfalso
      norm_num at hprime
    · omega
    · exfalso
      norm_num at hprime

/-- After appending `19`, the next finite search has `23` as the first prime
candidate. -/
theorem admissibleValues_threeFiveSevenElevenThirteenSeventeenNineteen :
    admissibleValues [3, 5, 7, 11, 13, 17, 19] =
      ({21, 23, 25, 29, 31, 35, 37} : Finset ℕ) := by
  norm_num [admissibleValues, lastTerm]

/-- The next Ulam-prime term after `3, 5, 7, 11, 13, 17, 19` is `23`. -/
theorem nextPrime_threeFiveSevenElevenThirteenSeventeenNineteen :
    NextPrime [3, 5, 7, 11, 13, 17, 19] 23 := by
  refine ⟨by decide, ?_, by norm_num, ?_⟩
  · norm_num [admissibleValues, lastTerm]
  · intro r hr hprime
    have hr' :
        r = 21 ∨ r = 23 ∨ r = 25 ∨ r = 29 ∨ r = 31 ∨ r = 35 ∨ r = 37 := by
      simpa [admissibleValues, lastTerm] using hr
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      norm_num at hprime
    · omega
    · exfalso
      norm_num at hprime
    · omega
    · omega
    · exfalso
      norm_num at hprime
    · omega

/-- The initial segment `3, 5, 7, 11, 13, 17, 19, 23` is generated by the
Ulam-prime recurrence starting from the seed `[3, 5]`. -/
theorem threeFive_prefix_3_5_7_11_13_17_19_23 :
    UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13, 17, 19, 23] := by
  have h0 : UlamPrimePrefixes [3, 5] [3, 5] :=
    UlamPrimePrefixes.base threeFive_isPrimeSeed
  have h1 : UlamPrimePrefixes [3, 5] [3, 5, 7] := by
    simpa using UlamPrimePrefixes.step h0 nextPrime_threeFive
  have h2 : UlamPrimePrefixes [3, 5] [3, 5, 7, 11] := by
    simpa using UlamPrimePrefixes.step h1 nextPrime_threeFiveSeven
  have h3 : UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13] := by
    simpa using UlamPrimePrefixes.step h2 nextPrime_threeFiveSevenEleven
  have h4 : UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13, 17] := by
    simpa using UlamPrimePrefixes.step h3 nextPrime_threeFiveSevenElevenThirteen
  have h5 : UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13, 17, 19] := by
    simpa using UlamPrimePrefixes.step h4 nextPrime_threeFiveSevenElevenThirteenSeventeen
  have h6 : UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13, 17, 19, 23] := by
    simpa using UlamPrimePrefixes.step h5
      nextPrime_threeFiveSevenElevenThirteenSeventeenNineteen
  exact h6

/-- The initial segment `3, 5, 7, 11, 13, 17` is generated by the Ulam-prime
recurrence starting from the seed `[3, 5]`. -/
theorem threeFive_prefix_3_5_7_11_13_17 :
    UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13, 17] := by
  have h0 : UlamPrimePrefixes [3, 5] [3, 5] :=
    UlamPrimePrefixes.base threeFive_isPrimeSeed
  have h1 : UlamPrimePrefixes [3, 5] [3, 5, 7] := by
    simpa using UlamPrimePrefixes.step h0 nextPrime_threeFive
  have h2 : UlamPrimePrefixes [3, 5] [3, 5, 7, 11] := by
    simpa using UlamPrimePrefixes.step h1 nextPrime_threeFiveSeven
  have h3 : UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13] := by
    simpa using UlamPrimePrefixes.step h2 nextPrime_threeFiveSevenEleven
  have h4 : UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13, 17] := by
    simpa using UlamPrimePrefixes.step h3 nextPrime_threeFiveSevenElevenThirteen
  exact h4

/-- In particular, the seed `[3, 5]` already yields a valid prefix of length
`8`. -/
theorem exists_threeFive_prefix_length_eight :
    ∃ s : List ℕ, UlamPrimePrefixes [3, 5] s ∧ 8 ≤ s.length := by
  refine ⟨[3, 5, 7, 11, 13, 17, 19, 23],
    threeFive_prefix_3_5_7_11_13_17_19_23, ?_⟩
  norm_num

/-- The earlier length-six bound remains available as a direct corollary. -/
theorem exists_threeFive_prefix_length_six :
    ∃ s : List ℕ, UlamPrimePrefixes [3, 5] s ∧ 6 ≤ s.length := by
  rcases exists_threeFive_prefix_length_eight with ⟨s, hs, hlen⟩
  exact ⟨s, hs, by omega⟩

/-- After appending `23`, the admissible values come from adding each earlier
term to `23` and subtracting `1`. -/
theorem admissibleValues_length8 :
    admissibleValues [3, 5, 7, 11, 13, 17, 19, 23] =
      ({25, 27, 29, 33, 35, 39, 41, 45} : Finset ℕ) := by
  norm_num [admissibleValues, lastTerm]

/-- The next Ulam-prime term after `3, 5, 7, 11, 13, 17, 19, 23` is `29`.

The admissible values `{25, 27, 29, 33, 35, 39, 41, 45}` contain exactly two
primes (`29` and `41`), so the minimum prime is `29`. -/
theorem nextPrime_length8_is_29 :
    NextPrime [3, 5, 7, 11, 13, 17, 19, 23] 29 := by
  refine ⟨by decide, ?_, by norm_num, ?_⟩
  · norm_num [admissibleValues, lastTerm]
  · intro r hr hprime
    have hr' :
        r = 25 ∨ r = 27 ∨ r = 29 ∨ r = 33 ∨ r = 35 ∨ r = 39 ∨ r = 41 ∨ r = 45 := by
      simpa [admissibleValues, lastTerm] using hr
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      norm_num at hprime
    · exfalso
      norm_num at hprime
    · omega
    · exfalso
      norm_num at hprime
    · exfalso
      norm_num at hprime
    · exfalso
      norm_num at hprime
    · omega
    · exfalso
      norm_num at hprime

/-- The initial segment `3, 5, 7, 11, 13, 17, 19, 23, 29` is generated by the
Ulam-prime recurrence starting from the seed `[3, 5]`. -/
theorem threeFive_prefix_length9 :
    UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13, 17, 19, 23, 29] := by
  simpa using
    UlamPrimePrefixes.step threeFive_prefix_3_5_7_11_13_17_19_23
      nextPrime_length8_is_29

/-- The seed `[3, 5]` yields a valid Ulam-prime prefix of length `9`. -/
theorem exists_threeFive_prefix_length_nine :
    ∃ s : List ℕ, UlamPrimePrefixes [3, 5] s ∧ 9 ≤ s.length := by
  refine ⟨[3, 5, 7, 11, 13, 17, 19, 23, 29], threeFive_prefix_length9, ?_⟩
  norm_num

/-- After appending `29`, the admissible values come from adding each earlier
term to `29` and subtracting `1`. -/
theorem admissibleValues_length9 :
    admissibleValues [3, 5, 7, 11, 13, 17, 19, 23, 29] =
      ({31, 33, 35, 39, 41, 45, 47, 51, 57} : Finset ℕ) := by
  norm_num [admissibleValues, lastTerm]

/-- The next Ulam-prime term after `3, 5, 7, 11, 13, 17, 19, 23, 29` is `31`.

The admissible values `{31, 33, 35, 39, 41, 45, 47, 51, 57}` contain three
primes (`31`, `41`, `47`), so the minimum prime is `31`. -/
theorem nextPrime_length9_is_31 :
    NextPrime [3, 5, 7, 11, 13, 17, 19, 23, 29] 31 := by
  refine ⟨by decide, ?_, by norm_num, ?_⟩
  · norm_num [admissibleValues, lastTerm]
  · intro r hr hprime
    have hr' :
        r = 31 ∨ r = 33 ∨ r = 35 ∨ r = 39 ∨ r = 41 ∨ r = 45 ∨ r = 47 ∨
          r = 51 ∨ r = 57 := by
      simpa [admissibleValues, lastTerm] using hr
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · exfalso
      norm_num at hprime
    · exfalso
      norm_num at hprime
    · exfalso
      norm_num at hprime
    · omega
    · exfalso
      norm_num at hprime
    · omega
    · exfalso
      norm_num at hprime
    · exfalso
      norm_num at hprime

/-- The initial segment `3, 5, 7, 11, 13, 17, 19, 23, 29, 31` is generated by
the Ulam-prime recurrence starting from the seed `[3, 5]`. -/
theorem threeFive_prefix_length10 :
    UlamPrimePrefixes [3, 5] [3, 5, 7, 11, 13, 17, 19, 23, 29, 31] := by
  simpa using
    UlamPrimePrefixes.step threeFive_prefix_length9 nextPrime_length9_is_31

/-- The seed `[3, 5]` yields a valid Ulam-prime prefix of length `10`. -/
theorem exists_threeFive_prefix_length_ten :
    ∃ s : List ℕ, UlamPrimePrefixes [3, 5] s ∧ 10 ≤ s.length := by
  refine ⟨[3, 5, 7, 11, 13, 17, 19, 23, 29, 31], threeFive_prefix_length10, ?_⟩
  norm_num

end UlamPrimeRecurrence
