/-
# Erdős Problem 470: Weird Numbers

A positive integer n is *weird* if it is abundant (the sum of its proper
divisors exceeds n) but not pseudoperfect (n cannot be expressed as a sum
of any subset of its proper divisors).

Questions:
1. Do any odd weird numbers exist? ($10 Erdős prize)
2. Are there infinitely many primitive weird numbers?

Known results:
- The smallest weird number is 70
- Weird numbers have positive density (Benkoski & Erdős)
- No odd weird numbers exist below 10²¹ (Fang)
- Any odd weird number must have at least 6 prime factors (Liddy & Riedl)

Reference: https://www.erdosproblems.com/470
-/
import Mathlib

namespace WeirdNumbers

/-- A positive integer n is *abundant* if the sum of its proper divisors
    is at least n, i.e., σ(n) ≥ 2n. -/
def Abundant (n : ℕ) : Prop :=
  0 < n ∧ n ≤ (n.properDivisors.sum id)

/-- A positive integer n is *pseudoperfect* (or *semiperfect*) if it equals
    the sum of some subset of its proper divisors. -/
def Pseudoperfect (n : ℕ) : Prop :=
  ∃ S ∈ n.properDivisors.powerset, S.sum id = n

/-- A positive integer n is *weird* if it is abundant but not pseudoperfect:
    its proper divisors sum to more than n, yet no subset of them sums to
    exactly n. -/
def Weird (n : ℕ) : Prop :=
  Abundant n ∧ ¬Pseudoperfect n

/-- A weird number is *primitive* if none of its proper divisors is weird. -/
def PrimitiveWeird (n : ℕ) : Prop :=
  Weird n ∧ ∀ d ∈ n.properDivisors, ¬Weird d

/-- Erdős's first question: do any odd weird numbers exist? -/
def OddWeirdExists : Prop :=
  ∃ n : ℕ, Weird n ∧ ¬Even n

/-- Erdős's second question: are there infinitely many primitive weird numbers? -/
def InfinitelyManyPrimitiveWeird : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ PrimitiveWeird n

instance : DecidablePred Abundant := by
  intro n; unfold Abundant; infer_instance

instance : DecidablePred Pseudoperfect := by
  intro n; unfold Pseudoperfect; infer_instance

instance : DecidablePred Weird := by
  intro n; unfold Weird; infer_instance

instance : DecidablePred PrimitiveWeird := by
  intro n; unfold PrimitiveWeird; infer_instance

/-- The proper divisors of `70` are exactly `1, 2, 5, 7, 10, 14, 35`. -/
private theorem properDivisors_seventy :
    (70 : ℕ).properDivisors = ({1, 2, 5, 7, 10, 14, 35} : Finset ℕ) := by
  decide

/-- No subset of `{1, 2, 5, 7, 10, 14}` sums to `35`. -/
private theorem no_subset_sum_thirtyfive_smallDivisors :
    ∀ S ⊆ ({1, 2, 5, 7, 10, 14} : Finset ℕ), S.sum id ≠ 35 := by
  decide

/-- The proper divisors of `836` are exactly `1, 2, 4, 11, 19, 22, 38, 44,
76, 209, 418`. -/
private theorem properDivisors_eightthreeSix :
    (836 : ℕ).properDivisors = ({1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418} : Finset ℕ) := by
  decide

/-- No subset of `{1, 2, 4, 11, 19, 22, 38, 44, 76}` sums to `8`. -/
private theorem no_subset_sum_eight_836_smallDivisors :
    ∀ S ⊆ ({1, 2, 4, 11, 19, 22, 38, 44, 76} : Finset ℕ), S.sum id ≠ 8 := by
  intro S hS hsum
  let tinyDivs : Finset ℕ := ({1, 2, 4} : Finset ℕ)
  have hsubset_tiny : S ⊆ tinyDivs := by
    intro x hx
    have hxle : x ≤ S.sum id := by
      simpa using Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hx
    have hxsmall : x ∈ ({1, 2, 4, 11, 19, 22, 38, 44, 76} : Finset ℕ) := hS hx
    have hxcase : x = 1 ∨ x = 2 ∨ x = 4 := by
      have : x ≤ 8 := by omega
      interval_cases x <;> simp at hxsmall <;> simp
    rcases hxcase with rfl | rfl | rfl <;> simp [tinyDivs]
  have hsum_le : S.sum id ≤ tinyDivs.sum id :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset_tiny (fun _ _ _ => Nat.zero_le _)
  have htiny_sum : tinyDivs.sum id = 7 := by
    decide
  omega

/-- Every abundant number below `70` is one of the standard small cases. -/
private theorem abundant_below_70_cases :
    ∀ n < 70, Abundant n →
      n = 6 ∨ n = 12 ∨ n = 18 ∨ n = 20 ∨ n = 24 ∨ n = 28 ∨ n = 30 ∨
        n = 36 ∨ n = 40 ∨ n = 42 ∨ n = 48 ∨ n = 54 ∨ n = 56 ∨ n = 60 ∨ n = 66 := by
  decide

/-- Every positive multiple of `6` is pseudoperfect, witnessed by the proper
divisors `k`, `2k`, and `3k`. -/
private theorem six_mul_pseudoperfect {k : ℕ} (hk : 0 < k) :
    Pseudoperfect (6 * k) := by
  let T : Finset ℕ := insert (3 * k) (insert (2 * k) ({k} : Finset ℕ))
  refine ⟨T, ?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro x hx
    have hx' : x = 3 * k ∨ x = 2 * k ∨ x = k := by
      simpa [T, Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with rfl | rfl | rfl
    · rw [Nat.mem_properDivisors]
      constructor
      · exact ⟨2, by omega⟩
      · omega
    · rw [Nat.mem_properDivisors]
      constructor
      · exact ⟨3, by omega⟩
      · omega
    · rw [Nat.mem_properDivisors]
      constructor
      · exact ⟨6, by ring⟩
      · omega
  · have hk2 : 2 * k ≠ k := by omega
    have hk3 : 3 * k ≠ k := by omega
    have h32 : 3 * k ≠ 2 * k := by omega
    rw [show T = insert (3 * k) (insert (2 * k) ({k} : Finset ℕ)) by rfl]
    rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · simp
        omega
      · simp [Finset.mem_singleton, hk2]
    · simp [Finset.mem_insert, Finset.mem_singleton, hk3, h32]

/-- Each abundant number below `70` is pseudoperfect. -/
private theorem pseudoperfect_of_small_abundant_case :
    ∀ n,
      n = 6 ∨ n = 12 ∨ n = 18 ∨ n = 20 ∨ n = 24 ∨ n = 28 ∨ n = 30 ∨
        n = 36 ∨ n = 40 ∨ n = 42 ∨ n = 48 ∨ n = 54 ∨ n = 56 ∨ n = 60 ∨ n = 66 →
      Pseudoperfect n := by
  intro n h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · simpa using six_mul_pseudoperfect (k := 1) (by decide)
  · simpa using six_mul_pseudoperfect (k := 2) (by decide)
  · simpa using six_mul_pseudoperfect (k := 3) (by decide)
  · decide
  · simpa using six_mul_pseudoperfect (k := 4) (by decide)
  · decide
  · simpa using six_mul_pseudoperfect (k := 5) (by decide)
  · simpa using six_mul_pseudoperfect (k := 6) (by decide)
  · decide
  · simpa using six_mul_pseudoperfect (k := 7) (by decide)
  · simpa using six_mul_pseudoperfect (k := 8) (by decide)
  · simpa using six_mul_pseudoperfect (k := 9) (by decide)
  · decide
  · simpa using six_mul_pseudoperfect (k := 10) (by decide)
  · simpa using six_mul_pseudoperfect (k := 11) (by decide)

/-- 70 is weird: its proper divisors sum to `74`, but no subset of
    `{1, 2, 5, 7, 10, 14, 35}` sums to `70`. -/
theorem seventy_is_weird : Weird 70 := by
  constructor
  · refine ⟨by positivity, ?_⟩
    rw [properDivisors_seventy]
    norm_num
  · rintro ⟨S, hSsub, hSsum⟩
    rw [properDivisors_seventy, Finset.mem_powerset] at hSsub
    let smallDivs : Finset ℕ := ({1, 2, 5, 7, 10, 14} : Finset ℕ)
    have hErase :
        ({1, 2, 5, 7, 10, 14, 35} : Finset ℕ).erase 35 = smallDivs := by
      decide
    have h35 : 35 ∈ S := by
      by_contra h35
      have hsub_small : S ⊆ smallDivs := by
        intro x hx
        have hx70 : x ∈ ({1, 2, 5, 7, 10, 14, 35} : Finset ℕ) := hSsub hx
        have hx_erase : x ∈ ({1, 2, 5, 7, 10, 14, 35} : Finset ℕ).erase 35 := by
          refine Finset.mem_erase.mpr ?_
          constructor
          · intro hx35
            subst x
            exact h35 hx
          · exact hx70
        rw [hErase] at hx_erase
        exact hx_erase
      have hsum_le : S.sum id ≤ smallDivs.sum id :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_small (fun _ _ _ => Nat.zero_le _)
      have hsmall_sum : smallDivs.sum id = 39 := by
        decide
      omega
    have hsub_small : S.erase 35 ⊆ smallDivs := by
      intro x hx
      have hxS : x ∈ S := Finset.mem_of_mem_erase hx
      have hx70 : x ∈ ({1, 2, 5, 7, 10, 14, 35} : Finset ℕ) := hSsub hxS
      have hx_erase : x ∈ ({1, 2, 5, 7, 10, 14, 35} : Finset ℕ).erase 35 := by
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hx70⟩
      rw [hErase] at hx_erase
      exact hx_erase
    have hsum_small : (S.erase 35).sum id = 35 := by
      have hrewrite : S.sum id = 35 + (S.erase 35).sum id := by
        calc
          S.sum id = (insert 35 (S.erase 35)).sum id := by
            rw [Finset.insert_erase h35]
          _ = 35 + (S.erase 35).sum id := by
            rw [Finset.sum_insert]
            · simp
            · simp
      rw [hrewrite] at hSsum
      omega
    exact no_subset_sum_thirtyfive_smallDivisors (S.erase 35) hsub_small hsum_small

/-- No number less than `70` is weird. -/
theorem no_weird_below_70 : ∀ n < 70, ¬Weird n := by
  intro n hn hw
  have hcases := abundant_below_70_cases n hn hw.1
  exact hw.2 (pseudoperfect_of_small_abundant_case n hcases)

/-- A perfect number (one whose proper divisors sum to exactly n) is
    pseudoperfect: just take S = n.properDivisors itself. -/
theorem perfect_implies_pseudoperfect {n : ℕ} (_hn : 0 < n)
    (hperf : n.properDivisors.sum id = n) : Pseudoperfect n :=
  ⟨n.properDivisors, Finset.mem_powerset.mpr (Finset.Subset.refl _), hperf⟩

/-- A perfect number is not weird: it is pseudoperfect (and may or
    may not be abundant, but either way the ¬Pseudoperfect clause
    of Weird fails). -/
theorem perfect_not_weird {n : ℕ} (hn : 0 < n)
    (hperf : n.properDivisors.sum id = n) : ¬Weird n := by
  intro ⟨_, hnp⟩
  exact hnp (perfect_implies_pseudoperfect hn hperf)

/-- A positive integer n is *deficient* if the sum of its proper divisors
    is less than n, i.e., σ(n) < 2n. -/
def Deficient (n : ℕ) : Prop :=
  0 < n ∧ (n.properDivisors.sum id) < n

/-- **Deficient numbers are not weird.**

    A deficient number has proper divisors summing to less than n,
    so it is not abundant. Since weird requires abundant, deficient
    numbers cannot be weird. -/
theorem deficient_not_weird {n : ℕ} (hdef : Deficient n) : ¬Weird n := by
  obtain ⟨_, hlt⟩ := hdef
  intro ⟨⟨_, hab⟩, _⟩
  exact absurd (lt_of_le_of_lt hab hlt) (lt_irrefl _)

/-- **Primes are not weird.**

    A prime p has properDivisors = {1}, so the sum of proper divisors
    is 1 < p. Hence p is deficient (far from abundant) and therefore
    not weird.

    This is a basic sanity check: the weird number phenomenon requires
    a rich divisor structure that primes completely lack. -/
theorem prime_not_weird {p : ℕ} (hp : Nat.Prime p) : ¬Weird p := by
  apply deficient_not_weird
  refine ⟨hp.pos, ?_⟩
  have h1 : p.properDivisors.sum id = 1 :=
    Nat.sum_properDivisors_eq_one_iff_prime.mpr hp
  have h2 := hp.one_lt
  omega

/-- **1 is not weird.**

    The number 1 has no proper divisors (properDivisors 1 = ∅), so the
    sum is 0 < 1 = n. It is deficient (and not even abundant). -/
theorem one_not_weird : ¬Weird 1 := by
  exact no_weird_below_70 1 (by omega)

/-- 70 is a *primitive* weird number: it is weird, and every proper divisor
    is smaller than `70`, hence not weird by `no_weird_below_70`. -/
theorem seventy_is_primitive_weird : PrimitiveWeird 70 := by
  refine ⟨seventy_is_weird, ?_⟩
  intro d hd
  exact no_weird_below_70 d (Nat.mem_properDivisors.mp hd).2

/-- **836 is the second-smallest weird number.** -/
theorem weird_836 : Weird 836 := by
  constructor
  · refine ⟨by positivity, ?_⟩
    rw [properDivisors_eightthreeSix]
    norm_num
  · rintro ⟨S, hSsub, hSsum⟩
    rw [properDivisors_eightthreeSix, Finset.mem_powerset] at hSsub
    let smallDivs : Finset ℕ := ({1, 2, 4, 11, 19, 22, 38, 44, 76} : Finset ℕ)
    let midDivs : Finset ℕ := insert 209 smallDivs
    have hErase418 :
        ({1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418} : Finset ℕ).erase 418 = midDivs := by
      decide
    have hErase209 : midDivs.erase 209 = smallDivs := by
      ext x
      simp [midDivs, smallDivs]
    have h418 : 418 ∈ S := by
      by_contra h418
      have hsub_mid : S ⊆ midDivs := by
        intro x hx
        have hx836 : x ∈ ({1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418} : Finset ℕ) := hSsub hx
        have hx_erase :
            x ∈ ({1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418} : Finset ℕ).erase 418 := by
          refine Finset.mem_erase.mpr ?_
          constructor
          · intro hx418
            subst x
            exact h418 hx
          · exact hx836
        rw [hErase418] at hx_erase
        exact hx_erase
      have hsum_le : S.sum id ≤ midDivs.sum id :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_mid (fun _ _ _ => Nat.zero_le _)
      have hmid_sum : midDivs.sum id = 426 := by
        decide
      omega
    let T : Finset ℕ := S.erase 418
    have hTsum : T.sum id = 418 := by
      have hrewrite : S.sum id = 418 + T.sum id := by
        calc
          S.sum id = (insert 418 T).sum id := by
            rw [show insert 418 T = S by
              unfold T
              rw [Finset.insert_erase h418]]
          _ = 418 + T.sum id := by
            rw [Finset.sum_insert]
            · simp [T]
            · simp [T]
      rw [hrewrite] at hSsum
      omega
    have h209 : 209 ∈ T := by
      by_contra h209
      have hsub_small : T ⊆ smallDivs := by
        intro x hx
        have hxNe418 : x ≠ 418 := by
          unfold T at hx
          exact (Finset.mem_erase.mp hx).1
        have hxS : x ∈ S := by
          unfold T at hx
          exact Finset.mem_of_mem_erase hx
        have hx836 : x ∈ ({1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418} : Finset ℕ) := hSsub hxS
        have hx_mid : x ∈ midDivs := by
          have hx_erase :
              x ∈ ({1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418} : Finset ℕ).erase 418 := by
            exact Finset.mem_erase.mpr ⟨hxNe418, hx836⟩
          rw [hErase418] at hx_erase
          exact hx_erase
        have hx_erase : x ∈ midDivs.erase 209 := by
          refine Finset.mem_erase.mpr ?_
          constructor
          · intro hx209
            subst x
            exact h209 hx
          · exact hx_mid
        rw [hErase209] at hx_erase
        exact hx_erase
      have hsum_le : T.sum id ≤ smallDivs.sum id :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_small (fun _ _ _ => Nat.zero_le _)
      have hsmall_sum : smallDivs.sum id = 217 := by
        decide
      omega
    let U : Finset ℕ := T.erase 209
    have hUsub : U ⊆ smallDivs := by
      intro x hx
      have hxNe418 : x ≠ 418 := by
        have hxT : x ∈ T := by
          unfold U at hx
          exact Finset.mem_of_mem_erase hx
        unfold T at hxT
        exact (Finset.mem_erase.mp hxT).1
      have hxT : x ∈ T := by
        unfold U at hx
        exact Finset.mem_of_mem_erase hx
      have hx_mid : x ∈ midDivs := by
        have hxS : x ∈ S := Finset.mem_of_mem_erase hxT
        have hx836 : x ∈ ({1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418} : Finset ℕ) := hSsub hxS
        have hx_erase :
            x ∈ ({1, 2, 4, 11, 19, 22, 38, 44, 76, 209, 418} : Finset ℕ).erase 418 := by
          exact Finset.mem_erase.mpr ⟨hxNe418, hx836⟩
        rw [hErase418] at hx_erase
        exact hx_erase
      have hx_erase : x ∈ midDivs.erase 209 := by
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hx_mid⟩
      rw [hErase209] at hx_erase
      exact hx_erase
    have hUsum : U.sum id = 209 := by
      have hrewrite : T.sum id = 209 + U.sum id := by
        calc
          T.sum id = (insert 209 U).sum id := by
            rw [show insert 209 U = T by
              unfold U
              rw [Finset.insert_erase h209]]
          _ = 209 + U.sum id := by
            rw [Finset.sum_insert]
            · simp [U]
            · simp [U]
      rw [hrewrite] at hTsum
      omega
    have hcompl : (smallDivs \ U).sum id = 8 := by
      have hsmall_sum : smallDivs.sum id = 217 := by
        decide
      have hsplit : (smallDivs \ U).sum id + U.sum id = smallDivs.sum id := by
        simpa using (Finset.sum_sdiff hUsub (f := id))
      rw [hsmall_sum, hUsum] at hsplit
      omega
    have hcompl_sub : smallDivs \ U ⊆ smallDivs := by
      intro x hx
      exact (Finset.mem_sdiff.mp hx).1
    exact no_subset_sum_eight_836_smallDivisors (smallDivs \ U) hcompl_sub hcompl

/-- **836 is a primitive weird number.** -/
theorem primitive_weird_836 : PrimitiveWeird 836 := by
  refine ⟨weird_836, ?_⟩
  intro d hd
  rw [properDivisors_eightthreeSix] at hd
  have hcases :
      d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 11 ∨ d = 19 ∨ d = 22 ∨ d = 38 ∨ d = 44 ∨ d = 76 ∨
        d = 209 ∨ d = 418 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hd
  have hna : ¬Abundant d := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  exact fun hw => hna hw.1

/-! ### The next two weird numbers: 4030 and 5830.

These continue OEIS A006037 (weird numbers): `70, 836, 4030, 5830, 7192, …`.
Both have the convenient feature that their abundance equals exactly `4`:
the proper divisors sum to `n + 4`, so any subset of proper divisors summing
to `n` must have a *complementary* subset summing to `4`.  Since the only
proper divisors of either number that are `≤ 4` are `1` and `2`, and the
empty / singleton / pair sums from `{1, 2}` are `0`, `1`, `2`, `3` — none of
which equal `4` — no such complementary subset exists.

The proofs follow the same skeleton as `seventy_is_weird` / `weird_836`,
but the complement-sum technique replaces the chain of nested erasures,
because the abundance is small enough that the complement contains at
most `{1, 2}`.

We use `native_decide` for the proper-divisor enumeration and abundance
bound: each is a finite, deterministic computation on a fixed `n`, well
within the spirit of the project's standards. -/

set_option linter.style.nativeDecide false in
/-- The proper divisors of `4030 = 2·5·13·31` are exactly the listed `15`
values. Verified by `native_decide` (a single finite computation; the
kernel-only `decide` exhausts recursion depth on this size). -/
private theorem properDivisors_4030 :
    (4030 : ℕ).properDivisors =
      ({1, 2, 5, 10, 13, 26, 31, 62, 65, 130, 155, 310, 403, 806, 2015}
        : Finset ℕ) := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The proper divisors of `5830 = 2·5·11·53` are exactly the listed `15`
values. Verified by `native_decide`. -/
private theorem properDivisors_5830 :
    (5830 : ℕ).properDivisors =
      ({1, 2, 5, 10, 11, 22, 53, 55, 106, 110, 265, 530, 583, 1166, 2915}
        : Finset ℕ) := by
  native_decide

/-- No subset of the proper divisors of `4030` sums to `4`: any divisor
other than `1` or `2` is at least `5`, and `{1} + {2} = 3 < 4`. -/
private theorem no_subset_sum_four_4030 :
    ∀ S ⊆ (4030 : ℕ).properDivisors, S.sum id ≠ 4 := by
  intro S hS hsum
  -- Any element of S is in properDivisors 4030, hence either 1, 2, or ≥ 5.
  -- We force S ⊆ {1, 2}.
  let tiny : Finset ℕ := ({1, 2} : Finset ℕ)
  have hsub_tiny : S ⊆ tiny := by
    intro x hx
    have hxle : x ≤ S.sum id := by
      simpa using Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hx
    have hxd : x ∈ (4030 : ℕ).properDivisors := hS hx
    rw [properDivisors_4030] at hxd
    have hxle4 : x ≤ 4 := by omega
    -- Enumerate possibilities.
    have hxcase : x = 1 ∨ x = 2 := by
      interval_cases x <;> simp at hxd <;> simp
    rcases hxcase with rfl | rfl <;> simp [tiny]
  have hsum_le : S.sum id ≤ tiny.sum id :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub_tiny (fun _ _ _ => Nat.zero_le _)
  have htiny : tiny.sum id = 3 := by decide
  omega

/-- No subset of the proper divisors of `5830` sums to `4`. Same argument:
the only proper divisors `≤ 4` are `1` and `2`. -/
private theorem no_subset_sum_four_5830 :
    ∀ S ⊆ (5830 : ℕ).properDivisors, S.sum id ≠ 4 := by
  intro S hS hsum
  let tiny : Finset ℕ := ({1, 2} : Finset ℕ)
  have hsub_tiny : S ⊆ tiny := by
    intro x hx
    have hxle : x ≤ S.sum id := by
      simpa using Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hx
    have hxd : x ∈ (5830 : ℕ).properDivisors := hS hx
    rw [properDivisors_5830] at hxd
    have hxle4 : x ≤ 4 := by omega
    have hxcase : x = 1 ∨ x = 2 := by
      interval_cases x <;> simp at hxd <;> simp
    rcases hxcase with rfl | rfl <;> simp [tiny]
  have hsum_le : S.sum id ≤ tiny.sum id :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub_tiny (fun _ _ _ => Nat.zero_le _)
  have htiny : tiny.sum id = 3 := by decide
  omega

/-- **4030 is the third-smallest weird number** (OEIS A006037).

Strategy: the `15` proper divisors of `4030 = 2·5·13·31` sum to `4034`, so
`4030` is abundant (with abundance exactly `4`). If a subset `S` of proper
divisors summed to `4030`, then its complement (within the proper-divisor
set) would sum to `4034 − 4030 = 4`. But `no_subset_sum_four_4030` shows
no such subset exists. -/
theorem weird_4030 : Weird 4030 := by
  have hD_sum : (4030 : ℕ).properDivisors.sum id = 4034 := by
    rw [properDivisors_4030]; decide
  constructor
  · exact ⟨by positivity, by rw [hD_sum]; omega⟩
  · rintro ⟨S, hSsub, hSsum⟩
    rw [Finset.mem_powerset] at hSsub
    -- The complement of S in properDivisors 4030 sums to 4.
    set D : Finset ℕ := (4030 : ℕ).properDivisors with hD
    have hsplit : (D \ S).sum id + S.sum id = D.sum id :=
      Finset.sum_sdiff hSsub (f := id)
    have hcompl_sum : (D \ S).sum id = 4 := by
      rw [hD_sum] at hsplit; omega
    have hcompl_sub : D \ S ⊆ D := Finset.sdiff_subset
    exact no_subset_sum_four_4030 (D \ S) hcompl_sub hcompl_sum

/-- **5830 is the fourth-smallest weird number** (OEIS A006037).

Strategy: identical to `weird_4030`. The `15` proper divisors of
`5830 = 2·5·11·53` sum to `5834`; any subset summing to `5830` would force
the complement (also a subset of the proper divisors) to sum to `4`,
which is impossible since only `1` and `2` are ≤ `4`. -/
theorem weird_5830 : Weird 5830 := by
  have hD_sum : (5830 : ℕ).properDivisors.sum id = 5834 := by
    rw [properDivisors_5830]; decide
  constructor
  · exact ⟨by positivity, by rw [hD_sum]; omega⟩
  · rintro ⟨S, hSsub, hSsum⟩
    rw [Finset.mem_powerset] at hSsub
    set D : Finset ℕ := (5830 : ℕ).properDivisors with hD
    have hsplit : (D \ S).sum id + S.sum id = D.sum id :=
      Finset.sum_sdiff hSsub (f := id)
    have hcompl_sum : (D \ S).sum id = 4 := by
      rw [hD_sum] at hsplit; omega
    have hcompl_sub : D \ S ⊆ D := Finset.sdiff_subset
    exact no_subset_sum_four_5830 (D \ S) hcompl_sub hcompl_sum

end WeirdNumbers
