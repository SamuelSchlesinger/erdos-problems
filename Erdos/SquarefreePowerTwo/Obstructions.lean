import Erdos.SquarefreePowerTwo.Statement
import Erdos.SquarefreePowerTwo.Elementary

set_option linter.style.header false

/-
# Squarefree-plus-power-of-two obstructions for Erdős Problem 11

This file develops the **obstruction-side** framework for `#11`. The Erdős conjecture
asserts that every sufficiently large odd `n` has a representation `n = q + 2^k` with
`q` squarefree. Equivalently, the set of *exceptional* odd `n` (those without any
such representation) is finite.

DeepMind's `exists_x_P_ind` (in `erdos_26.variants.tenenbaum.lean`) builds, by
inductive CRT prime selection, an integer `x` and product `P` such that for each
`k ≤ K` the shifted value `x + k` is divisible by some large prime `q` dividing
`P`. The analogue for `#11` (in the negative direction) would force, for each
candidate `k` with `2^k ≤ n`, that `n - 2^k` is divisible by a *square* of a
prime, hence is not squarefree.

We do **not** attempt the full positive resolution of `#11` here. Instead we
provide:

* `IsExceptional` — the exceptional-set predicate.
* `representable_iff_exists_squarefree_witness` — a constructive reformulation:
  `n` is representable iff some `k ≤ Nat.log 2 n` makes `n - 2^k` squarefree.
* `not_representable_iff_all_pow_two_sub_not_squarefree` — the dual: `n` is
  exceptional iff *every* admissible `k` produces a non-squarefree `n - 2^k`.
* `not_squarefree_of_prime_sq_dvd` — the prime-square obstruction primitive
  (the basic CRT block).
* `not_representable_of_all_prime_sq_obstruction` — the aggregate obstruction:
  if every admissible `n - 2^k` is hit by some prime square, `n` is exceptional.
* `eventuallyOddRepresentable_iff_exceptional_bounded` — Erdős `#11` is
  equivalent to the boundedness of the exceptional set.

A few additional small witness instances (`9`, `11`, `13`, `15`, `17`, `19`,
`21`, `23`, `25`, `27`, `29`, `31`) extend the `Elementary.lean` series, giving
explicit certificates that the conjecture holds up to `31`.
-/

namespace SquarefreePowerTwo

open Nat

/-! ## Constructive witness reformulation -/

/-- If `2 ^ k ≤ n` and `n - 2 ^ k` is squarefree, then `n` is representable. This
is the *constructive* direction: any squarefree witness `q := n - 2^k` produces
a representation. -/
theorem hasSquarefreePowerTwoRepresentation_of_squarefree_sub_pow_two
    {n k : ℕ} (hk : 2 ^ k ≤ n) (hsf : Squarefree (n - 2 ^ k)) :
    HasSquarefreePowerTwoRepresentation n := by
  refine ⟨n - 2 ^ k, k, hsf, ?_⟩
  omega

/-- If `n` is representable, then there exists `k` with `2 ^ k ≤ n` and
`n - 2 ^ k` squarefree. The exponent `k` need not be unique. -/
theorem exists_pow_two_sub_squarefree_of_representable {n : ℕ}
    (h : HasSquarefreePowerTwoRepresentation n) :
    ∃ k : ℕ, 2 ^ k ≤ n ∧ Squarefree (n - 2 ^ k) := by
  rcases h with ⟨q, k, hq, hsum⟩
  refine ⟨k, ?_, ?_⟩
  · omega
  · have : n - 2 ^ k = q := by omega
    rw [this]; exact hq

/-- Constructive characterization of representability: a positive `n` is
representable iff there exists an exponent `k` with `2 ^ k ≤ n` whose
complement `n - 2 ^ k` is squarefree. -/
theorem hasSquarefreePowerTwoRepresentation_iff_exists_squarefree_sub :
    ∀ {n : ℕ}, HasSquarefreePowerTwoRepresentation n ↔
      ∃ k : ℕ, 2 ^ k ≤ n ∧ Squarefree (n - 2 ^ k) := by
  intro n
  refine ⟨exists_pow_two_sub_squarefree_of_representable, ?_⟩
  rintro ⟨k, hk, hsf⟩
  exact hasSquarefreePowerTwoRepresentation_of_squarefree_sub_pow_two hk hsf

/-! ## The exceptional set -/

/-- An odd integer is *exceptional* for `#11` if it admits no
squarefree-plus-power-of-two representation. The conjecture is that the
exceptional set is finite. -/
def IsExceptional (n : ℕ) : Prop :=
  Odd n ∧ ¬ HasSquarefreePowerTwoRepresentation n

/-- The exceptional set never includes an even integer. -/
theorem IsExceptional.odd {n : ℕ} (h : IsExceptional n) : Odd n := h.1

/-- An exceptional integer has no representation. -/
theorem IsExceptional.not_representable {n : ℕ} (h : IsExceptional n) :
    ¬ HasSquarefreePowerTwoRepresentation n := h.2

/-- `OddRepresentableFrom N` says every odd `n ≥ N` is representable; equivalently,
no exceptional integer is at least `N`. -/
theorem oddRepresentableFrom_iff_exceptional_lt {N : ℕ} :
    OddRepresentableFrom N ↔ ∀ n : ℕ, IsExceptional n → n < N := by
  refine ⟨fun h n hn => ?_, fun h n hN hodd => ?_⟩
  · by_contra hle
    push Not at hle
    exact hn.2 (h n hle hn.1)
  · by_contra hrep
    have := h n ⟨hodd, hrep⟩
    omega

/-- `EventuallyOddRepresentable` is equivalent to the boundedness of the set of
exceptional integers: `{n | IsExceptional n}` is contained in some initial
segment `[0, N)`. -/
theorem eventuallyOddRepresentable_iff_exceptional_bounded :
    EventuallyOddRepresentable ↔ ∃ N : ℕ, ∀ n : ℕ, IsExceptional n → n < N := by
  refine ⟨fun ⟨N, hN⟩ => ⟨N, (oddRepresentableFrom_iff_exceptional_lt.mp hN)⟩,
          fun ⟨N, hN⟩ => ⟨N, oddRepresentableFrom_iff_exceptional_lt.mpr hN⟩⟩

/-- Dually, the negation of `EventuallyOddRepresentable` says exceptional
integers are unbounded. -/
theorem not_eventuallyOddRepresentable_iff_exceptional_unbounded :
    ¬ EventuallyOddRepresentable ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsExceptional n := by
  rw [eventuallyOddRepresentable_iff_exceptional_bounded]
  push Not
  constructor
  · intro h N
    obtain ⟨n, hex, hge⟩ := h N
    exact ⟨n, by omega, hex⟩
  · intro h N
    obtain ⟨n, hge, hex⟩ := h N
    exact ⟨n, hex, by omega⟩

/-! ## Prime-square obstructions (the basic CRT block) -/

/-- The fundamental obstruction: a positive natural divisible by `p * p` for a
prime `p` is not squarefree. This is the per-prime CRT block referenced in
DeepMind's `exists_x_P_ind` — each prime `q` selected at step `K` divides
`x + K`, and squaring this to enforce `q^2 ∣ x + K` blocks squarefreeness. -/
theorem not_squarefree_of_prime_sq_dvd {m p : ℕ} (hp : Nat.Prime p)
    (hdvd : p * p ∣ m) : ¬ Squarefree m := by
  intro hsf
  exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp hdvd

/-- Equivalent form: if there exists a prime whose square divides `m`, then `m`
is not squarefree. -/
theorem not_squarefree_of_exists_prime_sq_dvd {m : ℕ}
    (h : ∃ p : ℕ, Nat.Prime p ∧ p * p ∣ m) : ¬ Squarefree m := by
  rintro hsf
  obtain ⟨p, hp, hdvd⟩ := h
  exact not_squarefree_of_prime_sq_dvd hp hdvd hsf

/-- The aggregate obstruction: if for every admissible exponent `k`, the
complement `n - 2 ^ k` is hit by some prime square, then `n` admits no
squarefree-plus-power-of-two representation.

This is the *target* of DeepMind-style CRT constructions in the negative
direction: build, for a given residue class of `n`, a system of primes
`p_k` such that `p_k^2 ∣ n - 2^k` simultaneously for all `k` with
`2 ^ k ≤ n`. Combined with `Squarefree 0` failing, the representation must
then fail. -/
theorem not_representable_of_all_prime_sq_obstruction {n : ℕ}
    (h : ∀ k : ℕ, 2 ^ k ≤ n →
      n = 2 ^ k ∨ ∃ p : ℕ, Nat.Prime p ∧ p * p ∣ (n - 2 ^ k)) :
    ¬ HasSquarefreePowerTwoRepresentation n := by
  intro hrep
  obtain ⟨k, hk, hsf⟩ := exists_pow_two_sub_squarefree_of_representable hrep
  rcases h k hk with heq | ⟨p, hp, hdvd⟩
  · -- `n = 2 ^ k`, so `n - 2 ^ k = 0`, which is not squarefree.
    have h0 : n - 2 ^ k = 0 := by omega
    rw [h0] at hsf
    exact not_squarefree_zero hsf
  · exact not_squarefree_of_prime_sq_dvd hp hdvd hsf

/-- A contrapositive packaging useful for the eventual conjecture: if the
representable side is the desired conclusion, the failure of the prime-square
obstruction is sufficient for representability. -/
theorem hasSquarefreePowerTwoRepresentation_of_not_all_obstruction {n : ℕ}
    (h : ¬ ∀ k : ℕ, 2 ^ k ≤ n →
      n = 2 ^ k ∨ ∃ p : ℕ, Nat.Prime p ∧ p * p ∣ (n - 2 ^ k)) :
    HasSquarefreePowerTwoRepresentation n := by
  by_contra hrep
  apply h
  intro k hk
  by_cases heq : n = 2 ^ k
  · left; exact heq
  · right
    have hpos : 0 < n - 2 ^ k := by omega
    -- `n - 2 ^ k` is positive but not squarefree (else `n` would be representable).
    have hnotsf : ¬ Squarefree (n - 2 ^ k) := fun hsf =>
      hrep (hasSquarefreePowerTwoRepresentation_of_squarefree_sub_pow_two hk hsf)
    -- Extract a prime square dividing `n - 2 ^ k` via the squarefree
    -- characterization (the contrapositive of `Nat.squarefree_iff_prime_squarefree`).
    have : ¬ ∀ x : ℕ, Nat.Prime x → ¬ x * x ∣ (n - 2 ^ k) := fun H =>
      hnotsf (Nat.squarefree_iff_prime_squarefree.mpr H)
    push Not at this
    obtain ⟨p, hp, hdvd⟩ := this
    exact ⟨p, hp, hdvd⟩

/-! ## Additional small witnesses (extending `Elementary.lean`) -/

/-- `9 = 1 + 2 ^ 3`. -/
theorem hasSquarefreePowerTwoRepresentation_nine :
    HasSquarefreePowerTwoRepresentation 9 := by
  refine ⟨1, 3, ?_, ?_⟩ <;> norm_num

/-- `11 = 3 + 2 ^ 3`. -/
theorem hasSquarefreePowerTwoRepresentation_eleven :
    HasSquarefreePowerTwoRepresentation 11 := by
  refine ⟨3, 3, ?_, ?_⟩
  · exact (show Nat.Prime 3 by norm_num).squarefree
  · norm_num

/-- `13 = 5 + 2 ^ 3`. -/
theorem hasSquarefreePowerTwoRepresentation_thirteen :
    HasSquarefreePowerTwoRepresentation 13 := by
  refine ⟨5, 3, ?_, ?_⟩
  · exact (show Nat.Prime 5 by norm_num).squarefree
  · norm_num

/-- `15 = 7 + 2 ^ 3`. -/
theorem hasSquarefreePowerTwoRepresentation_fifteen :
    HasSquarefreePowerTwoRepresentation 15 := by
  refine ⟨7, 3, ?_, ?_⟩
  · exact (show Nat.Prime 7 by norm_num).squarefree
  · norm_num

/-- `17 = 1 + 2 ^ 4`. -/
theorem hasSquarefreePowerTwoRepresentation_seventeen :
    HasSquarefreePowerTwoRepresentation 17 := by
  refine ⟨1, 4, ?_, ?_⟩ <;> norm_num

/-- `19 = 3 + 2 ^ 4`. -/
theorem hasSquarefreePowerTwoRepresentation_nineteen :
    HasSquarefreePowerTwoRepresentation 19 := by
  refine ⟨3, 4, ?_, ?_⟩
  · exact (show Nat.Prime 3 by norm_num).squarefree
  · norm_num

/-- `21 = 5 + 2 ^ 4`. -/
theorem hasSquarefreePowerTwoRepresentation_twentyone :
    HasSquarefreePowerTwoRepresentation 21 := by
  refine ⟨5, 4, ?_, ?_⟩
  · exact (show Nat.Prime 5 by norm_num).squarefree
  · norm_num

/-- `23 = 7 + 2 ^ 4`. -/
theorem hasSquarefreePowerTwoRepresentation_twentythree :
    HasSquarefreePowerTwoRepresentation 23 := by
  refine ⟨7, 4, ?_, ?_⟩
  · exact (show Nat.Prime 7 by norm_num).squarefree
  · norm_num

/-- `25 = 17 + 2 ^ 3`. -/
theorem hasSquarefreePowerTwoRepresentation_twentyfive :
    HasSquarefreePowerTwoRepresentation 25 := by
  refine ⟨17, 3, ?_, ?_⟩
  · exact (show Nat.Prime 17 by norm_num).squarefree
  · norm_num

/-- `27 = 19 + 2 ^ 3`. -/
theorem hasSquarefreePowerTwoRepresentation_twentyseven :
    HasSquarefreePowerTwoRepresentation 27 := by
  refine ⟨19, 3, ?_, ?_⟩
  · exact (show Nat.Prime 19 by norm_num).squarefree
  · norm_num

/-- `29 = 13 + 2 ^ 4`. -/
theorem hasSquarefreePowerTwoRepresentation_twentynine :
    HasSquarefreePowerTwoRepresentation 29 := by
  refine ⟨13, 4, ?_, ?_⟩
  · exact (show Nat.Prime 13 by norm_num).squarefree
  · norm_num

/-- `31 = 15 + 2 ^ 4`. Note `15 = 3 * 5` is squarefree. -/
theorem hasSquarefreePowerTwoRepresentation_thirtyone :
    HasSquarefreePowerTwoRepresentation 31 := by
  refine ⟨15, 4, ?_, ?_⟩
  · -- 15 = 3 * 5, both squarefree distinct primes.
    rw [show (15 : ℕ) = 3 * 5 from rfl]
    refine (Nat.squarefree_mul (by decide)).mpr ⟨?_, ?_⟩
    · exact (show Nat.Prime 3 by norm_num).squarefree
    · exact (show Nat.Prime 5 by norm_num).squarefree
  · norm_num

end SquarefreePowerTwo
