/-
# Cambie's 5/8 Construction

Stijn Cambie observed that the set of odd integers in {1, …, ⌊N/4⌋}
together with all integers in {⌊N/2⌋+1, …, N} is triple-free,
giving f(N) ≥ (5/8 + o(1))N for Erdős Problem 302.

The proof uses three ingredients:
1. The upper half is triple-free (from UpperHalf.lean)
2. Odd numbers are triple-free (parity argument)
3. Cross-terms are impossible (magnitude + parity)
-/
import Erdos.UnitFractionTriples.UpperHalf

namespace UnitFractionTriples

/-- **Parity obstruction for triples.**
    If a and b are both odd positive integers, then the equation
    a * (b + c) = b * c has no solution with c a positive integer.

    Proof: if c is odd then b + c is even, so a*(b+c) is even, but
    b*c = odd*odd = odd — contradiction. If c is even then b + c is
    odd, so a*(b+c) = odd*odd = odd, but b*c = odd*even = even. -/
theorem no_triple_both_odd {a b c : ℕ} (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (haodd : ¬Even a) (hbodd : ¬Even b)
    (h : a * (b + c) = b * c) : False := by
  rw [Nat.not_even_iff_odd] at haodd hbodd
  by_cases hc : Even c
  · -- c even, b odd ⟹ b+c odd ⟹ a*(b+c) odd (odd*odd). But b*c even (odd*even).
    obtain ⟨k, hk⟩ := Odd.mul haodd (Odd.add_even hbodd hc)
    obtain ⟨j, hj⟩ := Even.mul_left hc b
    omega
  · -- c odd, b odd ⟹ b+c even ⟹ a*(b+c) even. But b*c odd (odd*odd).
    rw [Nat.not_even_iff_odd] at hc
    have heven : Even (a * (b + c)) := (Odd.add_odd hbodd hc).mul_left a
    obtain ⟨k, hk⟩ := heven
    obtain ⟨j, hj⟩ := Odd.mul hbodd hc
    omega

/-- **Odd numbers are triple-free.**

    No three distinct odd positive integers a, b, c satisfy
    1/a = 1/b + 1/c. The obstruction is parity: the equation
    a*(b+c) = b*c forces one side to be even and the other odd. -/
theorem odd_numbers_triple_free (N : ℕ) :
    TripleFree (Finset.filter (fun n => ¬Even n) (Finset.Icc 1 N)) := by
  intro a ha b hb c hc hab hac hbc htrip
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb hc
  obtain ⟨hapos, hbpos, hcpos, hq⟩ := htrip
  rw [triple_iff_div hapos hbpos hcpos] at hq
  exact no_triple_both_odd hapos hbpos hcpos ha.2 hb.2 hq

/-- The Cambie set: odd numbers in {1, …, ⌊N/4⌋} together with
    all numbers in {⌊N/2⌋+1, …, N}. -/
def cambieSet (N : ℕ) : Finset ℕ :=
  Finset.filter (fun n => ¬Even n) (Finset.Icc 1 (N / 4)) ∪
  Finset.Icc (N / 2 + 1) N

/-- **Cross-term elimination**: if a ≤ N/4 and b ≥ N/2 + 1, then
    b ≥ 2a + 1, so b - a ≥ a + 1. Combined with the factor identity
    (b-a)*(c-a) = a², this makes cross-term triples impossible. -/
private theorem cross_term_impossible {a b c N : ℕ}
    (ha : 0 < a) (haN : a ≤ N / 4)
    (hb : N / 2 + 1 ≤ b) (hc : N / 2 + 1 ≤ c)
    (hab : a < b) (hac : a < c)
    (h : a * (b + c) = b * c) : False := by
  have hfact := triple_factor_identity ha hab hac h
  -- b ≥ N/2 + 1 ≥ 2*(N/4) + 1 ≥ 2a + 1, so b - a ≥ a + 1
  have hba : a + 1 ≤ b - a := by omega
  have hca : a + 1 ≤ c - a := by omega
  -- (b-a)*(c-a) ≥ (a+1)² > a²
  have hsq : (a + 1) ^ 2 ≤ (b - a) * (c - a) := by
    calc (a + 1) ^ 2 = (a + 1) * (a + 1) := by ring
    _ ≤ (b - a) * (c - a) := Nat.mul_le_mul hba hca
  linarith

/-- **Cambie's construction is triple-free.**

    The set of odd numbers in {1, …, ⌊N/4⌋} together with all
    numbers in {⌊N/2⌋+1, …, N} contains no unit fraction triple.

    Proof cases:
    - All three in upper half: handled by `upper_half_triple_free`
    - a in odd part, b and c in upper half: cross-term (magnitude)
    - a and one of b,c in odd part: parity kills it
    - a in upper half: forces b, c > a > N/2, all in upper half -/
theorem cambie_triple_free (N : ℕ) : TripleFree (cambieSet N) := by
  intro a ha b hb c hc hab hac hbc htrip
  simp only [cambieSet, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at ha hb hc
  obtain ⟨hapos, hbpos, hcpos, hq⟩ := htrip
  have ⟨hab', hac'⟩ := triple_lt hapos hbpos hcpos hab hac hq
  rw [triple_iff_div hapos hbpos hcpos] at hq
  -- Case split on where a is
  rcases ha with ⟨⟨_, haN4⟩, haodd⟩ | ⟨haN2, _⟩
  · -- a is odd, in [1, N/4]
    rcases hb with ⟨⟨_, _⟩, hbodd⟩ | ⟨hbN2, _⟩
    · -- b is also odd in [1, N/4]: parity kills it regardless of c
      exact no_triple_both_odd hapos hbpos hcpos haodd hbodd hq
    · -- b in upper half [N/2+1, N]
      rcases hc with ⟨⟨_, _⟩, hcodd⟩ | ⟨hcN2, _⟩
      · -- c is odd: use symmetry of the equation
        -- a*(b+c) = b*c ⟹ a*(c+b) = c*b, and a, c are both odd
        have hq' : a * (c + b) = c * b := by linarith
        exact no_triple_both_odd hapos hcpos hbpos haodd hcodd hq'
      · -- b and c both in upper half: cross-term impossible
        exact cross_term_impossible hapos haN4 hbN2 hcN2 hab' hac' hq
  · -- a in upper half [N/2+1, N]: b > a > N/2 and c > a > N/2
    -- Both b and c must be in the upper half (can't be ≤ N/4 < N/2 < a)
    have hbN2 : N / 2 + 1 ≤ b := by
      rcases hb with ⟨⟨_, hbN4⟩, _⟩ | ⟨h, _⟩ <;> omega
    have hcN2 : N / 2 + 1 ≤ c := by
      rcases hc with ⟨⟨_, hcN4⟩, _⟩ | ⟨h, _⟩ <;> omega
    have hbN : b ≤ N := by
      rcases hb with ⟨⟨_, h⟩, _⟩ | ⟨_, h⟩ <;> omega
    have hcN : c ≤ N := by
      rcases hc with ⟨⟨_, h⟩, _⟩ | ⟨_, h⟩ <;> omega
    -- All three in upper half: use upper_half_triple_free
    exact upper_half_triple_free N a (Finset.mem_Icc.mpr ⟨haN2, by omega⟩)
      b (Finset.mem_Icc.mpr ⟨hbN2, hbN⟩)
      c (Finset.mem_Icc.mpr ⟨hcN2, hcN⟩)
      hab hac hbc ⟨hapos, hbpos, hcpos, (triple_iff_div hapos hbpos hcpos).mpr hq⟩

end UnitFractionTriples
