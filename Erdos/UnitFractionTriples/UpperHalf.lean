/-
# Upper Half is Triple-Free

Key structural result for Erdős Problem 302: the set (N/2, N] ∩ ℕ
contains no unit fraction triple 1/a = 1/b + 1/c with distinct a, b, c.

The proof hinges on an elegant algebraic identity: if a*(b+c) = b*c
with a < b and a < c, then (b−a)*(c−a) = a². This forces a ≤ N−a
(since b−a, c−a ≥ 1 and both ≤ N−a), i.e., a ≤ N/2, contradicting
a ∈ (N/2, N].
-/
import Erdos.UnitFractionTriples.Statement

namespace UnitFractionTriples

/-- **Factor identity for unit fraction triples.**
    If a*(b+c) = b*c (the divisibility form of 1/a = 1/b + 1/c) and
    a < b, a < c, then (b−a)*(c−a) = a².

    Proof: expand (b−a)(c−a) = bc − a(b+c) + a² = bc − bc + a² = a².
    We work in ℤ to avoid subtraction issues in ℕ. -/
theorem triple_factor_identity {a b c : ℕ} (_ha : 0 < a) (hab : a < b) (hac : a < c)
    (h : a * (b + c) = b * c) : (b - a) * (c - a) = a ^ 2 := by
  -- Work in ℤ where subtraction is well-behaved
  zify [show a ≤ b by omega, show a ≤ c by omega] at h ⊢
  nlinarith

/-- If a, b, c ∈ (N/2, N] form a unit fraction triple, then a ≤ N/2 —
    contradicting the membership hypothesis. This is the core of the
    upper-half-is-triple-free argument.

    From (b−a)*(c−a) = a² and b, c ≤ N we get a² ≤ (N−a)², so a ≤ N−a,
    i.e., 2a ≤ N. -/
theorem triple_forces_small {a b c N : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (_hbc : b ≠ c)
    (hbN : b ≤ N) (hcN : c ≤ N)
    (htrip : IsUnitFractionTriple a b c) : a * 2 ≤ N := by
  obtain ⟨_, _, _, hq⟩ := htrip
  have ⟨hab', hac'⟩ := triple_lt ha hb hc hab hac hq
  rw [triple_iff_div ha hb hc] at hq
  have hfact := triple_factor_identity ha hab' hac' hq
  -- (b-a)*(c-a) = a², with b-a ≤ N-a and c-a ≤ N-a (since b,c ≤ N)
  -- So a² ≤ (N-a)², hence a ≤ N-a, i.e., 2a ≤ N
  have hba : b - a ≤ N - a := Nat.sub_le_sub_right hbN a
  have hca : c - a ≤ N - a := Nat.sub_le_sub_right hcN a
  -- a² = (b-a)*(c-a) ≤ (N-a)*(N-a) = (N-a)²
  have hsq : a ^ 2 ≤ (N - a) ^ 2 := by
    rw [← hfact, sq]; exact Nat.mul_le_mul hba hca
  -- From a² ≤ (N-a)²: a ≤ N-a, so 2a ≤ N
  -- Use nlinarith in ℤ to handle the power reasoning
  zify [show a ≤ N by omega, show a ≤ b by omega, show a ≤ c by omega] at hsq hfact ⊢
  nlinarith [sq_nonneg ((a : ℤ) - (↑N - ↑a))]

/-- **The upper half (N/2, N] is triple-free.**

    For any N, the set {N/2 + 1, N/2 + 2, …, N} contains no distinct
    a, b, c with 1/a = 1/b + 1/c.

    This gives a lower bound f(N) ≥ ⌊N/2⌋ for Erdős Problem 302. -/
theorem upper_half_triple_free (N : ℕ) :
    TripleFree (Finset.Icc (N / 2 + 1) N) := by
  intro a ha b hb c hc hab hac hbc htrip
  simp only [Finset.mem_Icc] at ha hb hc
  have hapos : 0 < a := by omega
  have hbpos : 0 < b := by omega
  have hcpos : 0 < c := by omega
  have h2a := triple_forces_small hapos hbpos hcpos hab hac hbc hb.2 hc.2 htrip
  omega

end UnitFractionTriples
