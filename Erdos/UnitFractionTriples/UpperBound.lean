/-
# Upper Bound on Triple-Free Sets

For every k coprime to 6, the triple (2k, 3k, 6k) satisfies
  1/(2k) = 1/(3k) + 1/(6k).
These triples are pairwise disjoint for distinct k, so any triple-free
subset of {1, …, N} must exclude at least one element from each,
giving f₃₀₂(N) ≤ N − |{k ≤ N/6 : gcd(k,6) = 1}|.

Since the density of integers coprime to 6 is φ(6)/6 = 1/3, this
yields f₃₀₂(N) ≤ (17/18 + o(1))N.
-/
import Erdos.UnitFractionTriples.Statement

namespace UnitFractionTriples

/-! ### The (2k, 3k, 6k) family -/

/-- The triple (2k, 3k, 6k) is a unit fraction triple for all k ≥ 1:
    1/(2k) = 1/(3k) + 1/(6k), equivalently 2k·(3k + 6k) = 2k·9k = 18k² = 3k·6k. -/
theorem triple_2k_3k_6k (k : ℕ) (hk : 0 < k) : IsUnitFractionTriple (2 * k) (3 * k) (6 * k) := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [triple_iff_div (by omega) (by omega) (by omega)]
  ring

/-- A triple-free set cannot contain all three of 2k, 3k, 6k (for k ≥ 1). -/
theorem triple_free_excludes_one {A : Finset ℕ} (hA : TripleFree A) {k : ℕ}
    (hk : 0 < k) (h2 : 2 * k ∈ A) (h3 : 3 * k ∈ A) (h6 : 6 * k ∈ A) : False := by
  exact hA (2 * k) h2 (3 * k) h3 (6 * k) h6 (by omega) (by omega) (by omega)
    (triple_2k_3k_6k k hk)

/-! ### Disjointness of triples for distinct k coprime to 6 -/

/-- If k is coprime to 6 and 2k = 3m, then False: 3 ∣ 2k means 3 ∣ k
    (since gcd(2,3)=1), contradicting gcd(k,6)=1. -/
private theorem two_ne_three_coprime6 {k m : ℕ} (hk : Nat.Coprime k 6)
    (h : 2 * k = 3 * m) : False := by
  have h3 : 3 ∣ 2 * k := ⟨m, by omega⟩
  have : ¬(3 ∣ k) := by
    intro ⟨j, hj⟩
    have : 3 ∣ Nat.gcd k 6 := Nat.dvd_gcd ⟨j, hj⟩ ⟨2, by ring⟩
    rw [hk] at this; omega
  have : 3 ∣ k := by
    have := (Nat.Prime.dvd_mul Nat.prime_three).mp h3
    rcases this with h | h
    · omega
    · exact h
  contradiction

/-- If k is coprime to 6 and 2k = 6m, then False: 3 ∣ 2k. -/
private theorem two_ne_six_coprime6 {k m : ℕ} (hk : Nat.Coprime k 6)
    (h : 2 * k = 6 * m) : False :=
  two_ne_three_coprime6 hk (show 2 * k = 3 * (2 * m) by omega)

/-- If k is coprime to 6 and 3k = 2m, then False: 2 ∣ 3k means 2 ∣ k. -/
private theorem three_ne_two_coprime6 {k m : ℕ} (hk : Nat.Coprime k 6)
    (h : 3 * k = 2 * m) : False := by
  have h2 : 2 ∣ 3 * k := ⟨m, by omega⟩
  have : ¬(2 ∣ k) := by
    intro ⟨j, hj⟩
    have : 2 ∣ Nat.gcd k 6 := Nat.dvd_gcd ⟨j, hj⟩ ⟨3, by ring⟩
    rw [hk] at this; omega
  have : 2 ∣ k := by
    have := (Nat.Prime.dvd_mul Nat.prime_two).mp h2
    rcases this with h | h
    · omega
    · exact h
  contradiction

/-- If k is coprime to 6 and 3k = 6m, then k = 2m, contradicting 2 ∤ k. -/
private theorem three_ne_six_coprime6 {k m : ℕ} (hk : Nat.Coprime k 6)
    (h : 3 * k = 6 * m) : False :=
  three_ne_two_coprime6 hk (show 3 * k = 2 * (3 * m) by omega)

/-- If k is coprime to 6 and 6k = 2m, then m = 3k, so 3 ∣ m.
    But we use the *other* coprimality: 6k₁ = 2k₂ means k₂ = 3k₁,
    so 3 ∣ k₂, contradicting gcd(k₂, 6) = 1.
    Here we take the h2 : Nat.Coprime m 6 approach instead. -/
private theorem six_ne_two_coprime6 {k m : ℕ} (hm : Nat.Coprime m 6)
    (h : 6 * k = 2 * m) : False := by
  -- 6k = 2m means m = 3k, so 3 ∣ m
  have h3m : 3 ∣ m := ⟨k, by omega⟩
  have : 3 ∣ Nat.gcd m 6 := Nat.dvd_gcd h3m ⟨2, by ring⟩
  rw [hm] at this; omega

/-- If k is coprime to 6 and 6k = 3m, then m = 2k, so 2 ∣ m,
    contradicting gcd(m, 6) = 1. -/
private theorem six_ne_three_coprime6 {k m : ℕ} (hm : Nat.Coprime m 6)
    (h : 6 * k = 3 * m) : False := by
  have h2m : 2 ∣ m := ⟨k, by omega⟩
  have : 2 ∣ Nat.gcd m 6 := Nat.dvd_gcd h2m ⟨3, by ring⟩
  rw [hm] at this; omega

/-- For distinct k₁, k₂ both coprime to 6, the triples {2k₁, 3k₁, 6k₁} and
    {2k₂, 3k₂, 6k₂} are disjoint.

    We check all 9 cross-equalities. Same-multiplier equalities (2k₁ = 2k₂ etc.)
    give k₁ = k₂. Cross-multiplier equalities (2k₁ = 3k₂ etc.) contradict
    coprimality to 6. -/
theorem triples_disjoint_coprime6 {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂)
    (h1 : Nat.Coprime k₁ 6) (h2 : Nat.Coprime k₂ 6) :
    Disjoint ({2 * k₁, 3 * k₁, 6 * k₁} : Finset ℕ) {2 * k₂, 3 * k₂, 6 * k₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  -- x is one of {2k₁, 3k₁, 6k₁} and one of {2k₂, 3k₂, 6k₂}
  rcases hx₁ with rfl | rfl | rfl <;> rcases hx₂ with h | h | h
  -- 2k₁ vs {2k₂, 3k₂, 6k₂}
  · exact hne (by omega)
  · exact two_ne_three_coprime6 h1 (by omega)
  · exact two_ne_six_coprime6 h1 (by omega)
  -- 3k₁ vs {2k₂, 3k₂, 6k₂}
  · exact three_ne_two_coprime6 h1 (by omega)
  · exact hne (by omega)
  · exact three_ne_six_coprime6 h1 (by omega)
  -- 6k₁ vs {2k₂, 3k₂, 6k₂}
  · exact six_ne_two_coprime6 h2 (by omega)   -- note: h2 (coprimality of k₂)
  · exact six_ne_three_coprime6 h2 (by omega)  -- note: h2 (coprimality of k₂)
  · exact hne (by omega)

end UnitFractionTriples
