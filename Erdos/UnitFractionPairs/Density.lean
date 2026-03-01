/-
# Structural results for PairFree sets

The key result: (n, c·n) is a unit fraction pair iff (c+1) ∣ n.
This gives an infinite family of forbidden pair constraints for PairFree sets.
-/
import Erdos.UnitFractionPairs.Classification

namespace UnitFractionPairs

/-! ## General multiple characterization -/

/-- For any c ≥ 1 and n ≥ 1, (n, c·n) is a unit fraction pair iff (c+1) ∣ n.

    Proof: n + cn = (c+1)n and n · cn = cn². So (c+1)n ∣ cn²
    iff (c+1) ∣ cn iff (c+1) ∣ n (since gcd(c, c+1) = 1). -/
theorem pair_n_cn_iff {n c : ℕ} (hn : 0 < n) (hc : 0 < c) :
    IsUnitFractionPair n (c * n) ↔ (c + 1) ∣ n := by
  unfold IsUnitFractionPair
  constructor
  · intro ⟨k, hk⟩
    have h2 : n + c * n = (c + 1) * n := by ring
    rw [h2] at hk
    -- hk : n * (c * n) = (c + 1) * n * k
    have h3 : n * (c * n) = n * ((c + 1) * k) := by linarith
    have h4 : c * n = (c + 1) * k :=
      Nat.eq_of_mul_eq_mul_left hn h3
    have h5 : (c + 1) ∣ c * n := ⟨k, h4⟩
    have hcop : Nat.Coprime (c + 1) c := by
      rw [show c + 1 = c + 1 from rfl, Nat.coprime_self_add_left]
      exact Nat.coprime_one_left c
    exact hcop.dvd_of_dvd_mul_left h5
  · intro ⟨k, hk⟩
    subst hk
    exact ⟨c * k, by ring⟩

/-! ## Special cases -/

/-- (n, 2n) is a unit fraction pair iff 3 ∣ n. -/
theorem pair_n_2n_iff {n : ℕ} (hn : 0 < n) :
    IsUnitFractionPair n (2 * n) ↔ 3 ∣ n :=
  pair_n_cn_iff hn (by omega)

/-- (n, 3n) is a unit fraction pair iff 4 ∣ n. -/
theorem pair_n_3n_iff {n : ℕ} (hn : 0 < n) :
    IsUnitFractionPair n (3 * n) ↔ 4 ∣ n :=
  pair_n_cn_iff hn (by omega)

/-- (n, 4n) is a unit fraction pair iff 5 ∣ n. -/
theorem pair_n_4n_iff {n : ℕ} (hn : 0 < n) :
    IsUnitFractionPair n (4 * n) ↔ 5 ∣ n :=
  pair_n_cn_iff hn (by omega)

/-! ## Constraints on PairFree sets -/

/-- Symmetry: IsUnitFractionPair is symmetric. -/
theorem pair_symm {a b : ℕ} : IsUnitFractionPair a b ↔ IsUnitFractionPair b a := by
  unfold IsUnitFractionPair
  constructor <;> intro ⟨k, hk⟩ <;> exact ⟨k, by linarith⟩

/-- If n and 2n are both in a PairFree set, then 3 ∤ n. -/
theorem pair_free_double_not_div3 {A : Finset ℕ} (hA : PairFree A)
    {n : ℕ} (hn : 0 < n) (hn_mem : n ∈ A) (h2n_mem : 2 * n ∈ A) :
    ¬(3 ∣ n) := by
  intro hdvd
  exact hA n hn_mem (2 * n) h2n_mem (by omega) ((pair_n_2n_iff hn).mpr hdvd)

/-- If n and 3n are both in a PairFree set, then 4 ∤ n. -/
theorem pair_free_triple_not_div4 {A : Finset ℕ} (hA : PairFree A)
    {n : ℕ} (hn : 0 < n) (hn_mem : n ∈ A) (h3n_mem : 3 * n ∈ A) :
    ¬(4 ∣ n) := by
  intro hdvd
  exact hA n hn_mem (3 * n) h3n_mem (by omega) ((pair_n_3n_iff hn).mpr hdvd)

/-- Master constraint: a PairFree set that contains both n and c·n
    (with c ≥ 2) cannot have (c+1) ∣ n. -/
theorem pair_free_cn_constraint {A : Finset ℕ} (hA : PairFree A)
    {n c : ℕ} (hn : 0 < n) (hc : 1 < c) (hn_mem : n ∈ A)
    (hcn_mem : c * n ∈ A) : ¬((c + 1) ∣ n) := by
  intro hdvd
  have hne : n ≠ c * n := by nlinarith
  exact hA n hn_mem (c * n) hcn_mem hne ((pair_n_cn_iff hn (by omega)).mpr hdvd)

end UnitFractionPairs
