import Erdos.ResidueAvoidingDensity.Statement

/-
# Elementary Facts for Erdős Problem 25

This file records the first structural facts about residue-class avoidance:
membership unfolds to the defining condition, constraints are automatic before
their modulus appears, imposing no constraints gives the universal set, and
adding constraints can only shrink the avoided set.

Reference: https://www.erdosproblems.com/25
-/

namespace ResidueAvoidingDensity
namespace ResidueSystem

/-- Every modulus in a residue system is nonzero, because the system requires
positive moduli. -/
@[simp] theorem modulus_ne_zero (S : ResidueSystem) (i : ℕ) :
    S.modulus i ≠ 0 :=
  (S.modulus_pos i).ne'

/-- Membership in the full avoided set is exactly the condition of satisfying
every residue-class constraint. -/
@[simp] theorem mem_avoidedSet_iff {S : ResidueSystem} {n : ℕ} :
    n ∈ S.avoidedSet ↔ ∀ i, S.SatisfiesConstraint i n := by
  rfl

/-- Membership in a partially avoided set is the corresponding partial
avoidance predicate. -/
@[simp] theorem mem_avoidedSetOn_iff {S : ResidueSystem} {I : Set ℕ}
    {n : ℕ} :
    n ∈ S.avoidedSetOn I ↔ S.AvoidsOn I n := by
  rfl

/-- Membership in the finite avoided set for the first `k` constraints unfolds
to the predicate `AvoidsUpTo`. -/
@[simp] theorem mem_avoidedSetUpTo_iff {S : ResidueSystem} {k n : ℕ} :
    n ∈ S.avoidedSetUpTo k ↔ S.AvoidsUpTo k n := by
  rfl

/-- If `n` is smaller than the `i`-th modulus, then the `i`-th constraint is
automatically satisfied. This is the first alternative in the problem
statement. -/
@[simp] theorem satisfiesConstraint_of_lt {S : ResidueSystem} {i n : ℕ}
    (hn : n < S.modulus i) :
    S.SatisfiesConstraint i n := Or.inl hn

/-- Avoidance over the empty set of indices is vacuous. -/
@[simp] theorem avoidsOn_empty (S : ResidueSystem) (n : ℕ) :
    S.AvoidsOn ∅ n := by
  intro i hi
  simp at hi

/-- With no indexed constraints imposed, every integer is admitted. -/
@[simp] theorem avoidedSetOn_empty (S : ResidueSystem) :
    S.avoidedSetOn ∅ = Set.univ := by
  ext n
  simp [avoidedSetOn, AvoidsOn]

/-- Avoiding the first `0` constraints is a vacuous condition. -/
@[simp] theorem avoidsUpTo_zero (S : ResidueSystem) (n : ℕ) :
    S.AvoidsUpTo 0 n := by
  intro i hi
  omega

/-- The first `0` constraints impose no restriction. -/
@[simp] theorem avoidedSetUpTo_zero (S : ResidueSystem) :
    S.avoidedSetUpTo 0 = Set.univ := by
  ext n
  simp [avoidedSetUpTo, AvoidsUpTo]

/-- Avoiding all indices in `Set.univ` recovers the full avoided set. -/
@[simp] theorem avoidedSetOn_univ (S : ResidueSystem) :
    S.avoidedSetOn Set.univ = S.avoidedSet := by
  ext n
  simp [avoidedSetOn, AvoidsOn, avoidedSet]

/-- Enlarging the set of imposed indices can only shrink the avoided set. -/
theorem avoidedSetOn_antitone {S : ResidueSystem} {I J : Set ℕ}
    (hIJ : I ⊆ J) :
    S.avoidedSetOn J ⊆ S.avoidedSetOn I := by
  intro n hn i hi
  exact hn i (hIJ hi)

/-- Imposing more initial constraints can only shrink the finite avoided set. -/
theorem avoidedSetUpTo_mono {S : ResidueSystem} {k l : ℕ} (hkl : k ≤ l) :
    S.avoidedSetUpTo l ⊆ S.avoidedSetUpTo k := by
  intro n hn i hi
  exact hn i (lt_of_lt_of_le hi hkl)

/-- Adding the next constraint shrinks, or leaves unchanged, the finite avoided
set. -/
theorem avoidedSetUpTo_succ_subset {S : ResidueSystem} {k : ℕ} :
    S.avoidedSetUpTo (k + 1) ⊆ S.avoidedSetUpTo k := avoidedSetUpTo_mono (Nat.le_succ k)

/-- The full avoided set is contained in every finite avoided set. -/
theorem avoidedSet_subset_avoidedSetUpTo {S : ResidueSystem} {k : ℕ} :
    S.avoidedSet ⊆ S.avoidedSetUpTo k := by
  intro n hn i _hi
  exact hn i

/-- Satisfying the first `k + 1` constraints is the same as satisfying the
first `k` constraints and also the new `k`-th constraint. -/
theorem avoidsUpTo_succ_iff {S : ResidueSystem} {k n : ℕ} :
    S.AvoidsUpTo (k + 1) n ↔
      S.AvoidsUpTo k n ∧ S.SatisfiesConstraint k n := by
  constructor
  · intro hn
    refine ⟨?_, hn k (Nat.lt_succ_self k)⟩
    intro i hi
    exact hn i (Nat.lt_succ_of_lt hi)
  · rintro ⟨hpre, hk⟩ i hi
    by_cases hik : i < k
    · exact hpre i hik
    · have h_eq : i = k := by omega
      simpa [h_eq] using hk

/-- If `n ∈ A`, then its logarithmic weight in `A` is `1 / n`. -/
@[simp] theorem finiteLogWeight_of_mem {A : Set ℕ} {n : ℕ} (hn : n ∈ A) :
    finiteLogWeight A n = (n : ℝ)⁻¹ := by
  classical
  simp [finiteLogWeight, hn]

/-- If `n ∉ A`, then its logarithmic weight in `A` is zero. -/
@[simp] theorem finiteLogWeight_of_not_mem {A : Set ℕ} {n : ℕ}
    (hn : n ∉ A) :
    finiteLogWeight A n = 0 := by
  classical
  simp [finiteLogWeight, hn]

/-- The empty set has zero logarithmic weight at every integer. -/
@[simp] theorem finiteLogWeight_empty (n : ℕ) :
    finiteLogWeight (∅ : Set ℕ) n = 0 := by
  classical
  simp [finiteLogWeight]

/-- The universal set has the full logarithmic weight `1 / n` at every
integer. -/
@[simp] theorem finiteLogWeight_univ (n : ℕ) :
    finiteLogWeight (Set.univ : Set ℕ) n = (n : ℝ)⁻¹ := by
  classical
  simp [finiteLogWeight]

end ResidueSystem
end ResidueAvoidingDensity
