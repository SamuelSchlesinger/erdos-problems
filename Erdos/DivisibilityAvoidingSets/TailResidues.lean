import Erdos.DivisibilityAvoidingSets.Elementary

/-!
# Tail residue obstructions for Erdős problem #12

For a fixed element `a` of an avoiding set, the elements of the tail above `a`
cannot contain two distinct numbers whose residues add to zero modulo `a`.
This is the local residue constraint that any attack on the reciprocal-sum
question has to amplify across many values of `a`.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- The part of `A` strictly above `a`. -/
def tailAbove (A : Set ℕ) (a : ℕ) : Set ℕ :=
  {n | n ∈ A ∧ a < n}

/-- A set has no two distinct elements whose residues add to zero modulo `a`. -/
def PairwiseNoZeroResidueSum (a : ℕ) (B : Set ℕ) : Prop :=
  ∀ ⦃b c : ℕ⦄, b ∈ B → c ∈ B → b ≠ c →
    (b % a + c % a) % a ≠ 0

/-- If the residues of `b` and `c` add to zero modulo `a`, then `a ∣ b + c`. -/
theorem dvd_add_of_zero_residue_sum {a b c : ℕ}
    (hres : (b % a + c % a) % a = 0) :
    a ∣ b + c := by
  have hb : b ≡ b % a [MOD a] := (Nat.mod_modEq b a).symm
  have hc : c ≡ c % a [MOD a] := (Nat.mod_modEq c a).symm
  have hsum : b + c ≡ b % a + c % a [MOD a] := hb.add hc
  have hzero : b % a + c % a ≡ 0 [MOD a] :=
    (Nat.dvd_of_mod_eq_zero hres).modEq_zero_nat
  exact Nat.modEq_zero_iff_dvd.mp (hsum.trans hzero)

/-- In an avoiding set, two distinct tail elements above `a` cannot have sum
divisible by `a`. -/
theorem AvoidingSet.not_dvd_add_of_tail {A : Set ℕ} (hA : AvoidingSet A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) (hbc : b ≠ c) :
    ¬ a ∣ b + c := by
  intro hdvd
  exact hA ⟨ha, hb, hc, by omega, by omega, hbc, hdvd, hab, hac⟩

/-- In an avoiding set, two distinct tail elements above `a` cannot have
residues adding to zero modulo `a`. -/
theorem AvoidingSet.not_zero_residue_sum_of_tail {A : Set ℕ}
    (hA : AvoidingSet A) {a b c : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) (hbc : b ≠ c) :
    (b % a + c % a) % a ≠ 0 := by
  intro hres
  exact hA.not_dvd_add_of_tail ha hb hc hab hac hbc
    (dvd_add_of_zero_residue_sum hres)

/-- The tail above any element of an avoiding set has the no-zero-residue-sum
property modulo that element. -/
theorem AvoidingSet.tail_pairwiseNoZeroResidueSum {A : Set ℕ}
    (hA : AvoidingSet A) {a : ℕ} (ha : a ∈ A) :
    PairwiseNoZeroResidueSum a (tailAbove A a) := by
  intro b c hb hc hbc hres
  exact hA.not_zero_residue_sum_of_tail ha hb.1 hc.1 hb.2 hc.2 hbc hres

/-- The no-zero-residue-sum property passes to any subset of a tail. -/
theorem AvoidingSet.pairwiseNoZeroResidueSum_of_subset_tail {A B : Set ℕ}
    (hA : AvoidingSet A) {a : ℕ} (ha : a ∈ A)
    (hB : B ⊆ tailAbove A a) :
    PairwiseNoZeroResidueSum a B := by
  intro b c hb hc hbc hres
  exact hA.tail_pairwiseNoZeroResidueSum ha (hB hb) (hB hc) hbc hres

/-- In a set with the no-zero-residue-sum property, two elements whose residues
add to zero modulo `a` must be equal. -/
theorem PairwiseNoZeroResidueSum.eq_of_zero_residue_sum {a : ℕ} {B : Set ℕ}
    (hB : PairwiseNoZeroResidueSum a B) {b c : ℕ}
    (hb : b ∈ B) (hc : c ∈ B) (hres : (b % a + c % a) % a = 0) :
    b = c := by
  by_contra hne
  exact hB hb hc hne hres

/-- Tail equality form for avoiding sets: above `a`, complementary residues
modulo `a` can only occur on the diagonal. -/
theorem AvoidingSet.eq_of_tail_zero_residue_sum {A : Set ℕ} (hA : AvoidingSet A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) (hres : (b % a + c % a) % a = 0) :
    b = c := by
  exact PairwiseNoZeroResidueSum.eq_of_zero_residue_sum
    (hA.tail_pairwiseNoZeroResidueSum ha) ⟨hb, hab⟩ ⟨hc, hac⟩ hres

end DivisibilityAvoidingSets
