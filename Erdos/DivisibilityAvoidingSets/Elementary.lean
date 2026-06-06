import Erdos.DivisibilityAvoidingSets.Statement

/-
# Elementary Facts About Divisibility-Avoiding Sets

This file records the first structural facts for Erdős problem `#12`. The key
observation is hereditary: passing to a subset cannot create a forbidden
triple. As immediate base cases, the empty set and every subset of a singleton
are avoiding.

Reference: https://www.erdosproblems.com/12
-/
namespace DivisibilityAvoidingSets

/-- A forbidden triple remains forbidden after enlarging the ambient set. -/
theorem ForbiddenTriple.mono {A B : Set ℕ} {a b c : ℕ}
    (hAB : A ⊆ B) (h : ForbiddenTriple A a b c) :
    ForbiddenTriple B a b c := by
  rcases h with ⟨ha, hb, hc, hab, hac, hbc, hdvd, hltb, hltc⟩
  exact ⟨hAB ha, hAB hb, hAB hc, hab, hac, hbc, hdvd, hltb, hltc⟩

/-- Avoidance is monotone under taking subsets. -/
theorem AvoidingSet.mono {A B : Set ℕ} (hB : AvoidingSet B) (hAB : A ⊆ B) :
    AvoidingSet A := by
  intro a b c h
  exact hB (ForbiddenTriple.mono hAB h)

/-- The no-forbidden-triple formulation is equivalent to the problem-page
formulation: if three members `a,b,c` satisfy `a ∣ b + c` and both `b,c` are
larger than `a`, then the two larger members must be equal. -/
theorem avoidingSet_iff_eq_of_dvd {A : Set ℕ} :
    AvoidingSet A ↔
      ∀ ⦃a b c : ℕ⦄, a ∈ A → b ∈ A → c ∈ A →
        a ∣ b + c → a < b → a < c → b = c := by
  constructor
  · intro hA a b c ha hb hc hdvd hab hac
    by_contra hbc
    exact hA ⟨ha, hb, hc, hab.ne, hac.ne, hbc, hdvd, hab, hac⟩
  · intro hA a b c h
    rcases h with ⟨ha, hb, hc, _hab_ne, _hac_ne, hbc_ne, hdvd, hab, hac⟩
    exact hbc_ne (hA ha hb hc hdvd hab hac)

/-- Positivity is monotone under taking subsets. -/
theorem PositiveSet.mono {A B : Set ℕ} (hB : PositiveSet B) (hAB : A ⊆ B) :
    PositiveSet A := by
  intro n hn
  exact hB (hAB hn)

/-- The finset-filter definition of `countUpTo` agrees with the standard
`Set.ncard` count of `A ∩ {1, ..., N}`.  This bridge lets later arguments use
whichever finite-set API is most convenient. -/
theorem countUpTo_eq_ncard_inter_Icc (A : Set ℕ) (N : ℕ) :
    countUpTo A N = (A ∩ Set.Icc 1 N).ncard := by
  classical
  unfold countUpTo
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [Finset.mem_Icc]
  tauto

/-- Enlarging the set cannot decrease its counting function. -/
theorem countUpTo_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (N : ℕ) :
    countUpTo A N ≤ countUpTo B N := by
  classical
  unfold countUpTo
  exact Finset.card_le_card (by
    intro n hn
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hn).1, hAB (Finset.mem_filter.mp hn).2⟩)

/-- Increasing the cutoff cannot decrease the counting function. -/
theorem countUpTo_mono_right (A : Set ℕ) {M N : ℕ} (hMN : M ≤ N) :
    countUpTo A M ≤ countUpTo A N := by
  classical
  unfold countUpTo
  exact Finset.card_le_card (by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hI, hnA⟩
    have hI_N : n ∈ Finset.Icc 1 N := by
      rcases Finset.mem_Icc.mp hI with ⟨h1n, hnM⟩
      exact Finset.mem_Icc.mpr ⟨h1n, hnM.trans hMN⟩
    exact Finset.mem_filter.mpr ⟨hI_N, hnA⟩)

/-- The empty set contains no forbidden triple. -/
@[simp] theorem avoidingSet_empty :
    AvoidingSet (∅ : Set ℕ) := by
  intro a b c h
  exact h.1

/-- Any subset of a singleton is avoiding, since a forbidden triple would need
two distinct elements `b` and `c`. -/
theorem avoidingSet_of_subset_singleton {A : Set ℕ} {n : ℕ}
    (hA : A ⊆ ({n} : Set ℕ)) :
    AvoidingSet A := by
  intro a b c h
  rcases h with ⟨_, hb, hc, _, _, hbc, _, _, _⟩
  have hb_eq : b = n := by
    simpa using hA hb
  have hc_eq : c = n := by
    simpa using hA hc
  exact hbc (hb_eq.trans hc_eq.symm)

/-- A singleton is avoiding. -/
@[simp] theorem avoidingSet_singleton (n : ℕ) :
    AvoidingSet ({n} : Set ℕ) := by
  exact avoidingSet_of_subset_singleton (Set.Subset.rfl)

end DivisibilityAvoidingSets
