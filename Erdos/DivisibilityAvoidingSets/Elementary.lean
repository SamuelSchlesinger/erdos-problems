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
