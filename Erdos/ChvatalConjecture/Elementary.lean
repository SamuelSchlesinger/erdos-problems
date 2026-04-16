import Erdos.ChvatalConjecture.Statement

/-
# Elementary Facts About Chvátal's Conjecture

This file records the cleanest first case of problem `#701`: the full Boolean
lattice. Using Mathlib's general bound that an intersecting family in a
Boolean algebra occupies at most half the ambient space, we show that every
intersecting family of subsets of `Fin (n + 1)` is no larger than any
principal star of the full powerset.
-/
namespace ChvatalConjecture

@[simp] theorem mem_star {α : Type*} [DecidableEq α] {x : α} {𝒜 : Finset (Finset α)}
    {s : Finset α} :
    s ∈ star x 𝒜 ↔ s ∈ 𝒜 ∧ x ∈ s := by
  simp [star]

theorem downClosed_univ (n : ℕ) :
    DownClosed (Finset.univ : Finset (Finset (Fin (n + 1)))) := by
  intro s t hts hs
  simp

/-- A principal star in the full Boolean lattice is intersecting. -/
theorem star_univ_intersecting (n : ℕ) (x : Fin (n + 1)) :
    ((star x (Finset.univ : Finset (Finset (Fin (n + 1))))) :
      Set (Finset (Fin (n + 1)))).Intersecting := by
  intro a ha b hb
  have hax : x ∈ a := by
    simpa [mem_star] using ha
  have hbx : x ∈ b := by
    simpa [mem_star] using hb
  have hxab : x ∈ a ∩ b := by
    simp [hax, hbx]
  intro hab
  rw [Finset.disjoint_iff_inter_eq_empty] at hab
  simp [hab] at hxab

/-- In the full Boolean lattice, a principal star is maximal among intersecting
families: adjoining any set that misses `x` would force inclusion of its
complement, producing a disjoint pair. -/
theorem star_univ_isMax (n : ℕ) (x : Fin (n + 1)) :
    ∀ ℱ : Finset (Finset (Fin (n + 1))),
      (ℱ : Set (Finset (Fin (n + 1)))).Intersecting →
      star x (Finset.univ : Finset (Finset (Fin (n + 1)))) ⊆ ℱ →
      star x (Finset.univ : Finset (Finset (Fin (n + 1)))) = ℱ := by
  intro ℱ hℱ hstar
  apply le_antisymm hstar
  intro s hs
  by_contra hxs
  have hxs' : x ∉ s := by
    simpa [mem_star] using hxs
  have hcomplStar : sᶜ ∈ star x (Finset.univ : Finset (Finset (Fin (n + 1)))) := by
    simp [mem_star, hxs']
  have hcomplℱ : sᶜ ∈ ℱ := hstar hcomplStar
  exact hℱ hs hcomplℱ disjoint_compl_right

/-- Therefore every principal star in the full Boolean lattice has exactly half
the subsets. -/
theorem two_mul_card_star_univ (n : ℕ) (x : Fin (n + 1)) :
    2 * (star x (Finset.univ : Finset (Finset (Fin (n + 1))))).card = 2 ^ (n + 1) := by
  have hstar :
      2 * (star x (Finset.univ : Finset (Finset (Fin (n + 1))))).card =
        Fintype.card (Finset (Fin (n + 1))) := by
    exact (star_univ_intersecting n x).is_max_iff_card_eq.1 (star_univ_isMax n x)
  simpa using hstar

/-- Consequently every intersecting family of subsets of `Fin (n + 1)` has
cardinality at most that of any principal star. -/
theorem card_le_star_univ (n : ℕ) (x : Fin (n + 1))
    {ℱ : Finset (Finset (Fin (n + 1)))}
    (hℱ : (ℱ : Set (Finset (Fin (n + 1)))).Intersecting) :
    ℱ.card ≤ (star x (Finset.univ : Finset (Finset (Fin (n + 1))))).card := by
  have hcard : 2 * ℱ.card ≤ Fintype.card (Finset (Fin (n + 1))) :=
    hℱ.card_le
  have hstar :
      2 * (star x (Finset.univ : Finset (Finset (Fin (n + 1))))).card =
        Fintype.card (Finset (Fin (n + 1))) := by
    exact (star_univ_intersecting n x).is_max_iff_card_eq.1 (star_univ_isMax n x)
  exact Nat.le_of_mul_le_mul_left (hcard.trans_eq hstar.symm) Nat.two_pos

/-- The full powerset satisfies Chvátal's desired conclusion; the `0`-star is
already extremal. -/
theorem fullPowerset_zero_starMaximizes (n : ℕ) :
    StarMaximizesIntersecting 0 (Finset.univ : Finset (Finset (Fin (n + 1)))) := by
  intro ℱ hℱ hsub
  exact card_le_star_univ n 0 hℱ

/-- Hence the conjecture holds for the full Boolean lattice on `Fin (n + 1)`.
-/
theorem fullPowerset_case (n : ℕ) :
    DownClosed (Finset.univ : Finset (Finset (Fin (n + 1)))) ∧
      ∃ x : Fin (n + 1),
        StarMaximizesIntersecting x (Finset.univ : Finset (Finset (Fin (n + 1)))) := by
  exact ⟨downClosed_univ n, 0, fullPowerset_zero_starMaximizes n⟩

end ChvatalConjecture
