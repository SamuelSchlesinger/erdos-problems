import Erdos.PlanePairColorings.Statement

/-
# Elementary Facts About Plane Pair-Colorings

This file records the basic formal infrastructure around
`PlanePairColoringStatement k`. These are not deep set-theoretic results: they
show that uncountable sets contain two distinct points, that the one-color
variant is trivial, and that any solution with more colors yields one with
fewer colors by merging colors.
-/
namespace PlanePairColorings

/-- If a color appears on a set `A`, then it also appears on every larger set. -/
theorem HasColorOn.mono {k : ℕ} {c : PairColoring k} {A B : Set Plane} {i : Fin k}
    (hAB : A ⊆ B) :
    HasColorOn c A i → HasColorOn c B i := by
  rintro ⟨x, hx, y, hy, hxy, hcolor⟩
  exact ⟨x, hAB hx, y, hAB hy, hxy, hcolor⟩

/-- Hitting all colors is monotone under enlarging the ambient set. -/
theorem HitsAllColorsOn.mono {k : ℕ} {c : PairColoring k} {A B : Set Plane}
    (hAB : A ⊆ B) :
    HitsAllColorsOn c A → HitsAllColorsOn c B := by
  intro hA i
  exact HasColorOn.mono hAB (hA i)

/-- An uncountable set contains two distinct points. -/
theorem exists_ne_mem_of_not_countable {A : Set Plane} (hA : ¬ A.Countable) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y := by
  by_cases hEmpty : A = ∅
  · exact (hA (hEmpty.symm ▸ Set.countable_empty)).elim
  · obtain ⟨x, hx⟩ : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    by_cases hpair : ∃ y ∈ A, x ≠ y
    · rcases hpair with ⟨y, hy, hxy⟩
      exact ⟨x, hx, y, hy, hxy⟩
    · have hsubset : A ⊆ ({x} : Set Plane) := by
        intro y hy
        by_cases hyx : y = x
        · simp [hyx]
        · exact False.elim (hpair ⟨y, hy, by
            intro hxy
            exact hyx hxy.symm⟩)
      have hcount : A.Countable := (Set.countable_singleton x).mono hsubset
      exact (hA hcount).elim

/-- The constant recoloring associated to a map on the color set. -/
def recolor {k l : ℕ} (f : Fin l → Fin k) (c : PairColoring l) : PairColoring k :=
  fun x y => f (c x y)

theorem recolor_symmetric {k l : ℕ} {f : Fin l → Fin k} {c : PairColoring l}
    (hc : IsSymmetricColoring c) :
    IsSymmetricColoring (recolor f c) := by
  intro x y
  simp [recolor, hc x y]

theorem hitsAllColorsOn_recolor_of_surjective {k l : ℕ}
    {f : Fin l → Fin k} (hf : Function.Surjective f)
    {c : PairColoring l} {A : Set Plane}
    (hA : HitsAllColorsOn c A) :
    HitsAllColorsOn (recolor f c) A := by
  intro i
  rcases hf i with ⟨j, rfl⟩
  rcases hA j with ⟨x, hx, y, hy, hxy, hcolor⟩
  exact ⟨x, hx, y, hy, hxy, by
    simpa [recolor] using congrArg f hcolor⟩

/-- Collapse an `l`-coloring to a `k`-coloring by keeping the first `k - 1`
colors and sending every remaining color to `0`. -/
def truncateColor {k l : ℕ} (hk : 0 < k) : Fin l → Fin k :=
  fun i =>
    if hi : i.1 < k then ⟨i.1, hi⟩ else ⟨0, hk⟩

theorem truncateColor_surjective {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) :
    Function.Surjective (truncateColor (k := k) (l := l) hk) := by
  intro i
  refine ⟨⟨i.1, lt_of_lt_of_le i.2 hkl⟩, ?_⟩
  simp [truncateColor, i.2]

/-- A solution with `l` colors yields one with any smaller positive number `k`
of colors. -/
theorem planePairColoringStatement_mono {k l : ℕ}
    (hk : 0 < k) (hkl : k ≤ l) :
    PlanePairColoringStatement l → PlanePairColoringStatement k := by
  rintro ⟨c, hc, huncountable⟩
  refine ⟨recolor (truncateColor (k := k) (l := l) hk) c, recolor_symmetric hc, ?_⟩
  intro A hA
  exact hitsAllColorsOn_recolor_of_surjective
    (truncateColor_surjective hk hkl) (huncountable A hA)

/-- Zero colors are impossible, since there is no map from a nonempty domain to
`Fin 0`. -/
theorem not_planePairColoringStatement_zero :
    ¬ PlanePairColoringStatement 0 := by
  rintro ⟨c, _, _⟩
  exact Fin.elim0 (c (0, 0) (0, 0))

/-- The one-color variant is trivial: color every pair by the unique color. -/
theorem planePairColoringStatement_one : PlanePairColoringStatement 1 := by
  refine ⟨fun _ _ => 0, ?_, ?_⟩
  · intro x y
    rfl
  · intro A hA i
    rcases exists_ne_mem_of_not_countable hA with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, hxy, Subsingleton.elim _ _⟩

/-- In particular, a positive answer to problem `#474` would imply the already
known two-color variant. -/
theorem erdos474Statement_implies_twoColor :
    Erdos474Statement → PlanePairColoringStatement 2 :=
  planePairColoringStatement_mono (by decide : 0 < 2) (by decide : 2 ≤ 3)

end PlanePairColorings
