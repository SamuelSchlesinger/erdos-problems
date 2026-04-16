/- 
# The Erdős-Freud Reflected-Sidon Construction

If `B ⊆ {1, ..., ⌊N/3⌋}` is Sidon, then `B ∪ {N - b : b ∈ B}` is an
almost-Sidon set in `{1, ..., N}`. The only possible repeated sum is the
central value `N`.
-/
import Erdos.AlmostSidonSets.Statement

namespace AlmostSidonSets

open SidonSumsets

/-- Reflect a finite set across `N`. -/
def reflectFinset (N : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.image fun b => N - b

/-- The Erdős-Freud doubled set `B ∪ (N - B)`. -/
def doubledFinset (N : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B ∪ reflectFinset N B

@[simp] theorem mem_reflectFinset {N : ℕ} {B : Finset ℕ} {x : ℕ} :
    x ∈ reflectFinset N B ↔ ∃ b ∈ B, N - b = x := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨b, hb, hbx⟩
    exact ⟨b, hb, hbx⟩
  · rintro ⟨b, hb, rfl⟩
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

@[simp] theorem mem_doubledFinset {N : ℕ} {B : Finset ℕ} {x : ℕ} :
    x ∈ doubledFinset N B ↔ x ∈ B ∨ x ∈ reflectFinset N B := by
  simp [doubledFinset]

/-- Sidon sets have unique unordered two-term sum representations. -/
theorem IsSidon.eq_or_eq_swap_of_add_eq {A : Set ℕ} (hA : IsSidon A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hsum : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hminab : min a b ∈ A := by
    by_cases hab : a ≤ b
    · simpa [Nat.min_eq_left hab] using ha
    · simpa [Nat.min_eq_right (le_of_not_ge hab)] using hb
  have hmaxab : max a b ∈ A := by
    by_cases hab : a ≤ b
    · simpa [Nat.max_eq_right hab] using hb
    · simpa [Nat.max_eq_left (le_of_not_ge hab)] using ha
  have hmincd : min c d ∈ A := by
    by_cases hcd : c ≤ d
    · simpa [Nat.min_eq_left hcd] using hc
    · simpa [Nat.min_eq_right (le_of_not_ge hcd)] using hd
  have hmaxcd : max c d ∈ A := by
    by_cases hcd : c ≤ d
    · simpa [Nat.max_eq_right hcd] using hd
    · simpa [Nat.max_eq_left (le_of_not_ge hcd)] using hc
  have hsum' : min a b + max a b = min c d + max c d := by
    rw [min_add_max, min_add_max, hsum]
  have hleab : min a b ≤ max a b := by
    exact le_max_of_le_left (min_le_left _ _)
  have hlecd : min c d ≤ max c d := by
    exact le_max_of_le_left (min_le_left _ _)
  rcases hA hminab hmaxab hmincd hmaxcd hleab hlecd hsum' with
    ⟨hmin, hmax⟩
  by_cases hab : a ≤ b
  · by_cases hcd : c ≤ d
    · left
      constructor
      · simpa [Nat.min_eq_left hab, Nat.min_eq_left hcd] using hmin
      · simpa [Nat.max_eq_right hab, Nat.max_eq_right hcd] using hmax
    · right
      constructor
      · simpa [Nat.min_eq_left hab, Nat.min_eq_right (le_of_not_ge hcd)] using hmin
      · simpa [Nat.max_eq_right hab, Nat.max_eq_left (le_of_not_ge hcd)] using hmax
  · by_cases hcd : c ≤ d
    · right
      constructor
      · simpa [Nat.max_eq_left (le_of_not_ge hab), Nat.max_eq_right hcd] using hmax
      · simpa [Nat.min_eq_right (le_of_not_ge hab), Nat.min_eq_left hcd] using hmin
    · left
      constructor
      · simpa [Nat.max_eq_left (le_of_not_ge hab), Nat.max_eq_left (le_of_not_ge hcd)] using hmax
      · simpa [Nat.min_eq_right (le_of_not_ge hab), Nat.min_eq_right (le_of_not_ge hcd)] using hmin

/-- Elements of `B ⊆ {1, ..., ⌊N/3⌋}` lie in the lower third of the interval. -/
theorem mem_base_bounds {N : ℕ} {B : Finset ℕ}
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) {b : ℕ} (hb : b ∈ B) :
    1 ≤ b ∧ 3 * b ≤ N := by
  have hb' := hBground b hb
  rw [mem_ground] at hb'
  omega

/-- Reflected points lie in the upper part of the interval. -/
theorem mem_reflect_bounds {N : ℕ} {B : Finset ℕ}
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) {x : ℕ}
    (hx : x ∈ reflectFinset N B) :
    1 ≤ x ∧ x ≤ N ∧ 2 * N ≤ 3 * x := by
  rcases mem_reflectFinset.mp hx with ⟨b, hb, rfl⟩
  have hb' := mem_base_bounds hBground hb
  omega

/-- Lower-third elements are always below reflected elements. -/
theorem base_le_reflect {N : ℕ} {B : Finset ℕ}
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) {a b : ℕ}
    (ha : a ∈ B) (hb : N - b ∈ reflectFinset N B) :
    a ≤ N - b := by
  have ha' := mem_base_bounds hBground ha
  have hb' := mem_reflect_bounds hBground hb
  omega

/-- Lower-third elements are strictly below reflected elements. -/
theorem base_lt_reflected_value {N : ℕ} {B : Finset ℕ}
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) {a b : ℕ}
    (ha : a ∈ B) (hb : b ∈ B) :
    a < N - b := by
  have ha' := mem_base_bounds hBground ha
  have hb' := mem_base_bounds hBground hb
  omega

/-- The reflected copy is disjoint from the original set. -/
theorem disjoint_base_reflect {N : ℕ} {B : Finset ℕ}
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) :
    Disjoint B (reflectFinset N B) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxB hxR
  have hxB' := mem_base_bounds hBground hxB
  have hxR' := mem_reflect_bounds hBground hxR
  omega

/-- Reflection preserves cardinality on lower-third sets. -/
theorem card_reflectFinset {N : ℕ} {B : Finset ℕ}
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) :
    (reflectFinset N B).card = B.card := by
  unfold reflectFinset
  refine Finset.card_image_of_injOn ?_
  intro a ha b hb hab
  have ha' := mem_base_bounds hBground ha
  have hb' := mem_base_bounds hBground hb
  have haN : a ≤ N := by omega
  have hbN : b ≤ N := by omega
  have hcast : ((N : ℤ) - a : ℤ) = (N : ℤ) - b := by
    exact_mod_cast hab
  omega

/-- Therefore the doubled set has exactly twice the cardinality. -/
theorem card_doubledFinset {N : ℕ} {B : Finset ℕ}
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) :
    (doubledFinset N B).card = 2 * B.card := by
  have hdisj : Disjoint B (reflectFinset N B) := disjoint_base_reflect hBground
  calc
    (doubledFinset N B).card = B.card + (reflectFinset N B).card := by
      simpa [doubledFinset, Nat.add_comm] using Finset.card_union_of_disjoint hdisj
    _ = B.card + B.card := by rw [card_reflectFinset hBground]
    _ = 2 * B.card := by omega

/-- The doubled set stays inside `{1, ..., N}`. -/
theorem doubledFinset_subset_ground {N : ℕ} {B : Finset ℕ}
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) :
    ∀ x ∈ doubledFinset N B, x ∈ ground N := by
  intro x hx
  rcases mem_doubledFinset.mp hx with hxB | hxR
  · have hx' := mem_base_bounds hBground hxB
    rw [mem_ground]
    omega
  · have hx' := mem_reflect_bounds hBground hxR
    rw [mem_ground]
    omega

/-- A repeated sum inside the doubled set must be the central sum `N`. -/
theorem hasTwoSumReprs_doubled_forces_center
    {N : ℕ} {B : Finset ℕ}
    (hSidon : IsSidonFinset B)
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3))
    {n : ℕ} (hn : HasTwoSumReprs (doubledFinset N B) n) :
    n = N := by
  rcases hn with ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, ha12, hb12, han, hbn, hneq⟩
  rcases mem_doubledFinset.mp ha₁ with ha₁B | ha₁R
  · rcases mem_doubledFinset.mp ha₂ with ha₂B | ha₂R
    · rcases mem_doubledFinset.mp hb₁ with hb₁B | hb₁R
      · rcases mem_doubledFinset.mp hb₂ with hb₂B | hb₂R
        · rcases IsSidon.eq_or_eq_swap_of_add_eq hSidon ha₁B ha₂B hb₁B hb₂B (by omega) with
            hsame | hswap
          · rcases hsame with ⟨rfl, rfl⟩
            rcases hneq with h | h <;> contradiction
          · have hsame : a₁ = b₁ ∧ a₂ = b₂ := by
              rcases hswap with ⟨h1, h2⟩
              omega
            rcases hsame with ⟨rfl, rfl⟩
            rcases hneq with h | h <;> contradiction
        · have hlow : 3 * n ≤ 2 * N := by
            have ha₁' := mem_base_bounds hBground ha₁B
            have ha₂' := mem_base_bounds hBground ha₂B
            omega
          have hcross : 2 * N < 3 * n := by
            have hb₁' := mem_base_bounds hBground hb₁B
            have hb₂' := mem_reflect_bounds hBground hb₂R
            omega
          exact (not_lt_of_ge hlow hcross).elim
      · rcases mem_doubledFinset.mp hb₂ with hb₂B | hb₂R
        · have hbad : b₂ < b₁ := by
            have hb₁' := mem_reflect_bounds hBground hb₁R
            have hb₂' := mem_base_bounds hBground hb₂B
            omega
          omega
        · have hlow : 3 * n ≤ 2 * N := by
            have ha₁' := mem_base_bounds hBground ha₁B
            have ha₂' := mem_base_bounds hBground ha₂B
            omega
          have hhigh : 4 * N ≤ 3 * n := by
            have hb₁' := mem_reflect_bounds hBground hb₁R
            have hb₂' := mem_reflect_bounds hBground hb₂R
            omega
          omega
    · rcases mem_doubledFinset.mp hb₁ with hb₁B | hb₁R
      · rcases mem_doubledFinset.mp hb₂ with hb₂B | hb₂R
        · have hcross : 2 * N < 3 * n := by
            have ha₁' := mem_base_bounds hBground ha₁B
            have ha₂' := mem_reflect_bounds hBground ha₂R
            omega
          have hlow : 3 * n ≤ 2 * N := by
            have hb₁' := mem_base_bounds hBground hb₁B
            have hb₂' := mem_base_bounds hBground hb₂B
            omega
          exact (not_lt_of_ge hlow hcross).elim
        · rcases mem_reflectFinset.mp ha₂R with ⟨y, hyB, rfl⟩
          rcases mem_reflectFinset.mp hb₂R with ⟨v, hvB, rfl⟩
          rcases IsSidon.eq_or_eq_swap_of_add_eq hSidon ha₁B hvB hb₁B hyB (by omega) with
            hsame | hswap
          · rcases hsame with ⟨h1, h2⟩
            subst h1
            subst h2
            rcases hneq with h | h <;> contradiction
          · rcases hswap with ⟨hxy, hvu⟩
            omega
      · rcases mem_doubledFinset.mp hb₂ with hb₂B | hb₂R
        · have hbad : b₂ < b₁ := by
            rcases mem_reflectFinset.mp hb₁R with ⟨y, hyB, rfl⟩
            exact base_lt_reflected_value hBground hb₂B hyB
          exact (not_lt_of_ge hb12 hbad).elim
        · have hcross : 3 * n < 4 * N := by
            have ha₁' := mem_base_bounds hBground ha₁B
            rcases mem_reflectFinset.mp ha₂R with ⟨y, hyB, rfl⟩
            have hy' := mem_base_bounds hBground hyB
            omega
          have hhigh : 4 * N ≤ 3 * n := by
            have hb₁' := mem_reflect_bounds hBground hb₁R
            have hb₂' := mem_reflect_bounds hBground hb₂R
            omega
          exact (not_lt_of_ge hhigh hcross).elim
  · rcases mem_doubledFinset.mp ha₂ with ha₂B | ha₂R
    · have hbad : a₂ < a₁ := by
        have ha₁' := mem_reflect_bounds hBground ha₁R
        have ha₂' := mem_base_bounds hBground ha₂B
        omega
      exact (not_lt_of_ge ha12 hbad).elim
    · rcases mem_doubledFinset.mp hb₁ with hb₁B | hb₁R
      · rcases mem_doubledFinset.mp hb₂ with hb₂B | hb₂R
        · have hhigh : 4 * N ≤ 3 * n := by
            have ha₁' := mem_reflect_bounds hBground ha₁R
            have ha₂' := mem_reflect_bounds hBground ha₂R
            omega
          have hlow : 3 * n ≤ 2 * N := by
            have hb₁' := mem_base_bounds hBground hb₁B
            have hb₂' := mem_base_bounds hBground hb₂B
            omega
          omega
        · have hcross : 3 * n < 4 * N := by
            have hb₁' := mem_base_bounds hBground hb₁B
            rcases mem_reflectFinset.mp hb₂R with ⟨y, hyB, rfl⟩
            have hy' := mem_base_bounds hBground hyB
            omega
          have hhigh : 4 * N ≤ 3 * n := by
            have ha₁' := mem_reflect_bounds hBground ha₁R
            have ha₂' := mem_reflect_bounds hBground ha₂R
            omega
          omega
      · rcases mem_doubledFinset.mp hb₂ with hb₂B | hb₂R
        · have hbad : b₂ < b₁ := by
            rcases mem_reflectFinset.mp hb₁R with ⟨y, hyB, rfl⟩
            exact base_lt_reflected_value hBground hb₂B hyB
          exact (not_lt_of_ge hb12 hbad).elim
        · rcases mem_reflectFinset.mp ha₁R with ⟨x, hxB, rfl⟩
          rcases mem_reflectFinset.mp ha₂R with ⟨y, hyB, rfl⟩
          rcases mem_reflectFinset.mp hb₁R with ⟨u, huB, rfl⟩
          rcases mem_reflectFinset.mp hb₂R with ⟨v, hvB, rfl⟩
          have hx' := mem_base_bounds hBground hxB
          have hy' := mem_base_bounds hBground hyB
          have hu' := mem_base_bounds hBground huB
          have hv' := mem_base_bounds hBground hvB
          have hsumxy : x + y = u + v := by
            omega
          rcases IsSidon.eq_or_eq_swap_of_add_eq hSidon hxB hyB huB hvB hsumxy with
            hsame | hswap
          · rcases hsame with ⟨h1, h2⟩
            subst h1
            subst h2
            rcases hneq with h | h <;> contradiction
          · have hsame : N - x = N - u ∧ N - y = N - v := by
              rcases hswap with ⟨h1, h2⟩
              omega
            rcases hsame with ⟨h1, h2⟩
            have hxu : x = u := by omega
            have hyv : y = v := by omega
            subst hxu
            subst hyv
            rcases hneq with h | h <;> contradiction

/-- Hence the reflected-Sidon construction is almost Sidon. -/
theorem doubledFinset_almostSidon
    {N : ℕ} {B : Finset ℕ}
    (hSidon : IsSidonFinset B)
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) :
    AlmostSidonFinset (doubledFinset N B) := by
  intro m n hm hn
  rw [hasTwoSumReprs_doubled_forces_center hSidon hBground hm,
    hasTwoSumReprs_doubled_forces_center hSidon hBground hn]

/-- The reflected-Sidon construction produces an almost-Sidon set of size
exactly `2|B|` inside `{1, ..., N}`. -/
theorem doubledFinset_almostSidonInInterval
    {N : ℕ} {B : Finset ℕ}
    (hSidon : IsSidonFinset B)
    (hBground : ∀ b ∈ B, b ∈ ground (N / 3)) :
    AlmostSidonInInterval (doubledFinset N B) N ∧
      (doubledFinset N B).card = 2 * B.card := by
  refine ⟨⟨doubledFinset_almostSidon hSidon hBground, doubledFinset_subset_ground hBground⟩,
    card_doubledFinset hBground⟩

end AlmostSidonSets
