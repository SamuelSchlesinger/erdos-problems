/- 
# Fast-Growth Sidon Sequences

A rapidly growing sequence forces stable isolated doubles in its sumset. This
gives a concrete infinite family satisfying the isolated-sums conclusion
suggested by Erdős problem #152.

Reference: https://www.erdosproblems.com/152
-/
import Erdos.SidonSumsets.Stability

namespace SidonSumsets

/-- A sequence has a strong gap if each term lies strictly above `2 * u n + 1`. -/
def StrongGap (u : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 2 * u n + 1 < u (n + 1)

/-- Strong gaps force strict monotonicity. -/
theorem strictMono_of_strongGap {u : ℕ → ℕ} (hgap : StrongGap u) : StrictMono u := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have h := hgap n
  omega

/-- A positive initial term keeps the whole sequence positive. -/
theorem pos_of_strongGap {u : ℕ → ℕ} (hgap : StrongGap u) (h0 : 0 < u 0) (n : ℕ) :
    0 < u n := by
  have hmono := (strictMono_of_strongGap hgap).monotone
  exact lt_of_lt_of_le h0 (hmono (Nat.zero_le n))

/-- Under strong gaps, the `n`th term dominates its index. -/
theorem index_succ_le_term_of_strongGap {u : ℕ → ℕ} (hgap : StrongGap u) (h0 : 0 < u 0) :
    ∀ n : ℕ, n + 1 ≤ u n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      have h := hgap n
      omega

/-- Strong gaps prevent the right neighbor of a doubled term from appearing in
the sumset. -/
theorem double_succ_not_mem_sumset_of_strongGap {u : ℕ → ℕ} (hgap : StrongGap u) (n : ℕ) :
    2 * u n + 1 ∉ sumset (Set.range u) := by
  let hmono : Monotone u := (strictMono_of_strongGap hgap).monotone
  intro hs
  rcases hs with ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, hsum⟩
  have hordered :
      ∀ ⦃x y : ℕ⦄, x ≤ y → u x + u y ≠ 2 * u n + 1 := by
    intro x y hxy
    by_cases hyn : y ≤ n
    · have hx_le : u x ≤ u n := hmono (le_trans hxy hyn)
      have hy_le : u y ≤ u n := hmono hyn
      omega
    · have hny : n < y := Nat.lt_of_not_ge hyn
      have hy_big : u (n + 1) ≤ u y := hmono (Nat.succ_le_of_lt hny)
      have h := hgap n
      omega
  rcases le_total i j with hij | hji
  · exact hordered hij hsum
  · exact hordered hji (by simpa [Nat.add_comm] using hsum)

/-- Strong gaps also prevent the left neighbor of a doubled term from appearing
in the sumset. -/
theorem double_pred_not_mem_sumset_of_strongGap {u : ℕ → ℕ}
    (hgap : StrongGap u) (h0 : 0 < u 0) (n : ℕ) :
    2 * u n - 1 ∉ sumset (Set.range u) := by
  let hstrict : StrictMono u := strictMono_of_strongGap hgap
  let hmono : Monotone u := hstrict.monotone
  have hpos : 0 < u n := pos_of_strongGap hgap h0 n
  intro hs
  rcases hs with ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, hsum⟩
  have hordered :
      ∀ ⦃x y : ℕ⦄, x ≤ y → u x + u y ≠ 2 * u n - 1 := by
    intro x y hxy
    by_cases hyn : y < n
    · have hxy' : u x ≤ u y := hmono hxy
      have hy_lt : u y < u n := hstrict hyn
      omega
    · by_cases hy_eq : y = n
      · rw [hy_eq] at ⊢
        by_cases hxn : x = n
        · subst hxn
          omega
        · have hxy' : x ≤ n := by simpa [hy_eq] using hxy
          have hxn' : x < n := lt_of_le_of_ne hxy' hxn
          have hx_small_step : u x + 1 < u n := by
            have hx_gap : 2 * u x + 1 < u (x + 1) := hgap x
            have hnext : x + 1 ≤ n := Nat.succ_le_of_lt hxn'
            have hnext_le : u (x + 1) ≤ u n := hmono hnext
            omega
          omega
      · have hny : n < y := lt_of_not_ge (by
            intro hle
            exact hy_eq (le_antisymm hle (Nat.le_of_not_gt hyn)))
        have hy_big : u (n + 1) ≤ u y := hmono (Nat.succ_le_of_lt hny)
        have h := hgap n
        omega
  rcases le_total i j with hij | hji
  · exact hordered hij hsum
  · exact hordered hji (by simpa [Nat.add_comm] using hsum)

/-- Every doubled term of a positive strong-gap sequence is isolated in the full
sumset. -/
theorem double_isolated_of_strongGap {u : ℕ → ℕ}
    (hgap : StrongGap u) (h0 : 0 < u 0) (n : ℕ) :
    Isolated (sumset (Set.range u)) (2 * u n) := by
  refine ⟨?_, double_pred_not_mem_sumset_of_strongGap hgap h0 n,
    double_succ_not_mem_sumset_of_strongGap hgap n⟩
  exact ⟨u n, ⟨n, rfl⟩, u n, ⟨n, rfl⟩, by ring⟩

/-- The isolated doubles coming from a strong-gap sequence already appear below
the next value cutoff, hence are stable lower-isolated witnesses. -/
theorem double_mem_lowerIsolated_of_strongGap {u : ℕ → ℕ}
    (hgap : StrongGap u) (h0 : 0 < u 0) (n : ℕ) :
    2 * u n ∈ lowerIsolated (Set.range u) (u (n + 1)) := by
  refine ⟨by
      have h := hgap n
      omega, ?_⟩
  exact (isolated_iff_isolated_truncateByValue_of_lt (A := Set.range u)
    (N := u (n + 1)) (s := 2 * u n) (by
      have h := hgap n
      omega)).mpr (double_isolated_of_strongGap hgap h0 n)

/-- Any positive strong-gap sequence yields arbitrarily large stable
lower-isolated witnesses. -/
theorem arbitrarily_large_lowerIsolated_of_strongGap {u : ℕ → ℕ}
    (hgap : StrongGap u) (h0 : 0 < u 0) :
    ∀ K : ℕ, ∃ N s, K ≤ s ∧ s ∈ lowerIsolated (Set.range u) N := by
  intro K
  refine ⟨u (K + 1), 2 * u K, ?_, double_mem_lowerIsolated_of_strongGap hgap h0 K⟩
  have hidx : K + 1 ≤ u K := index_succ_le_term_of_strongGap hgap h0 K
  omega

/-- The range of a positive strong-gap sequence has infinitely many isolated
sums. -/
theorem infinite_isolated_range_of_strongGap {u : ℕ → ℕ}
    (hgap : StrongGap u) (h0 : 0 < u 0) :
    {s : ℕ | Isolated (sumset (Set.range u)) s}.Infinite := by
  exact infinite_isolated_of_arbitrarily_large_lowerIsolated
    (arbitrarily_large_lowerIsolated_of_strongGap hgap h0)

/-- Positive strong-gap sequences are Sidon. -/
theorem isSidon_range_of_strongGap {u : ℕ → ℕ} (hgap : StrongGap u) :
    IsSidon (Set.range u) := by
  let hstrict : StrictMono u := strictMono_of_strongGap hgap
  let hmono : Monotone u := hstrict.monotone
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha₁₂ hb₁₂ hsum
  rcases ha₁ with ⟨i, rfl⟩
  rcases ha₂ with ⟨j, rfl⟩
  rcases hb₁ with ⟨k, rfl⟩
  rcases hb₂ with ⟨l, rfl⟩
  have hij : i ≤ j := by
    by_contra hij
    exact (not_le_of_gt (hstrict (Nat.lt_of_not_ge hij))) ha₁₂
  have hkl : k ≤ l := by
    by_contra hkl
    exact (not_le_of_gt (hstrict (Nat.lt_of_not_ge hkl))) hb₁₂
  have hjl : j = l := by
    rcases lt_trichotomy j l with hjl | hjl | hlj
    · have hbig : u (j + 1) ≤ u l := hmono (Nat.succ_le_of_lt hjl)
      have hgapj := hgap j
      have hi_le : u i ≤ u j := hmono hij
      omega
    · exact hjl
    · have hbig : u (l + 1) ≤ u j := hmono (Nat.succ_le_of_lt hlj)
      have hgapl := hgap l
      have hk_le : u k ≤ u l := hmono hkl
      omega
  subst hjl
  have hik : i = k := hstrict.injective (Nat.add_right_cancel hsum)
  subst hik
  exact ⟨rfl, rfl⟩

end SidonSumsets
