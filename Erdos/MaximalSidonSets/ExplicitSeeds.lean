/- 
# Explicit Geometric Seeds for Maximal Sidon Sets

The geometric progression `1, 4, 4², ..., 4^m` is a finite Sidon set because
its ambient infinite range has strong gaps. Therefore, whenever `4^m ≤ N`, this
prefix lies inside `{1, ..., N}` and extends to a maximal Sidon subset of the
interval.
-/
import Erdos.MaximalSidonSets.Existence
import Erdos.SidonSumsets.FastGrowth

namespace MaximalSidonSets

open SidonSumsets

/-- The first `m + 1` values of a sequence, viewed as a finite set. -/
def strongGapPrefix (u : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).image u

/-- A strong-gap prefix has the expected cardinality. -/
theorem strongGapPrefix_card {u : ℕ → ℕ} (hgap : StrongGap u) (m : ℕ) :
    (strongGapPrefix u m).card = m + 1 := by
  unfold strongGapPrefix
  calc
    ((Finset.range (m + 1)).image u).card = (Finset.range (m + 1)).card := by
      exact Finset.card_image_of_injective _ (strictMono_of_strongGap hgap).injective
    _ = m + 1 := Finset.card_range (m + 1)

/-- Any finite prefix of a strong-gap sequence is Sidon. -/
theorem strongGapPrefix_isSidon {u : ℕ → ℕ} (hgap : StrongGap u) (m : ℕ) :
    IsSidonFinset (strongGapPrefix u m) := by
  let hRange : IsSidon (Set.range u) := isSidon_range_of_strongGap hgap
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha₁₂ hb₁₂ hsum
  exact hRange
    (by
      rcases Finset.mem_image.mp (Finset.mem_coe.mp ha₁) with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩)
    (by
      rcases Finset.mem_image.mp (Finset.mem_coe.mp ha₂) with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩)
    (by
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hb₁) with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩)
    (by
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hb₂) with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩)
    ha₁₂ hb₁₂ hsum

/-- If `u` has strong gaps and starts positively, then every finite prefix lies
inside any interval containing its last term. -/
theorem strongGapPrefix_sidonInInterval {u : ℕ → ℕ}
    (hgap : StrongGap u) (h0 : 0 < u 0) {m N : ℕ} (hN : u m ≤ N) :
    SidonInInterval (strongGapPrefix u m) N := by
  refine ⟨strongGapPrefix_isSidon hgap m, ?_⟩
  let hmono : Monotone u := (strictMono_of_strongGap hgap).monotone
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
  have hi' : i ≤ m := by simpa using Finset.mem_range.mp hi
  exact mem_ground.mpr ⟨pos_of_strongGap hgap h0 i, le_trans (hmono hi') hN⟩

/-- Hence every positive strong-gap prefix extends to a maximal Sidon set in
any interval containing its last term. -/
theorem exists_maximalSidonInInterval_extends_strongGapPrefix {u : ℕ → ℕ}
    (hgap : StrongGap u) (h0 : 0 < u 0) {m N : ℕ} (hN : u m ≤ N) :
    ∃ A : Finset ℕ, strongGapPrefix u m ⊆ A ∧ IsMaximalSidonInInterval A N := by
  exact exists_maximalSidonInInterval_extends
    (strongGapPrefix_sidonInInterval hgap h0 hN)

/-- Therefore such an interval admits a maximal Sidon set whose cardinality is
at least the length of the chosen strong-gap prefix. -/
theorem exists_maximalSidonInInterval_card_ge_strongGapPrefix {u : ℕ → ℕ}
    (hgap : StrongGap u) (h0 : 0 < u 0) {m N : ℕ} (hN : u m ≤ N) :
    ∃ A : Finset ℕ, IsMaximalSidonInInterval A N ∧ m + 1 ≤ A.card := by
  rcases exists_maximalSidonInInterval_extends_strongGapPrefix hgap h0 hN with
    ⟨A, hsub, hA⟩
  refine ⟨A, hA, ?_⟩
  simpa [strongGapPrefix_card hgap m] using Finset.card_le_card hsub

/-- The finite geometric seed `{1, 4, 4², ..., 4^m}`. -/
def powFourPrefix (m : ℕ) : Finset ℕ :=
  strongGapPrefix (fun n : ℕ => 4 ^ n) m

/-- The powers of `4` have strong gaps. -/
theorem powFour_strongGap : StrongGap (fun n : ℕ => 4 ^ n) := by
  intro n
  change 2 * 4 ^ n + 1 < 4 ^ (n + 1)
  rw [pow_succ]
  have hpow : 0 < 4 ^ n := pow_pos (by decide : 0 < 4) _
  omega

/-- The geometric seed has the expected cardinality. -/
theorem powFourPrefix_card (m : ℕ) : (powFourPrefix m).card = m + 1 := by
  simpa [powFourPrefix] using strongGapPrefix_card powFour_strongGap m

/-- The geometric seed is Sidon. -/
theorem powFourPrefix_isSidon (m : ℕ) : IsSidonFinset (powFourPrefix m) := by
  simpa [powFourPrefix] using strongGapPrefix_isSidon powFour_strongGap m

/-- If `4^m ≤ N`, then the geometric seed lies inside `{1, ..., N}`. -/
theorem powFourPrefix_sidonInInterval {m N : ℕ} (hN : 4 ^ m ≤ N) :
    SidonInInterval (powFourPrefix m) N := by
  simpa [powFourPrefix] using
    strongGapPrefix_sidonInInterval powFour_strongGap (by norm_num : 0 < (4 : ℕ) ^ 0) hN

/-- Any interval large enough to contain the geometric seed admits a maximal
Sidon extension of that seed. -/
theorem exists_maximalSidonInInterval_extends_powFourPrefix {m N : ℕ}
    (hN : 4 ^ m ≤ N) :
    ∃ A : Finset ℕ, powFourPrefix m ⊆ A ∧ IsMaximalSidonInInterval A N := by
  simpa [powFourPrefix] using
    exists_maximalSidonInInterval_extends_strongGapPrefix
      powFour_strongGap (by norm_num : 0 < (4 : ℕ) ^ 0) hN

/-- Hence such an interval admits a maximal Sidon set of cardinality at least
`m + 1`. -/
theorem exists_maximalSidonInInterval_card_ge_powFourPrefix {m N : ℕ}
    (hN : 4 ^ m ≤ N) :
    ∃ A : Finset ℕ, IsMaximalSidonInInterval A N ∧ m + 1 ≤ A.card := by
  simpa [powFourPrefix] using
    exists_maximalSidonInInterval_card_ge_strongGapPrefix
      powFour_strongGap (by norm_num : 0 < (4 : ℕ) ^ 0) hN

end MaximalSidonSets
