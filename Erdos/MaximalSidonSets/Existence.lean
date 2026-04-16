/- 
# Existence of Maximal Sidon Extensions

Since `{1, ..., N}` is finite, every Sidon subset can be extended to a maximal
Sidon subset inside the same interval by choosing a Sidon extension of maximal
cardinality.
-/
import Erdos.MaximalSidonSets.Statement

namespace MaximalSidonSets

/-- Sidon supersets of `A` lying inside `{1, ..., N}`. -/
noncomputable def extensionCandidates (A : Finset ℕ) (N : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (ground N).powerset.filter fun B => A ⊆ B ∧ IsSidonFinset B

@[simp] theorem mem_extensionCandidates_iff {A B : Finset ℕ} {N : ℕ} :
    B ∈ extensionCandidates A N ↔ A ⊆ B ∧ SidonInInterval B N := by
  constructor
  · intro h
    simp only [extensionCandidates, Finset.mem_filter, Finset.mem_powerset] at h
    exact ⟨h.2.1, h.2.2, h.1⟩
  · rintro ⟨hAB, hSidonB, hGroundB⟩
    simp only [extensionCandidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hGroundB, hAB, hSidonB⟩

/-- Any Sidon set in `{1, ..., N}` belongs to its own extension-candidate family. -/
theorem self_mem_extensionCandidates {A : Finset ℕ} {N : ℕ} (hA : SidonInInterval A N) :
    A ∈ extensionCandidates A N := by
  exact mem_extensionCandidates_iff.mpr ⟨subset_rfl, hA⟩

/-- Every Sidon set in `{1, ..., N}` extends to a maximal Sidon set in the same
interval. -/
theorem exists_maximalSidonInInterval_extends {A : Finset ℕ} {N : ℕ}
    (hA : SidonInInterval A N) :
    ∃ B : Finset ℕ, A ⊆ B ∧ IsMaximalSidonInInterval B N := by
  classical
  obtain ⟨B, hBmem, hBmax⟩ :=
    Finset.exists_max_image (extensionCandidates A N) Finset.card
      ⟨A, self_mem_extensionCandidates hA⟩
  have hB : A ⊆ B ∧ SidonInInterval B N := mem_extensionCandidates_iff.mp hBmem
  refine ⟨B, hB.1, hB.2, ?_⟩
  intro x hx hxB hSidonInsert
  have hInsert : A ⊆ insert x B := by
    exact hB.1.trans (Finset.subset_insert _ _)
  have hInsertGround : ∀ b ∈ insert x B, b ∈ ground N := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hbB
    · exact hx
    · exact hB.2.2 b hbB
  have hInsertMem : insert x B ∈ extensionCandidates A N := by
    exact mem_extensionCandidates_iff.mpr ⟨hInsert, ⟨hSidonInsert, hInsertGround⟩⟩
  have hle : (insert x B).card ≤ B.card := hBmax (insert x B) hInsertMem
  have hlt : B.card < (insert x B).card := by simp [hxB]
  omega

/-- In particular, every interval `{1, ..., N}` admits a maximal Sidon subset. -/
theorem exists_maximalSidonInInterval (N : ℕ) :
    ∃ B : Finset ℕ, IsMaximalSidonInInterval B N := by
  have hEmpty : SidonInInterval (∅ : Finset ℕ) N := by
    refine ⟨?_, ?_⟩
    · intro a₁ a₂ b₁ b₂ ha₁ _ _ _ _ _ _
      simp at ha₁
    · intro a ha
      simp at ha
  rcases exists_maximalSidonInInterval_extends hEmpty with ⟨B, _, hB⟩
  exact ⟨B, hB⟩

end MaximalSidonSets
