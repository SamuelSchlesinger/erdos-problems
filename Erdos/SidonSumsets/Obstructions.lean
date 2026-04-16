/- 
# Finite Obstruction Family for Lower-Isolated Sums

The naive finite strengthening of Erdős problem #152 is false: even among
finite Sidon sets, the lower-isolated region can be empty. This file gives an
explicit infinite family of such obstructions.

Reference: https://www.erdosproblems.com/152
-/
import Erdos.SidonSumsets.FastGrowth

namespace SidonSumsets

/-- The fast-growth sequence used in the obstruction family. -/
def obstructionSeq (n : ℕ) : ℕ :=
  2 * 4 ^ n

/-- The lower-isolated cutoff used for the `m`th obstruction. -/
def obstructionCutoff (m : ℕ) : ℕ :=
  2 * obstructionSeq m

/-- The large even tail of the `m`th obstruction family. -/
def obstructionTail (m : ℕ) : Set ℕ :=
  {x : ℕ | ∃ i ≤ m, x = obstructionSeq m + obstructionSeq i}

/-- The full obstruction family: `{0, 1}` plus a translated fast-growth tail. -/
def obstructionSet (m : ℕ) : Set ℕ :=
  ({0, 1} : Set ℕ) ∪ obstructionTail m

theorem obstructionSeq_strongGap : StrongGap obstructionSeq := by
  intro n
  dsimp [obstructionSeq]
  rw [pow_succ]
  have hpow : 0 < 4 ^ n := pow_pos (by decide : 0 < 4) _
  omega

theorem obstructionSeq_pos0 : 0 < obstructionSeq 0 := by
  norm_num [obstructionSeq]

theorem obstructionSeq_pos (n : ℕ) : 0 < obstructionSeq n :=
  pos_of_strongGap obstructionSeq_strongGap obstructionSeq_pos0 n

theorem two_le_obstructionSeq (n : ℕ) : 2 ≤ obstructionSeq n := by
  dsimp [obstructionSeq]
  have hpow : 0 < 4 ^ n := pow_pos (by decide : 0 < 4) _
  omega

theorem one_le_obstructionCutoff (m : ℕ) : 1 ≤ obstructionCutoff m := by
  dsimp [obstructionCutoff]
  have hpos : 0 < obstructionSeq m := obstructionSeq_pos m
  omega

/-- Sidon property passes to subsets. -/
theorem IsSidon.subset {A B : Set ℕ} (hA : IsSidon A) (hBA : B ⊆ A) : IsSidon B := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha₁₂ hb₁₂ hsum
  exact hA (hBA ha₁) (hBA ha₂) (hBA hb₁) (hBA hb₂) ha₁₂ hb₁₂ hsum

/-- Translating a Sidon range by a constant preserves the Sidon property. -/
theorem isSidon_range_add_const {u : ℕ → ℕ} (hU : IsSidon (Set.range u)) (c : ℕ) :
    IsSidon (Set.range fun n => c + u n) := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha₁₂ hb₁₂ hsum
  rcases ha₁ with ⟨i, rfl⟩
  rcases ha₂ with ⟨j, rfl⟩
  rcases hb₁ with ⟨k, rfl⟩
  rcases hb₂ with ⟨l, rfl⟩
  have hij : u i ≤ u j := (add_le_add_iff_left c).mp ha₁₂
  have hkl : u k ≤ u l := (add_le_add_iff_left c).mp hb₁₂
  have hsum' : u i + u j = u k + u l := by
    have hsum1 : u i + (c + u j) = u k + (c + u l) := by
      exact Nat.add_left_cancel (n := c) (by simpa [Nat.add_assoc] using hsum)
    have hsum2 : u i + u j + c = u k + u l + c := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum1
    omega
  rcases hU ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ ⟨l, rfl⟩ hij hkl hsum' with ⟨hik, hjl⟩
  constructor <;> simp [hik, hjl]

theorem obstructionTail_subset_translatedRange (m : ℕ) :
    obstructionTail m ⊆ Set.range (fun n => obstructionSeq m + obstructionSeq n) := by
  intro x hx
  rcases hx with ⟨i, _, rfl⟩
  exact ⟨i, rfl⟩

theorem obstructionTail_isSidon (m : ℕ) : IsSidon (obstructionTail m) := by
  let hRange : IsSidon (Set.range obstructionSeq) :=
    isSidon_range_of_strongGap obstructionSeq_strongGap
  let hTranslated : IsSidon (Set.range (fun n => obstructionSeq m + obstructionSeq n)) :=
    isSidon_range_add_const hRange (obstructionSeq m)
  exact hTranslated.subset (obstructionTail_subset_translatedRange m)

theorem mem_obstructionSet_iff {m x : ℕ} :
    x ∈ obstructionSet m ↔ x = 0 ∨ x = 1 ∨ x ∈ obstructionTail m := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr hx
  · intro hx
    rcases hx with rfl | rfl | hx
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inr hx

theorem obstructionTail_even {m x : ℕ} (hx : x ∈ obstructionTail m) : Even x := by
  rcases hx with ⟨i, _, rfl⟩
  refine ⟨4 ^ m + 4 ^ i, ?_⟩
  dsimp [obstructionSeq]
  ring

theorem obstructionTail_bounds {m x : ℕ} (hx : x ∈ obstructionTail m) :
    obstructionSeq m < x ∧ x ≤ obstructionCutoff m := by
  rcases hx with ⟨i, hi, rfl⟩
  constructor
  · have hpos : 0 < obstructionSeq i := obstructionSeq_pos i
    omega
  · have hi' : obstructionSeq i ≤ obstructionSeq m :=
      (strictMono_of_strongGap obstructionSeq_strongGap).monotone hi
    dsimp [obstructionCutoff]
    omega

theorem obstructionTail_gt_two {m x : ℕ} (hx : x ∈ obstructionTail m) : 2 < x := by
  have hsmall : 2 ≤ obstructionSeq m := two_le_obstructionSeq m
  have hbig : obstructionSeq m < x := (obstructionTail_bounds hx).1
  omega

theorem obstructionTail_gt_one {m x : ℕ} (hx : x ∈ obstructionTail m) : 1 < x := by
  have hbig : 2 < x := obstructionTail_gt_two hx
  omega

theorem obstructionTail_sum_large {m x y : ℕ}
    (hx : x ∈ obstructionTail m) (hy : y ∈ obstructionTail m) :
    obstructionCutoff m + 1 < x + y := by
  have hx' := obstructionTail_bounds hx
  have hy' := obstructionTail_bounds hy
  have hxs : obstructionSeq m + 1 ≤ x := Nat.succ_le_of_lt hx'.1
  have hys : obstructionSeq m + 1 ≤ y := Nat.succ_le_of_lt hy'.1
  dsimp [obstructionCutoff] at *
  omega

theorem obstructionSet_mem_of_tail {m x : ℕ} (hx : x ∈ obstructionTail m) :
    x ∈ obstructionSet m := by
  exact Or.inr hx

theorem zero_mem_obstructionSet (m : ℕ) : 0 ∈ obstructionSet m := by
  simp [obstructionSet]

theorem one_mem_obstructionSet (m : ℕ) : 1 ∈ obstructionSet m := by
  simp [obstructionSet]

theorem obstructionSet_le_cutoff {m x : ℕ} (hx : x ∈ obstructionSet m) :
    x ≤ obstructionCutoff m := by
  rcases mem_obstructionSet_iff.mp hx with rfl | rfl | hxTail
  · exact Nat.zero_le _
  · exact one_le_obstructionCutoff m
  · exact (obstructionTail_bounds hxTail).2

theorem eq_zero_or_one_of_mem_obstructionSet_of_le_two {m x : ℕ}
    (hx : x ∈ obstructionSet m) (hx2 : x ≤ 2) : x = 0 ∨ x = 1 := by
  rcases mem_obstructionSet_iff.mp hx with rfl | rfl | hxTail
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have hbig : 2 < x := obstructionTail_gt_two hxTail
    omega

theorem zero_mem_truncate_obstructionSet (m : ℕ) :
    0 ∈ truncateByValue (obstructionSet m) (obstructionCutoff m) := by
  exact ⟨zero_mem_obstructionSet m, Nat.zero_le _⟩

theorem one_mem_truncate_obstructionSet (m : ℕ) :
    1 ∈ truncateByValue (obstructionSet m) (obstructionCutoff m) := by
  exact ⟨one_mem_obstructionSet m, one_le_obstructionCutoff m⟩

theorem tail_mem_truncate_obstructionSet {m x : ℕ} (hx : x ∈ obstructionTail m) :
    x ∈ truncateByValue (obstructionSet m) (obstructionCutoff m) := by
  exact ⟨obstructionSet_mem_of_tail hx, (obstructionTail_bounds hx).2⟩

theorem middle_pair_structure {m a b : ℕ}
    (ha : a ∈ obstructionSet m) (hb : b ∈ obstructionSet m) (hab : a ≤ b)
    (hgt : 2 < a + b) (hle : a + b ≤ obstructionCutoff m + 1) :
    (a = 0 ∧ b ∈ obstructionTail m) ∨ (a = 1 ∧ b ∈ obstructionTail m) := by
  rcases mem_obstructionSet_iff.mp ha with rfl | rfl | haTail
  · rcases mem_obstructionSet_iff.mp hb with rfl | rfl | hbTail
    · omega
    · omega
    · exact Or.inl ⟨rfl, hbTail⟩
  · rcases mem_obstructionSet_iff.mp hb with rfl | rfl | hbTail
    · omega
    · omega
    · exact Or.inr ⟨rfl, hbTail⟩
  · rcases mem_obstructionSet_iff.mp hb with rfl | rfl | hbTail
    · have hbig : 1 < a := obstructionTail_gt_one haTail
      omega
    · have hbig : 1 < a := obstructionTail_gt_one haTail
      omega
    · have hlarge := obstructionTail_sum_large haTail hbTail
      omega

theorem middle_pair_unique {m a₁ a₂ b₁ b₂ : ℕ}
    (ha₁ : a₁ ∈ obstructionSet m) (ha₂ : a₂ ∈ obstructionSet m)
    (hb₁ : b₁ ∈ obstructionSet m) (hb₂ : b₂ ∈ obstructionSet m)
    (ha₁₂ : a₁ ≤ a₂) (hb₁₂ : b₁ ≤ b₂)
    (hsum : a₁ + a₂ = b₁ + b₂)
    (hgt : 2 < a₁ + a₂) (hle : a₁ + a₂ ≤ obstructionCutoff m + 1) :
    a₁ = b₁ ∧ a₂ = b₂ := by
  have ha :
      (a₁ = 0 ∧ a₂ ∈ obstructionTail m) ∨ (a₁ = 1 ∧ a₂ ∈ obstructionTail m) :=
    middle_pair_structure ha₁ ha₂ ha₁₂ hgt hle
  have hb :
      (b₁ = 0 ∧ b₂ ∈ obstructionTail m) ∨ (b₁ = 1 ∧ b₂ ∈ obstructionTail m) := by
    refine middle_pair_structure hb₁ hb₂ hb₁₂ ?_ ?_
    · simpa [hsum] using hgt
    · simpa [hsum] using hle
  rcases ha with ⟨rfl, ha₂Tail⟩ | ⟨rfl, ha₂Tail⟩
  · rcases hb with ⟨rfl, hb₂Tail⟩ | ⟨rfl, hb₂Tail⟩
    · constructor <;> omega
    · exfalso
      rcases obstructionTail_even ha₂Tail with ⟨ra, hra⟩
      rcases obstructionTail_even hb₂Tail with ⟨rb, hrb⟩
      rw [hra, hrb] at hsum
      omega
  · rcases hb with ⟨rfl, hb₂Tail⟩ | ⟨rfl, hb₂Tail⟩
    · exfalso
      rcases obstructionTail_even ha₂Tail with ⟨ra, hra⟩
      rcases obstructionTail_even hb₂Tail with ⟨rb, hrb⟩
      rw [hra, hrb] at hsum
      omega
    · constructor <;> omega

theorem obstructionSet_isSidon (m : ℕ) : IsSidon (obstructionSet m) := by
  have hTail : IsSidon (obstructionTail m) := obstructionTail_isSidon m
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ ha₁₂ hb₁₂ hsum
  by_cases hsmall : a₁ + a₂ ≤ 2
  · have ha₁Small : a₁ = 0 ∨ a₁ = 1 :=
      eq_zero_or_one_of_mem_obstructionSet_of_le_two ha₁ (by omega)
    have ha₂Small : a₂ = 0 ∨ a₂ = 1 :=
      eq_zero_or_one_of_mem_obstructionSet_of_le_two ha₂ (by omega)
    have hb₁Small : b₁ = 0 ∨ b₁ = 1 :=
      eq_zero_or_one_of_mem_obstructionSet_of_le_two hb₁ (by omega)
    have hb₂Small : b₂ = 0 ∨ b₂ = 1 :=
      eq_zero_or_one_of_mem_obstructionSet_of_le_two hb₂ (by omega)
    rcases ha₁Small with rfl | rfl <;>
      rcases ha₂Small with rfl | rfl <;>
      rcases hb₁Small with rfl | rfl <;>
      rcases hb₂Small with rfl | rfl <;> omega
  · by_cases hlarge : obstructionCutoff m + 1 < a₁ + a₂
    · have ha₁Tail : a₁ ∈ obstructionTail m := by
        rcases mem_obstructionSet_iff.mp ha₁ with rfl | rfl | ha₁Tail
        · have hbound : a₂ ≤ obstructionCutoff m := obstructionSet_le_cutoff ha₂
          omega
        · have hbound : a₂ ≤ obstructionCutoff m := obstructionSet_le_cutoff ha₂
          omega
        · exact ha₁Tail
      have ha₂Tail : a₂ ∈ obstructionTail m := by
        rcases mem_obstructionSet_iff.mp ha₂ with rfl | rfl | ha₂Tail
        · have hbound : a₁ ≤ obstructionCutoff m := obstructionSet_le_cutoff ha₁
          omega
        · have hbound : a₁ ≤ obstructionCutoff m := obstructionSet_le_cutoff ha₁
          omega
        · exact ha₂Tail
      have hb₁Tail : b₁ ∈ obstructionTail m := by
        rcases mem_obstructionSet_iff.mp hb₁ with rfl | rfl | hb₁Tail
        · have hbound : b₂ ≤ obstructionCutoff m := obstructionSet_le_cutoff hb₂
          omega
        · have hbound : b₂ ≤ obstructionCutoff m := obstructionSet_le_cutoff hb₂
          omega
        · exact hb₁Tail
      have hb₂Tail : b₂ ∈ obstructionTail m := by
        rcases mem_obstructionSet_iff.mp hb₂ with rfl | rfl | hb₂Tail
        · have hbound : b₁ ≤ obstructionCutoff m := obstructionSet_le_cutoff hb₁
          omega
        · have hbound : b₁ ≤ obstructionCutoff m := obstructionSet_le_cutoff hb₁
          omega
        · exact hb₂Tail
      exact hTail ha₁Tail ha₂Tail hb₁Tail hb₂Tail ha₁₂ hb₁₂ hsum
    · have hmidGt : 2 < a₁ + a₂ := by omega
      have hmidLe : a₁ + a₂ ≤ obstructionCutoff m + 1 := by omega
      exact middle_pair_unique ha₁ ha₂ hb₁ hb₂ ha₁₂ hb₁₂ hsum hmidGt hmidLe

theorem obstructionSet_no_lowerIsolated (m : ℕ) :
    lowerIsolated (obstructionSet m) (obstructionCutoff m) = ∅ := by
  ext s
  constructor
  · intro hs
    change False
    rcases hs with ⟨hslt, hIso⟩
    rcases hIso with ⟨hsmem, hpred, hsucc⟩
    rcases hsmem with ⟨a, ha, b, hb, habs⟩
    have haA : a ∈ obstructionSet m := ha.1
    have hbA : b ∈ obstructionSet m := hb.1
    subst s
    by_cases haTail : a ∈ obstructionTail m
    · by_cases hbTail : b ∈ obstructionTail m
      · have hlarge := obstructionTail_sum_large haTail hbTail
        omega
      · rcases mem_obstructionSet_iff.mp hbA with rfl | rfl | hbTail'
        · exact hsucc ⟨1, one_mem_truncate_obstructionSet m, a,
            tail_mem_truncate_obstructionSet haTail, by omega⟩
        · exact hpred ⟨0, zero_mem_truncate_obstructionSet m, a,
            tail_mem_truncate_obstructionSet haTail, by omega⟩
        · exact False.elim (hbTail hbTail')
    · rcases mem_obstructionSet_iff.mp haA with rfl | rfl | haTail'
      · by_cases hbTail : b ∈ obstructionTail m
        · exact hsucc ⟨1, one_mem_truncate_obstructionSet m, b,
            tail_mem_truncate_obstructionSet hbTail, by omega⟩
        · rcases mem_obstructionSet_iff.mp hbA with rfl | rfl | hbTail'
          · exact hsucc ⟨0, zero_mem_truncate_obstructionSet m, 1,
              one_mem_truncate_obstructionSet m, by omega⟩
          · exact hpred ⟨0, zero_mem_truncate_obstructionSet m, 0,
              zero_mem_truncate_obstructionSet m, by omega⟩
          · exact False.elim (hbTail hbTail')
      · by_cases hbTail : b ∈ obstructionTail m
        · exact hpred ⟨0, zero_mem_truncate_obstructionSet m, b,
            tail_mem_truncate_obstructionSet hbTail, by omega⟩
        · rcases mem_obstructionSet_iff.mp hbA with rfl | rfl | hbTail'
          · exact hsucc ⟨1, one_mem_truncate_obstructionSet m, 1,
              one_mem_truncate_obstructionSet m, by omega⟩
          · exact hpred ⟨0, zero_mem_truncate_obstructionSet m, 1,
              one_mem_truncate_obstructionSet m, by omega⟩
          · exact False.elim (hbTail hbTail')
      · exact False.elim (haTail haTail')
  · intro hs
    simp at hs

/-- Explicit obstruction family: for every `m`, the set `obstructionSet m` is
Sidon but has no lower-isolated sums below the cutoff `obstructionCutoff m`. -/
theorem finite_obstruction_family (m : ℕ) :
    IsSidon (obstructionSet m) ∧ lowerIsolated (obstructionSet m) (obstructionCutoff m) = ∅ := by
  exact ⟨obstructionSet_isSidon m, obstructionSet_no_lowerIsolated m⟩

end SidonSumsets
