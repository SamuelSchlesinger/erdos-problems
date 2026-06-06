import Erdos.DivisibilityAvoidingSets.Elementary

/-!
# Tagged block templates for Erdős problem #12

This file isolates the main combinatorial mechanism used in the dense
construction for problem #12.  We build an avoiding set as an ordered union of
finite blocks.  Each block `i` is internally avoiding, every member of block
`i` is divisible by a tag `q i`, and all later blocks are congruent to `1`
modulo `q i`.  Then a forbidden triple whose smallest element lies in block
`i` is impossible: the two larger terms are either both in block `i`, handled
internally, or their sum is congruent to `1` or `2` modulo `q i`.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- The finite arithmetic-progression block
`{r + M * (T + t) | 0 ≤ t < L}`. -/
def apBlock (r M T L : ℕ) : Set ℕ :=
  {n | ∃ t : ℕ, t < L ∧ n = r + M * (T + t)}

/-- The first element of an arithmetic-progression block. -/
def apMin (r M T : ℕ) : ℕ :=
  r + M * T

/-- The last possible element of an arithmetic-progression block.  For
`L = 0` this is harmless junk; membership in `apBlock r M T 0` is impossible. -/
def apMax (r M T L : ℕ) : ℕ :=
  r + M * (T + (L - 1))

/-- The finset version of `apBlock`, useful for exact cardinality counts. -/
def apBlockFinset (r M T L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun t => r + M * (T + t)

@[simp] theorem mem_apBlockFinset {r M T L n : ℕ} :
    n ∈ apBlockFinset r M T L ↔ n ∈ apBlock r M T L := by
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩

/-- The first element is a lower bound for an arithmetic-progression block. -/
theorem apMin_le_of_mem_apBlock {r M T L n : ℕ} (hn : n ∈ apBlock r M T L) :
    apMin r M T ≤ n := by
  rcases hn with ⟨t, _ht, rfl⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_left M (Nat.le_add_right T t)) r

/-- The last possible element is an upper bound for an arithmetic-progression
block. -/
theorem le_apMax_of_mem_apBlock {r M T L n : ℕ} (hn : n ∈ apBlock r M T L) :
    n ≤ apMax r M T L := by
  rcases hn with ⟨t, ht, rfl⟩
  have htle : t ≤ L - 1 := Nat.le_pred_of_lt ht
  exact Nat.add_le_add_left (Nat.mul_le_mul_left M (Nat.add_le_add_left htle T)) r

/-- An arithmetic-progression block has exactly the advertised cardinality. -/
theorem apBlockFinset_card {r M T L : ℕ} (hM : 0 < M) :
    (apBlockFinset r M T L).card = L := by
  unfold apBlockFinset
  rw [Finset.card_image_of_injective _]
  · simp
  · intro x y hxy
    have hmul : M * (T + x) = M * (T + y) := Nat.add_left_cancel hxy
    have hT : T + x = T + y := mul_left_cancel₀ hM.ne' hmul
    omega

/-- A sufficiently narrow arithmetic-progression block is internally avoiding:
if all elements lie in an interval with `2 * max < 3 * min`, no larger pair can
sum to a multiple of the smallest element. -/
theorem avoidingSet_apBlock_of_narrow {r M T L : ℕ}
    (hmin : 0 < apMin r M T)
    (hnarrow : 2 * apMax r M T L < 3 * apMin r M T) :
    AvoidingSet (apBlock r M T L) := by
  intro a b c h
  rcases h with ⟨ha, hb, hc, _hab, _hac, _hbc, hadvd, haltb, haltc⟩
  have hmina : apMin r M T ≤ a := apMin_le_of_mem_apBlock ha
  have hbmax : b ≤ apMax r M T L := le_apMax_of_mem_apBlock hb
  have hcmax : c ≤ apMax r M T L := le_apMax_of_mem_apBlock hc
  have ha_pos : 0 < a := hmin.trans_le hmina
  have hlow : 2 * a < b + c := by omega
  have hhigh : b + c < 3 * a := by
    have hbcmax : b + c ≤ 2 * apMax r M T L := by omega
    have hmax_lt : 2 * apMax r M T L < 3 * a := by
      exact hnarrow.trans_le (Nat.mul_le_mul_left 3 hmina)
    omega
  rcases hadvd with ⟨d, hd⟩
  have hd_gt_two : 2 < d := by
    have hmul : a * 2 < a * d := by
      simpa [two_mul, mul_comm, hd] using hlow
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hd_lt_three : d < 3 := by
    have hmul : a * d < a * 3 := by
      simpa [mul_comm, hd] using hhigh
    exact Nat.lt_of_mul_lt_mul_left hmul
  omega

/-- Congruence of an arithmetic-progression block is inherited from its
residue when the step is a multiple of the modulus. -/
theorem modEq_of_mem_apBlock {r M T L n q v : ℕ}
    (hM : q ∣ M) (hr : r ≡ v [MOD q]) (hn : n ∈ apBlock r M T L) :
    n ≡ v [MOD q] := by
  rcases hn with ⟨t, _ht, rfl⟩
  have hstep : M * (T + t) ≡ 0 [MOD q] :=
    (dvd_mul_of_dvd_left hM (T + t)).modEq_zero_nat
  simpa using hr.add hstep

/-- An ordered tagged family of avoiding blocks has an avoiding union. -/
theorem avoidingSet_iUnion_of_tagged_blocks {B : ℕ → Set ℕ} {q : ℕ → ℕ}
    (horder : ∀ ⦃i j x y : ℕ⦄, i < j → x ∈ B i → y ∈ B j → x < y)
    (hsame : ∀ i, AvoidingSet (B i))
    (htag_zero : ∀ ⦃i x : ℕ⦄, x ∈ B i → q i ∣ x)
    (htag_one : ∀ ⦃i j x : ℕ⦄, i < j → x ∈ B j → x ≡ 1 [MOD q i])
    (hq_not_dvd_one : ∀ i, ¬ q i ∣ 1)
    (hq_not_dvd_two : ∀ i, ¬ q i ∣ 2) :
    AvoidingSet (⋃ i, B i) := by
  intro a b c h
  rcases h with ⟨ha, hb, hc, hab, hac, hbc, hadvd, haltb, haltc⟩
  rcases Set.mem_iUnion.mp ha with ⟨i, hai⟩
  rcases Set.mem_iUnion.mp hb with ⟨j, hbj⟩
  rcases Set.mem_iUnion.mp hc with ⟨k, hck⟩
  have hq_sum : q i ∣ b + c := (htag_zero hai).trans hadvd
  have hsum_zero : b + c ≡ 0 [MOD q i] := hq_sum.modEq_zero_nat
  have hij_le : i ≤ j := by
    by_contra hle
    have hji : j < i := Nat.lt_of_not_ge hle
    have hb_lt_a : b < a := horder hji hbj hai
    exact (not_lt_of_ge haltb.le) hb_lt_a
  have hik_le : i ≤ k := by
    by_contra hle
    have hki : k < i := Nat.lt_of_not_ge hle
    have hc_lt_a : c < a := horder hki hck hai
    exact (not_lt_of_ge haltc.le) hc_lt_a
  rcases lt_or_eq_of_le hij_le with hij | rfl
  · rcases lt_or_eq_of_le hik_le with hik | rfl
    · have hb_one : b ≡ 1 [MOD q i] := htag_one hij hbj
      have hc_one : c ≡ 1 [MOD q i] := htag_one hik hck
      have hsum_two : b + c ≡ 2 [MOD q i] := by
        simpa using hb_one.add hc_one
      have htwo_zero : 2 ≡ 0 [MOD q i] := hsum_two.symm.trans hsum_zero
      exact hq_not_dvd_two i (Nat.modEq_zero_iff_dvd.mp htwo_zero)
    · have hb_one : b ≡ 1 [MOD q i] := htag_one hij hbj
      have hc_zero : c ≡ 0 [MOD q i] := (htag_zero hck).modEq_zero_nat
      have hsum_one : b + c ≡ 1 [MOD q i] := by
        simpa using hb_one.add hc_zero
      have hone_zero : 1 ≡ 0 [MOD q i] := hsum_one.symm.trans hsum_zero
      exact hq_not_dvd_one i (Nat.modEq_zero_iff_dvd.mp hone_zero)
  · rcases lt_or_eq_of_le hik_le with hik | rfl
    · have hb_zero : b ≡ 0 [MOD q i] := (htag_zero hbj).modEq_zero_nat
      have hc_one : c ≡ 1 [MOD q i] := htag_one hik hck
      have hsum_one : b + c ≡ 1 [MOD q i] := by
        simpa using hb_zero.add hc_one
      have hone_zero : 1 ≡ 0 [MOD q i] := hsum_one.symm.trans hsum_zero
      exact hq_not_dvd_one i (Nat.modEq_zero_iff_dvd.mp hone_zero)
    · exact hsame i ⟨hai, hbj, hck, hab, hac, hbc, hadvd, haltb, haltc⟩

end DivisibilityAvoidingSets
