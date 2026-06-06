import Erdos.DivisibilityAvoidingSets.BertrandTags
import Erdos.DivisibilityAvoidingSets.ReciprocalCriteria

/-!
# An explicit Bertrand-prime construction for Erdős problem #12

This file instantiates the tagged arithmetic-progression block criterion with
the Bertrand prime tags from `BertrandTags`.  The block lengths are
`L i = 2^((i + 10)^4)`, the block starts are `4 * L i + 1`, and the endpoint
for block `i` is `6 * M i * L i`, where `M i` is the product of tags up to
`i`.

The quartic exponent is deliberately overpowered.  Bertrand's postulate gives
`q i ≤ 2^(i+2)`, hence `M i ≤ 2^((i+2)^2)`, and the quartic margin absorbs this
quadratic modulus growth between consecutive blocks.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- The exponent used for the explicit block length. -/
def bertrandScaleExp (i : ℕ) : ℕ :=
  (i + 10) ^ 4

/-- The length of the `i`th block. -/
def bertrandLength (i : ℕ) : ℕ :=
  2 ^ bertrandScaleExp i

/-- The start parameter for the `i`th AP block.  The choice `4L+1` makes each
block narrow enough to be internally avoiding. -/
def bertrandStart (i : ℕ) : ℕ :=
  4 * bertrandLength i + 1

/-- A convenient endpoint above the `i`th block. -/
noncomputable def bertrandEndpoint (i : ℕ) : ℕ :=
  6 * tagModulus i * bertrandLength i

theorem tagModulus_succ (i : ℕ) :
    tagModulus (i + 1) = tagModulus i * oddPrimeTag (i + 1) := by
  unfold tagModulus
  rw [Finset.prod_range_succ]

/-- The Bertrand tag modulus has at least geometric growth: every tag is at
least `3`, and `tagModulus i` contains `i + 1` tags. -/
theorem three_pow_succ_le_tagModulus (i : ℕ) :
    3 ^ (i + 1) ≤ tagModulus i := by
  unfold tagModulus
  calc
    3 ^ (i + 1) = ∏ _j ∈ Finset.range (i + 1), (3 : ℕ) := by
      rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ Finset.range (i + 1), oddPrimeTag j := by
      exact Finset.prod_le_prod
        (fun _ _ => by norm_num)
        (fun j _ => by
          have hlt : 2 < oddPrimeTag j := oddPrimeTag_two_lt j
          omega)

/-- The reciprocal moduli in the Bertrand-prime construction are summable.
This is the analytic cost of using fresh CRT protection at every block. -/
theorem summable_inv_tagModulus :
    Summable fun i : ℕ => (1 : ℝ) / (tagModulus i : ℝ) := by
  refine Summable.of_nonneg_of_le
    (f := fun i : ℕ => (1 / 3 : ℝ) ^ (i + 1))
    (g := fun i : ℕ => (1 : ℝ) / (tagModulus i : ℝ))
    (fun i => by positivity) ?_ ?_
  · intro i
    have hle_nat : 3 ^ (i + 1) ≤ tagModulus i :=
      three_pow_succ_le_tagModulus i
    have hle_real : ((3 : ℝ) ^ (i + 1)) ≤ (tagModulus i : ℝ) := by
      exact_mod_cast hle_nat
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (i + 1) := by positivity
    have h := one_div_le_one_div_of_le hpos hle_real
    simpa [one_div, inv_pow] using h
  · have hgeo : Summable fun i : ℕ => (1 / 3 : ℝ) ^ i :=
      summable_geometric_of_lt_one
        (by norm_num : 0 ≤ (1 / 3 : ℝ))
        (by norm_num : (1 / 3 : ℝ) < 1)
    simpa [Nat.add_comm] using (summable_nat_add_iff 1).mpr hgeo

/-- Bertrand's recursive tags are bounded by a simple power of two. -/
theorem oddPrimeTag_le_two_pow (i : ℕ) :
    oddPrimeTag i ≤ 2 ^ (i + 2) := by
  induction i with
  | zero =>
      change 3 ≤ 2 ^ (0 + 2)
      norm_num
  | succ i ih =>
      have h := oddPrimeTag_succ_le_two_mul i
      calc
        oddPrimeTag (i + 1) ≤ 2 * oddPrimeTag i := h
        _ ≤ 2 * 2 ^ (i + 2) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (i + 1 + 2) := by
          rw [mul_comm, ← pow_succ]

/-- The product modulus grows at most quadratically in the exponent. -/
theorem tagModulus_le_two_pow_sq (i : ℕ) :
    tagModulus i ≤ 2 ^ ((i + 2) ^ 2) := by
  induction i with
  | zero =>
      unfold tagModulus
      change 3 ≤ 2 ^ ((0 + 2) ^ 2)
      norm_num
  | succ i ih =>
      rw [tagModulus_succ]
      calc
        tagModulus i * oddPrimeTag (i + 1)
            ≤ 2 ^ ((i + 2) ^ 2) * 2 ^ (i + 1 + 2) :=
          Nat.mul_le_mul ih (oddPrimeTag_le_two_pow (i + 1))
        _ = 2 ^ (((i + 2) ^ 2) + (i + 1 + 2)) := by
          rw [← pow_add]
        _ ≤ 2 ^ ((i + 1 + 2) ^ 2) := by
          exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem bertrandScaleExp_lt_succ (i : ℕ) :
    bertrandScaleExp i < bertrandScaleExp (i + 1) := by
  unfold bertrandScaleExp
  exact Nat.pow_lt_pow_left (by omega) (by norm_num : 4 ≠ 0)

/-- The block lengths strictly increase. -/
theorem bertrandLength_lt_succ (i : ℕ) :
    bertrandLength i < bertrandLength (i + 1) := by
  unfold bertrandLength
  exact Nat.pow_lt_pow_right (by norm_num) (bertrandScaleExp_lt_succ i)

theorem bertrandLength_pos (i : ℕ) :
    0 < bertrandLength i := by
  unfold bertrandLength
  positivity

theorem bertrandStart_pos (i : ℕ) :
    0 < bertrandStart i := by
  unfold bertrandStart
  omega

/-- The quartic margin absorbs the next modulus. -/
theorem bertrandScaleExp_cover_margin (i : ℕ) :
    (i + 3) ^ 2 + bertrandScaleExp (i + 1) ≤ 2 * bertrandScaleExp i := by
  unfold bertrandScaleExp
  ring_nf
  nlinarith

/-- The next endpoint, without its harmless constant, fits below `L_i^2`. -/
theorem bertrandLength_mul_tagModulus_succ_le_sq (i : ℕ) :
    tagModulus (i + 1) * bertrandLength (i + 1) ≤
      bertrandLength i * bertrandLength i := by
  unfold bertrandLength
  calc
    tagModulus (i + 1) * 2 ^ bertrandScaleExp (i + 1)
        ≤ 2 ^ ((i + 1 + 2) ^ 2) * 2 ^ bertrandScaleExp (i + 1) :=
      Nat.mul_le_mul_right _ (tagModulus_le_two_pow_sq (i + 1))
    _ = 2 ^ ((i + 1 + 2) ^ 2 + bertrandScaleExp (i + 1)) := by
      rw [← pow_add]
    _ ≤ 2 ^ (2 * bertrandScaleExp i) := by
      exact Nat.pow_le_pow_right
        (by norm_num) (by simpa using bertrandScaleExp_cover_margin i)
    _ = 2 ^ bertrandScaleExp i * 2 ^ bertrandScaleExp i := by
      rw [two_mul, pow_add]

/-- Blocks with start `4L+1` are narrow enough for the internal avoiding
argument. -/
theorem apBlock_narrow_four_mul {r M L : ℕ} (hM : 0 < M) (hL : 0 < L) :
    2 * apMax r M (4 * L + 1) L < 3 * apMin r M (4 * L + 1) := by
  unfold apMax apMin
  have hsum : 4 * L + 1 + (L - 1) = 5 * L := by
    omega
  rw [hsum]
  nlinarith

/-- With residue below the modulus, the block maximum lies below `6ML`. -/
theorem apMax_four_mul_le_six_mul {r M L : ℕ} (hr : r < M) (hL : 0 < L) :
    apMax r M (4 * L + 1) L ≤ 6 * M * L := by
  unfold apMax
  have hsum : 4 * L + 1 + (L - 1) = 5 * L := by
    omega
  rw [hsum]
  nlinarith

theorem bertrand_apMin_one (i : ℕ) :
    1 ≤ apMin (tagResidue i) (tagModulus i) (bertrandStart i) := by
  unfold apMin
  have hM := tagModulus_pos i
  have hT := bertrandStart_pos i
  have hmul : 0 < tagModulus i * bertrandStart i := Nat.mul_pos hM hT
  omega

theorem bertrand_apMax_le_endpoint (i : ℕ) :
    apMax (tagResidue i) (tagModulus i) (bertrandStart i) (bertrandLength i) ≤
      bertrandEndpoint i := by
  unfold bertrandStart bertrandEndpoint
  exact apMax_four_mul_le_six_mul
    (tagResidue_lt_tagModulus i) (bertrandLength_pos i)

theorem bertrand_apMin_le_endpoint (i : ℕ) :
    apMin (tagResidue i) (tagModulus i) (bertrandStart i) ≤
      bertrandEndpoint i := by
  have hmem :
      apMin (tagResidue i) (tagModulus i) (bertrandStart i) ∈
        apBlock (tagResidue i) (tagModulus i) (bertrandStart i)
          (bertrandLength i) := by
    refine ⟨0, bertrandLength_pos i, ?_⟩
    simp [apMin]
  exact (le_apMax_of_mem_apBlock hmem).trans (bertrand_apMax_le_endpoint i)

/-- Each endpoint is below the next block's first element. -/
theorem bertrand_endpoint_lt_next_min (i : ℕ) :
    bertrandEndpoint i <
      apMin (tagResidue (i + 1)) (tagModulus (i + 1))
        (bertrandStart (i + 1)) := by
  unfold bertrandEndpoint apMin bertrandStart
  rw [tagModulus_succ]
  let M := tagModulus i
  let q := oddPrimeTag (i + 1)
  let Li := bertrandLength i
  let Lj := bertrandLength (i + 1)
  have hM : 0 < M := tagModulus_pos i
  have hq : 3 ≤ q := by
    have hlt := oddPrimeTag_two_lt (i + 1)
    omega
  have hL : Li ≤ Lj := (bertrandLength_lt_succ i).le
  have hLj : 0 < Lj := bertrandLength_pos (i + 1)
  have hqstart : 12 * Lj ≤ q * (4 * Lj + 1) := by
    calc
      12 * Lj = 3 * (4 * Lj) := by
        ring
      _ ≤ q * (4 * Lj + 1) := Nat.mul_le_mul hq (by omega)
  have hmain : 6 * M * Li < M * q * (4 * Lj + 1) := by
    calc
      6 * M * Li ≤ 6 * M * Lj := by
        exact Nat.mul_le_mul_left (6 * M) hL
      _ < 12 * M * Lj := by
        nlinarith
      _ = M * (12 * Lj) := by
        ring
      _ ≤ M * (q * (4 * Lj + 1)) := Nat.mul_le_mul_left M hqstart
      _ = M * q * (4 * Lj + 1) := by
        ring
  exact hmain.trans_le (Nat.le_add_left _ _)

theorem bertrandEndpoint_lt_succ (i : ℕ) :
    bertrandEndpoint i < bertrandEndpoint (i + 1) :=
  (bertrand_endpoint_lt_next_min i).trans_le
    (bertrand_apMin_le_endpoint (i + 1))

theorem bertrandEndpoint_strictMono :
    StrictMono bertrandEndpoint :=
  strictMono_nat_of_lt_succ bertrandEndpoint_lt_succ

theorem bertrand_endpoint_lt_min_of_lt {i j : ℕ} (hij : i < j) :
    bertrandEndpoint i <
      apMin (tagResidue j) (tagModulus j) (bertrandStart j) := by
  have hjpos : 0 < j := Nat.lt_of_le_of_lt (Nat.zero_le i) hij
  let k := j - 1
  have hk_succ : k + 1 = j := Nat.succ_pred_eq_of_pos hjpos
  have hik : i ≤ k := by
    omega
  have hEiEk : bertrandEndpoint i ≤ bertrandEndpoint k :=
    bertrandEndpoint_strictMono.monotone hik
  have hEkmin :
      bertrandEndpoint k <
        apMin (tagResidue j) (tagModulus j) (bertrandStart j) := by
    simpa [k, hk_succ] using bertrand_endpoint_lt_next_min k
  exact hEiEk.trans_lt hEkmin

/-- Earlier blocks lie below later blocks. -/
theorem bertrand_order {i j x y : ℕ} (hij : i < j)
    (hx :
      x ∈ apBlock (tagResidue i) (tagModulus i) (bertrandStart i)
        (bertrandLength i))
    (hy :
      y ∈ apBlock (tagResidue j) (tagModulus j) (bertrandStart j)
        (bertrandLength j)) :
    x < y := by
  have hxE : x ≤ bertrandEndpoint i :=
    (le_apMax_of_mem_apBlock hx).trans (bertrand_apMax_le_endpoint i)
  have hEy :
      bertrandEndpoint i <
        apMin (tagResidue j) (tagModulus j) (bertrandStart j) :=
    bertrand_endpoint_lt_min_of_lt hij
  have hymin :
      apMin (tagResidue j) (tagModulus j) (bertrandStart j) ≤ y :=
    apMin_le_of_mem_apBlock hy
  exact hxE.trans_lt (hEy.trans_le hymin)

theorem bertrand_narrow (i : ℕ) :
    2 *
        apMax (tagResidue i) (tagModulus i) (bertrandStart i)
          (bertrandLength i) <
      3 * apMin (tagResidue i) (tagModulus i) (bertrandStart i) := by
  unfold bertrandStart
  exact apBlock_narrow_four_mul (tagModulus_pos i) (bertrandLength_pos i)

theorem bertrandEndpoint_succ_le_hundred_sq (i : ℕ) :
    bertrandEndpoint (i + 1) ≤ (10 * bertrandLength i) ^ 2 := by
  unfold bertrandEndpoint
  have h := bertrandLength_mul_tagModulus_succ_le_sq i
  calc
    6 * tagModulus (i + 1) * bertrandLength (i + 1)
        = 6 * (tagModulus (i + 1) * bertrandLength (i + 1)) := by
      ring
    _ ≤ 6 * (bertrandLength i * bertrandLength i) :=
      Nat.mul_le_mul_left 6 h
    _ ≤ (10 * bertrandLength i) ^ 2 := by
      nlinarith

theorem one_tenth_sqrt_le_of_le_hundred_sq {E L : ℕ}
    (hEL : E ≤ (10 * L) ^ 2) :
    (1 / 10 : ℝ) * Real.sqrt (E : ℝ) ≤ (L : ℝ) := by
  have hreal_nat : (E : ℝ) ≤ (((10 * L) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hEL
  have hcast :
      (((10 * L) ^ 2 : ℕ) : ℝ) = ((10 : ℝ) * (L : ℝ)) ^ 2 := by
    norm_num [Nat.cast_mul, Nat.cast_pow]
  have hreal : (E : ℝ) ≤ ((10 : ℝ) * (L : ℝ)) ^ 2 :=
    hreal_nat.trans_eq hcast
  have hsqrt : Real.sqrt (E : ℝ) ≤ (10 : ℝ) * (L : ℝ) := by
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hreal⟩
  nlinarith

theorem bertrand_cover (i : ℕ) :
    (1 / 10 : ℝ) * Real.sqrt (bertrandEndpoint (i + 1) : ℝ) ≤
      (bertrandLength i : ℝ) :=
  one_tenth_sqrt_le_of_le_hundred_sq
    (bertrandEndpoint_succ_le_hundred_sq i)

/-- The reciprocal mass of the `i`th block in the explicit construction is at
most `1 / M_i`.  This is the formal version of the usual CRT-construction
barrier: the same large modulus that protects the construction also makes each
block harmonically cheap. -/
theorem bertrand_block_sum_reciprocal_le_inv_tagModulus (i : ℕ) :
    (∑ n ∈ apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
        (bertrandLength i), (1 : ℝ) / (n : ℝ)) ≤
      (1 : ℝ) / (tagModulus i : ℝ) := by
  have hblock := apBlockFinset_sum_reciprocal_le_length_div_min
    (r := tagResidue i) (M := tagModulus i) (T := bertrandStart i)
    (L := bertrandLength i) (tagModulus_pos i)
    (lt_of_lt_of_le Nat.zero_lt_one (bertrand_apMin_one i))
  have hmin :
      (bertrandLength i : ℝ) /
          (apMin (tagResidue i) (tagModulus i) (bertrandStart i) : ℝ) ≤
        (1 : ℝ) / (tagModulus i : ℝ) := by
    unfold apMin bertrandStart
    have hMpos : (0 : ℝ) < tagModulus i :=
      Nat.cast_pos.mpr (tagModulus_pos i)
    have hdenpos :
        (0 : ℝ) <
          (tagResidue i + tagModulus i * (4 * bertrandLength i + 1) : ℕ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (bertrand_apMin_one i))
    rw [div_le_div_iff₀ hdenpos hMpos]
    norm_num
    nlinarith
  exact hblock.trans hmin

/-- Consequently, the sequence of reciprocal masses of the Bertrand blocks is
summable.  Thus this explicit CRT block construction cannot be upgraded to a
divergent reciprocal-sum example just by taking all of its blocks. -/
theorem summable_bertrand_block_sum_reciprocal :
    Summable fun i : ℕ =>
      ∑ n ∈ apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
        (bertrandLength i), (1 : ℝ) / (n : ℝ) := by
  refine Summable.of_nonneg_of_le
    (f := fun i : ℕ => (1 : ℝ) / (tagModulus i : ℝ))
    (g := fun i : ℕ =>
      ∑ n ∈ apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
        (bertrandLength i), (1 : ℝ) / (n : ℝ))
    ?_ ?_ summable_inv_tagModulus
  · intro i
    exact Finset.sum_nonneg fun n _hn => by positivity
  · intro i
    exact bertrand_block_sum_reciprocal_le_inv_tagModulus i

/-- The `i`th block of the explicit Bertrand-prime construction. -/
noncomputable def bertrandBlock (i : ℕ) : Set ℕ :=
  apBlock (tagResidue i) (tagModulus i) (bertrandStart i) (bertrandLength i)

/-- The explicit Bertrand-prime union used for the square-root density
construction. -/
noncomputable def bertrandSet : Set ℕ :=
  ⋃ i, bertrandBlock i

/-- The `i`th Bertrand block, viewed as a subset of the full Bertrand union. -/
def bertrandBlockInSubtype (i : ℕ) : Set bertrandSet :=
  {a : bertrandSet | (a : ℕ) ∈ bertrandBlock i}

theorem bertrandBlock_finite (i : ℕ) :
    (bertrandBlock i).Finite := by
  have hfin : ((apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
      (bertrandLength i) : Finset ℕ) : Set ℕ).Finite :=
    (apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
      (bertrandLength i)).finite_toSet
  exact hfin.subset (by
    intro n hn
    simpa [bertrandBlock] using hn)

theorem bertrandBlockInSubtype_finite (i : ℕ) :
    (bertrandBlockInSubtype i).Finite := by
  unfold bertrandBlockInSubtype
  exact Set.Finite.preimage_embedding
    (Function.Embedding.subtype fun n : ℕ => n ∈ bertrandSet)
    (bertrandBlock_finite i)

/-- Ordered Bertrand blocks partition the full union. -/
theorem existsUnique_mem_bertrandBlockInSubtype (a : bertrandSet) :
    ∃! i : ℕ, a ∈ bertrandBlockInSubtype i := by
  rcases Set.mem_iUnion.mp a.property with ⟨i, hi⟩
  refine ⟨i, ?_, ?_⟩
  · simpa [bertrandBlockInSubtype] using hi
  · intro j hj
    have hj' : (a : ℕ) ∈ bertrandBlock j := by
      simpa [bertrandBlockInSubtype] using hj
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hself : (a : ℕ) < (a : ℕ) :=
        bertrand_order hij (by simpa [bertrandBlock] using hi)
          (by simpa [bertrandBlock] using hj')
      exact False.elim (lt_irrefl _ hself)
    · rfl
    · have hself : (a : ℕ) < (a : ℕ) :=
        bertrand_order hji (by simpa [bertrandBlock] using hj')
          (by simpa [bertrandBlock] using hi)
      exact False.elim (lt_irrefl _ hself)

/-- The subtype reciprocal mass of one Bertrand block is bounded by the
corresponding finite AP reciprocal sum. -/
theorem bertrandBlockInSubtype_reciprocal_tsum_le (i : ℕ) :
    (∑' a : bertrandBlockInSubtype i,
        (1 : ℝ) / (((a : bertrandSet) : ℕ) : ℝ)) ≤
      ∑ n ∈ apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
        (bertrandLength i), (1 : ℝ) / (n : ℝ) := by
  classical
  let S : Set bertrandSet := bertrandBlockInSubtype i
  have hSfin : S.Finite := bertrandBlockInSubtype_finite i
  haveI : Fintype S := hSfin.fintype
  let G : Finset ℕ :=
    (Finset.univ : Finset S).image fun a : S => ((a : bertrandSet) : ℕ)
  have hGsub : G ⊆ apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
      (bertrandLength i) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨a, _ha, rfl⟩
    have ha : ((a : bertrandSet) : ℕ) ∈ bertrandBlock i := a.property
    simpa [bertrandBlock] using ha
  calc
    (∑' a : S, (1 : ℝ) / (((a : bertrandSet) : ℕ) : ℝ)) =
        ∑ a : S, (1 : ℝ) / (((a : bertrandSet) : ℕ) : ℝ) := by
      rw [tsum_fintype]
    _ = ∑ n ∈ G, (1 : ℝ) / (n : ℝ) := by
      unfold G
      rw [Finset.sum_image]
      · intro a _ha b _hb h
        ext
        exact h
    _ ≤ ∑ n ∈ apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
        (bertrandLength i), (1 : ℝ) / (n : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hGsub (by
        intro n _hnF _hnG
        positivity)

/-- The full explicit Bertrand-prime block union has convergent reciprocal sum.
The construction proves the positive square-root density part of Erdős problem
#12, but it cannot itself witness failure of reciprocal summability. -/
theorem bertrandSet_reciprocalSummable :
    ReciprocalSummable bertrandSet := by
  unfold ReciprocalSummable
  have hf_nonneg :
      (0 : bertrandSet → ℝ) ≤
        fun a : bertrandSet => (1 : ℝ) / (((a : bertrandSet) : ℕ) : ℝ) := by
    intro a
    positivity
  rw [summable_partition hf_nonneg existsUnique_mem_bertrandBlockInSubtype]
  constructor
  · intro i
    exact (bertrandBlockInSubtype_finite i).summable
      (fun a : bertrandSet => (1 : ℝ) / (((a : bertrandSet) : ℕ) : ℝ))
  · exact Summable.of_nonneg_of_le
      (f := fun i : ℕ =>
        ∑ n ∈ apBlockFinset (tagResidue i) (tagModulus i) (bertrandStart i)
          (bertrandLength i), (1 : ℝ) / (n : ℝ))
      (g := fun i : ℕ =>
        ∑' a : bertrandBlockInSubtype i,
          (1 : ℝ) / (((a : bertrandSet) : ℕ) : ℝ))
      (fun i => tsum_nonneg fun a => by positivity)
      (fun i => bertrandBlockInSubtype_reciprocal_tsum_le i)
      summable_bertrand_block_sum_reciprocal

/-- The explicit Bertrand-prime block construction answers the positive
square-root density question in Erdős problem #12. -/
theorem erdos12_positiveSqrtDensity_bertrand :
    Erdos12PositiveSqrtDensityQuestion := by
  exact erdos12_positiveSqrtDensity_of_bertrand_tagged_ap_blocks
    (T := bertrandStart) (L := bertrandLength) (E := bertrandEndpoint)
    (c := (1 / 10 : ℝ))
    (by norm_num)
    bertrandEndpoint_strictMono
    bertrandLength_pos
    bertrand_apMin_one
    bertrand_apMax_le_endpoint
    bertrand_cover
    (fun {i} {j} {x} {y} hij hx hy => bertrand_order hij hx hy)
    bertrand_narrow

end DivisibilityAvoidingSets
