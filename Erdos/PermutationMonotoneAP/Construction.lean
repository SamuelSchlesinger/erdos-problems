import Erdos.PermutationMonotoneAP.VanDerCorput
import Erdos.PermutationMonotoneAP.Density

/-!
# A positive-density 3-free set (LeSaulnier–Vijay lower bound)

We build the LeSaulnier–Vijay set `S = ⋃ₖ [2qₖ, 3qₖ−1]` with `q₀ = 2`,
`qₖ₊₁ = 3qₖ − 1`, en route to `α(3) ≥` a positive constant. The blocks grow
geometrically (ratio → 3) with comparable gaps, so:

* **every 3-term AP of `S` lies within a single block** (`threeAP_same_block`),
  via the slick LV argument: if the two larger terms are in different blocks then
  `z ≥ 2y`, forcing the smallest term `x = 2y − z ≤ 0`; and if all-but-`x` share a
  block while `x` is earlier, the gap `x − ... ` is too large for an AP;
* within a block, the van der Corput order scrambles every 3-AP
  (`VDC.vdc_middle_not_between`).

So ordering `S` block-by-block, vdc-within-block, avoids monotone 3-APs. This
file establishes the key arithmetic (`threeAP_same_block`); the enumeration and
density bound build on it.

Reference: LeSaulnier, Vijay, arXiv:1004.1740.
-/

namespace PermutationMonotoneAP
namespace Construction

/-- LeSaulnier–Vijay block parameter: `q 0 = 2`, `q (k+1) = 3 q k − 1`. -/
def q : ℕ → ℕ
  | 0 => 2
  | (k + 1) => 3 * q k - 1

@[simp] lemma q_zero : q 0 = 2 := rfl
lemma q_succ (k : ℕ) : q (k + 1) = 3 * q k - 1 := rfl

lemma q_ge_two : ∀ k, 2 ≤ q k
  | 0 => le_refl 2
  | (k + 1) => by rw [q_succ]; have := q_ge_two k; omega

lemma q_strictMono : StrictMono q := by
  apply strictMono_nat_of_lt_succ
  intro k; rw [q_succ]; have := q_ge_two k; omega

lemma q_mono : Monotone q := q_strictMono.monotone

/-- `n` lies in block `k`, the interval `[2 q k, 3 q k − 1]`. -/
def inBlock (n k : ℕ) : Prop := 2 * q k ≤ n ∧ n ≤ 3 * q k - 1

/-- The LeSaulnier–Vijay set: the union of all blocks. -/
def S : Set ℕ := {n | ∃ k, inBlock n k}

/-- Block indices respect order: a smaller element cannot be in a later block. -/
lemma block_le_of_lt {x y jx jy : ℕ} (hx : inBlock x jx) (hy : inBlock y jy)
    (hxy : x < y) : jx ≤ jy := by
  by_contra h
  rw [not_le] at h
  have h1 : q (jy + 1) ≤ q jx := q_mono (by omega)
  have h2 : q (jy + 1) = 3 * q jy - 1 := q_succ jy
  have := q_ge_two jy
  have hxlb : 2 * q jx ≤ x := hx.1
  have hyub : y ≤ 3 * q jy - 1 := hy.2
  omega

/-- **Key arithmetic lemma.** Every 3-term AP `x < y < z` (with `x + z = 2y`) of
elements of `S` lies within a single block. -/
lemma threeAP_same_block {x y z : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : x < y) (hyz : y < z) (hAP : x + z = 2 * y) :
    ∃ k, inBlock x k ∧ inBlock y k ∧ inBlock z k := by
  obtain ⟨jx, hjx⟩ := hx
  obtain ⟨jy, hjy⟩ := hy
  obtain ⟨jz, hjz⟩ := hz
  have hxle : jx ≤ jy := block_le_of_lt hjx hjy hxy
  have hyle : jy ≤ jz := block_le_of_lt hjy hjz hyz
  rcases eq_or_lt_of_le hyle with hjeq | hjlt
  · -- y and z share block `jy`; locate x
    subst hjeq
    rcases eq_or_lt_of_le hxle with hjxeq | hjxlt
    · exact ⟨jy, hjxeq ▸ hjx, hjy, hjz⟩
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, jy = m + 1 := ⟨jy - 1, by omega⟩
      have hqm : q (m + 1) = 3 * q m - 1 := q_succ m
      have hjxm : q jx ≤ q m := q_mono (by omega)
      have hxub : x ≤ 3 * q jx - 1 := hjx.2
      have hylb : 2 * q (m + 1) ≤ y := hjy.1
      have hzub : z ≤ 3 * q (m + 1) - 1 := hjz.2
      have := q_ge_two jx; have := q_ge_two m
      omega
  · -- y and z are in different blocks: z ≥ 2y forces x ≤ 0
    exfalso
    have h1 : q (jy + 1) ≤ q jz := q_mono (by omega)
    have h2 : q (jy + 1) = 3 * q jy - 1 := q_succ jy
    have := q_ge_two jy
    have hzlb : 2 * q jz ≤ z := hjz.1
    have hyub : y ≤ 3 * q jy - 1 := hjy.2
    have hxlb : 2 * q jx ≤ x := hjx.1
    have := q_ge_two jx
    omega

/-! ### Block finsets and basic counts -/

/-- Block `k` as a `Finset`: the interval `[2 q k, 3 q k − 1]`. -/
def blockFinset (k : ℕ) : Finset ℕ := Finset.Icc (2 * q k) (3 * q k - 1)

@[simp] lemma mem_blockFinset {n k : ℕ} : n ∈ blockFinset k ↔ inBlock n k := by
  simp [blockFinset, inBlock, Finset.mem_Icc]

/-- Block `k` has exactly `q k` elements. -/
lemma blockFinset_card (k : ℕ) : (blockFinset k).card = q k := by
  rw [blockFinset, Nat.card_Icc]; have := q_ge_two k; omega

/-- Distinct blocks are disjoint (each element lies in a unique block). -/
lemma blockFinset_disjoint {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (blockFinset j) (blockFinset k) := by
  rw [Finset.disjoint_left]
  intro n hnj hnk
  simp only [mem_blockFinset, inBlock] at hnj hnk
  rcases lt_or_gt_of_ne hjk with h | h
  · -- j < k: 3 q j - 1 < 2 q k ≤ n ≤ 3 q j - 1
    have h1 : q (j + 1) ≤ q k := q_mono (by omega)
    have h2 : q (j + 1) = 3 * q j - 1 := q_succ j
    have := q_ge_two j
    omega
  · have h1 : q (k + 1) ≤ q j := q_mono (by omega)
    have h2 : q (k + 1) = 3 * q k - 1 := q_succ k
    have := q_ge_two k
    omega

/-- `S` is infinite: it contains `2 q k` for every `k`, and `k ↦ 2 q k` is injective. -/
theorem S_infinite : S.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k => 2 * q k) ?_ ?_
  · intro a b hab
    have : q a = q b := by simpa using hab
    exact q_strictMono.injective this
  · intro k
    have hmem : 2 * q k ∈ S := ⟨k, le_refl _, by have := q_ge_two k; omega⟩
    exact hmem

/-! ### Within-block van der Corput rank

`cntIn k v` is the number of block-`k` elements strictly below `v` in the van der
Corput order — the position `v` would occupy if block `k` were enumerated in vdc
order. It is strictly monotone in `vdcLt`, hence an injection of block `k` into
`{0, …, q k − 1}`, and (by cardinality) a bijection. -/

open scoped Classical in
/-- The van der Corput rank of `v` within block `k`. -/
noncomputable def cntIn (k v : ℕ) : ℕ :=
  ((blockFinset k).filter (fun w => VDC.vdcLt w v)).card

/-- `cntIn` is strictly monotone along `vdcLt` within a block. -/
lemma cntIn_lt_of_vdcLt {k v w : ℕ} (hv : v ∈ blockFinset k) (h : VDC.vdcLt v w) :
    cntIn k v < cntIn k w := by
  classical
  rw [cntIn, cntIn]
  apply Finset.card_lt_card
  have hsub : (blockFinset k).filter (fun u => VDC.vdcLt u v) ⊆
      (blockFinset k).filter (fun u => VDC.vdcLt u w) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, VDC.vdcLt_trans hx.2 h⟩
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, h⟩,
    fun hc => VDC.vdcLt_irrefl v (Finset.mem_filter.mp hc).2⟩

/-- Within a block, `cntIn k` is injective. -/
lemma cntIn_injOn (k : ℕ) : Set.InjOn (cntIn k) (blockFinset k) := by
  intro v hv w hw hvw
  by_contra hne
  rcases VDC.vdcLt_total hne with h | h
  · exact absurd hvw (cntIn_lt_of_vdcLt hv h).ne
  · exact absurd hvw.symm (cntIn_lt_of_vdcLt hw h).ne

/-- The vdc rank within block `k` is `< q k`. -/
lemma cntIn_lt {k v : ℕ} (hv : v ∈ blockFinset k) : cntIn k v < q k := by
  classical
  rw [cntIn, ← blockFinset_card k]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨v, hv, fun hc => VDC.vdcLt_irrefl v (Finset.mem_filter.mp hc).2⟩

/-! ### The global enumeration `↥S ≃ ℕ`

Order `S` block-by-block, vdc-within-block: the rank of `v` is
`C (blockIdx v) + cntIn (blockIdx v) v`, where `C k = q 0 + … + q (k−1)`. -/

/-- Cumulative block sizes: `C k` is the number of `S`-elements in blocks `< k`. -/
def C (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, q j

@[simp] lemma C_zero : C 0 = 0 := by simp [C]
lemma C_succ (k : ℕ) : C (k + 1) = C k + q k := Finset.sum_range_succ _ _

lemma C_strictMono : StrictMono C := by
  apply strictMono_nat_of_lt_succ
  intro k; rw [C_succ]; have := q_ge_two k; omega

lemma C_mono : Monotone C := C_strictMono.monotone

lemma le_C (k : ℕ) : k ≤ C k := by
  induction k with
  | zero => simp
  | succ i ih => rw [C_succ]; have := q_ge_two i; omega

instance decInBlock (n : ℕ) : DecidablePred (inBlock n) :=
  fun k => inferInstanceAs (Decidable (2 * q k ≤ n ∧ n ≤ 3 * q k - 1))

/-- The (unique) block index of an element of `S`. -/
noncomputable def blockIdx {n : ℕ} (hn : n ∈ S) : ℕ := Nat.find hn

lemma blockIdx_spec {n : ℕ} (hn : n ∈ S) : inBlock n (blockIdx hn) := Nat.find_spec hn

lemma mem_blockFinset_blockIdx {n : ℕ} (hn : n ∈ S) : n ∈ blockFinset (blockIdx hn) :=
  mem_blockFinset.mpr (blockIdx_spec hn)

/-- The block index is determined by any block containing `n` (blocks are disjoint). -/
lemma blockIdx_eq {n k : ℕ} (hn : n ∈ S) (hk : inBlock n k) : blockIdx hn = k := by
  by_contra h
  exact Finset.disjoint_left.mp (blockFinset_disjoint h)
    (mem_blockFinset_blockIdx hn) (mem_blockFinset.mpr hk)

/-- Global rank: blocks in index order, vdc order within each block. -/
noncomputable def rank (x : S) : ℕ := C (blockIdx x.2) + cntIn (blockIdx x.2) (x : ℕ)

lemma rank_injective : Function.Injective rank := by
  intro x y hxy
  simp only [rank] at hxy
  set kx := blockIdx x.2 with hkxdef
  set ky := blockIdx y.2 with hkydef
  have hxb : (x : ℕ) ∈ blockFinset kx := mem_blockFinset_blockIdx x.2
  have hyb : (y : ℕ) ∈ blockFinset ky := mem_blockFinset_blockIdx y.2
  rcases lt_trichotomy kx ky with h | h | h
  · exfalso
    have hcx : cntIn kx (x : ℕ) < q kx := cntIn_lt hxb
    have hC : C (kx + 1) ≤ C ky := C_mono (by omega)
    rw [C_succ] at hC
    omega
  · have hxb' : (x : ℕ) ∈ blockFinset ky := h ▸ hxb
    rw [h] at hxy
    have heq : cntIn ky (x : ℕ) = cntIn ky (y : ℕ) := by omega
    exact Subtype.ext (cntIn_injOn ky hxb' hyb heq)
  · exfalso
    have hcy : cntIn ky (y : ℕ) < q ky := cntIn_lt hyb
    have hC : C (ky + 1) ≤ C kx := C_mono (by omega)
    rw [C_succ] at hC
    omega

/-- Every `n` lies in a unique cumulative window `[C k, C (k+1))`. -/
lemma exists_block_of_le (n : ℕ) : ∃ k, C k ≤ n ∧ n < C (k + 1) := by
  classical
  have hunb : ∃ k, n < C (k + 1) := ⟨n, by have := le_C (n + 1); omega⟩
  refine ⟨Nat.find hunb, ?_, Nat.find_spec hunb⟩
  rcases Nat.eq_zero_or_pos (Nat.find hunb) with hk0 | hkpos
  · rw [hk0]; simp
  · have hmin := Nat.find_min hunb (m := Nat.find hunb - 1) (by omega)
    have hk1 : Nat.find hunb - 1 + 1 = Nat.find hunb := by omega
    rw [hk1] at hmin
    omega

lemma rank_surjective : Function.Surjective rank := by
  intro n
  obtain ⟨k, hk1, hk2⟩ := exists_block_of_le n
  have hoff : n - C k < q k := by rw [C_succ] at hk2; omega
  have hmaps : Set.MapsTo (cntIn k) ↑(blockFinset k) ↑(Finset.range (q k)) := by
    intro v hv
    rw [Finset.mem_coe] at hv
    rw [Finset.coe_range, Set.mem_Iio]
    exact cntIn_lt hv
  have hcard : (Finset.range (q k)).card ≤ (blockFinset k).card := by
    rw [Finset.card_range, blockFinset_card]
  have hsurj := Finset.surjOn_of_injOn_of_card_le (cntIn k) hmaps (cntIn_injOn k) hcard
  have hmem : (n - C k) ∈ Finset.range (q k) := Finset.mem_range.mpr hoff
  obtain ⟨v, hv, hcv⟩ := hsurj (Finset.mem_coe.mpr hmem)
  rw [Finset.mem_coe] at hv
  have hvS : v ∈ S := ⟨k, mem_blockFinset.mp hv⟩
  refine ⟨⟨v, hvS⟩, ?_⟩
  simp only [rank]
  rw [blockIdx_eq hvS (mem_blockFinset.mp hv)]
  show C k + cntIn k v = n
  rw [hcv]; omega

theorem rank_bijective : Function.Bijective rank := ⟨rank_injective, rank_surjective⟩

/-- The block-by-block, vdc-within-block enumeration `ℕ ≃ ↥S`. -/
noncomputable def enum : ℕ ≃ S := (Equiv.ofBijective rank rank_bijective).symm

lemma rank_enum (m : ℕ) : rank (enum m) = m :=
  (Equiv.ofBijective rank rank_bijective).apply_symm_apply m

/-! ### `S` is 3-free -/

/-- Within a block, `cntIn` order recovers the vdc order. -/
lemma vdcLt_of_cntIn_lt {k v w : ℕ} (_hv : v ∈ blockFinset k) (hw : w ∈ blockFinset k)
    (h : cntIn k v < cntIn k w) : VDC.vdcLt v w := by
  rcases eq_or_ne v w with rfl | hne
  · exact absurd h (lt_irrefl _)
  · rcases VDC.vdcLt_total hne with h' | h'
    · exact h'
    · exact absurd (cntIn_lt_of_vdcLt hw h') (by omega)

/-- An AP triple `v0, v1, v2` cannot have `v1` strictly vdc-between the endpoints. -/
lemma ap_triple_false {v0 v1 v2 : ℕ} (hAP : v0 + v2 = 2 * v1) (hne : v0 ≠ v2)
    (h01 : VDC.vdcLt v0 v1) (h12 : VDC.vdcLt v1 v2) : False := by
  rcases lt_or_gt_of_ne hne with h | h
  · apply VDC.vdc_middle_not_between v0 (v1 - v0) (by omega)
    rw [show v0 + (v1 - v0) = v1 by omega, show v0 + 2 * (v1 - v0) = v2 by omega]
    exact Or.inl ⟨h01, h12⟩
  · apply VDC.vdc_middle_not_between v2 (v1 - v2) (by omega)
    rw [show v2 + (v1 - v2) = v1 by omega, show v2 + 2 * (v1 - v2) = v0 by omega]
    exact Or.inr ⟨h01, h12⟩

/-- **The LeSaulnier–Vijay set `S` is 3-free.** Enumerated block-by-block in van der
Corput order, no monotone 3-term AP appears: such an AP would lie in a single block
(`threeAP_same_block`), but there the vdc order forbids it (`vdc_middle_not_between`). -/
theorem isFree_S : IsFree S 3 := by
  refine ⟨enum, ?_⟩
  rintro ⟨p, hp, a, d, hAP⟩
  have hp01 : p 0 < p 1 := hp (by omega)
  have hp12 : p 1 < p 2 := hp (by omega)
  have e0 := hAP 0 (by omega)
  have e1 := hAP 1 (by omega)
  have e2 := hAP 2 (by omega)
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul, add_zero] at e0 e1 e2
  have h0 := rank_enum (p 0); simp only [rank] at h0
  have h1 := rank_enum (p 1); simp only [rank] at h1
  have h2 := rank_enum (p 2); simp only [rank] at h2
  have hAPnat : (↑(enum (p 0)) : ℕ) + ↑(enum (p 2)) = 2 * ↑(enum (p 1)) := by
    have h : ((↑(enum (p 0)) : ℕ) : ℤ) + ((↑(enum (p 2)) : ℕ) : ℤ)
        = 2 * ((↑(enum (p 1)) : ℕ) : ℤ) := by rw [e0, e1, e2]; ring
    exact_mod_cast h
  have hne02 : (↑(enum (p 0)) : ℕ) ≠ ↑(enum (p 2)) := fun h =>
    (hp (show (0 : ℕ) < 2 by omega)).ne (enum.injective (Subtype.ext h))
  obtain ⟨k, hb0, hb1, hb2⟩ : ∃ k, inBlock (↑(enum (p 0))) k ∧ inBlock (↑(enum (p 1))) k ∧
      inBlock (↑(enum (p 2))) k := by
    rcases lt_or_gt_of_ne hne02 with h | h
    · exact threeAP_same_block (enum (p 0)).2 (enum (p 1)).2 (enum (p 2)).2
        (by omega) (by omega) hAPnat
    · obtain ⟨k, c2, c1, c0⟩ := threeAP_same_block (enum (p 2)).2 (enum (p 1)).2 (enum (p 0)).2
        (by omega) (by omega) (by omega)
      exact ⟨k, c0, c1, c2⟩
  rw [blockIdx_eq (enum (p 0)).2 hb0] at h0
  rw [blockIdx_eq (enum (p 1)).2 hb1] at h1
  rw [blockIdx_eq (enum (p 2)).2 hb2] at h2
  exact ap_triple_false hAPnat hne02
    (vdcLt_of_cntIn_lt (mem_blockFinset.mpr hb0) (mem_blockFinset.mpr hb1) (by omega))
    (vdcLt_of_cntIn_lt (mem_blockFinset.mpr hb1) (mem_blockFinset.mpr hb2) (by omega))

/-! ### Positive density

`S` has upper density `≥ 1/4`: block `k` (with `q k` elements) sits entirely below
`3 q k + 1`, so the density ratio there is `≥ q k / (3 q k + 1) ≥ 1/4`, infinitely
often. Hence `α(3) ≥ 1/4 > 0`. -/

lemma blockFinset_subset (k : ℕ) :
    (↑(blockFinset k) : Set ℕ) ⊆ S ∩ Set.Iio (3 * q k + 1) := by
  intro n hn
  rw [Finset.mem_coe, mem_blockFinset] at hn
  exact ⟨⟨k, hn⟩, by have := hn.2; rw [Set.mem_Iio]; omega⟩

/-- At least `q k` elements of `S` lie below `3 q k + 1`. -/
lemma le_countMem (k : ℕ) : q k ≤ countMem S (3 * q k + 1) := by
  have hfin : (S ∩ Set.Iio (3 * q k + 1)).Finite :=
    (Set.finite_Iio _).subset Set.inter_subset_right
  calc q k = (blockFinset k).card := (blockFinset_card k).symm
    _ = (↑(blockFinset k) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (S ∩ Set.Iio (3 * q k + 1)).ncard := Set.ncard_le_ncard (blockFinset_subset k) hfin

/-- The density ratio at `3 q k + 1` is at least `1/4`. -/
lemma densityRatio_ge (k : ℕ) : (1 : ℝ) / 4 ≤ densityRatio S (3 * q k + 1) := by
  have h1 : (q k : ℝ) ≤ (countMem S (3 * q k + 1) : ℝ) := by exact_mod_cast le_countMem k
  have h2 : (2 : ℝ) ≤ (q k : ℝ) := by exact_mod_cast q_ge_two k
  rw [densityRatio, le_div_iff₀ (by positivity)]
  push_cast
  linarith

/-- **The LeSaulnier–Vijay set has upper density `≥ 1/4`.** Combined with `isFree_S`,
this is a positive-density 3-free set: `α(3) ≥ 1/4 > 0`. -/
theorem upperDensity_S_ge : (1 : ℝ) / 4 ≤ upperDensity S := by
  have hfreq : ∃ᶠ n in Filter.atTop, (1 : ℝ) / 4 ≤ densityRatio S n := by
    rw [Filter.frequently_atTop]
    refine fun a => ⟨3 * q a + 1, ?_, densityRatio_ge a⟩
    have : a ≤ q a := q_strictMono.le_apply
    omega
  exact Filter.le_limsup_of_frequently_le hfreq (isBoundedUnder_le_densityRatio S)

theorem upperDensity_S_pos : 0 < upperDensity S := lt_of_lt_of_le (by norm_num) upperDensity_S_ge

/-- **A positive-density 3-free set exists** (the LeSaulnier–Vijay lower bound,
`α(3) ≥ 1/4 > 0`): there is a set `S ⊆ ℕ` of upper density `≥ 1/4` that can be
enumerated avoiding all monotone 3-term arithmetic progressions. -/
theorem exists_isFree_upperDensity_pos :
    ∃ T : Set ℕ, IsFree T 3 ∧ (1 : ℝ) / 4 ≤ upperDensity T :=
  ⟨S, isFree_S, upperDensity_S_ge⟩

end Construction
end PermutationMonotoneAP
