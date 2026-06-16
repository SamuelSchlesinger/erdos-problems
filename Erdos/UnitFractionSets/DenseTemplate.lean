/-
# Dense Template Bound for Problem #301

This file proves the asymptotic upper bound

  f₃₀₁(N) ≤ (163/195 + o(1))N,

improving the project's earlier `145/168` same-signature bound
(`UpperBound.lean`).  The headline theorem is
`sum_free_dense_template_163_195_bound`, with the limiting constant recorded in
`dense_template_density_calculation`.

It comes from the `{2:4,3:3,5:2}` p-adic signature grid on the 23 multipliers
dividing `360`, whose 219 forbidden reciprocal identities force a per-cutoff
hitting deficit.  The finite hitting check runs as a bitmask branch search over
`Fin 23` (`maskSearch`, in `TemplateSchema.lean`): the witness edges are carried
as plain `List`/`Nat` data so the certificate verifies in seconds, with `Finset`
confined to the kernel-checked proof layer via the structural bridge
`maskOfList_eq_maskOfFn_toFinset`.

The parameter class below fixes

* `v₂(a) ≡ 0 mod 4`,
* `v₃(a) ≡ 0 mod 3`,
* `v₅(a) ≡ 0 mod 2`.

This has density `4/13`, and its residue signature separates the 23 multipliers
used by the searched certificate.
-/
import Erdos.UnitFractionSets.Statement
import Erdos.UnitFractionSets.TemplateSchema
import Erdos.Common.PackingBound
import Erdos.Common.ValSignature

namespace UnitFractionSets

open scoped BigOperators

/-- Parameter class for the dense `{2:4,3:3,5:2}` signature grid. -/
def DenseParam (a : ℕ) : Prop :=
  4 ∣ padicValNat 2 a ∧ 3 ∣ padicValNat 3 a ∧ Even (padicValNat 5 a)

instance : DecidablePred DenseParam := fun a =>
  inferInstanceAs
    (Decidable (4 ∣ padicValNat 2 a ∧ 3 ∣ padicValNat 3 a ∧
      Even (padicValNat 5 a)))

/-- The formal multiplier list for the searched `163/195` candidate. -/
private def denseMul (i : Fin 23) : ℕ :=
  ![2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 60, 72, 90,
    120, 180, 360] i

private theorem denseMul_injective : Function.Injective denseMul := by
  decide

private theorem denseMul_pos (i : Fin 23) : 0 < denseMul i := by
  fin_cases i <;> decide

private theorem denseMul_dvd_threeSixty (i : Fin 23) : denseMul i ∣ 360 := by
  fin_cases i <;> decide

private theorem denseMul_mul_injective {a : ℕ} (ha : 0 < a) :
    Function.Injective fun i : Fin 23 => denseMul i * a := by
  intro i j h
  exact denseMul_injective (Nat.eq_of_mul_eq_mul_right ha h)

private def denseSig (n : ℕ) : ℕ × ℕ × ℕ :=
  (padicValNat 2 n % 4, padicValNat 3 n % 3, padicValNat 5 n % 2)

private def denseResidue (i : Fin 23) : ℕ × ℕ × ℕ :=
  ![(1, 0, 0), (0, 1, 0), (2, 0, 0), (0, 0, 1), (1, 1, 0), (3, 0, 0),
    (0, 2, 0), (1, 0, 1), (2, 1, 0), (0, 1, 1), (1, 2, 0), (2, 0, 1),
    (3, 1, 0), (1, 1, 1), (2, 2, 0), (3, 0, 1), (0, 2, 1), (2, 1, 1),
    (3, 2, 0), (1, 2, 1), (3, 1, 1), (2, 2, 1), (3, 2, 1)] i

private theorem denseResidue_injective : Function.Injective denseResidue := by
  decide

set_option linter.style.nativeDecide false in
private theorem denseResidue_eq_valuation (i : Fin 23) :
    denseResidue i =
      (padicValNat 2 (denseMul i) % 4, padicValNat 3 (denseMul i) % 3,
        padicValNat 5 (denseMul i) % 2) := by
  revert i
  native_decide

private theorem denseSig_mul (i : Fin 23) {a : ℕ} (ha : a ≠ 0)
    (hv : DenseParam a) :
    denseSig (denseMul i * a) = denseResidue i := by
  unfold denseSig
  have hc : denseMul i ≠ 0 := Nat.ne_of_gt (denseMul_pos i)
  have h2 : padicValNat 2 (denseMul i * a) % 4 =
      padicValNat 2 (denseMul i) % 4 := by
    rw [padicValNat.mul hc ha]
    obtain ⟨k, hk⟩ := hv.1
    rw [hk]
    omega
  have h3 : padicValNat 3 (denseMul i * a) % 3 =
      padicValNat 3 (denseMul i) % 3 := by
    rw [padicValNat.mul hc ha]
    obtain ⟨k, hk⟩ := hv.2.1
    rw [hk]
    omega
  have h5 : padicValNat 5 (denseMul i * a) % 2 =
      padicValNat 5 (denseMul i) % 2 := by
    rw [padicValNat.mul hc ha]
    obtain ⟨k, hk⟩ := hv.2.2
    rw [hk]
    omega
  rw [h2, h3, h5, denseResidue_eq_valuation]

/-- The residue signature separates full dense-template gadgets for distinct
parameters in the chosen `DenseParam` class. -/
private theorem dense_full_gadgets_disjoint {a₁ a₂ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hne : a₁ ≠ a₂)
    (hv₁ : DenseParam a₁) (hv₂ : DenseParam a₂) :
    Disjoint ((Finset.univ : Finset (Fin 23)).image fun i => denseMul i * a₁)
      ((Finset.univ : Finset (Fin 23)).image fun i => denseMul i * a₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  rcases Finset.mem_image.mp hx₁ with ⟨i, _hi, rfl⟩
  rcases Finset.mem_image.mp hx₂ with ⟨j, _hj, hEq⟩
  have hsig := congrArg denseSig hEq.symm
  rw [denseSig_mul i (by omega) hv₁, denseSig_mul j (by omega) hv₂] at hsig
  have hij : i = j := denseResidue_injective hsig
  subst j
  have haeq : a₁ = a₂ := Nat.eq_of_mul_eq_mul_left (denseMul_pos i) hEq.symm
  exact hne haeq

private def densePrefix (c : ℕ) : Finset (Fin 23) :=
  Finset.univ.filter fun i => denseMul i ≤ c

private def denseGadget (c a : ℕ) : Finset ℕ :=
  (densePrefix c).image fun i => denseMul i * a

private theorem denseGadget_card_eq_prefix_card {c a : ℕ} (ha : 0 < a) :
    (denseGadget c a).card = (densePrefix c).card := by
  simpa [denseGadget] using
    Finset.card_image_of_injective (densePrefix c) (denseMul_mul_injective ha)

private theorem denseGadget_subset_full {c a : ℕ} (hc : c ≤ 360) :
    denseGadget c a ⊆ denseGadget 360 a := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  have hle : denseMul i ≤ c := by
    simpa [densePrefix] using (Finset.mem_filter.mp hi).2
  simp [densePrefix, hle.trans hc]

private theorem denseGadget_subset_Icc {c a N : ℕ} (ha : 0 < a) (hcN : c * a ≤ N) :
    denseGadget c a ⊆ Finset.Icc 1 N := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  have hle : denseMul i ≤ c := by
    simpa [densePrefix] using (Finset.mem_filter.mp hi).2
  have hmul : denseMul i * a ≤ c * a := Nat.mul_le_mul_right a hle
  simp only [Finset.mem_Icc]
  exact ⟨by nlinarith [denseMul_pos i, ha], hmul.trans hcN⟩

private theorem dense_preimage_image_eq (A : Finset ℕ) (c a : ℕ) :
    ((densePrefix c).filter fun i => denseMul i * a ∈ A).image
        (fun i => denseMul i * a) =
      denseGadget c a ∩ A := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩,
        (Finset.mem_filter.mp hi).2⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxg, hxA⟩
    rcases Finset.mem_image.mp hxg with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hxA⟩, rfl⟩

private theorem dense_preimage_card_eq_inter {A : Finset ℕ} {c a : ℕ} (ha : 0 < a) :
    ((densePrefix c).filter fun i => denseMul i * a ∈ A).card =
      (denseGadget c a ∩ A).card := by
  rw [← dense_preimage_image_eq A c a]
  exact (Finset.card_image_of_injective
    ((densePrefix c).filter fun i => denseMul i * a ∈ A)
    (denseMul_mul_injective ha)).symm

/-- Generic scaled reciprocal obstruction indexed by dense-template positions. -/
private theorem not_sf_dense_index_identity {A : Finset ℕ} (hA : SumFree A) {a : ℕ}
    (ha : 0 < a) {target : Fin 23} {Ridx : Finset (Fin 23)}
    (htargetA : denseMul target * a ∈ A)
    (hRidxA : ∀ i ∈ Ridx, denseMul i * a ∈ A)
    (htarget_not_R : target ∉ Ridx) (hRnonempty : Ridx.Nonempty)
    (hid : (1 / (denseMul target : ℚ)) =
      ∑ i ∈ Ridx, (1 / (denseMul i : ℚ))) : False := by
  let S : Finset ℕ := Ridx.image fun i => denseMul i * a
  have hSsubset : S ⊆ A.erase (denseMul target * a) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rw [Finset.mem_erase]
    exact ⟨fun hEq => by
      have hit : i = target := denseMul_mul_injective ha hEq
      exact htarget_not_R (hit ▸ hi), hRidxA i hi⟩
  have hSnonempty : S.Nonempty := by
    obtain ⟨i, hi⟩ := hRnonempty
    exact ⟨denseMul i * a, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hsum_image :
      (∑ b ∈ S, (1 / b : ℚ)) =
        ∑ i ∈ Ridx, (1 / (denseMul i * a : ℕ) : ℚ) := by
    dsimp [S]
    rw [Finset.sum_image]
    intro i _ j _ hEq
    exact denseMul_mul_injective ha hEq
  have hscaled :
      (1 / (denseMul target * a : ℕ) : ℚ) =
        ∑ i ∈ Ridx, (1 / (denseMul i * a : ℕ) : ℚ) := by
    have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have htargetQ : (denseMul target : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (denseMul_pos target))
    have htarget_scale :
        (1 / (denseMul target * a : ℕ) : ℚ) =
          (1 / (a : ℚ)) * (1 / (denseMul target : ℚ)) := by
      push_cast
      field_simp [haQ, htargetQ]
    calc
      (1 / (denseMul target * a : ℕ) : ℚ)
          = (1 / (a : ℚ)) * (1 / (denseMul target : ℚ)) := htarget_scale
      _ = (1 / (a : ℚ)) * (∑ i ∈ Ridx, (1 / (denseMul i : ℚ))) := by
        rw [hid]
      _ = ∑ i ∈ Ridx, (1 / (a : ℚ)) * (1 / (denseMul i : ℚ)) := by
        rw [Finset.mul_sum]
      _ = ∑ i ∈ Ridx, (1 / (denseMul i * a : ℕ) : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        have hiQ : (denseMul i : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt (denseMul_pos i))
        symm
        push_cast
        field_simp [haQ, hiQ]
  exact hA (denseMul target * a) htargetA S hSsubset hSnonempty
    (hscaled.trans hsum_image.symm)

private theorem dense_identity_edge_forbidden {A : Finset ℕ} (hA : SumFree A) {a : ℕ}
    (ha : 0 < a) {target : Fin 23} {Ridx : Finset (Fin 23)}
    (hEA : ∀ i ∈ insert target Ridx, denseMul i * a ∈ A)
    (htarget_not_R : target ∉ Ridx) (hRnonempty : Ridx.Nonempty)
    (hid : (1 / (denseMul target : ℚ)) =
      ∑ i ∈ Ridx, (1 / (denseMul i : ℚ))) : False := by
  refine not_sf_dense_index_identity hA ha
    (target := target) (Ridx := Ridx)
    (hEA target (Finset.mem_insert_self _ _)) ?_ htarget_not_R hRnonempty hid
  intro i hi
  exact hEA i (Finset.mem_insert_of_mem hi)

/-- Cast a denominator-cleared identity with common denominator `360` to the
corresponding rational reciprocal identity. -/
private theorem dense_reciprocal_identity_of_clear {target : Fin 23} {Ridx : Finset (Fin 23)}
    (hclear : 360 / denseMul target = ∑ i ∈ Ridx, 360 / denseMul i) :
    (1 / (denseMul target : ℚ)) = ∑ i ∈ Ridx, (1 / (denseMul i : ℚ)) := by
  have hdiv_cast : ∀ i : Fin 23,
      ((360 / denseMul i : ℕ) : ℚ) = (360 : ℚ) / (denseMul i : ℚ) := by
    intro i
    have hmQ : (denseMul i : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (denseMul_pos i))
    have hmul_nat : denseMul i * (360 / denseMul i) = 360 :=
      Nat.mul_div_cancel' (denseMul_dvd_threeSixty i)
    have hmul_q : (denseMul i : ℚ) * ((360 / denseMul i : ℕ) : ℚ) = (360 : ℚ) := by
      exact_mod_cast hmul_nat
    rw [eq_div_iff hmQ]
    simpa [mul_comm] using hmul_q
  have htarget :
      ((360 / denseMul target : ℕ) : ℚ) = (360 : ℚ) / (denseMul target : ℚ) :=
    hdiv_cast target
  have hrhs : ((∑ i ∈ Ridx, 360 / denseMul i : ℕ) : ℚ) =
      ∑ i ∈ Ridx, (360 : ℚ) / (denseMul i : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => hdiv_cast i
  have hq : ((360 / denseMul target : ℕ) : ℚ) =
      ((∑ i ∈ Ridx, 360 / denseMul i : ℕ) : ℚ) := by
    exact_mod_cast hclear
  rw [htarget, hrhs] at hq
  have h360 : (360 : ℚ) ≠ 0 := by norm_num
  have htQ : (denseMul target : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (denseMul_pos target))
  calc
    (1 / (denseMul target : ℕ) : ℚ) =
        ((360 : ℚ) / (denseMul target : ℚ)) / 360 := by
      field_simp [h360, htQ]
    _ = (∑ i ∈ Ridx, (360 : ℚ) / (denseMul i : ℚ)) / 360 := by rw [hq]
    _ = ∑ i ∈ Ridx, ((360 : ℚ) / (denseMul i : ℚ)) / 360 := by
      rw [Finset.sum_div]
    _ = ∑ i ∈ Ridx, (1 / denseMul i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hiQ : (denseMul i : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (denseMul_pos i))
      field_simp [h360, hiQ]

/-- The 219 compressed witness edges as explicit index lists `[target, rhs…]`
(indices into the 23 multipliers).  Pure `List`/`Fin` literals — no `Finset`
nesting — so elaboration and the closed search both stay cheap.  Verified
externally: all 219 reciprocal identities hold over the common denominator
`360`, no target lies in its own right-hand side, and all indices are
distinct. -/
private def denseEdges : List (List (Fin 23)) :=
  [[0, 1, 4],
   [0, 1, 5, 12],
   [0, 1, 5, 14, 18],
   [0, 1, 5, 16, 18, 21],
   [0, 1, 5, 16, 19, 20],
   [0, 1, 6, 10],
   [0, 1, 6, 12, 18],
   [0, 1, 6, 13, 16],
   [0, 1, 6, 13, 18, 20],
   [0, 1, 7, 9],
   [0, 1, 7, 10, 19],
   [0, 1, 7, 11, 17],
   [0, 1, 7, 12, 15],
   [0, 1, 9, 10, 15, 18, 21],
   [0, 1, 10, 11, 15, 16, 18],
   [0, 3, 4, 5, 20],
   [0, 3, 4, 6, 16],
   [0, 3, 4, 8, 11],
   [0, 3, 4, 10, 11, 14],
   [0, 3, 5, 6, 12, 16],
   [0, 3, 5, 6, 12, 17, 21],
   [0, 3, 5, 6, 14, 15, 19],
   [0, 3, 5, 8, 9, 15],
   [0, 3, 5, 9, 10, 14, 15],
   [0, 3, 6, 8, 10, 11],
   [0, 3, 6, 8, 11, 12, 18],
   [0, 4, 5, 6, 11, 15, 16],
   [0, 5, 6, 7, 9, 10, 12],
   [1, 2, 8],
   [1, 2, 9, 17],
   [1, 2, 9, 19, 21],
   [1, 2, 10, 14],
   [1, 2, 10, 16, 21],
   [1, 2, 10, 17, 19],
   [1, 2, 11, 13],
   [1, 2, 11, 14, 21],
   [1, 2, 11, 15, 20],
   [1, 2, 11, 16, 19],
   [1, 2, 13, 14, 16],
   [1, 3, 5, 20],
   [1, 3, 6, 16],
   [1, 3, 7, 13],
   [1, 3, 8, 11],
   [1, 3, 8, 12, 20],
   [1, 3, 8, 13, 17],
   [1, 5, 6, 10, 12],
   [1, 5, 6, 11, 15, 16],
   [1, 5, 7, 10, 16, 17, 18],
   [1, 6, 7, 9, 10],
   [2, 3, 11],
   [2, 3, 12, 20],
   [2, 3, 13, 17],
   [2, 3, 13, 19, 21],
   [2, 3, 14, 16],
   [2, 3, 14, 17, 21],
   [2, 3, 14, 18, 20],
   [2, 3, 16, 17, 19],
   [2, 4, 8],
   [2, 4, 9, 17],
   [2, 4, 9, 19, 21],
   [2, 4, 10, 14],
   [2, 4, 10, 16, 21],
   [2, 4, 10, 17, 19],
   [2, 4, 11, 13],
   [2, 4, 11, 14, 21],
   [2, 4, 11, 15, 20],
   [2, 4, 11, 16, 19],
   [2, 4, 13, 14, 16],
   [2, 6, 7, 15, 18],
   [2, 6, 7, 16, 17],
   [2, 6, 8, 10],
   [2, 6, 8, 12, 18],
   [2, 6, 8, 13, 16],
   [2, 6, 9, 10, 17],
   [2, 6, 9, 11, 16],
   [2, 6, 9, 13, 15, 18],
   [2, 6, 11, 12, 15, 16],
   [2, 7, 8, 9],
   [2, 7, 8, 12, 15],
   [2, 7, 9, 10, 14],
   [2, 7, 10, 12, 14, 15],
   [2, 8, 9, 10, 15, 18, 21],
   [2, 8, 10, 11, 15, 16, 18],
   [3, 4, 13],
   [3, 4, 14, 21],
   [3, 4, 15, 20],
   [3, 4, 16, 19],
   [3, 5, 9, 20],
   [3, 5, 10, 18, 21],
   [3, 5, 10, 19, 20],
   [3, 5, 11, 15],
   [3, 5, 12, 13],
   [3, 5, 12, 14, 21],
   [3, 5, 12, 16, 19],
   [3, 5, 13, 14, 18],
   [3, 5, 14, 15, 16],
   [3, 6, 8, 21],
   [3, 6, 9, 16],
   [3, 6, 10, 13],
   [3, 6, 10, 15, 20],
   [3, 6, 10, 16, 19],
   [3, 6, 11, 15, 18],
   [3, 6, 12, 15, 16],
   [3, 8, 9, 11],
   [3, 8, 10, 15, 16, 18],
   [3, 8, 11, 12, 15],
   [3, 9, 10, 11, 14],
   [4, 5, 12],
   [4, 5, 13, 20],
   [4, 5, 15, 17],
   [4, 5, 16, 18, 21],
   [4, 5, 16, 19, 20],
   [4, 6, 10],
   [4, 6, 12, 18],
   [4, 6, 13, 16],
   [4, 6, 13, 18, 20],
   [4, 7, 9],
   [4, 7, 10, 19],
   [4, 7, 11, 17],
   [4, 7, 12, 15],
   [4, 10, 11, 15, 16, 18],
   [5, 6, 18],
   [5, 6, 20, 21],
   [5, 7, 15],
   [5, 7, 17, 20],
   [5, 7, 18, 19],
   [5, 8, 12],
   [5, 8, 13, 20],
   [5, 8, 14, 18],
   [5, 8, 15, 17],
   [5, 8, 16, 18, 21],
   [5, 8, 16, 19, 20],
   [5, 9, 11, 20],
   [5, 9, 12, 17],
   [5, 9, 13, 15],
   [5, 9, 13, 18, 19],
   [5, 9, 14, 16, 20],
   [5, 9, 14, 17, 18],
   [5, 9, 15, 16, 19],
   [5, 10, 12, 14],
   [5, 10, 12, 16, 21],
   [5, 10, 12, 17, 19],
   [5, 10, 13, 15, 19],
   [5, 11, 12, 13],
   [5, 11, 13, 14, 18],
   [6, 7, 19],
   [6, 8, 14],
   [6, 8, 16, 21],
   [6, 9, 13, 19],
   [6, 9, 14, 17],
   [6, 9, 15, 19, 20],
   [6, 11, 13, 14],
   [6, 11, 14, 15, 20],
   [6, 11, 15, 16, 18],
   [6, 12, 13, 16, 18],
   [7, 8, 17],
   [7, 8, 19, 21],
   [7, 9, 13],
   [7, 9, 14, 21],
   [7, 9, 15, 20],
   [7, 10, 13, 19],
   [7, 10, 14, 17],
   [7, 10, 15, 18, 21],
   [7, 10, 15, 19, 20],
   [7, 12, 13, 15],
   [7, 12, 15, 16, 19],
   [7, 13, 14, 16, 17],
   [8, 9, 17],
   [8, 10, 14],
   [8, 10, 16, 21],
   [8, 10, 17, 19],
   [8, 11, 13],
   [8, 11, 15, 20],
   [8, 11, 16, 19],
   [8, 13, 14, 16],
   [9, 10, 19],
   [9, 11, 17],
   [9, 11, 19, 21],
   [9, 12, 15],
   [9, 12, 18, 19],
   [9, 14, 15, 18],
   [9, 14, 16, 17],
   [9, 15, 16, 18, 21],
   [10, 11, 21],
   [10, 12, 18],
   [10, 12, 20, 21],
   [10, 13, 16],
   [10, 13, 17, 21],
   [10, 15, 16, 20],
   [10, 15, 17, 18],
   [11, 12, 20],
   [11, 13, 17],
   [11, 14, 16],
   [11, 14, 17, 21],
   [11, 14, 18, 20],
   [11, 16, 17, 19],
   [12, 13, 20],
   [12, 14, 18],
   [12, 14, 20, 21],
   [12, 15, 17],
   [12, 15, 19, 21],
   [12, 16, 18, 21],
   [12, 16, 19, 20],
   [13, 14, 21],
   [13, 15, 20],
   [13, 16, 19],
   [13, 18, 19, 20],
   [14, 15, 22],
   [14, 16, 21],
   [14, 17, 19],
   [15, 16, 22],
   [15, 17, 20],
   [15, 18, 19],
   [15, 19, 20, 21],
   [16, 17, 21],
   [16, 18, 20],
   [17, 18, 22],
   [17, 19, 21],
   [18, 20, 21]]
/-- The witness edges as a `Finset` of `Finset`s (proof layer only).  `Finset`
nesting appears here but never in the compute path. -/
private def denseBadEdges : Finset (Finset (Fin 23)) :=
  (denseEdges.map List.toFinset).toFinset

private theorem denseEdges_toFinset_mem_badEdges :
    ∀ l ∈ denseEdges, l.toFinset ∈ denseBadEdges := by
  intro l hl
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, rfl⟩)

/-- The witness edges as bitmasks over `Fin 23`, built with the pure `List`/`Nat`
`maskOfList`, so the search inner loop is plain `Nat` bitwise arithmetic with no
`Finset` in the compute path. -/
private def denseEdgeMasks : List ℕ :=
  denseEdges.map (maskOfList Fin.val)

/-- The prefix as a list, in *descending* multiplier order: branching on the
most-constrained vertices first keeps the executable search tree small (about
`1.9 × 10⁵` nodes across all rows, versus `4.4 × 10⁵` in ascending order). -/
private def densePrefixList (c : ℕ) : List (Fin 23) :=
  (List.finRange 23).reverse.filter fun i => decide (denseMul i ≤ c)

private theorem densePrefixList_toFinset (c : ℕ) :
    (densePrefixList c).toFinset = densePrefix c := by
  ext i
  simp [densePrefixList, densePrefix, decide_eq_true_eq]

private def denseCutoff (i : Fin 19) : ℕ :=
  ![360, 180, 120, 90, 72, 60, 45, 40, 36, 30, 24, 20, 18, 15, 12, 10, 9, 8,
    6] i

private def denseSize (i : Fin 19) : ℕ :=
  ![23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5] i

private def denseKeep (i : Fin 19) : ℕ :=
  ![10, 10, 10, 10, 10, 9, 9, 9, 9, 8, 8, 8, 8, 7, 7, 7, 6, 5, 4] i

private theorem densePrefix_card_eq_size (i : Fin 19) :
    (densePrefix (denseCutoff i)).card = denseSize i := by
  fin_cases i <;> decide

private theorem denseCutoff_le_threeSixty (i : Fin 19) : denseCutoff i ≤ 360 := by
  fin_cases i <;> decide

private theorem denseKeep_le_size (i : Fin 19) : denseKeep i ≤ denseSize i := by
  fin_cases i <;> decide

private theorem densePrefix_hitting_of_branch_certificate (i : Fin 19)
    {cert : BranchCert (Fin 23)}
    (hcheck :
      cert.check denseBadEdges (densePrefixList (denseCutoff i)) (denseKeep i + 1) ∅ = true) :
    ∀ S : Finset (Fin 23), S ⊆ densePrefix (denseCutoff i) → denseKeep i < S.card →
      ContainsHyperedge denseBadEdges S :=
  prefix_hitting_of_branch_certificate
    (badEdges := denseBadEdges) (cert := cert)
    (P := densePrefix (denseCutoff i)) (xs := densePrefixList (denseCutoff i))
    (keep := denseKeep i) (densePrefixList_toFinset (denseCutoff i)) hcheck

private theorem densePrefix_hitting_of_cover_certificate (i : Fin 19)
    {cert : CoverLowerCert (Fin 23)}
    (hcheck :
      cert.check (denseBadEdges.filter fun E => decide (E ⊆ densePrefix (denseCutoff i)))
        (denseSize i - denseKeep i) = true) :
    ∀ S : Finset (Fin 23), S ⊆ densePrefix (denseCutoff i) → denseKeep i < S.card →
      ContainsHyperedge denseBadEdges S := by
  refine prefix_hitting_of_cover_lower_certificate
    (badEdges := denseBadEdges) (cert := cert)
    (P := densePrefix (denseCutoff i)) (keep := denseKeep i)
    (lower := denseSize i - denseKeep i) ?_ hcheck
  rw [densePrefix_card_eq_size]
  have hle := denseKeep_le_size i
  omega

private theorem denseGadget_inter_card_le_of_branch_certificate {A : Finset ℕ} {a : ℕ}
    (ha : 0 < a) (i : Fin 19)
    {cert : BranchCert (Fin 23)}
    (hcheck :
      cert.check denseBadEdges (densePrefixList (denseCutoff i)) (denseKeep i + 1) ∅ = true)
    (hForbidden :
      ∀ E ∈ denseBadEdges, (∀ j ∈ E, denseMul j * a ∈ A) → False) :
    (denseGadget (denseCutoff i) a ∩ A).card ≤ denseKeep i := by
  rw [denseGadget]
  refine hypergraph_hitting_image_inter_card_le
    (P := densePrefix (denseCutoff i)) (A := A)
    (f := fun j : Fin 23 => denseMul j * a)
    (badEdges := denseBadEdges) (keep := denseKeep i)
    (hf := denseMul_mul_injective ha) ?_ ?_
  · intro E hE hEA
    exact hForbidden E hE hEA
  · exact densePrefix_hitting_of_branch_certificate i hcheck

private theorem denseGadget_inter_card_le_of_cover_certificate {A : Finset ℕ} {a : ℕ}
    (ha : 0 < a) (i : Fin 19)
    {cert : CoverLowerCert (Fin 23)}
    (hcheck :
      cert.check (denseBadEdges.filter fun E => decide (E ⊆ densePrefix (denseCutoff i)))
        (denseSize i - denseKeep i) = true)
    (hForbidden :
      ∀ E ∈ denseBadEdges, (∀ j ∈ E, denseMul j * a ∈ A) → False) :
    (denseGadget (denseCutoff i) a ∩ A).card ≤ denseKeep i := by
  rw [denseGadget]
  refine hypergraph_hitting_image_inter_card_le
    (P := densePrefix (denseCutoff i)) (A := A)
    (f := fun j : Fin 23 => denseMul j * a)
    (badEdges := denseBadEdges) (keep := denseKeep i)
    (hf := denseMul_mul_injective ha) ?_ ?_
  · intro E hE hEA
    exact hForbidden E hE hEA
  · exact densePrefix_hitting_of_cover_certificate i hcheck

/-- Arithmetic density factor for the dense signature class:
`8/15 * 9/13 * 5/6 = 4/13`. -/
theorem denseParam_density_constant :
    ((8 : ℚ) / 15) * (9 / 13) * (5 / 6) = 4 / 13 := by
  norm_num

/-! ### The witness edges are forbidden in sum-free sets

Each of the 219 compressed witness rows encodes a reciprocal identity
`1/m_t = ∑_{m ∈ rhs} 1/m` among the 23 multipliers.  After scaling by any
positive parameter `a`, a sum-free set cannot contain the full scaled edge. -/

set_option linter.style.nativeDecide false in
/-- Structural validity of all 219 compressed witness rows, stated purely over
`List`/`Nat`: each row `l` is nonempty with a nonempty tail, has no duplicate
indices (so the target `l.head` is not on the right-hand side `l.tail`), and the
denominator-cleared reciprocal identity over the common denominator `360` holds
as a `List.sum`.  This is a closed finite computation over the `denseEdges`
list — pure `List`/`Nat`, no `Finset` in the compute path. -/
private theorem denseWitness_list_facts :
    ∀ l ∈ denseEdges,
      2 ≤ l.length ∧ l.Nodup ∧
        360 / denseMul l.headI =
          (l.tail.map fun j => 360 / denseMul j).sum := by
  native_decide

/-- No bad edge of the dense template can be fully present (after scaling by a
positive parameter `a`) inside a sum-free set.

Each `Finset` edge `E ∈ denseBadEdges` is `l.toFinset` for some row
`l = target :: tail ∈ denseEdges`.  Its target is `l.head`, its right-hand side
is `tail.toFinset`, and the list-level reciprocal identity bridges to the
`Finset`-sum identity via the nodup of the row. -/
private theorem denseBadEdge_forbidden {A : Finset ℕ} (hA : SumFree A) {a : ℕ}
    (ha : 0 < a) :
    ∀ E ∈ denseBadEdges, (∀ j ∈ E, denseMul j * a ∈ A) → False := by
  intro E hE hEA
  rcases List.mem_map.mp (List.mem_toFinset.mp hE) with ⟨l, hl, rfl⟩
  obtain ⟨hlen, hnodup, hclear⟩ := denseWitness_list_facts l hl
  -- Write the row as `target :: tail`.
  obtain ⟨t, ts, rfl⟩ : ∃ t ts, l = t :: ts := by
    cases l with
    | nil => simp at hlen
    | cons t ts => exact ⟨t, ts, rfl⟩
  have hts : ts ≠ [] := by
    rcases ts with _ | _
    · simp at hlen
    · exact List.cons_ne_nil _ _
  simp only [List.headI, List.tail] at hclear
  -- Target = `t`, right-hand side = `ts.toFinset`.
  have htarget_not_R : t ∉ ts.toFinset := by
    rw [List.mem_toFinset]
    exact (List.nodup_cons.mp hnodup).1
  have hRnonempty : (ts.toFinset).Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil ts hts
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  -- Bridge the list-sum identity to a Finset-sum over `ts.toFinset`.
  have htail_nodup : ts.Nodup := (List.nodup_cons.mp hnodup).2
  have hsum_bridge :
      (∑ j ∈ ts.toFinset, 360 / denseMul j) =
        (ts.map fun j => 360 / denseMul j).sum :=
    List.sum_toFinset (fun j => 360 / denseMul j) htail_nodup
  have hclear' :
      360 / denseMul t = ∑ j ∈ ts.toFinset, 360 / denseMul j := by
    rw [hsum_bridge]; exact hclear
  refine dense_identity_edge_forbidden hA ha ?_ htarget_not_R hRnonempty
    (dense_reciprocal_identity_of_clear hclear')
  intro j hj
  apply hEA
  rw [List.toFinset_cons]
  exact hj

/-! ### Prefix hitting via the executable bitmask search -/

/-- All 19 branch searches bundled into one closed boolean: the chosen set is
a bitmask and the prefix vertices are bit indices, so the whole computation
is `Nat` bitwise arithmetic. -/
private def denseMaskSearchAll : Bool :=
  (List.finRange 19).all fun i =>
    !maskSearch denseEdgeMasks ((densePrefixList (denseCutoff i)).map Fin.val)
      (denseKeep i + 1) 0

set_option linter.style.nativeDecide false in
/-- Closed finite check of the prefix hitting property for all 19 cutoffs:
the exhaustive branch search over each (≤ 23)-element prefix finds no
edge-free subset of size `denseKeep i + 1`.  The computation is over subsets
of `Fin 23`, not an unbounded domain; the rows explore about `1.9 × 10⁵`
branch nodes in total, and the bitmask representation keeps the evaluated
run to a few seconds.  (Kernel `decide` is infeasible here: substitution
duplicates the mask list across the ~4 × 10⁵ recursive calls and exhausts
memory.)  The keep numbers were cross-checked externally by an independent
maximum-independent-set search, and the fractional-matching LP value of
every row is strictly below the integral deficit, so no small one-shot
packing certificate can replace this search. -/
private theorem dense_mask_search_all : denseMaskSearchAll = true := by
  native_decide

/-- Per-row reading of `dense_mask_search_all`. -/
private theorem dense_mask_search (i : Fin 19) :
    maskSearch denseEdgeMasks ((densePrefixList (denseCutoff i)).map Fin.val)
      (denseKeep i + 1) 0 = false := by
  have h := dense_mask_search_all
  rw [denseMaskSearchAll, List.all_eq_true] at h
  have hi := h i (List.mem_finRange i)
  simpa using hi

/-- Every subset of the cutoff prefix larger than the keep number contains a
forbidden edge. -/
private theorem dense_prefix_hitting (i : Fin 19) :
    ∀ S : Finset (Fin 23), S ⊆ densePrefix (denseCutoff i) →
      denseKeep i < S.card → ContainsHyperedge denseBadEdges S :=
  prefix_hitting_of_mask_search_list Fin.val_injective
    denseEdges_toFinset_mem_badEdges
    (densePrefixList_toFinset (denseCutoff i)) (dense_mask_search i)

/-- In a sum-free set, each dense gadget keeps at most `denseKeep i` of its
`denseSize i` elements. -/
private theorem denseGadget_inter_le_keep {A : Finset ℕ} (hA : SumFree A)
    {a : ℕ} (ha : 0 < a) (i : Fin 19) :
    (denseGadget (denseCutoff i) a ∩ A).card ≤ denseKeep i := by
  rw [denseGadget]
  refine hypergraph_hitting_image_inter_card_le
    (P := densePrefix (denseCutoff i)) (A := A)
    (f := fun j : Fin 23 => denseMul j * a)
    (badEdges := denseBadEdges) (keep := denseKeep i)
    (hf := denseMul_mul_injective ha) ?_ ?_
  · intro E hE hEA
    exact denseBadEdge_forbidden hA ha E hE hEA
  · exact dense_prefix_hitting i

/-! ### Nineteen parameter bands and the packing bound -/

/-- The previous cutoff for each band, with the convention `0` for the first
band (`N / 0 = 0`, so the first band starts at `1`; in the asymptotic
calculation `(0 : ℚ)⁻¹ = 0` encodes the empty width above cutoff `360`). -/
private def densePrevCutoff (i : Fin 19) : ℕ :=
  ![0, 360, 180, 120, 90, 72, 60, 45, 40, 36, 30, 24, 20, 18, 15, 12, 10, 9,
    8] i

private def denseLo (N : ℕ) (i : Fin 19) : ℕ :=
  ![1, N / 360 + 1, N / 180 + 1, N / 120 + 1, N / 90 + 1, N / 72 + 1,
    N / 60 + 1, N / 45 + 1, N / 40 + 1, N / 36 + 1, N / 30 + 1, N / 24 + 1,
    N / 20 + 1, N / 18 + 1, N / 15 + 1, N / 12 + 1, N / 10 + 1, N / 9 + 1,
    N / 8 + 1] i

private def denseHi (N : ℕ) (i : Fin 19) : ℕ :=
  ![N / 360, N / 180, N / 120, N / 90, N / 72, N / 60, N / 45, N / 40,
    N / 36, N / 30, N / 24, N / 20, N / 18, N / 15, N / 12, N / 10, N / 9,
    N / 8, N / 6] i

/-- The parameter band feeding the `i`-th cutoff: dense-signature parameters
whose full `denseCutoff i`-prefix gadget fits inside `[1, N]` but whose next
larger prefix does not. -/
private def denseBand (N : ℕ) (i : Fin 19) : Finset ℕ :=
  (Finset.Icc (denseLo N i) (denseHi N i)).filter DenseParam

private theorem denseHi_eq (N : ℕ) (i : Fin 19) :
    denseHi N i = N / denseCutoff i := by
  fin_cases i <;> rfl

private theorem denseLo_eq (N : ℕ) (i : Fin 19) :
    denseLo N i = N / densePrevCutoff i + 1 := by
  fin_cases i <;> simp [denseLo, densePrevCutoff]

private theorem denseCutoff_pos (i : Fin 19) : 0 < denseCutoff i := by
  fin_cases i <;> decide

/-- The cutoff tables interleave: for `i < j`, the previous cutoff of band `j`
is positive and at most the cutoff of band `i`. -/
private theorem densePrevCutoff_pos_le {i j : Fin 19} (hij : i < j) :
    0 < densePrevCutoff j ∧ densePrevCutoff j ≤ denseCutoff i := by
  revert i j
  decide

private theorem denseBand_mem {N : ℕ} (i : Fin 19) {a : ℕ}
    (ha : a ∈ denseBand N i) :
    0 < a ∧ DenseParam a ∧ denseCutoff i * a ≤ N := by
  obtain ⟨hIcc, hv⟩ := Finset.mem_filter.mp ha
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hIcc
  rw [denseHi_eq] at hhi
  rw [denseLo_eq] at hlo
  refine ⟨Nat.lt_of_lt_of_le (Nat.succ_pos _) hlo, hv, ?_⟩
  rw [mul_comm]
  exact (Nat.le_div_iff_mul_le (denseCutoff_pos i)).mp hhi

/-- Bands at distinct indices contain distinct parameters: the bands are
sub-intervals of `[1, N/6]` listed in increasing order. -/
private theorem denseBand_param_ne {N : ℕ} {i j : Fin 19} (hij : i ≠ j)
    {a₁ a₂ : ℕ} (ha₁ : a₁ ∈ denseBand N i) (ha₂ : a₂ ∈ denseBand N j) :
    a₁ ≠ a₂ := by
  have key : ∀ {i' j' : Fin 19}, i' < j' → ∀ {b₁ b₂ : ℕ},
      b₁ ∈ denseBand N i' → b₂ ∈ denseBand N j' → b₁ < b₂ := by
    intro i' j' hij' b₁ b₂ hb₁ hb₂
    obtain ⟨hpos, hle⟩ := densePrevCutoff_pos_le hij'
    have h₁ : b₁ ≤ denseHi N i' :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hb₁).1).2
    have h₂ : denseLo N j' ≤ b₂ :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hb₂).1).1
    rw [denseHi_eq] at h₁
    rw [denseLo_eq] at h₂
    have hdiv : N / denseCutoff i' ≤ N / densePrevCutoff j' :=
      Nat.div_le_div_left hle hpos
    exact Nat.lt_of_le_of_lt (h₁.trans hdiv)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h₂)
  rcases lt_or_gt_of_ne hij with h | h
  · exact Nat.ne_of_lt (key h ha₁ ha₂)
  · exact (Nat.ne_of_lt (key h ha₂ ha₁)).symm

private theorem denseGadget_threeSixty_eq (a : ℕ) :
    denseGadget 360 a =
      (Finset.univ : Finset (Fin 23)).image fun i => denseMul i * a := by
  rw [denseGadget]
  congr 1

/-- Full dense gadgets at distinct dense-signature parameters are disjoint. -/
private theorem dense_full_gadgets_disjoint' {a₁ a₂ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hne : a₁ ≠ a₂)
    (hv₁ : DenseParam a₁) (hv₂ : DenseParam a₂) :
    Disjoint (denseGadget 360 a₁) (denseGadget 360 a₂) := by
  rw [denseGadget_threeSixty_eq, denseGadget_threeSixty_eq]
  exact dense_full_gadgets_disjoint ha₁ ha₂ hne hv₁ hv₂

/-- **Nineteen-band packing bound from the dense `{2:4,3:3,5:2}` signature
template.**

Every sum-free `A ⊆ {1, …, N}` loses at least `denseSize i - denseKeep i`
elements from each scaled multiplier gadget, summed over all dense-signature
parameters in the nineteen bands.  The per-band deficits are
`13,12,11,10,9,9,8,7,6,6,5,4,3,3,2,1,1,1,1` at cutoffs
`360,180,120,90,72,60,45,40,36,30,24,20,18,15,12,10,9,8,6`.  Weighted by the
band widths `1/cᵢ - 1/cᵢ₋₁`, the deficits sum to `192/360 = 8/15`; since
`DenseParam` has asymptotic density `4/13`, the forced omission mass is
`(4/13)·(8/15) = 32/195`, i.e. asymptotic shape `f₃₀₁(N) ≤ (163/195 + o(1))N`.
This improves the same-signature bound `145/168` from `UpperBound.lean`. -/
theorem sum_free_dense_template_163_195_bound (N : ℕ) (A : Finset ℕ)
    (hA : SumFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ∑ i : Fin 19, (denseSize i - denseKeep i) * (denseBand N i).card ≤ N := by
  let J : Finset (Fin 19) := Finset.univ
  let gadget : Fin 19 → ℕ → Finset ℕ := fun i a => denseGadget (denseCutoff i) a
  have h := PackingBound.indexed_family_bound N A J (denseBand N) gadget denseSize denseKeep
    (fun i _ => denseKeep_le_size i) hAN
    (by
      intro i _hi a₁ ha₁ a₂ ha₂ hne
      have hm₁ := denseBand_mem i (Finset.mem_coe.mp ha₁)
      have hm₂ := denseBand_mem i (Finset.mem_coe.mp ha₂)
      exact (dense_full_gadgets_disjoint' hm₁.1 hm₂.1 hne hm₁.2.1 hm₂.2.1).mono
        (denseGadget_subset_full (denseCutoff_le_threeSixty i))
        (denseGadget_subset_full (denseCutoff_le_threeSixty i)))
    (by
      intro i _hi a ha
      have hm := denseBand_mem i ha
      calc
        (gadget i a).card = (densePrefix (denseCutoff i)).card :=
          denseGadget_card_eq_prefix_card hm.1
        _ = denseSize i := densePrefix_card_eq_size i)
    (by
      intro i _hi a ha
      exact denseGadget_inter_le_keep hA (denseBand_mem i ha).1 i)
    (by
      intro i _hi
      exact Finset.biUnion_subset.mpr fun a ha =>
        denseGadget_subset_Icc (denseBand_mem i ha).1 (denseBand_mem i ha).2.2)
    (by
      intro i _hi j _hj hij
      rw [Finset.disjoint_biUnion_left]
      intro a₁ ha₁
      rw [Finset.disjoint_biUnion_right]
      intro a₂ ha₂
      have hm₁ := denseBand_mem i ha₁
      have hm₂ := denseBand_mem j ha₂
      have hne : a₁ ≠ a₂ := denseBand_param_ne hij ha₁ ha₂
      exact (dense_full_gadgets_disjoint' hm₁.1 hm₂.1 hne hm₁.2.1 hm₂.2.1).mono
        (denseGadget_subset_full (denseCutoff_le_threeSixty i))
        (denseGadget_subset_full (denseCutoff_le_threeSixty j)))
  simpa [J] using h

/-! ### The asymptotic calculation -/

/-- **The asymptotic deficit mass of the dense template is `32/195`.**

The deficits `denseSize i - denseKeep i` weighted by the band widths
`1/cᵢ - 1/cᵢ₋₁` sum to `8/15`; multiplied by the `4/13` density of the
`DenseParam` signature class this gives the forced omission density
`32/195`, hence the asymptotic upper bound `(163/195 + o(1))·N` for
Problem #301. -/
theorem dense_template_density_calculation :
    (4 / 13 : ℚ) *
        (∑ i : Fin 19, ((denseSize i : ℚ) - (denseKeep i : ℚ)) *
          ((denseCutoff i : ℚ)⁻¹ - (densePrevCutoff i : ℚ)⁻¹)) = 32 / 195 ∧
      (1 : ℚ) - 32 / 195 = 163 / 195 := by
  constructor
  · norm_num [Fin.sum_univ_succ, denseSize, denseKeep, denseCutoff,
      densePrevCutoff]
  · norm_num

end UnitFractionSets
