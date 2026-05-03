/-
# Dense Template Candidate for Problem #301

This file starts the Lean formalization of the next concrete step in
`FinalTheoremStrategy.md`: the `{2:4,3:3,5:2}` p-adic signature grid whose
finite search certificate has asymptotic shape

  f₃₀₁(N) ≤ (163/195 + o(1))N.

The first job is to make the 23-multiplier grid usable in packing proofs.  The
parameter class below fixes

* `v₂(a) ≡ 0 mod 4`,
* `v₃(a) ≡ 0 mod 3`,
* `v₅(a) ≡ 0 mod 2`.

This has density `4/13`, and its residue signature separates the 23 multipliers
used by the searched certificate.
-/
import Erdos.UnitFractionSets.Statement
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
  fin_cases i <;> native_decide

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

/-- The compressed 219-witness edge certificate found by `scripts/weighted_sumfree_lp.py`. -/
private def denseWitnessTarget (i : Fin 219) : Fin 23 :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩,
    ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩,
    ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩,
    ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩,
    ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
    ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
    ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
    ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
    ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
    ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
    ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
    ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
    ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
    ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩,
    ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩,
    ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩,
    ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩,
    ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩,
    ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩,
    ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩,
    ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩,
    ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩,
    ⟨7, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩,
    ⟨7, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩,
    ⟨8, by decide⟩, ⟨8, by decide⟩, ⟨8, by decide⟩, ⟨8, by decide⟩, ⟨8, by decide⟩, ⟨8, by decide⟩,
    ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩,
    ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩, ⟨10, by
    decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩,
    ⟨11, by decide⟩, ⟨11, by decide⟩, ⟨11, by decide⟩, ⟨11, by decide⟩, ⟨11, by decide⟩, ⟨12, by
    decide⟩, ⟨12, by decide⟩, ⟨12, by decide⟩, ⟨12, by decide⟩, ⟨12, by decide⟩, ⟨12, by decide⟩,
    ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨13, by decide⟩, ⟨13, by decide⟩, ⟨13, by decide⟩, ⟨14, by
    decide⟩, ⟨14, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨15, by decide⟩, ⟨15, by decide⟩,
    ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨17, by decide⟩, ⟨18, by
    decide⟩] i

private def denseWitnessRhs (i : Fin 219) : Finset (Fin 23) :=
  ![({⟨1, by decide⟩, ⟨4, by decide⟩} : Finset (Fin 23)), ({⟨1, by decide⟩, ⟨5, by decide⟩, ⟨12, by
    decide⟩} : Finset (Fin 23)), ({⟨1, by decide⟩, ⟨5, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩}
    : Finset (Fin 23)), ({⟨1, by decide⟩, ⟨5, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨21, by
    decide⟩} : Finset (Fin 23)), ({⟨1, by decide⟩, ⟨5, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩,
    ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨1, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩} : Finset
    (Fin 23)), ({⟨1, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨18, by decide⟩} : Finset (Fin
    23)), ({⟨1, by decide⟩, ⟨6, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)),
    ({⟨1, by decide⟩, ⟨6, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩} : Finset
    (Fin 23)), ({⟨1, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩} : Finset (Fin 23)), ({⟨1, by
    decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨1, by decide⟩,
    ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨1, by decide⟩, ⟨7, by
    decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩} : Finset (Fin 23)), ({⟨1, by decide⟩, ⟨9, by decide⟩,
    ⟨10, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨1, by
    decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩} :
    Finset (Fin 23)), ({⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨20, by decide⟩} : Finset
    (Fin 23)), ({⟨3, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨16, by decide⟩} : Finset (Fin
    23)), ({⟨3, by decide⟩, ⟨4, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩} : Finset (Fin 23)),
    ({⟨3, by decide⟩, ⟨4, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩} : Finset
    (Fin 23)), ({⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩} :
    Finset (Fin 23)), ({⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨12, by decide⟩, ⟨17, by
    decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩,
    ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨5, by
    decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨15, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩,
    ⟨5, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩} : Finset (Fin
    23)), ({⟨3, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩} :
    Finset (Fin 23)), ({⟨3, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ⟨12, by
    decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩,
    ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨6, by
    decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩} : Finset (Fin 23)),
    ({⟨2, by decide⟩, ⟨8, by decide⟩} : Finset (Fin 23)), ({⟨2, by decide⟩, ⟨9, by decide⟩, ⟨17, by
    decide⟩} : Finset (Fin 23)), ({⟨2, by decide⟩, ⟨9, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩}
    : Finset (Fin 23)), ({⟨2, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩} : Finset (Fin 23)),
    ({⟨2, by decide⟩, ⟨10, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨2,
    by decide⟩, ⟨10, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨2, by
    decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩} : Finset (Fin 23)), ({⟨2, by decide⟩, ⟨11, by
    decide⟩, ⟨14, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨2, by decide⟩, ⟨11, by
    decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨2, by decide⟩, ⟨11, by
    decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨2, by decide⟩, ⟨13, by
    decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨5, by decide⟩,
    ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨6, by decide⟩, ⟨16, by decide⟩} : Finset
    (Fin 23)), ({⟨3, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩} : Finset (Fin 23)), ({⟨3, by
    decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨8, by decide⟩,
    ⟨12, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨8, by decide⟩, ⟨13, by
    decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩,
    ⟨12, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨6, by decide⟩, ⟨11, by decide⟩, ⟨15, by
    decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩,
    ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨7, by
    decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨11, by decide⟩}
    : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨12, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)),
    ({⟨3, by decide⟩, ⟨13, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨13,
    by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨14, by
    decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨14, by decide⟩, ⟨17, by
    decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨14, by decide⟩, ⟨18, by
    decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨3, by decide⟩, ⟨16, by decide⟩, ⟨17, by
    decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨8, by decide⟩} : Finset (Fin
    23)), ({⟨4, by decide⟩, ⟨9, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩,
    ⟨9, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨10, by
    decide⟩, ⟨14, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨10, by decide⟩, ⟨16, by
    decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨10, by decide⟩, ⟨17, by
    decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨11, by decide⟩, ⟨13, by
    decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨21, by
    decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨20, by
    decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨11, by decide⟩, ⟨16, by decide⟩, ⟨19, by
    decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by
    decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨7, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩}
    : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨7, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩} : Finset
    (Fin 23)), ({⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩} : Finset (Fin 23)), ({⟨6, by
    decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩,
    ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨9, by
    decide⟩, ⟨10, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨9, by decide⟩,
    ⟨11, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨9, by decide⟩, ⟨13, by
    decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨11, by
    decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨7, by
    decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩, ⟨8, by decide⟩,
    ⟨12, by decide⟩, ⟨15, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩, ⟨9, by decide⟩, ⟨10, by
    decide⟩, ⟨14, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩, ⟨10, by decide⟩, ⟨12, by
    decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨9, by decide⟩,
    ⟨10, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨8, by
    decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩} :
    Finset (Fin 23)), ({⟨4, by decide⟩, ⟨13, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨14,
    by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨15, by decide⟩, ⟨20, by
    decide⟩} : Finset (Fin 23)), ({⟨4, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩} : Finset (Fin
    23)), ({⟨5, by decide⟩, ⟨9, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩,
    ⟨10, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨10, by
    decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨11, by
    decide⟩, ⟨15, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨12, by decide⟩, ⟨13, by
    decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨21, by
    decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨19, by
    decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨18, by
    decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by
    decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨8, by decide⟩, ⟨21, by decide⟩} : Finset (Fin
    23)), ({⟨6, by decide⟩, ⟨9, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩,
    ⟨10, by decide⟩, ⟨13, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨10, by decide⟩, ⟨15, by
    decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨10, by decide⟩, ⟨16, by
    decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨11, by decide⟩, ⟨15, by
    decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨12, by decide⟩, ⟨15, by
    decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩}
    : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨18, by
    decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨15, by
    decide⟩} : Finset (Fin 23)), ({⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨14, by
    decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨12, by decide⟩} : Finset (Fin 23)), ({⟨5, by
    decide⟩, ⟨13, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨15, by
    decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨16, by decide⟩, ⟨18, by
    decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨5, by decide⟩, ⟨16, by decide⟩, ⟨19, by
    decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨10, by decide⟩} : Finset (Fin
    23)), ({⟨6, by decide⟩, ⟨12, by decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩,
    ⟨13, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨13, by decide⟩, ⟨18, by
    decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩, ⟨9, by decide⟩} : Finset (Fin
    23)), ({⟨7, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩,
    ⟨11, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩, ⟨12, by decide⟩, ⟨15, by
    decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨16, by
    decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨6, by decide⟩, ⟨18, by decide⟩} : Finset (Fin
    23)), ({⟨6, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩,
    ⟨15, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩, ⟨17, by decide⟩, ⟨20, by decide⟩} :
    Finset (Fin 23)), ({⟨7, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨8,
    by decide⟩, ⟨12, by decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨13, by decide⟩, ⟨20, by
    decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩} : Finset (Fin
    23)), ({⟨8, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩,
    ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨16, by
    decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨9, by decide⟩, ⟨11, by
    decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨9, by decide⟩, ⟨12, by decide⟩, ⟨17, by
    decide⟩} : Finset (Fin 23)), ({⟨9, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩} : Finset (Fin
    23)), ({⟨9, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)),
    ({⟨9, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨9,
    by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨9, by
    decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨10, by
    decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨12, by
    decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨12, by
    decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨13, by
    decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨11, by decide⟩, ⟨12, by
    decide⟩, ⟨13, by decide⟩} : Finset (Fin 23)), ({⟨11, by decide⟩, ⟨13, by decide⟩, ⟨14, by
    decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨7, by decide⟩, ⟨19, by decide⟩} : Finset (Fin
    23)), ({⟨8, by decide⟩, ⟨14, by decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨16, by decide⟩,
    ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨9, by decide⟩, ⟨13, by decide⟩, ⟨19, by decide⟩} :
    Finset (Fin 23)), ({⟨9, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨9,
    by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨11, by
    decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩} : Finset (Fin 23)), ({⟨11, by decide⟩, ⟨14, by
    decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨11, by decide⟩, ⟨15, by
    decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨12, by decide⟩, ⟨13, by
    decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨17, by
    decide⟩} : Finset (Fin 23)), ({⟨8, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩} : Finset (Fin
    23)), ({⟨9, by decide⟩, ⟨13, by decide⟩} : Finset (Fin 23)), ({⟨9, by decide⟩, ⟨14, by decide⟩,
    ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨9, by decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩} :
    Finset (Fin 23)), ({⟨10, by decide⟩, ⟨13, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)),
    ({⟨10, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨15,
    by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨15, by
    decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨12, by decide⟩, ⟨13, by
    decide⟩, ⟨15, by decide⟩} : Finset (Fin 23)), ({⟨12, by decide⟩, ⟨15, by decide⟩, ⟨16, by
    decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by
    decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨9, by decide⟩, ⟨17, by decide⟩} : Finset (Fin
    23)), ({⟨10, by decide⟩, ⟨14, by decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨16, by
    decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨17, by decide⟩, ⟨19, by
    decide⟩} : Finset (Fin 23)), ({⟨11, by decide⟩, ⟨13, by decide⟩} : Finset (Fin 23)), ({⟨11, by
    decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨11, by decide⟩, ⟨16, by
    decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by
    decide⟩} : Finset (Fin 23)), ({⟨10, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨11, by
    decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨11, by decide⟩, ⟨19, by decide⟩, ⟨21, by
    decide⟩} : Finset (Fin 23)), ({⟨12, by decide⟩, ⟨15, by decide⟩} : Finset (Fin 23)), ({⟨12, by
    decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨14, by decide⟩, ⟨15, by
    decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨14, by decide⟩, ⟨16, by decide⟩, ⟨17, by
    decide⟩} : Finset (Fin 23)), ({⟨15, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨21, by
    decide⟩} : Finset (Fin 23)), ({⟨11, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨12, by
    decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨12, by decide⟩, ⟨20, by decide⟩, ⟨21, by
    decide⟩} : Finset (Fin 23)), ({⟨13, by decide⟩, ⟨16, by decide⟩} : Finset (Fin 23)), ({⟨13, by
    decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨15, by decide⟩, ⟨16, by
    decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨15, by decide⟩, ⟨17, by decide⟩, ⟨18, by
    decide⟩} : Finset (Fin 23)), ({⟨12, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨13, by
    decide⟩, ⟨17, by decide⟩} : Finset (Fin 23)), ({⟨14, by decide⟩, ⟨16, by decide⟩} : Finset (Fin
    23)), ({⟨14, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨14, by
    decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨16, by decide⟩, ⟨17, by
    decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨13, by decide⟩, ⟨20, by decide⟩} : Finset (Fin
    23)), ({⟨14, by decide⟩, ⟨18, by decide⟩} : Finset (Fin 23)), ({⟨14, by decide⟩, ⟨20, by
    decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨15, by decide⟩, ⟨17, by decide⟩} : Finset (Fin
    23)), ({⟨15, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨16, by
    decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨16, by decide⟩, ⟨19, by
    decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨14, by decide⟩, ⟨21, by decide⟩} : Finset (Fin
    23)), ({⟨15, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨16, by decide⟩, ⟨19, by
    decide⟩} : Finset (Fin 23)), ({⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩} : Finset (Fin
    23)), ({⟨15, by decide⟩, ⟨22, by decide⟩} : Finset (Fin 23)), ({⟨16, by decide⟩, ⟨21, by
    decide⟩} : Finset (Fin 23)), ({⟨17, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨16, by
    decide⟩, ⟨22, by decide⟩} : Finset (Fin 23)), ({⟨17, by decide⟩, ⟨20, by decide⟩} : Finset (Fin
    23)), ({⟨18, by decide⟩, ⟨19, by decide⟩} : Finset (Fin 23)), ({⟨19, by decide⟩, ⟨20, by
    decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨17, by decide⟩, ⟨21, by decide⟩} : Finset (Fin
    23)), ({⟨18, by decide⟩, ⟨20, by decide⟩} : Finset (Fin 23)), ({⟨18, by decide⟩, ⟨22, by
    decide⟩} : Finset (Fin 23)), ({⟨19, by decide⟩, ⟨21, by decide⟩} : Finset (Fin 23)), ({⟨20, by
    decide⟩, ⟨21, by decide⟩} : Finset (Fin 23))] i

private def denseWitnessEdge (i : Fin 219) : Finset (Fin 23) :=
  insert (denseWitnessTarget i) (denseWitnessRhs i)

private def denseBadEdges : Finset (Finset (Fin 23)) :=
  (Finset.univ : Finset (Fin 219)).image denseWitnessEdge

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

/-- Arithmetic density factor for the dense signature class:
`8/15 * 9/13 * 5/6 = 4/13`. -/
theorem denseParam_density_constant :
    ((8 : ℚ) / 15) * (9 / 13) * (5 / 6) = 4 / 13 := by
  norm_num

end UnitFractionSets
