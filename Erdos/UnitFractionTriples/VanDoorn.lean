/-
# Van Doorn's 9/10 Upper Bound for Triple-Free Sets

Two independent families of unit fraction triples:
- **S-family**: S_a = {2a, 3a, 6a} with 1/(2a) = 1/(3a) + 1/(6a)
- **T-family**: T_e = {4e, 5e, 20e} with 1/(4e) = 1/(5e) + 1/(20e)

Parameter predicates control which parameters are valid:
- SParam(a): v₂(a) even ∧ v₃(a) even
- TParam(e): 4 ∣ v₂(e) ∧ v₃(e) even ∧ v₅(e) even

The p-adic valuation parity argument ensures:
- S-triples are pairwise disjoint (valuation signature injective)
- T-triples are pairwise disjoint
- S-triples and T-triples are cross-disjoint

Combined: A.card + |D_S| + |D_T| ≤ N where D_S ⊆ [1,N/6], D_T ⊆ [1,N/20].
This gives f₃₀₂(N) ≤ 9N/10 + o(N).

Reference: van Doorn, erdosproblems.com/302
-/
import Erdos.UnitFractionTriples.UpperBound

namespace UnitFractionTriples

/-! ### Section 1: The T-family triple identity -/

/-- The triple (4e, 5e, 20e) is a unit fraction triple for all e ≥ 1:
    1/(4e) = 1/(5e) + 1/(20e), equivalently 4e·(5e + 20e) = 100e² = 5e·20e. -/
theorem triple_4e_5e_20e (e : ℕ) (he : 0 < e) :
    IsUnitFractionTriple (4 * e) (5 * e) (20 * e) := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [triple_iff_div (by omega) (by omega) (by omega)]
  ring

/-- A triple-free set cannot contain all three of 4e, 5e, 20e (for e ≥ 1). -/
theorem triple_free_excludes_one_T {A : Finset ℕ} (hA : TripleFree A) {e : ℕ}
    (he : 0 < e) (h4 : 4 * e ∈ A) (h5 : 5 * e ∈ A) (h20 : 20 * e ∈ A) : False :=
  hA (4 * e) h4 (5 * e) h5 (20 * e) h20 (by omega) (by omega) (by omega)
    (triple_4e_5e_20e e he)

/-! ### Section 2: Parameter predicates -/

/-- SParam(a) holds when v₂(a) and v₃(a) are both even.
    Equivalently, a = 4^b · 9^c · d where gcd(d,6) = 1. -/
def SParam (a : ℕ) : Prop :=
  Even (padicValNat 2 a) ∧ Even (padicValNat 3 a)

/-- TParam(e) holds when 4 ∣ v₂(e), v₃(e) is even, and v₅(e) is even.
    Equivalently, e = 16^f · 9^g · 25^h · i where gcd(i,30) = 1. -/
def TParam (e : ℕ) : Prop :=
  4 ∣ padicValNat 2 e ∧ Even (padicValNat 3 e) ∧ Even (padicValNat 5 e)

instance : DecidablePred SParam := fun a =>
  inferInstanceAs (Decidable (Even (padicValNat 2 a) ∧ Even (padicValNat 3 a)))

instance : DecidablePred TParam := fun e =>
  inferInstanceAs (Decidable (4 ∣ padicValNat 2 e ∧ Even (padicValNat 3 e) ∧
    Even (padicValNat 5 e)))

/-! ### Section 3: Valuation computation lemmas

For each multiplier c ∈ {2,3,4,5,6,20} and relevant prime p, we compute
the parity of v_p(c·a) = v_p(c) + v_p(a) using `padicValNat.mul`. -/

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- v₂(2) = 1 -/
private lemma v2_two : padicValNat 2 2 = 1 := by simp

/-- v₂(3) = 0 -/
private lemma v2_three : padicValNat 2 3 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

/-- v₂(4) = 2 -/
private lemma v2_four : padicValNat 2 4 = 2 := by
  have : padicValNat 2 (2 * 2) = padicValNat 2 2 + padicValNat 2 2 :=
    padicValNat.mul (by decide) (by decide)
  simp at this ⊢; linarith

/-- v₂(5) = 0 -/
private lemma v2_five : padicValNat 2 5 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

/-- v₂(6) = 1 -/
private lemma v2_six : padicValNat 2 6 = 1 := by
  have : padicValNat 2 (2 * 3) = padicValNat 2 2 + padicValNat 2 3 :=
    padicValNat.mul (by decide) (by decide)
  simp [v2_three] at this
  exact this

/-- v₂(20) = 2 -/
private lemma v2_twenty : padicValNat 2 20 = 2 := by
  have : padicValNat 2 (4 * 5) = padicValNat 2 4 + padicValNat 2 5 :=
    padicValNat.mul (by decide) (by decide)
  simp [v2_four, v2_five] at this
  exact this

/-- v₃(2) = 0 -/
private lemma v3_two : padicValNat 3 2 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

/-- v₃(3) = 1 -/
private lemma v3_three : padicValNat 3 3 = 1 := by simp

/-- v₃(4) = 0 -/
private lemma v3_four : padicValNat 3 4 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

/-- v₃(5) = 0 -/
private lemma v3_five : padicValNat 3 5 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

/-- v₃(6) = 1 -/
private lemma v3_six : padicValNat 3 6 = 1 := by
  have h : padicValNat 3 (2 * 3) = padicValNat 3 2 + padicValNat 3 3 :=
    padicValNat.mul (by decide) (by decide)
  rw [v3_two, v3_three] at h; exact h

/-- v₃(20) = 0 -/
private lemma v3_twenty : padicValNat 3 20 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

/-- v₅(4) = 0 -/
private lemma v5_four : padicValNat 5 4 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

/-- v₅(5) = 1 -/
private lemma v5_five : padicValNat 5 5 = 1 := by simp

/-- v₅(20) = 1 -/
private lemma v5_twenty : padicValNat 5 20 = 1 := by
  have h : padicValNat 5 (4 * 5) = padicValNat 5 4 + padicValNat 5 5 :=
    padicValNat.mul (by decide) (by decide)
  rw [v5_four, v5_five] at h; exact h

/-! #### Parity transfer lemmas for the S-family multipliers {2, 3, 6} -/

/-- v₂(2·a) is odd when v₂(a) is even. -/
private lemma v2_two_mul_odd {a : ℕ} (ha : a ≠ 0) (hev : Even (padicValNat 2 a)) :
    ¬Even (padicValNat 2 (2 * a)) := by
  rw [padicValNat.mul (by decide) ha, v2_two]
  obtain ⟨k, hk⟩ := hev; rw [hk]; intro ⟨m, hm⟩; omega

/-- v₃(3·a) is odd when v₃(a) is even. -/
private lemma v3_three_mul_odd {a : ℕ} (ha : a ≠ 0) (hev : Even (padicValNat 3 a)) :
    ¬Even (padicValNat 3 (3 * a)) := by
  rw [padicValNat.mul (by decide) ha, v3_three]
  obtain ⟨k, hk⟩ := hev; rw [hk]; intro ⟨m, hm⟩; omega

/-- v₂(3·a) = v₂(a), so parity is preserved. -/
private lemma v2_three_mul {a : ℕ} (ha : a ≠ 0) :
    padicValNat 2 (3 * a) = padicValNat 2 a := by
  rw [padicValNat.mul (by decide) ha, v2_three, zero_add]

/-- v₃(2·a) = v₃(a), so parity is preserved. -/
private lemma v3_two_mul {a : ℕ} (ha : a ≠ 0) :
    padicValNat 3 (2 * a) = padicValNat 3 a := by
  rw [padicValNat.mul (by decide) ha, v3_two, zero_add]

/-- v₂(6·a) is odd when v₂(a) is even (since v₂(6) = 1). -/
private lemma v2_six_mul_odd {a : ℕ} (ha : a ≠ 0) (hev : Even (padicValNat 2 a)) :
    ¬Even (padicValNat 2 (6 * a)) := by
  rw [padicValNat.mul (by decide) ha, v2_six]
  obtain ⟨k, hk⟩ := hev; rw [hk]; intro ⟨m, hm⟩; omega

/-- v₃(6·a) is odd when v₃(a) is even (since v₃(6) = 1). -/
private lemma v3_six_mul_odd {a : ℕ} (ha : a ≠ 0) (hev : Even (padicValNat 3 a)) :
    ¬Even (padicValNat 3 (6 * a)) := by
  rw [padicValNat.mul (by decide) ha, v3_six]
  obtain ⟨k, hk⟩ := hev; rw [hk]; intro ⟨m, hm⟩; omega

/-! #### Parity transfer lemmas for the T-family multipliers {4, 5, 20} -/

/-- v₂(4·e) = 2 + v₂(e). -/
private lemma v2_four_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 2 (4 * e) = 2 + padicValNat 2 e := by
  rw [padicValNat.mul (by decide) he, v2_four]

/-- v₂(5·e) = v₂(e). -/
private lemma v2_five_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 2 (5 * e) = padicValNat 2 e := by
  rw [padicValNat.mul (by decide) he, v2_five, zero_add]

/-- v₂(20·e) = 2 + v₂(e). -/
private lemma v2_twenty_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 2 (20 * e) = 2 + padicValNat 2 e := by
  rw [padicValNat.mul (by decide) he, v2_twenty]

/-- v₃(4·e) = v₃(e). -/
private lemma v3_four_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 3 (4 * e) = padicValNat 3 e := by
  rw [padicValNat.mul (by decide) he, v3_four, zero_add]

/-- v₃(5·e) = v₃(e). -/
private lemma v3_five_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 3 (5 * e) = padicValNat 3 e := by
  rw [padicValNat.mul (by decide) he, v3_five, zero_add]

/-- v₃(20·e) = v₃(e). -/
private lemma v3_twenty_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 3 (20 * e) = padicValNat 3 e := by
  rw [padicValNat.mul (by decide) he, v3_twenty, zero_add]

/-- v₅(4·e) = v₅(e). -/
private lemma v5_four_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 5 (4 * e) = padicValNat 5 e := by
  rw [padicValNat.mul (by decide) he, v5_four, zero_add]

/-- v₅(5·e) = 1 + v₅(e). -/
private lemma v5_five_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 5 (5 * e) = 1 + padicValNat 5 e := by
  rw [padicValNat.mul (by decide) he, v5_five]

/-- v₅(20·e) = 1 + v₅(e). -/
private lemma v5_twenty_mul {e : ℕ} (he : e ≠ 0) :
    padicValNat 5 (20 * e) = 1 + padicValNat 5 e := by
  rw [padicValNat.mul (by decide) he, v5_twenty]

/-! ### Section 4: S-family intra-disjointness

The valuation signature (v₂ mod 2, v₃ mod 2) distinguishes the multipliers:
  - 2a: v₂ odd, v₃ even   (signature (1,0))
  - 3a: v₂ even, v₃ odd   (signature (0,1))
  - 6a: v₂ odd, v₃ odd    (signature (1,1))
So if c₁·a₁ = c₂·a₂ with SParam, then c₁ = c₂ (same signature), hence a₁ = a₂. -/

/-- For distinct a₁, a₂ with SParam, the triples {2a₁, 3a₁, 6a₁} and
    {2a₂, 3a₂, 6a₂} are disjoint. -/
theorem s_triples_disjoint {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hne : a₁ ≠ a₂) (hs₁ : SParam a₁) (hs₂ : SParam a₂) :
    Disjoint ({2*a₁, 3*a₁, 6*a₁} : Finset ℕ) {2*a₂, 3*a₂, 6*a₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  have ha₁' : a₁ ≠ 0 := by omega
  have ha₂' : a₂ ≠ 0 := by omega
  rcases hx₁ with rfl | rfl | rfl <;> rcases hx₂ with h | h | h
  -- 2a₁ = 2a₂ → a₁ = a₂
  · exact hne (by omega)
  -- 2a₁ = 3a₂ → v₂(LHS) = 1 + even = odd, v₂(RHS) = 0 + even = even
  · have h1 := v2_two_mul_odd ha₁' hs₁.1
    rw [h] at h1; exact h1 (by rw [v2_three_mul ha₂']; exact hs₂.1)
  -- 2a₁ = 6a₂ → v₃(LHS) = 0 + even = even, v₃(RHS) = 1 + even = odd
  · have h1 : Even (padicValNat 3 (2 * a₁)) := by rw [v3_two_mul ha₁']; exact hs₁.2
    rw [h] at h1; exact v3_six_mul_odd ha₂' hs₂.2 h1
  -- 3a₁ = 2a₂ → v₂(LHS) even, v₂(RHS) odd
  · have h1 : Even (padicValNat 2 (3 * a₁)) := by rw [v2_three_mul ha₁']; exact hs₁.1
    rw [h] at h1; exact v2_two_mul_odd ha₂' hs₂.1 h1
  -- 3a₁ = 3a₂ → a₁ = a₂
  · exact hne (by omega)
  -- 3a₁ = 6a₂ → v₂(LHS) even, v₂(RHS) odd
  · have h1 : Even (padicValNat 2 (3 * a₁)) := by rw [v2_three_mul ha₁']; exact hs₁.1
    rw [h] at h1; exact v2_six_mul_odd ha₂' hs₂.1 h1
  -- 6a₁ = 2a₂ → v₃(LHS) odd, v₃(RHS) even
  · have h1 := v3_six_mul_odd ha₁' hs₁.2
    rw [h] at h1; exact h1 (by rw [v3_two_mul ha₂']; exact hs₂.2)
  -- 6a₁ = 3a₂ → v₂(LHS) odd, v₂(RHS) even
  · have h1 := v2_six_mul_odd ha₁' hs₁.1
    rw [h] at h1; exact h1 (by rw [v2_three_mul ha₂']; exact hs₂.1)
  -- 6a₁ = 6a₂ → a₁ = a₂
  · exact hne (by omega)

/-! ### Section 5: T-family intra-disjointness

The valuation signature distinguishes the multipliers {4, 5, 20}:
  - 4e:  v₅ even, v₂ ≡ 2 mod 4  (from v₂(4e) = 2 + v₂(e), 4 | v₂(e))
  - 5e:  v₅ odd,  v₂ ≡ 0 mod 4  (from v₂(5e) = v₂(e), 4 | v₂(e))
  - 20e: v₅ odd,  v₂ ≡ 2 mod 4  (from v₂(20e) = 2 + v₂(e), 4 | v₂(e))

Cases (4,5), (5,4), (4,20), (20,4): v₅ parity mismatch.
Cases (5,20), (20,5): v₂ mod 4 mismatch.
Diagonal: a₁ = a₂. -/

/-- v₅(4·e) is even when v₅(e) is even. -/
private lemma v5_four_mul_even {e : ℕ} (he : e ≠ 0) (hev : Even (padicValNat 5 e)) :
    Even (padicValNat 5 (4 * e)) := by
  rw [v5_four_mul he]; exact hev

/-- v₅(5·e) is odd when v₅(e) is even. -/
private lemma v5_five_mul_odd {e : ℕ} (he : e ≠ 0) (hev : Even (padicValNat 5 e)) :
    ¬Even (padicValNat 5 (5 * e)) := by
  rw [v5_five_mul he]
  obtain ⟨k, hk⟩ := hev; rw [hk]; intro ⟨m, hm⟩; omega

/-- v₅(20·e) is odd when v₅(e) is even. -/
private lemma v5_twenty_mul_odd {e : ℕ} (he : e ≠ 0) (hev : Even (padicValNat 5 e)) :
    ¬Even (padicValNat 5 (20 * e)) := by
  rw [v5_twenty_mul he]
  obtain ⟨k, hk⟩ := hev; rw [hk]; intro ⟨m, hm⟩; omega

/-- v₂(5·e) mod 4 = 0 when 4 | v₂(e). -/
private lemma v2_five_mul_mod4 {e : ℕ} (he : e ≠ 0) (h4 : 4 ∣ padicValNat 2 e) :
    4 ∣ padicValNat 2 (5 * e) := by
  rw [v2_five_mul he]; exact h4

/-- v₂(4·e) mod 4 = 2 when 4 | v₂(e), so ¬(4 | v₂(4e)). -/
private lemma v2_four_mul_not_mod4 {e : ℕ} (he : e ≠ 0) (h4 : 4 ∣ padicValNat 2 e) :
    ¬(4 ∣ padicValNat 2 (4 * e)) := by
  rw [v2_four_mul he]
  obtain ⟨k, hk⟩ := h4; rw [hk]; intro ⟨m, hm⟩; omega

/-- v₂(20·e) mod 4 = 2 when 4 | v₂(e), so ¬(4 | v₂(20e)). -/
private lemma v2_twenty_mul_not_mod4 {e : ℕ} (he : e ≠ 0) (h4 : 4 ∣ padicValNat 2 e) :
    ¬(4 ∣ padicValNat 2 (20 * e)) := by
  rw [v2_twenty_mul he]
  obtain ⟨k, hk⟩ := h4; rw [hk]; intro ⟨m, hm⟩; omega

/-- For distinct e₁, e₂ with TParam, the triples {4e₁, 5e₁, 20e₁} and
    {4e₂, 5e₂, 20e₂} are disjoint. -/
theorem t_triples_disjoint {e₁ e₂ : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hne : e₁ ≠ e₂) (ht₁ : TParam e₁) (ht₂ : TParam e₂) :
    Disjoint ({4*e₁, 5*e₁, 20*e₁} : Finset ℕ) {4*e₂, 5*e₂, 20*e₂} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  have he₁' : e₁ ≠ 0 := by omega
  have he₂' : e₂ ≠ 0 := by omega
  rcases hx₁ with rfl | rfl | rfl <;> rcases hx₂ with h | h | h
  -- 4e₁ = 4e₂ → e₁ = e₂
  · exact hne (by omega)
  -- 4e₁ = 5e₂ → v₅(LHS) even, v₅(RHS) odd
  · have h1 := v5_four_mul_even he₁' ht₁.2.2
    rw [h] at h1; exact v5_five_mul_odd he₂' ht₂.2.2 h1
  -- 4e₁ = 20e₂ → v₅(LHS) even, v₅(RHS) odd
  · have h1 := v5_four_mul_even he₁' ht₁.2.2
    rw [h] at h1; exact v5_twenty_mul_odd he₂' ht₂.2.2 h1
  -- 5e₁ = 4e₂ → v₅(LHS) odd, v₅(RHS) even
  · have h1 := v5_five_mul_odd he₁' ht₁.2.2
    rw [h] at h1; exact h1 (v5_four_mul_even he₂' ht₂.2.2)
  -- 5e₁ = 5e₂ → e₁ = e₂
  · exact hne (by omega)
  -- 5e₁ = 20e₂ → v₂(LHS) ≡ 0 mod 4, v₂(RHS) ≡ 2 mod 4
  · have h1 := v2_five_mul_mod4 he₁' ht₁.1
    rw [h] at h1; exact v2_twenty_mul_not_mod4 he₂' ht₂.1 h1
  -- 20e₁ = 4e₂ → v₅(LHS) odd, v₅(RHS) even
  · have h1 := v5_twenty_mul_odd he₁' ht₁.2.2
    rw [h] at h1; exact h1 (v5_four_mul_even he₂' ht₂.2.2)
  -- 20e₁ = 5e₂ → v₂(LHS) ≡ 2 mod 4, v₂(RHS) ≡ 0 mod 4
  · have h1 := v2_twenty_mul_not_mod4 he₁' ht₁.1
    rw [h] at h1; exact h1 (v2_five_mul_mod4 he₂' ht₂.1)
  -- 20e₁ = 20e₂ → e₁ = e₂
  · exact hne (by omega)

/-! ### Section 6: Cross-family disjointness

Every S-element has odd v₂ or odd v₃. Every T-element has even v₂ and even v₃.
So no element can be in both families. -/

/-- Every element of {2a, 3a, 6a} with SParam(a) has odd v₂ or odd v₃. -/
private lemma s_element_odd_val {a x : ℕ} (ha : 0 < a) (hs : SParam a)
    (hx : x ∈ ({2*a, 3*a, 6*a} : Finset ℕ)) :
    ¬Even (padicValNat 2 x) ∨ ¬Even (padicValNat 3 x) := by
  have ha' : a ≠ 0 := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact Or.inl (v2_two_mul_odd ha' hs.1)
  · exact Or.inr (v3_three_mul_odd ha' hs.2)
  · exact Or.inl (v2_six_mul_odd ha' hs.1)

/-- Every element of {4e, 5e, 20e} with TParam(e) has even v₂ and even v₃. -/
private lemma t_element_even_vals {e x : ℕ} (he : 0 < e) (ht : TParam e)
    (hx : x ∈ ({4*e, 5*e, 20*e} : Finset ℕ)) :
    Even (padicValNat 2 x) ∧ Even (padicValNat 3 x) := by
  have he' : e ≠ 0 := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · -- 4e: v₂ = 2 + v₂(e), 4|v₂(e) so even; v₃ = v₃(e), even
    constructor
    · rw [v2_four_mul he']; obtain ⟨k, hk⟩ := ht.1; rw [hk]; exact ⟨k * 2 + 1, by omega⟩
    · rw [v3_four_mul he']; exact ht.2.1
  · -- 5e: v₂ = v₂(e), 4|v₂(e) so even; v₃ = v₃(e), even
    constructor
    · rw [v2_five_mul he']; obtain ⟨k, hk⟩ := ht.1; exact ⟨k * 2, by omega⟩
    · rw [v3_five_mul he']; exact ht.2.1
  · -- 20e: v₂ = 2 + v₂(e), 4|v₂(e) so even; v₃ = v₃(e), even
    constructor
    · rw [v2_twenty_mul he']; obtain ⟨k, hk⟩ := ht.1; rw [hk]; exact ⟨k * 2 + 1, by omega⟩
    · rw [v3_twenty_mul he']; exact ht.2.1

/-- S-triples and T-triples are cross-disjoint: any shared element would need
    to have both (odd v₂ or odd v₃) and (even v₂ and even v₃). -/
theorem s_t_cross_disjoint {a e : ℕ} (ha : 0 < a) (he : 0 < e)
    (hsa : SParam a) (hte : TParam e) :
    Disjoint ({2*a, 3*a, 6*a} : Finset ℕ) {4*e, 5*e, 20*e} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  obtain ⟨hev2, hev3⟩ := t_element_even_vals he hte hx₂
  rcases s_element_odd_val ha hsa hx₁ with hodd | hodd
  · exact hodd hev2
  · exact hodd hev3

/-! ### Section 7: T-family Finset infrastructure -/

/-- The T-triple {4e, 5e, 20e} has exactly 3 elements for e > 0. -/
theorem t_triple_card_eq_three {e : ℕ} (he : 0 < e) :
    ({4*e, 5*e, 20*e} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

/-- The T-triple {4e, 5e, 20e} ⊆ {1, …, N} when 20e ≤ N and e > 0. -/
theorem t_triple_subset_Icc {e N : ℕ} (he : 0 < e) (h20 : 20 * e ≤ N) :
    ({4*e, 5*e, 20*e} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl <;> omega

/-- A triple-free set keeps at most 2 elements from {4e, 5e, 20e}. -/
theorem t_triple_inter_card_le_two {A : Finset ℕ} (hA : TripleFree A)
    {e : ℕ} (he : 0 < e) :
    (({4*e, 5*e, 20*e} : Finset ℕ) ∩ A).card ≤ 2 := by
  suffices h : ∃ x ∈ ({4*e, 5*e, 20*e} : Finset ℕ), x ∉ A by
    obtain ⟨x, hxT, hxA⟩ := h
    calc (({4*e, 5*e, 20*e} : Finset ℕ) ∩ A).card
        ≤ (({4*e, 5*e, 20*e} : Finset ℕ).erase x).card :=
          Finset.card_le_card fun a ha =>
            Finset.mem_erase.mpr ⟨fun h => by subst h; exact hxA (Finset.mem_inter.mp ha).2,
              (Finset.mem_inter.mp ha).1⟩
      _ = ({4*e, 5*e, 20*e} : Finset ℕ).card - 1 := Finset.card_erase_of_mem hxT
      _ = 2 := by rw [t_triple_card_eq_three he]
  by_contra h; push_neg at h
  exact triple_free_excludes_one_T hA he (h _ (by simp)) (h _ (by simp)) (h _ (by simp))

/-- The S-triple {2d, 3d, 6d} has exactly 3 elements for d > 0. -/
private theorem s_triple_card_eq_three {d : ℕ} (hd : 0 < d) :
    ({2*d, 3*d, 6*d} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  rw [Finset.card_insert_of_notMem (by simp; omega)]
  simp

/-- The S-triple {2d, 3d, 6d} ⊆ {1, …, N} when 6d ≤ N and d > 0. -/
private theorem s_triple_subset_Icc {d N : ℕ} (hd : 0 < d) (h6 : 6 * d ≤ N) :
    ({2*d, 3*d, 6*d} : Finset ℕ) ⊆ Finset.Icc 1 N := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl | rfl <;> omega

/-- A triple-free set keeps at most 2 elements from {2d, 3d, 6d}. -/
private theorem s_triple_inter_card_le_two {A : Finset ℕ} (hA : TripleFree A)
    {d : ℕ} (hd : 0 < d) :
    (({2*d, 3*d, 6*d} : Finset ℕ) ∩ A).card ≤ 2 := by
  suffices h : ∃ x ∈ ({2*d, 3*d, 6*d} : Finset ℕ), x ∉ A by
    obtain ⟨x, hxT, hxA⟩ := h
    calc (({2*d, 3*d, 6*d} : Finset ℕ) ∩ A).card
        ≤ (({2*d, 3*d, 6*d} : Finset ℕ).erase x).card :=
          Finset.card_le_card fun a ha =>
            Finset.mem_erase.mpr ⟨fun h => by subst h; exact hxA (Finset.mem_inter.mp ha).2,
              (Finset.mem_inter.mp ha).1⟩
      _ = ({2*d, 3*d, 6*d} : Finset ℕ).card - 1 := Finset.card_erase_of_mem hxT
      _ = 2 := by rw [s_triple_card_eq_three hd]
  by_contra h; push_neg at h
  exact triple_free_excludes_one hA hd (h _ (by simp)) (h _ (by simp)) (h _ (by simp))

/-! ### Section 8: Capstone counting theorem -/

/-- **Van Doorn's structural bound.** For D_S = {a ∈ [1,N/6] : SParam a} and
    D_T = {e ∈ [1,N/20] : TParam e}, all S-triples and T-triples are pairwise
    disjoint (within and across families), each forcing ≥1 exclusion from a
    triple-free set A ⊆ {1,…,N}. Combined: A.card + |D_S| + |D_T| ≤ N.

    Since |D_S| ≈ N/12 and |D_T| ≈ N/60, this gives f₃₀₂(N) ≤ 9N/10 + o(N). -/
theorem van_doorn_upper_bound (N : ℕ) (A : Finset ℕ)
    (hA : TripleFree A) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card + ((Finset.Icc 1 (N / 6)).filter SParam).card
           + ((Finset.Icc 1 (N / 20)).filter TParam).card ≤ N := by
  set D_S := (Finset.Icc 1 (N / 6)).filter SParam with hDS_def
  set D_T := (Finset.Icc 1 (N / 20)).filter TParam with hDT_def
  let s_triple : ℕ → Finset ℕ := fun a => {2*a, 3*a, 6*a}
  let t_triple : ℕ → Finset ℕ := fun e => {4*e, 5*e, 20*e}
  -- Properties of D_S and D_T members
  have hDS_mem : ∀ a ∈ D_S, 0 < a ∧ SParam a ∧ 6 * a ≤ N := by
    intro a ha; simp only [hDS_def, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨by omega, ha.2, by omega⟩
  have hDT_mem : ∀ e ∈ D_T, 0 < e ∧ TParam e ∧ 20 * e ≤ N := by
    intro e he; simp only [hDT_def, Finset.mem_filter, Finset.mem_Icc] at he
    exact ⟨by omega, he.2, by omega⟩
  -- Step 1: S-triples are pairwise disjoint on D_S
  have hpwd_S : (↑D_S : Set ℕ).PairwiseDisjoint s_triple := by
    intro a₁ ha₁ a₂ ha₂ hne
    exact s_triples_disjoint
      (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).1
      (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).1
      hne
      (hDS_mem a₁ (Finset.mem_coe.mp ha₁)).2.1
      (hDS_mem a₂ (Finset.mem_coe.mp ha₂)).2.1
  -- Step 2: T-triples are pairwise disjoint on D_T
  have hpwd_T : (↑D_T : Set ℕ).PairwiseDisjoint t_triple := by
    intro e₁ he₁ e₂ he₂ hne
    exact t_triples_disjoint
      (hDT_mem e₁ (Finset.mem_coe.mp he₁)).1
      (hDT_mem e₂ (Finset.mem_coe.mp he₂)).1
      hne
      (hDT_mem e₁ (Finset.mem_coe.mp he₁)).2.1
      (hDT_mem e₂ (Finset.mem_coe.mp he₂)).2.1
  -- Step 3: Define unions
  set U_S := D_S.biUnion s_triple with hUS_def
  set U_T := D_T.biUnion t_triple with hUT_def
  -- Step 4: U_S ⊆ Icc 1 N
  have hUSsub : U_S ⊆ Finset.Icc 1 N :=
    Finset.biUnion_subset.mpr fun a ha =>
      s_triple_subset_Icc (hDS_mem a ha).1 (hDS_mem a ha).2.2
  -- Step 5: U_T ⊆ Icc 1 N
  have hUTsub : U_T ⊆ Finset.Icc 1 N :=
    Finset.biUnion_subset.mpr fun e he =>
      t_triple_subset_Icc (hDT_mem e he).1 (hDT_mem e he).2.2
  -- Step 6: U_S and U_T are disjoint (cross-family)
  have hU_disj : Disjoint U_S U_T := by
    rw [hUS_def, hUT_def, Finset.disjoint_biUnion_left]
    intro a ha
    rw [Finset.disjoint_biUnion_right]
    intro e he
    exact s_t_cross_disjoint (hDS_mem a ha).1 (hDT_mem e he).1
      (hDS_mem a ha).2.1 (hDT_mem e he).2.1
  -- Step 7: |U_S| = 3|D_S|
  have hUScard : U_S.card = 3 * D_S.card := by
    rw [hUS_def, Finset.card_biUnion hpwd_S,
        Finset.sum_const_nat (fun a ha => s_triple_card_eq_three (hDS_mem a ha).1)]
    ring
  -- Step 8: |U_T| = 3|D_T|
  have hUTcard : U_T.card = 3 * D_T.card := by
    rw [hUT_def, Finset.card_biUnion hpwd_T,
        Finset.sum_const_nat (fun e he => t_triple_card_eq_three (hDT_mem e he).1)]
    ring
  -- Step 9: |U_S ∪ U_T| = |U_S| + |U_T|
  have hU_card : (U_S ∪ U_T).card = U_S.card + U_T.card :=
    Finset.card_union_of_disjoint hU_disj
  -- Step 10: U_S ∪ U_T ⊆ Icc 1 N
  have hUsub : U_S ∪ U_T ⊆ Finset.Icc 1 N :=
    Finset.union_subset hUSsub hUTsub
  -- Step 11: |U_S ∩ A| ≤ 2|D_S|
  have hUSA : (U_S ∩ A).card ≤ 2 * D_S.card := by
    rw [show U_S = D_S.biUnion s_triple from rfl, Finset.biUnion_inter]
    have hpwd_S' : (↑D_S : Set ℕ).PairwiseDisjoint (fun a => s_triple a ∩ A) := by
      intro a₁ ha₁ a₂ ha₂ hne
      exact (hpwd_S ha₁ ha₂ hne).mono Finset.inter_subset_left Finset.inter_subset_left
    calc (D_S.biUnion (fun a => s_triple a ∩ A)).card
        = ∑ a ∈ D_S, (s_triple a ∩ A).card := Finset.card_biUnion hpwd_S'
      _ ≤ ∑ a ∈ D_S, 2 := Finset.sum_le_sum (fun a ha =>
          s_triple_inter_card_le_two hA (hDS_mem a ha).1)
      _ = D_S.card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
      _ = 2 * D_S.card := by ring
  -- Step 12: |U_T ∩ A| ≤ 2|D_T|
  have hUTA : (U_T ∩ A).card ≤ 2 * D_T.card := by
    rw [show U_T = D_T.biUnion t_triple from rfl, Finset.biUnion_inter]
    have hpwd_T' : (↑D_T : Set ℕ).PairwiseDisjoint (fun e => t_triple e ∩ A) := by
      intro e₁ he₁ e₂ he₂ hne
      exact (hpwd_T he₁ he₂ hne).mono Finset.inter_subset_left Finset.inter_subset_left
    calc (D_T.biUnion (fun e => t_triple e ∩ A)).card
        = ∑ e ∈ D_T, (t_triple e ∩ A).card := Finset.card_biUnion hpwd_T'
      _ ≤ ∑ e ∈ D_T, 2 := Finset.sum_le_sum (fun e he =>
          t_triple_inter_card_le_two hA (hDT_mem e he).1)
      _ = D_T.card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
      _ = 2 * D_T.card := by ring
  -- Step 13: |(U_S ∪ U_T) ∩ A| ≤ 2|D_S| + 2|D_T|
  have hUA : ((U_S ∪ U_T) ∩ A).card ≤ 2 * D_S.card + 2 * D_T.card :=
    calc ((U_S ∪ U_T) ∩ A).card
        ≤ (U_S ∩ A).card + (U_T ∩ A).card := by
          rw [Finset.union_inter_distrib_right]
          exact Finset.card_union_le _ _
      _ ≤ 2 * D_S.card + 2 * D_T.card := Nat.add_le_add hUSA hUTA
  -- Step 14: A.card ≤ |(U_S∪U_T) ∩ A| + |Icc \ (U_S∪U_T)|
  have hAle : A.card ≤ ((U_S ∪ U_T) ∩ A).card +
      (Finset.Icc 1 N \ (U_S ∪ U_T)).card :=
    calc A.card
        ≤ ((U_S ∪ U_T) ∩ A ∪ (Finset.Icc 1 N \ (U_S ∪ U_T))).card :=
          Finset.card_le_card fun x hx => by
            by_cases hxU : x ∈ U_S ∪ U_T
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxU, hx⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hAN hx, hxU⟩)
      _ ≤ _ := Finset.card_union_le _ _
  -- Step 15: |Icc \ (U_S∪U_T)| + |U_S∪U_T| = N
  have hsdiff : (Finset.Icc 1 N \ (U_S ∪ U_T)).card + (U_S ∪ U_T).card =
      (Finset.Icc 1 N).card := Finset.card_sdiff_add_card_eq_card hUsub
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  -- Combine with omega
  omega

end UnitFractionTriples
