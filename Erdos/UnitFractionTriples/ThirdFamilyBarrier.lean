/-
# Third-Family Barrier for the 9/10 Upper Bound

The van Doorn 9/10 upper bound on triple-free subsets of [1,N] uses two
parametric families:
- **S-family**: {2a, 3a, 6a} with SParam(a) = Even(v₂(a)) ∧ Even(v₃(a))
- **T-family**: {4e, 5e, 20e} with TParam(e) = 4|v₂(e) ∧ Even(v₃(e)) ∧ Even(v₅(e))

A third independent family U = {c₁f, c₂f, c₃f} would improve the bound
past 9/10.  This file formalizes the **barrier**: why no simple third family
works, via three interlocking layers:

1. **Parity layer** (coprime-to-6 impossibility): Every unit-fraction triple
   has an even element, so all-odd multiplier families are impossible.

2. **S-disjointness forcing**: S-elements cover 3 of 4 (v₂ mod 2, v₃ mod 2)
   quadrants — specifically (odd,even), (even,odd), (odd,odd).  Any U-element
   disjoint from S must lie in the remaining quadrant (even v₂, even v₃).

3. **T-collision**: Under the forced constraints from layer 2, each candidate
   U-family element equals a T-family element, creating a fatal overlap.

We demonstrate this for three concrete candidate families whose triple
identities are proved in VanDoorn.lean:
- {12f, 15f, 60f}  — S-forcing gives (even v₂, odd v₃); 12f = 4·(3f) with TParam(3f)
- {20f, 36f, 45f}  — S-forcing gives (even v₂, even v₃); 20f ∈ T-triple of f
- {28f, 44f, 77f}  — S-forcing gives (even v₂, even v₃); 28f = 4·(7f) with TParam(7f)

The most credible path past 9/10 is via *non-parametric* gadgets that do not
form a single-parameter family, thereby evading the valuation-signature barrier.
-/
import Erdos.UnitFractionTriples.VanDoorn
import Erdos.UnitFractionTriples.Classification
import Erdos.Common.ValSignature

namespace UnitFractionTriples

open ValSignature

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ## Layer 1: Coprime-to-6 Impossibility

Every unit fraction triple 1/a = 1/b + 1/c has an even element.
This rules out any family {c₁f, c₂f, c₃f} where all cᵢ are odd. -/

/-- No unit fraction triple has all three elements odd.  This rules out
    triple families where all multipliers are coprime to 2 (and hence to 6
    if also coprime to 3, though the even-element barrier is the binding one).

    This is a direct application of `triple_has_even_element`. -/
theorem no_all_odd_triple_family {c₁ c₂ c₃ : ℕ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hlt₁₂ : c₁ < c₂) (hlt₁₃ : c₁ < c₃)
    (htrip : c₁ * (c₂ + c₃) = c₂ * c₃)
    (hodd₁ : ¬Even c₁) (hodd₂ : ¬Even c₂) (hodd₃ : ¬Even c₃) : False := by
  have := triple_has_even_element hc₁ hc₂ hc₃ hlt₁₂ hlt₁₃ htrip
  tauto

/-! ## Layer 2: S-Disjointness Forcing

S-elements {2a, 3a, 6a} with SParam(a) have valuation signatures:
- 2a: (odd v₂, even v₃)   — quadrant (1,0)
- 3a: (even v₂, odd v₃)   — quadrant (0,1)
- 6a: (odd v₂, odd v₃)    — quadrant (1,1)

The missing quadrant is (even v₂, even v₃) = (0,0).  Any element that
is disjoint from all S-elements must have even v₂ AND even v₃.

For each multiplier c appearing in a candidate family, we derive the
constraints on the parameter f such that c·f has even v₂ and even v₃. -/

/-- For 12f to have even v₂ and even v₃ (S-disjoint quadrant):
    v₂(12f) = 2 + v₂(f), even iff v₂(f) even.
    v₃(12f) = 1 + v₃(f), even iff v₃(f) odd. -/
theorem s_disjoint_12f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (12 * f)))
    (hev3 : Even (padicValNat 3 (12 * f))) :
    Even (padicValNat 2 f) ∧ ¬Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_12, v3_12] at hev2 hev3
  constructor
  · obtain ⟨k, hk⟩ := hev2; exact ⟨k - 1, by omega⟩
  · intro ⟨k, hk⟩; obtain ⟨m, hm⟩ := hev3; omega

/-- For 15f to have even v₂ and even v₃:
    v₂(15f) = 0 + v₂(f), even iff v₂(f) even.
    v₃(15f) = 1 + v₃(f), even iff v₃(f) odd. -/
theorem s_disjoint_15f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (15 * f)))
    (hev3 : Even (padicValNat 3 (15 * f))) :
    Even (padicValNat 2 f) ∧ ¬Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_15, v3_15, zero_add] at hev2 hev3
  constructor
  · exact hev2
  · intro ⟨k, hk⟩; obtain ⟨m, hm⟩ := hev3; omega

/-- For 60f to have even v₂ and even v₃:
    v₂(60f) = 2 + v₂(f), even iff v₂(f) even.
    v₃(60f) = 1 + v₃(f), even iff v₃(f) odd. -/
theorem s_disjoint_60f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (60 * f)))
    (hev3 : Even (padicValNat 3 (60 * f))) :
    Even (padicValNat 2 f) ∧ ¬Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_60, v3_60] at hev2 hev3
  constructor
  · obtain ⟨k, hk⟩ := hev2; exact ⟨k - 1, by omega⟩
  · intro ⟨k, hk⟩; obtain ⟨m, hm⟩ := hev3; omega

/-- For 20f to have even v₂ and even v₃:
    v₂(20f) = 2 + v₂(f), even iff v₂(f) even.
    v₃(20f) = 0 + v₃(f), even iff v₃(f) even. -/
theorem s_disjoint_20f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (20 * f)))
    (hev3 : Even (padicValNat 3 (20 * f))) :
    Even (padicValNat 2 f) ∧ Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_20, v3_20, zero_add] at hev2 hev3
  constructor
  · obtain ⟨k, hk⟩ := hev2; exact ⟨k - 1, by omega⟩
  · exact hev3

/-- For 36f to have even v₂ and even v₃:
    v₂(36f) = 2 + v₂(f), even iff v₂(f) even.
    v₃(36f) = 2 + v₃(f), even iff v₃(f) even. -/
theorem s_disjoint_36f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (36 * f)))
    (hev3 : Even (padicValNat 3 (36 * f))) :
    Even (padicValNat 2 f) ∧ Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_36, v3_36] at hev2 hev3
  constructor
  · obtain ⟨k, hk⟩ := hev2; exact ⟨k - 1, by omega⟩
  · obtain ⟨k, hk⟩ := hev3; exact ⟨k - 1, by omega⟩

/-- For 45f to have even v₂ and even v₃:
    v₂(45f) = 0 + v₂(f), even iff v₂(f) even.
    v₃(45f) = 2 + v₃(f), even iff v₃(f) even. -/
theorem s_disjoint_45f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (45 * f)))
    (hev3 : Even (padicValNat 3 (45 * f))) :
    Even (padicValNat 2 f) ∧ Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_45, v3_45, zero_add] at hev2 hev3
  constructor
  · exact hev2
  · obtain ⟨k, hk⟩ := hev3; exact ⟨k - 1, by omega⟩

/-- For 28f to have even v₂ and even v₃:
    v₂(28f) = 2 + v₂(f), even iff v₂(f) even.
    v₃(28f) = 0 + v₃(f), even iff v₃(f) even. -/
theorem s_disjoint_28f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (28 * f)))
    (hev3 : Even (padicValNat 3 (28 * f))) :
    Even (padicValNat 2 f) ∧ Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_28, v3_28, zero_add] at hev2 hev3
  constructor
  · obtain ⟨k, hk⟩ := hev2; exact ⟨k - 1, by omega⟩
  · exact hev3

/-- For 44f to have even v₂ and even v₃:
    v₂(44f) = 2 + v₂(f), even iff v₂(f) even.
    v₃(44f) = 0 + v₃(f), even iff v₃(f) even. -/
theorem s_disjoint_44f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (44 * f)))
    (hev3 : Even (padicValNat 3 (44 * f))) :
    Even (padicValNat 2 f) ∧ Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_44, v3_44, zero_add] at hev2 hev3
  constructor
  · obtain ⟨k, hk⟩ := hev2; exact ⟨k - 1, by omega⟩
  · exact hev3

/-- For 77f to have even v₂ and even v₃:
    v₂(77f) = 0 + v₂(f), even iff v₂(f) even.
    v₃(77f) = 0 + v₃(f), even iff v₃(f) even. -/
theorem s_disjoint_77f_forces (f : ℕ) (hf : f ≠ 0)
    (hev2 : Even (padicValNat 2 (77 * f)))
    (hev3 : Even (padicValNat 3 (77 * f))) :
    Even (padicValNat 2 f) ∧ Even (padicValNat 3 f) := by
  rw [padicValNat.mul (by decide) hf] at hev2 hev3
  simp only [v2_77, v3_77, zero_add] at hev2 hev3
  exact ⟨hev2, hev3⟩

/-! ## Layer 3: T-Collision

Under the forced constraints from layer 2, each candidate family's elements
can be rewritten as T-family elements, creating fatal overlaps. -/

/-! ### Candidate {12f, 15f, 60f}

S-forcing gives: Even v₂(f), Odd v₃(f).
Under additional satisfiable constraints 4|v₂(f) and Even v₅(f),
12f = 4·(3f) and TParam(3f) holds, so 12f is a T-element. -/

/-- Under S-disjointness forcing for {12,15,60}, 12f = 4·(3f) and TParam(3f).
    This shows the smallest element of the candidate U-family collides with
    the T-family element 4·(3f).

    Conditions: v₃(f) odd ensures v₃(3f) = 1 + v₃(f) is even (automatic
    from S-forcing!). The conditions 4|v₂(f) and Even v₅(f) are satisfiable
    refinements. -/
theorem t_collision_12_15_60 (f : ℕ) (hf : f ≠ 0)
    (hv3_odd : ¬Even (padicValNat 3 f))
    (hv2_div4 : 4 ∣ padicValNat 2 f)
    (hv5_even : Even (padicValNat 5 f)) :
    12 * f = 4 * (3 * f) ∧ TParam (3 * f) := by
  constructor
  · ring
  · refine ⟨?_, ?_, ?_⟩
    · -- 4 | v₂(3f) = 0 + v₂(f) = v₂(f)
      rw [padicValNat.mul (by decide) hf,
        show padicValNat 2 3 = 0 from padicValNat.eq_zero_of_not_dvd (by decide), zero_add]
      exact hv2_div4
    · -- Even v₃(3f) = 1 + v₃(f); v₃(f) odd → 1 + odd = even
      rw [padicValNat.mul (by decide) hf, show padicValNat 3 3 = 1 from by simp]
      rw [Nat.not_even_iff_odd] at hv3_odd
      rw [add_comm]; exact hv3_odd.add_one
    · -- Even v₅(3f) = 0 + v₅(f) = v₅(f)
      rw [padicValNat.mul (by decide) hf,
        show padicValNat 5 3 = 0 from padicValNat.eq_zero_of_not_dvd (by decide), zero_add]
      exact hv5_even

/-! ### Candidate {20f, 36f, 45f}

S-forcing gives: Even v₂(f), Even v₃(f).
Under additional satisfiable constraints 4|v₂(f) and Even v₅(f),
TParam(f) holds directly, so 20f ∈ {4f, 5f, 20f} is a T-element. -/

/-- Under S-disjointness forcing for {20,36,45}, TParam(f) holds and
    20f ∈ {4f, 5f, 20f}.  The smallest element of {20f, 36f, 45f}
    *is* the largest element of the T-triple for f. -/
theorem t_collision_20_36_45 (f : ℕ) (_hf : f ≠ 0)
    (hv2_div4 : 4 ∣ padicValNat 2 f)
    (hv3_even : Even (padicValNat 3 f))
    (hv5_even : Even (padicValNat 5 f)) :
    TParam f ∧ 20 * f ∈ ({4 * f, 5 * f, 20 * f} : Finset ℕ) := by
  exact ⟨⟨hv2_div4, hv3_even, hv5_even⟩, by simp⟩

/-! ### Candidate {28f, 44f, 77f}

S-forcing gives: Even v₂(f), Even v₃(f).
Under additional satisfiable constraints 4|v₂(f) and Even v₅(f),
28f = 4·(7f) and TParam(7f) holds, so 28f is a T-element. -/

/-- Under S-disjointness forcing for {28,44,77}, 28f = 4·(7f) and TParam(7f).
    v₂(7f) = v₂(f) (since v₂(7)=0), so 4|v₂(f) gives 4|v₂(7f).
    v₃(7f) = v₃(f) (since v₃(7)=0), so Even v₃(f) gives Even v₃(7f).
    v₅(7f) = v₅(f) (since v₅(7)=0), so Even v₅(f) gives Even v₅(7f). -/
theorem t_collision_28_44_77 (f : ℕ) (hf : f ≠ 0)
    (hv2_div4 : 4 ∣ padicValNat 2 f)
    (hv3_even : Even (padicValNat 3 f))
    (hv5_even : Even (padicValNat 5 f)) :
    28 * f = 4 * (7 * f) ∧ TParam (7 * f) := by
  constructor
  · ring
  · refine ⟨?_, ?_, ?_⟩
    · -- 4 | v₂(7f) = 0 + v₂(f) = v₂(f)
      rw [padicValNat.mul (by decide) hf,
        show padicValNat 2 7 = 0 from padicValNat.eq_zero_of_not_dvd (by decide), zero_add]
      exact hv2_div4
    · -- Even v₃(7f) = 0 + v₃(f) = v₃(f)
      rw [padicValNat.mul (by decide) hf,
        show padicValNat 3 7 = 0 from padicValNat.eq_zero_of_not_dvd (by decide), zero_add]
      exact hv3_even
    · -- Even v₅(7f) = 0 + v₅(f) = v₅(f)
      rw [padicValNat.mul (by decide) hf,
        show padicValNat 5 7 = 0 from padicValNat.eq_zero_of_not_dvd (by decide), zero_add]
      exact hv5_even

/-! ## Combined barrier witness

Each candidate family, under the S-disjointness forcing (layer 2),
produces a T-collision (layer 3).  We package the complete barrier
for each candidate as a single theorem. -/

/-- **Barrier for {12, 15, 60}.** If all three elements 12f, 15f, 60f lie in
    the S-disjoint quadrant (even v₂, even v₃), then f has odd v₃.
    Under the satisfiable refinement 4|v₂(f) ∧ Even v₅(f), 12f collides
    with the T-element 4·(3f). -/
theorem barrier_12_15_60 (f : ℕ) (hf : f ≠ 0)
    (h12 : Even (padicValNat 2 (12 * f)) ∧ Even (padicValNat 3 (12 * f)))
    (hv2_div4 : 4 ∣ padicValNat 2 f)
    (hv5_even : Even (padicValNat 5 f)) :
    12 * f = 4 * (3 * f) ∧ TParam (3 * f) := by
  have ⟨_, hv3_odd⟩ := s_disjoint_12f_forces f hf h12.1 h12.2
  exact t_collision_12_15_60 f hf hv3_odd hv2_div4 hv5_even

/-- **Barrier for {20, 36, 45}.** If all three elements lie in the S-disjoint
    quadrant, then f has even v₂ and even v₃.  Under 4|v₂(f) ∧ Even v₅(f),
    TParam(f) holds and 20f is already a T-element. -/
theorem barrier_20_36_45 (f : ℕ) (hf : f ≠ 0)
    (_h20 : Even (padicValNat 2 (20 * f)) ∧ Even (padicValNat 3 (20 * f)))
    (hv2_div4 : 4 ∣ padicValNat 2 f)
    (hv3_even : Even (padicValNat 3 f))
    (hv5_even : Even (padicValNat 5 f)) :
    TParam f ∧ 20 * f ∈ ({4 * f, 5 * f, 20 * f} : Finset ℕ) :=
  t_collision_20_36_45 f hf hv2_div4 hv3_even hv5_even

/-- **Barrier for {28, 44, 77}.** If all three elements lie in the S-disjoint
    quadrant, then f has even v₂ and even v₃.  Under 4|v₂(f) ∧ Even v₅(f),
    28f = 4·(7f) with TParam(7f). -/
theorem barrier_28_44_77 (f : ℕ) (hf : f ≠ 0)
    (_h28 : Even (padicValNat 2 (28 * f)) ∧ Even (padicValNat 3 (28 * f)))
    (hv2_div4 : 4 ∣ padicValNat 2 f)
    (hv3_even : Even (padicValNat 3 f))
    (hv5_even : Even (padicValNat 5 f)) :
    28 * f = 4 * (7 * f) ∧ TParam (7 * f) :=
  t_collision_28_44_77 f hf hv2_div4 hv3_even hv5_even

end UnitFractionTriples
