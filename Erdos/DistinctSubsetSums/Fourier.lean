import Erdos.DistinctSubsetSums.Statement

/-!
# Erdős Problem #1: the Fourier engine (Elkies' method)

The classical best-known lower bound `a_max ≳ √(2/π)·2^n/√n` (Elkies) runs through the
Fourier identity: a set has distinct subset sums **iff** `∫₀¹ |∏ⱼ(1 + e^{2πi aⱼ t})|² dt = 2^n`.
This file formalizes the engine of that identity — character orthogonality and the resulting
"distinctness as an integral". The analytic estimate `∫₀¹ ∏ⱼ cos²(π aⱼ t) dt ≤ C/√(∑aⱼ²)`
needed to extract the `√(2/π)` bound (Gaussian main term + secondary-peak tail control) is left
as documented future work.
-/

namespace DistinctSubsetSums

open Complex intervalIntegral

/-- **Character orthogonality on `[0,1]`.** For an integer frequency `k`,
`∫₀¹ e^{2πi k t} dt = 1` if `k = 0` and `0` otherwise. -/
theorem char_orthogonality (k : ℤ) :
    (∫ t in (0 : ℝ)..1, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * (t : ℂ)))
      = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)
          = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]; simp

/-- The character `t ↦ e^{2πi k t}`. -/
private noncomputable def e (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * (t : ℂ))

private theorem e_mul (a b : ℤ) (t : ℝ) : e a t * e b t = e (a + b) t := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem e_continuous (k : ℤ) : Continuous (e k) := by
  unfold e; fun_prop

private theorem e_integrable (k : ℤ) :
    IntervalIntegrable (e k) MeasureTheory.volume 0 1 :=
  (e_continuous k).intervalIntegrable 0 1

private theorem e_integral (k : ℤ) : (∫ t in (0 : ℝ)..1, e k t) = if k = 0 then 1 else 0 := by
  unfold e; exact char_orthogonality k

/-- **Distinctness as an integral (the Fourier engine).** If `A` has distinct subset sums then
`∫₀¹ |∑_{S⊆A} e^{2πi σ(S) t}|² dt = 2^{|A|}`, where `σ(S) = ∑_{x∈S} x`. (The squared modulus is
written as the product of the character sum with its conjugate.) Since `∑_{S⊆A} e^{2πi σ(S) t}`
expands as the product `∏_{x∈A}(1 + e^{2πi x t})`, this is the identity
`∫₀¹ |∏_{x∈A}(1 + e^{2πi x t})|² dt = 2^{|A|}` at the heart of Elkies' `√(2/π)·2ⁿ/√n`
bound. The proof is character
orthogonality (`char_orthogonality`) plus distinctness collapsing the double sum to its diagonal. -/
theorem distinct_subset_sums_integral {A : Finset ℕ} (h : HasDistinctSubsetSums A) :
    (∫ t in (0 : ℝ)..1,
        (∑ S ∈ A.powerset, e (∑ x ∈ S, (x : ℤ)) t)
          * (∑ T ∈ A.powerset, e (-(∑ x ∈ T, (x : ℤ))) t))
      = (2 : ℂ) ^ A.card := by
  classical
  -- pointwise: the integrand is the double sum of `e(σS − σT)`
  have hpt : ∀ t : ℝ,
      (∑ S ∈ A.powerset, e (∑ x ∈ S, (x : ℤ)) t)
        * (∑ T ∈ A.powerset, e (-(∑ x ∈ T, (x : ℤ))) t)
      = ∑ p ∈ A.powerset ×ˢ A.powerset,
          e ((∑ x ∈ p.1, (x : ℤ)) - (∑ x ∈ p.2, (x : ℤ))) t := by
    intro t
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
    rw [e_mul, sub_eq_add_neg]
  -- the inner diagonal count: distinctness ⟹ exactly one `T` matches each `S`
  have inner : ∀ S ∈ A.powerset,
      (∑ T ∈ A.powerset,
        (if (∑ x ∈ S, (x : ℤ)) - (∑ x ∈ T, (x : ℤ)) = 0 then (1 : ℂ) else 0)) = 1 := by
    intro S hS
    rw [Finset.sum_eq_single S]
    · simp
    · intro T hT hTS
      rw [if_neg]
      intro hz
      apply hTS
      have hnat : ∑ x ∈ S, x = ∑ x ∈ T, x := by
        have h2 : ((∑ x ∈ S, x : ℕ) : ℤ) = ((∑ x ∈ T, x : ℕ) : ℤ) := by
          push_cast; exact sub_eq_zero.mp hz
        exact_mod_cast h2
      exact (h (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hnat).symm
    · intro hSnot; exact absurd hS hSnot
  calc (∫ t in (0 : ℝ)..1,
          (∑ S ∈ A.powerset, e (∑ x ∈ S, (x : ℤ)) t)
            * (∑ T ∈ A.powerset, e (-(∑ x ∈ T, (x : ℤ))) t))
      = ∫ t in (0 : ℝ)..1, ∑ p ∈ A.powerset ×ˢ A.powerset,
          e ((∑ x ∈ p.1, (x : ℤ)) - (∑ x ∈ p.2, (x : ℤ))) t :=
        intervalIntegral.integral_congr (fun t _ => hpt t)
    _ = ∑ p ∈ A.powerset ×ˢ A.powerset,
          ∫ t in (0 : ℝ)..1, e ((∑ x ∈ p.1, (x : ℤ)) - (∑ x ∈ p.2, (x : ℤ))) t :=
        intervalIntegral.integral_finset_sum (fun p _ => e_integrable _)
    _ = ∑ p ∈ A.powerset ×ˢ A.powerset,
          (if (∑ x ∈ p.1, (x : ℤ)) - (∑ x ∈ p.2, (x : ℤ)) = 0 then (1 : ℂ) else 0) := by
        simp_rw [e_integral]
    _ = ∑ S ∈ A.powerset, ∑ T ∈ A.powerset,
          (if (∑ x ∈ S, (x : ℤ)) - (∑ x ∈ T, (x : ℤ)) = 0 then (1 : ℂ) else 0) := by
        rw [Finset.sum_product]
    _ = ∑ _S ∈ A.powerset, (1 : ℂ) := Finset.sum_congr rfl inner
    _ = (2 : ℂ) ^ A.card := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]; push_cast; ring

end DistinctSubsetSums
