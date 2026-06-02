import Erdos.DistinctSubsetSums.ElementaryBounds

/-!
# Erdős Problem #1: the Erdős–Moser second-moment bound

We improve the elementary counting bound to the classical `≳ 2^{|A|}/√{|A|}` of Erdős–Moser.
The engine is a sign-orthogonality identity: writing `T = ∑ A` and centering each subset sum,

`∑_{S ⊆ A} (2·∑_S − T)² = 2^{|A|} · ∑_{x ∈ A} x²`.

(The centered values `2·∑_S − T` are the `±1`-combinations `∑_{x∈A} ε_x x`; squaring and summing
over all sign patterns kills the cross terms, leaving the diagonal `2^{|A|}∑x²`.) Since the
centered values are `2^{|A|}` *distinct* integers, the left side is large, forcing a large `∑x²`
and hence a large maximum element.
-/

namespace DistinctSubsetSums

open Finset

/-- **Sign-orthogonality identity.** For any finite `A ⊆ ℕ`, summing the squared centered subset
sums `(2·∑_S − ∑_A)²` over all subsets `S ⊆ A` gives `2^{|A|} · ∑_{x∈A} x²`. Proved by induction:
splitting `(insert a A).powerset` into subsets with and without `a` contributes
`(p − a)² + (p + a)² = 2p² + 2a²`, doubling the inductive sum and adding `2a²` per subset. -/
theorem sum_powerset_centered_sq (A : Finset ℕ) :
    ∑ S ∈ A.powerset, (2 * (∑ x ∈ S, (x : ℤ)) - ∑ x ∈ A, (x : ℤ)) ^ 2
      = 2 ^ A.card * ∑ x ∈ A, (x : ℤ) ^ 2 := by
  classical
  induction A using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_powerset_insert ha]
    -- rewrite each summand of the two pieces into `2·(centered_s)² + 2a²`
    have key : ∀ S ∈ s.powerset,
        (2 * (∑ x ∈ S, (x : ℤ)) - ∑ x ∈ insert a s, (x : ℤ)) ^ 2
          + (2 * (∑ x ∈ insert a S, (x : ℤ)) - ∑ x ∈ insert a s, (x : ℤ)) ^ 2
        = 2 * (2 * (∑ x ∈ S, (x : ℤ)) - ∑ x ∈ s, (x : ℤ)) ^ 2 + 2 * (a : ℤ) ^ 2 := by
      intro S hS
      have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
      rw [Finset.sum_insert ha, Finset.sum_insert haS]
      ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl key, Finset.sum_add_distrib,
        ← Finset.mul_sum, ih, Finset.sum_const, Finset.card_powerset,
        Finset.card_insert_of_notMem ha, Finset.sum_insert ha, pow_succ, nsmul_eq_mul]
    push_cast
    ring

/-- `∑_{r<n} (2r+1) = n²`. -/
private theorem sum_two_mul_add_one (n : ℕ) :
    ∑ r ∈ Finset.range n, (2 * (r : ℤ) + 1) = (n : ℤ) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `3·∑_{r<n} (2r+1)² = 4n³ − n` (the sum of squares of the first `n` odd numbers). -/
private theorem sum_two_mul_add_one_sq (n : ℕ) :
    3 * ∑ r ∈ Finset.range n, (2 * (r : ℤ) + 1) ^ 2 = 4 * (n : ℤ) ^ 3 - n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

/-- **Tight spread bound (layer cake).** For any finite set `G` of integers and any `R`,
`∑_{r<R} (2r+1)·(|G| − (2r+1)) ≤ ∑_{y∈G} y²`. Summing all shells `r` (rather than using a
single threshold) is what yields the sharp constant: `∑ y² ≥ |G|³/12` near optimum. -/
theorem layer_le_sum_sq (G : Finset ℤ) (R : ℕ) :
    ∑ r ∈ Finset.range R, (2 * (r : ℤ) + 1) * ((G.card : ℤ) - (2 * r + 1)) ≤ ∑ y ∈ G, y ^ 2 := by
  classical
  calc ∑ r ∈ Finset.range R, (2 * (r : ℤ) + 1) * ((G.card : ℤ) - (2 * r + 1))
      ≤ ∑ r ∈ Finset.range R,
          (2 * (r : ℤ) + 1) * ((G.filter (fun y => (r : ℤ) < |y|)).card : ℤ) := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        -- `|G| − (2r+1) ≤ #{y : r < |y|}` since at most `2r+1` elements have `|y| ≤ r`
        have hsmall : (G.filter (fun y => ¬ (r : ℤ) < |y|)).card ≤ 2 * r + 1 := by
          calc (G.filter (fun y => ¬ (r : ℤ) < |y|)).card
              ≤ (Finset.Icc (-(r : ℤ)) r).card := by
                refine Finset.card_le_card (fun y hy => ?_)
                rw [Finset.mem_filter] at hy
                rw [Finset.mem_Icc, ← abs_le]; exact not_lt.mp hy.2
            _ = 2 * r + 1 := by rw [Int.card_Icc]; omega
        have hsplit : (G.filter (fun y => (r : ℤ) < |y|)).card
            + (G.filter (fun y => ¬ (r : ℤ) < |y|)).card = G.card :=
          Finset.filter_card_add_filter_neg_card_eq_card _
        have e : (G.card : ℤ)
            = ((G.filter (fun y => (r : ℤ) < |y|)).card : ℤ)
              + ((G.filter (fun y => ¬ (r : ℤ) < |y|)).card : ℤ) := by exact_mod_cast hsplit.symm
        have hle : ((G.filter (fun y => ¬ (r : ℤ) < |y|)).card : ℤ) ≤ 2 * r + 1 := by
          exact_mod_cast hsmall
        linarith
    _ = ∑ r ∈ Finset.range R, ∑ y ∈ G, (if (r : ℤ) < |y| then 2 * (r : ℤ) + 1 else 0) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ y ∈ G, ∑ r ∈ Finset.range R, (if (r : ℤ) < |y| then 2 * (r : ℤ) + 1 else 0) :=
        Finset.sum_comm
    _ ≤ ∑ y ∈ G, y ^ 2 := by
        refine Finset.sum_le_sum (fun y _ => ?_)
        have hcast : ((y.natAbs : ℤ)) ^ 2 = y ^ 2 := by
          rw [← Int.abs_eq_natAbs]; exact sq_abs y
        calc ∑ r ∈ Finset.range R, (if (r : ℤ) < |y| then 2 * (r : ℤ) + 1 else 0)
            ≤ ∑ r ∈ Finset.range y.natAbs, (2 * (r : ℤ) + 1) := by
              rw [← Finset.sum_filter]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun r _ _ => by positivity)
              intro r hr
              rw [Finset.mem_filter] at hr
              rw [Finset.mem_range, ← Int.ofNat_lt, Int.abs_eq_natAbs] at *
              exact_mod_cast hr.2
          _ = (y.natAbs : ℤ) ^ 2 := sum_two_mul_add_one y.natAbs
          _ = y ^ 2 := hcast

/-- A nonempty set with distinct subset sums has all elements `≥ 1` (`0 ∈ A` would give `∅` and
`{0}` the same sum, contradicting distinctness). -/
theorem one_le_of_mem {A : Finset ℕ} (h : HasDistinctSubsetSums A) {x : ℕ} (hx : x ∈ A) :
    1 ≤ x := by
  rcases Nat.eq_zero_or_pos x with hx0 | hpos
  · refine absurd (h (Finset.empty_subset A) (Finset.singleton_subset_iff.mpr hx) ?_).symm
      (Finset.singleton_ne_empty x)
    simp [hx0]
  · exact hpos

/-- **Erdős–Moser second-moment bound (sharp constant).** If `A` has distinct subset sums and
every element is `≤ M`, then `2^{2|A|} ≤ 12 · |A| · M²` — equivalently the largest element
satisfies `M ≥ 2^{|A|}/(2√3·√{|A|})`. This is the classical `2^n/√n`-shape improvement over the
elementary counting bound `2^n/n` (`inv_card_mul_pred_le_of_hasDistinct`), with the sharp
second-moment constant `1/(2√3)` (Erdős–Moser). The engine is the sign-orthogonality identity
`sum_powerset_centered_sq` together with the layer-cake spread bound `layer_le_sum_sq`. -/
theorem two_pow_two_mul_card_le {A : Finset ℕ} {M : ℕ}
    (h : HasDistinctSubsetSums A) (hM : ∀ x ∈ A, x ≤ M) (hA : A.Nonempty) :
    2 ^ (2 * A.card) ≤ 12 * A.card * M ^ 2 := by
  classical
  set g : Finset ℕ → ℤ := fun S => 2 * (∑ x ∈ S, (x : ℤ)) - ∑ x ∈ A, (x : ℤ) with hg
  -- injectivity of the centered subset-sum map
  have hinj : Set.InjOn g ↑A.powerset := by
    intro B hB C hC hBC
    rw [Finset.mem_coe, Finset.mem_powerset] at hB hC
    simp only [hg] at hBC
    have heqN : ∑ x ∈ B, x = ∑ x ∈ C, x := by
      have h2 : ((∑ x ∈ B, x : ℕ) : ℤ) = ((∑ x ∈ C, x : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast h2
    exact h hB hC heqN
  have hGcard : (A.powerset.image g).card = 2 ^ A.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
  -- the distinct centered values have sum of squares `2^n · ∑ a²`
  have hsumeq : ∑ y ∈ A.powerset.image g, y ^ 2 = 2 ^ A.card * ∑ x ∈ A, (x : ℤ) ^ 2 := by
    rw [Finset.sum_image
        (fun a ha b hb => hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb))]
    exact sum_powerset_centered_sq A
  -- ∑ a² ≤ n · M²
  have hsumsq_le : ∑ x ∈ A, (x : ℤ) ^ 2 ≤ (A.card : ℤ) * M ^ 2 := by
    calc ∑ x ∈ A, (x : ℤ) ^ 2 ≤ ∑ _x ∈ A, (M : ℤ) ^ 2 := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          have hxM : (x : ℤ) ≤ M := by exact_mod_cast hM x hx
          have hx0 : (0 : ℤ) ≤ x := by positivity
          nlinarith [hxM, hx0]
      _ = (A.card : ℤ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  -- tight extremal at threshold-sum `R = 2^{|A|-1}` (every dyadic shell counted)
  have hcardpos : 1 ≤ A.card := Finset.card_pos.mpr hA
  set R : ℕ := 2 ^ (A.card - 1) with hR
  have hRpos : (0 : ℤ) < R := by rw [hR]; positivity
  have hR2 : (2 : ℤ) ^ A.card = 2 * (R : ℤ) := by
    rw [hR]; push_cast
    conv_lhs => rw [← Nat.sub_add_cancel hcardpos, pow_succ]
    ring
  have hGcZ : ((2 ^ A.card : ℕ) : ℤ) = 2 * (R : ℤ) := by push_cast; exact hR2
  have hextr := layer_le_sum_sq (A.powerset.image g) R
  rw [hGcard, hGcZ, hsumeq, hR2] at hextr
  -- `3·(layer sum at |G| = 2R) = 2R³ + R`
  have cubic : 3 * ∑ r ∈ Finset.range R, (2 * (r : ℤ) + 1) * (2 * (R : ℤ) - (2 * r + 1))
      = 2 * (R : ℤ) ^ 3 + R := by
    have expand : ∑ r ∈ Finset.range R, (2 * (r : ℤ) + 1) * (2 * (R : ℤ) - (2 * r + 1))
        = 2 * (R : ℤ) * (∑ r ∈ Finset.range R, (2 * (r : ℤ) + 1))
          - ∑ r ∈ Finset.range R, (2 * (r : ℤ) + 1) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [expand, sum_two_mul_add_one]
    linear_combination -sum_two_mul_add_one_sq R
  have hprod : 6 * (R : ℤ) * (∑ x ∈ A, (x : ℤ) ^ 2) ≤ 6 * (R : ℤ) * ((A.card : ℤ) * M ^ 2) :=
    mul_le_mul_of_nonneg_left hsumsq_le (by positivity)
  have key : 2 * (R : ℤ) ^ 3 ≤ 6 * (R : ℤ) * ((A.card : ℤ) * M ^ 2) := by
    nlinarith [cubic, hextr, hprod, hRpos]
  have hcancel : (R : ℤ) ^ 2 ≤ 3 * ((A.card : ℤ) * M ^ 2) := by
    have hmul : 2 * (R : ℤ) * (R ^ 2) ≤ 2 * (R : ℤ) * (3 * ((A.card : ℤ) * M ^ 2)) := by
      nlinarith [key]
    exact le_of_mul_le_mul_left hmul (by linarith)
  have hpow : (2 : ℤ) ^ (2 * A.card) = 4 * (R : ℤ) ^ 2 := by rw [two_mul, pow_add, hR2]; ring
  have hgoalZ : (2 : ℤ) ^ (2 * A.card) ≤ 12 * A.card * M ^ 2 := by rw [hpow]; nlinarith [hcancel]
  exact_mod_cast hgoalZ

/-- **Erdős–Moser, square-root form (sharp constant).** A set with distinct subset sums and all
elements `≤ M` satisfies `2^{|A|} ≤ √(12|A|)·M = 2√3·√{|A|}·M`, i.e. its largest element is at
least `2^{|A|}/(2√3·√{|A|})` — the classical `Θ(2^n/√n)` lower bound with the sharp second-moment
constant `1/(2√3) ≈ 0.289`. -/
theorem two_pow_le_sqrt_mul {A : Finset ℕ} {M : ℕ}
    (h : HasDistinctSubsetSums A) (hM : ∀ x ∈ A, x ≤ M) (hA : A.Nonempty) :
    (2 : ℝ) ^ A.card ≤ Real.sqrt (12 * A.card) * M := by
  have hbR : (2 : ℝ) ^ (2 * A.card) ≤ 12 * A.card * M ^ 2 := by
    exact_mod_cast two_pow_two_mul_card_le h hM hA
  have hsq : (Real.sqrt (12 * A.card) * M) ^ 2 = 12 * A.card * M ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have e2n : ((2 : ℝ) ^ A.card) ^ 2 = (2 : ℝ) ^ (2 * A.card) := by
    rw [two_mul, pow_add, pow_two]
  have key : ((2 : ℝ) ^ A.card) ^ 2 ≤ (Real.sqrt (12 * A.card) * M) ^ 2 := by
    rw [e2n, hsq]; exact hbR
  have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ A.card := by positivity
  have hrhs : (0 : ℝ) ≤ Real.sqrt (12 * A.card) * M := by positivity
  have hsqrt := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq h2n, Real.sqrt_sq hrhs] at hsqrt

end DistinctSubsetSums
