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

/-- **Distinct integers spread out.** For any finite set `G` of integers and any `k`, at most
`2k+1` of its elements lie in `[−k, k]`, so the sum of squares is at least
`(|G| − (2k+1)) · (k+1)²`: the remaining elements each have `|y| ≥ k+1`. -/
theorem card_sub_mul_le_sum_sq (G : Finset ℤ) (k : ℕ) :
    ((G.card : ℤ) - (2 * (k : ℤ) + 1)) * ((k : ℤ) + 1) ^ 2 ≤ ∑ y ∈ G, y ^ 2 := by
  classical
  set Gbig := G.filter (fun y => (k : ℤ) < |y|) with hGbig
  -- the "small" part embeds in `Icc (-k) k`, of size `2k+1`
  have hsmall : G.filter (fun y => ¬ (k : ℤ) < |y|) ⊆ Finset.Icc (-(k : ℤ)) k := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_Icc]
    have hyabs : |y| ≤ (k : ℤ) := not_lt.mp hy.2
    rwa [abs_le] at hyabs
  have hsmallcard : (G.filter (fun y => ¬ (k : ℤ) < |y|)).card ≤ 2 * k + 1 := by
    calc (G.filter (fun y => ¬ (k : ℤ) < |y|)).card
        ≤ (Finset.Icc (-(k : ℤ)) k).card := Finset.card_le_card hsmall
      _ = 2 * k + 1 := by rw [Int.card_Icc]; omega
  have hcardsplit : Gbig.card + (G.filter (fun y => ¬ (k : ℤ) < |y|)).card = G.card := by
    rw [hGbig]; exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hbigcard : (G.card : ℤ) - (2 * (k : ℤ) + 1) ≤ (Gbig.card : ℤ) := by
    have e : (G.card : ℤ)
        = (Gbig.card : ℤ) + ((G.filter (fun y => ¬ (k : ℤ) < |y|)).card : ℤ) := by
      exact_mod_cast hcardsplit.symm
    have hle : ((G.filter (fun y => ¬ (k : ℤ) < |y|)).card : ℤ) ≤ 2 * (k : ℤ) + 1 := by
      exact_mod_cast hsmallcard
    linarith
  -- each big element contributes at least `(k+1)²`
  have hpt : ∀ y ∈ Gbig, ((k : ℤ) + 1) ^ 2 ≤ y ^ 2 := by
    intro y hy
    rw [hGbig, Finset.mem_filter] at hy
    have h1 : (k : ℤ) + 1 ≤ |y| := Int.add_one_le_iff.mpr hy.2
    have h0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
    rw [← sq_abs y]
    nlinarith [h1, h0, abs_nonneg y]
  calc ((G.card : ℤ) - (2 * (k : ℤ) + 1)) * ((k : ℤ) + 1) ^ 2
      ≤ (Gbig.card : ℤ) * ((k : ℤ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hbigcard (by positivity)
    _ = ∑ _y ∈ Gbig, ((k : ℤ) + 1) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ Gbig, y ^ 2 := Finset.sum_le_sum hpt
    _ ≤ ∑ y ∈ G, y ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun y _ _ => sq_nonneg y)

/-- A nonempty set with distinct subset sums has all elements `≥ 1` (`0 ∈ A` would give `∅` and
`{0}` the same sum, contradicting distinctness). -/
theorem one_le_of_mem {A : Finset ℕ} (h : HasDistinctSubsetSums A) {x : ℕ} (hx : x ∈ A) :
    1 ≤ x := by
  rcases Nat.eq_zero_or_pos x with hx0 | hpos
  · refine absurd (h (Finset.empty_subset A) (Finset.singleton_subset_iff.mpr hx) ?_).symm
      (Finset.singleton_ne_empty x)
    simp [hx0]
  · exact hpos

/-- **Erdős–Moser second-moment bound.** If `A` has distinct subset sums and every element is
`≤ M`, then `2^{2|A|} ≤ 64 · |A| · M²` — equivalently the largest element satisfies
`M ≥ 2^{|A|}/(8√{|A|})`. This is the classical `2^n/√n`-shape improvement over the elementary
counting bound `2^n/n` (`inv_card_mul_pred_le_of_hasDistinct`). The engine is the sign-orthogonality
identity `sum_powerset_centered_sq` together with the spread bound `card_sub_mul_le_sum_sq`. -/
theorem two_pow_two_mul_card_le {A : Finset ℕ} {M : ℕ}
    (h : HasDistinctSubsetSums A) (hM : ∀ x ∈ A, x ≤ M) (hA : A.Nonempty) :
    2 ^ (2 * A.card) ≤ 64 * A.card * M ^ 2 := by
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
  rcases Nat.lt_or_ge A.card 2 with hlt | hge
  · -- |A| = 1: `4 ≤ 64 M²` with `M ≥ 1`
    obtain ⟨x, hxA⟩ := hA
    have hM1 : 1 ≤ M := le_trans (one_le_of_mem h hxA) (hM x hxA)
    have hc1 : A.card = 1 := by have := Finset.card_pos.mpr ⟨x, hxA⟩; omega
    have hMsq : 1 ≤ M ^ 2 := Nat.one_le_pow 2 M (by omega)
    rw [hc1]
    calc (2 : ℕ) ^ (2 * 1) = 4 := by norm_num
      _ ≤ 64 * 1 * M ^ 2 := by nlinarith [hMsq]
  · -- |A| ≥ 2: write |A| = m + 2 and run the second moment
    obtain ⟨m, hmcard⟩ : ∃ m, A.card = m + 2 := ⟨A.card - 2, by omega⟩
    set t : ℤ := (2 : ℤ) ^ m with ht
    have ht1 : (1 : ℤ) ≤ t := one_le_pow₀ (by norm_num)
    have ht0 : (0 : ℤ) < t := by linarith
    have hP1 : (2 : ℤ) ^ A.card = 4 * t := by rw [hmcard, ht, pow_add]; ring
    have hP1' : ((2 ^ A.card : ℕ) : ℤ) = 4 * t := by rw [hmcard, ht]; push_cast; ring
    have htk : ((2 ^ m : ℕ) : ℤ) = t := by rw [ht]; push_cast; ring
    -- combine the extremal bound with the identity and `∑a² ≤ n M²`
    have hextr := card_sub_mul_le_sum_sq (A.powerset.image g) (2 ^ m)
    rw [hGcard, hsumeq, hP1, htk, hP1'] at hextr
    -- hextr : (4t − (2t+1))(t+1)² ≤ 4t · ∑a²
    have hchain : (2 * t - 1) * (t + 1) ^ 2 ≤ 4 * t * ((A.card : ℤ) * M ^ 2) := by
      nlinarith [hextr, hsumsq_le, ht0]
    have hpoly : t ^ 3 ≤ (2 * t - 1) * (t + 1) ^ 2 := by nlinarith [ht1]
    have hcube : t * t ^ 2 ≤ t * (4 * ((A.card : ℤ) * M ^ 2)) := by nlinarith [hchain, hpoly]
    have hcancel : t ^ 2 ≤ 4 * ((A.card : ℤ) * M ^ 2) := le_of_mul_le_mul_left hcube ht0
    have hP2 : (2 : ℤ) ^ (2 * A.card) = 16 * t ^ 2 := by
      rw [hmcard, ht]; rw [show 2 * (m + 2) = m * 2 + 4 by ring, pow_add, pow_mul]; ring
    have hgoalZ : (2 : ℤ) ^ (2 * A.card) ≤ 64 * A.card * M ^ 2 := by
      rw [hP2]; nlinarith [hcancel]
    exact_mod_cast hgoalZ

/-- **Erdős–Moser, square-root form.** A set with distinct subset sums and all elements `≤ M`
satisfies `2^{|A|} ≤ 8·√{|A|}·M`, i.e. its largest element is at least `2^{|A|}/(8√{|A|})` — the
classical `Θ(2^n/√n)` lower bound. -/
theorem two_pow_le_sqrt_mul {A : Finset ℕ} {M : ℕ}
    (h : HasDistinctSubsetSums A) (hM : ∀ x ∈ A, x ≤ M) (hA : A.Nonempty) :
    (2 : ℝ) ^ A.card ≤ 8 * Real.sqrt A.card * M := by
  have hbR : (2 : ℝ) ^ (2 * A.card) ≤ 64 * A.card * M ^ 2 := by
    exact_mod_cast two_pow_two_mul_card_le h hM hA
  have hsq : (8 * Real.sqrt A.card * M) ^ 2 = 64 * A.card * M ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have e2n : ((2 : ℝ) ^ A.card) ^ 2 = (2 : ℝ) ^ (2 * A.card) := by
    rw [← pow_mul, mul_comm]
  have key : ((2 : ℝ) ^ A.card) ^ 2 ≤ (8 * Real.sqrt A.card * M) ^ 2 := by
    rw [e2n, hsq]; exact hbR
  have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ A.card := by positivity
  have hrhs : (0 : ℝ) ≤ 8 * Real.sqrt A.card * M := by positivity
  have hsqrt := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq h2n, Real.sqrt_sq hrhs] at hsqrt

end DistinctSubsetSums
