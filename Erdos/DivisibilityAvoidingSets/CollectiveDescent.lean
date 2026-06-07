import Erdos.DivisibilityAvoidingSets.ThresholdStrategy

/-!
# Collective descent for the high-rank room-cover obstruction (Erdős #12)

The bounded-rank room-cover obstruction is closed in `ThresholdStrategy.lean`
because the core support primes are confined to a *fixed finite* prime set `P`,
so a pigeonhole forces one `p ∈ P` to carry non-summable mass — a descent
contradicting quotient-irreducibility.

The high-rank case fails that pigeonhole: "fresh" support primes (those outside a
chosen small-prime box `P = Q.primesBelow`) proliferate with the scale, and no
single fresh prime need carry infinite mass.

This file develops the *collective-descent* route.  The first ingredient,
established here, replaces the coarse harmonic majorant `k·F/Q` for the
fresh-prime room mass by the **actual reciprocal mass of the fresh prime layers**:
each fresh support prime is prime, so under irreducibility its multiple layer is
reciprocal-summable, and the room mass it captures is at most its full layer
budget.  Consequently the entire fresh capture is bounded by
`∑_{p fresh} primeLayerBudget A p`.

The payoff (subsequent lemmas / the open case): if this fresh-layer sum stays
*bounded* as the scale grows, the unbounded room mass must be carried by the
*fixed finite* old box `P`, which reactivates the bounded-support descent.  The
residual open case is precisely *unbounded fresh-layer mass*.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- **Room-on-`p` mass is at most the full `p`-layer budget.**  Every room
element divisible by `p` is an `A`-multiple of `p`, so its reciprocal mass is a
finite sub-sum of the reciprocal-summable `p`-multiple layer.  Valid for any
prime `p` in a quotient-irreducible counterexample. -/
theorem SummabilityCounterexample.lcmRoomPrimeDivisorMass_le_primeLayerBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {k p : ℕ} {J : Finset ℕ} (hp : Nat.Prime p) :
    lcmRoomPrimeDivisorMass A k J p ≤ primeLayerBudget A p := by
  classical
  have hsum : ReciprocalSummable (multipleLayer p A) :=
    hA.reciprocalSummable_multipleLayer_prime_of_quotient_irreducible hirred hp
  unfold lcmRoomPrimeDivisorMass primeLayerBudget
  refine finset_sum_reciprocal_le_tsum_indicator_of_subset hsum ?_
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hxRoom, hpx⟩ := hx
  have hxA : x ∈ A := (mem_lcmRoomFinset.mp hxRoom).2.2.1
  exact mem_multipleLayer.mpr ⟨hxA, hpx⟩

/-- **Fresh-prime room capture is bounded by the actual fresh-layer mass.**  The
reciprocal mass the room concentrates on support primes outside the box `P` is at
most the sum, over those fresh support primes, of their full `A`-multiple-layer
budgets.  This is the scale-uniform replacement for the coarse `k·F/Q` harmonic
majorant: it sees the real arithmetic of `A`, not the dyadic interval length. -/
theorem SummabilityCounterexample.lcmRoomFreshPrimeSupportMass_le_sum_primeLayerBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {k : ℕ} {J P : Finset ℕ} :
    lcmRoomFreshPrimeSupportMass A k J P ≤
      ∑ p ∈ (corePrimeSupport J).filter (fun p => p ∉ P), primeLayerBudget A p := by
  classical
  unfold lcmRoomFreshPrimeSupportMass
  refine Finset.sum_le_sum ?_
  intro p hp
  have hpprime : Nat.Prime p :=
    prime_of_mem_corePrimeSupport (Finset.mem_filter.mp hp).1
  exact hA.lcmRoomPrimeDivisorMass_le_primeLayerBudget hirred hpprime

/-- **Scale-uniform covered-room mass bound.**  When the LCM room of a core `J`
is covered by the prime support of `J`, the entire room reciprocal mass is at
most the sum of the *actual* `A`-multiple-layer budgets of the support primes —
a quantity that depends only on the arithmetic of `A` along those primes, *not*
on the dyadic scale `K`.

This is the sharp replacement for the coarse `K · ∑_{p} 1/p` majorant used in the
`false_of_uniform_prior_scalePrimeSupportBound` route.  It pins the residual open
problem to a single inequality: **is `∑_{p ∈ corePrimeSupport J} primeLayerBudget A p`
bounded as the room-cover witnesses run to infinity?**  The support proliferates
with fresh primes, but each individual layer is finite under irreducibility, so
the whole question is whether their collective mass stays bounded. -/
theorem SummabilityCounterexample.lcmRoomReciprocalMass_le_sum_primeLayerBudget_of_room_cover
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {k : ℕ} {J : Finset ℕ}
    (hcover : ((lcmRoomFinset A k J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    lcmRoomReciprocalMass A k J ≤
      ∑ p ∈ corePrimeSupport J, primeLayerBudget A p := by
  classical
  calc
    lcmRoomReciprocalMass A k J
        ≤ lcmRoomPrimeSupportMass A k J :=
      lcmRoomReciprocalMass_le_primeSupportMass_of_room_cover hcover
    _ = ∑ p ∈ corePrimeSupport J, lcmRoomPrimeDivisorMass A k J p := rfl
    _ ≤ ∑ p ∈ corePrimeSupport J, primeLayerBudget A p := by
        refine Finset.sum_le_sum ?_
        intro p hp
        exact hA.lcmRoomPrimeDivisorMass_le_primeLayerBudget hirred
          (prime_of_mem_corePrimeSupport hp)

/-- **Sharp prefix-mass bound.**  A delayed dyadic prefix of a covered
LCM-minimal core is paid for by the core's own rank contribution `r / 2^N` plus
the collective support-layer mass `∑_{p ∈ support} primeLayerBudget A p`.  This
is the scale-uniform form of the obstruction inequality: the only `K`-dependence
left is hidden inside the rank `r`, and the room term no longer carries the
coarse `K · ∑ 1/p` factor. -/
theorem SummabilityCounterexample.dyadicPrefixReciprocalMass_le_rank_div_add_sum_primeLayerBudget
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N m K r : ℕ} {J : Finset ℕ}
    (hJ : CoprimeLCMSelection.LCMMinimal A K r J) (hN : 2 ≤ N)
    (hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K)
    (hcover : ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
      ⋃ p ∈ corePrimeSupport J, {x | p ∣ x}) :
    dyadicPrefixReciprocalMass A N m ≤
      (r : ℝ) / (((2 ^ N : ℕ) : ℝ)) +
        ∑ p ∈ corePrimeSupport J, primeLayerBudget A p := by
  have hbase :=
    dyadicPrefixReciprocalMass_le_card_div_pow_add_lcmRoomReciprocalMass_of_delay
      hJ.1 hN hdelay
  have hroom :=
    hA.lcmRoomReciprocalMass_le_sum_primeLayerBudget_of_room_cover hirred hcover
  rw [hJ.card_eq] at hbase
  linarith

/-- **Bounded collective layer mass forces unbounded coprime rank.**  Suppose an
irreducible counterexample has endless delayed room covers (one for every late
prefix) whose collective support-layer mass stays below a fixed bound `B`.  Then
for every target rank `ρ` some witness core already has rank `> ρ`: the heavy
prefix cannot be paid by the bounded room term, so the rank term `r / 2^N` must
absorb it.

This closes the *bounded-collective-mass* sub-case down to unbounded rank — but
honestly **not** the whole obstruction: it yields arbitrarily large coprime cores
at *some* scales, which only refutes *bounded* rank.  It does not deliver the
*scale-synchronised* fast growth (`rank ≳ log scale` at every scale) that
`EventuallyFastCoprimeRank` needs.  The residual open case is precisely *slow
unbounded rank with unbounded collective layer mass*. -/
theorem SummabilityCounterexample.exists_large_coprime_core_of_bounded_collectiveLayerMass
    {A : Set ℕ} (hA : SummabilityCounterexample A)
    (hirred : ∀ a d : ℕ, d ∣ a → 1 < d →
      ¬ SummabilityCounterexample (quotientSet d (multipleLayer d A)))
    {N : ℕ} (hN : 2 ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hendless : ∀ m, N ≤ m →
      ∃ (T K r : ℕ) (J J₀ : Finset ℕ),
        CoprimeLCMSelection.LCMMinimal A K r J ∧
        CoprimeLCMSelection A T r J₀ ∧
        T ≤ K ∧
        J₀.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K ∧
        ((lcmRoomFinset A K J : Finset ℕ) : Set ℕ) ⊆
          ⋃ p ∈ corePrimeSupport J, {x | p ∣ x} ∧
        (∑ p ∈ corePrimeSupport J, primeLayerBudget A p) ≤ B)
    (ρ : ℕ) :
    ∃ (K r : ℕ) (J : Finset ℕ), ρ < r ∧ CoprimeLCMSelection A K r J := by
  set D : ℝ := ((2 ^ N : ℕ) : ℝ) with hDdef
  have hD : (0 : ℝ) < D := by rw [hDdef]; positivity
  set C : ℝ := (ρ : ℝ) / D + B + 1 with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ (ρ : ℝ) / D := by positivity
    linarith
  obtain ⟨n, hNn, hprefix⟩ :=
    exists_lt_dyadicPrefixReciprocalMass_of_not_reciprocalSummable
      hA.2.1 hA.2.2.2 hC N
  set m := n - 1 with hm
  have hNm : N ≤ m := by omega
  obtain ⟨T, K, r, J, J₀, hJ, hJ₀, hTK, hdelay₀, hcover, hSig⟩ := hendless m hNm
  have hdelay : J.lcm (fun a : ℕ => a) * 2 ^ (m + 1) ≤ 2 ^ K :=
    hJ.delay_of_prior_selection hJ₀ hTK hdelay₀
  have hpref :=
    hA.dyadicPrefixReciprocalMass_le_rank_div_add_sum_primeLayerBudget
      hirred hJ hN hdelay hcover
  refine ⟨K, r, J, ?_, hJ.1⟩
  -- C < prefix ≤ r/D + Σ ≤ r/D + B, and C = ρ/D + B + 1, so ρ/D < r/D, so ρ < r
  have hlt : (ρ : ℝ) / D < (r : ℝ) / D := by
    have h1 : C < (r : ℝ) / D + ∑ p ∈ corePrimeSupport J, primeLayerBudget A p :=
      lt_of_lt_of_le hprefix hpref
    rw [hCdef] at h1
    linarith [hSig]
  have hmul := mul_lt_mul_of_pos_right hlt hD
  rw [div_mul_cancel₀ _ hD.ne', div_mul_cancel₀ _ hD.ne'] at hmul
  exact_mod_cast hmul

/-- **The `Q`-smooth part of any set has summable reciprocals** (Euler product
bound `∏_{p<Q} (1-1/p)⁻¹`).  Purely an Euler-product fact about smooth numbers;
needs no hypothesis on `A`. -/
theorem reciprocalSummable_inter_smoothNumbers (A : Set ℕ) (Q : ℕ) :
    ReciprocalSummable (A ∩ Nat.smoothNumbers Q) := by
  classical
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_one' := by norm_num
      map_mul' := fun m n => by push_cast; rw [mul_inv] }
  have hfval : ∀ n : ℕ, f n = (n : ℝ)⁻¹ := fun _ => rfl
  have hf : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := by
    intro p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    rw [hfval, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_lt_one₀ hppos]
    exact_mod_cast hp.one_lt
  have hsmooth : Summable (fun m : Nat.smoothNumbers Q => ‖f (m : ℕ)‖) :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hf Q).1
  refine (hsmooth.comp_injective
    (Set.inclusion_injective (Set.inter_subset_right))).congr (fun x => ?_)
  show ‖f (x : ℕ)‖ = (1 : ℝ) / ((x : ℕ) : ℝ)
  rw [hfval, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div]

end DivisibilityAvoidingSets
