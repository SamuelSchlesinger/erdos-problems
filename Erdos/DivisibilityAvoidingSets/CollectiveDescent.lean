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

end DivisibilityAvoidingSets
