import Erdos.DivisibilityAvoidingSets.ThresholdStrategy

/-!
# The coprime-rank-growth kernel for Erdős #12 (reciprocal summability)

The positive route to the reciprocal-summability part of Erdős problem #12 is
spread across many hundreds of lemmas in `ThresholdStrategy.lean`, organised
around a *room-cover* obstruction.  This file distills that sprawl into a single
named target.

## The one sharp target

The dyadic-shell geometric bound `AvoidingSet.dyadicShell_mass_le_two_mul`
`_geometric_of_coprime` (in `CoprimeSelection.lean`) says: if at dyadic scale `k`
an avoiding set has `t` pairwise-coprime members below `2^k` with product
`≤ 2^k`, then the reciprocal mass of its `k`-th dyadic shell is `≤ 2·(3/4)^t`.
Summing shells, reciprocal summability follows the instant these geometric
majorants are summable.  That is exactly `EventuallyFastCoprimeRank`:

> every dyadic scale `k` carries a coprime-LCM core of rank `f k`, with
> `∑ₖ 2·(3/4)^{f k} < ∞`.

`f k ≥ c·log₂ k` with `c > 1 / log₂(4/3) ≈ 2.41` already suffices (then
`(3/4)^{f k} ≤ k^{-c·log₂(4/3)}` is summable), so the target is the modest
**coprime rank grows at least logarithmically in the scale.**

## The four-case landscape (what is, and is not, proved)

A hypothetical `SummabilityCounterexample A` must, by
`not_eventuallyFastCoprimeRank` below, *fail* `EventuallyFastCoprimeRank`: its
coprime rank grows too slowly to be summable.  Splitting on that growth:

1. **Reducible** (`A` has a proper common-factor quotient that is itself a
   counterexample).  Handled in principle by common-factor descent, but the
   well-founded *termination* of that descent is **not** formalized — `hirred`
   (quotient-irreducibility) remains a hypothesis throughout `ThresholdStrategy`.
2. **Irreducible, bounded rank.**  Closed:
   `SummabilityCounterexample.not_endless_prior_room_covers_rank_le_of_irreducible`
   forces a fixed finite prime set to carry the room cover, hence a descent,
   contradicting irreducibility.
3. **Irreducible, fast unbounded rank** (`≥ c·log₂ k`).  Closed: it *is*
   `EventuallyFastCoprimeRank`, so `reciprocalSummable_of_eventuallyFastCoprimeRank`
   applies — contradicting `¬ ReciprocalSummable`.
4. **Irreducible, slow unbounded rank** (`→ ∞` but `= o(log k)`).  **Open.**
   Support primes proliferate ("fresh" primes at every scale), so no single
   prime carries infinite mass (no descent), yet decay is too slow to sum.  This
   is precisely the residual content isolated by
   `NoLargeScaleGapPriorRoomCover`.

So modulo the descent-termination of case 1, the entire open problem is case 4:
ruling out *slow unbounded coprime rank*.
-/

namespace DivisibilityAvoidingSets

set_option linter.style.header false

/-- **The positive kernel of Erdős #12.**  An avoiding set has *summably fast
coprime rank* when there is a rank schedule `f` with summable geometric shell
majorant `2·(3/4)^{f k}` realised at every dyadic scale by an actual coprime-LCM
core. -/
def EventuallyFastCoprimeRank (A : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, Summable (fun k => 2 * ((3 / 4 : ℝ) ^ f k)) ∧
    ∀ k, ∃ J : Finset ℕ, CoprimeLCMSelection A k (f k) J

/-- Summably fast coprime rank is sufficient for reciprocal summability: feed the
scale-by-scale coprime cores into the geometric dyadic-shell criterion. -/
theorem AvoidingSet.reciprocalSummable_of_eventuallyFastCoprimeRank
    {A : Set ℕ} (hA : AvoidingSet A) (hpos : PositiveSet A)
    (h : EventuallyFastCoprimeRank A) :
    ReciprocalSummable A := by
  classical
  obtain ⟨f, hfsum, hsel⟩ := h
  choose J hJ using hsel
  refine hA.reciprocalSummable_of_coprime_lcm_selection_card_lower
    (J := J) (m := fun _ a => a) (f := f) hpos hfsum ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k i hi; exact (hJ k).1 i hi
  · intro k i hi
    exact lt_of_lt_of_le (by norm_num) ((hJ k).2.2.2.2.1 i hi)
  · intro k i hi; exact (hJ k).2.1 i hi
  · intro k; exact (hJ k).2.2.1
  · intro k; exact (hJ k).2.2.2.1
  · intro k i hi; exact (hJ k).2.2.2.2.1 i hi
  · intro k; exact (hJ k).2.2.2.2.2

/-- **Reduction.**  To settle the reciprocal-summability part of Erdős #12 it is
enough to prove that *every* infinite positive avoiding set has summably fast
coprime rank.  This is the single sharp target the positive route is chasing. -/
theorem erdos12Summability_of_eventuallyFastCoprimeRank
    (h : ∀ A : Set ℕ, A.Infinite → PositiveSet A → AvoidingSet A →
        EventuallyFastCoprimeRank A) :
    Erdos12SummabilityQuestion := by
  intro A hinf hpos havoid
  exact havoid.reciprocalSummable_of_eventuallyFastCoprimeRank hpos
    (h A hinf hpos havoid)

/-- **Contrapositive, naming the open kernel.**  A summability counterexample is
exactly a set whose coprime-LCM rank fails to grow summably fast: the rank may
tend to infinity, but only in the "slow unbounded" regime of case 4.  Ruling out
this single possibility resolves the problem. -/
theorem SummabilityCounterexample.not_eventuallyFastCoprimeRank
    {A : Set ℕ} (hA : SummabilityCounterexample A) :
    ¬ EventuallyFastCoprimeRank A := by
  intro h
  exact hA.2.2.2
    (hA.2.2.1.reciprocalSummable_of_eventuallyFastCoprimeRank hA.2.1 h)

end DivisibilityAvoidingSets
