# Extras Bound Attack: `e(A) ≥ 2 ⇒ |A| ≤ C·√N` with `C < 2/√3`?

**Date:** 2026-05-22. PI assignment: subproblem of Erdős #864 closure.

**Setup.** Let `A ⊆ {1, ..., N}` be a strong almost-Sidon (SAS) set with
exception value `n*`, multiplicity `r := r_A(n*)`, and self-pair indicator
`δ ∈ {0, 1}` (`δ = 1` iff some `c ∈ A` has `2c = n*`). Let `P :=
pairElements(A, n*)` (set of elements participating in an n*-pair), so
`|P| = 2r − δ` (R4's counting lemma). Define **extras**
`X := A ∖ P` with `e := |X| = |A| − (2r − δ)`. Equivalently:
`|A| = 2r + e − δ`. Empirically `e ∈ {0, 1}` for all 12 known extremizers.

**Task.** Prove: if `e ≥ 2` then `|A| ≤ C·√N(1 + o(1))` for some
`C < 2/√3 ≈ 1.1547`. With R4 (which closes the `e = 0` case via the
EF lower bound), this would close `#864` to `2/√3`.

## Structural decomposition

Write `P = L ∪ U` where `L := {b : b ∈ A, 2b < n*}` (lower halves of
n*-pairs) and `U := {n* − b : b ∈ L}` (upper halves). In the no-self-pair
case (`δ = 0`), `|L| = |U| = r`, and `L ⊆ [1, ⌊(n*−1)/2⌋]`,
`U ⊆ [⌈(n*+1)/2⌉, n*]`. Each of `L`, `U` is **Sidon**: their pair-sums
live strictly below (resp. above) `n*`, the unique SAS exception value,
so they have no allowed collisions.

Split extras by side: `X_- := X ∩ [1, n*/2]`, `X_+ := X ∩ (n*/2, N]`,
so `e = e_- + e_+` with `e_± := |X_±|`.

## Key Sidon-extraction lemma (extras-tracked)

**Lemma E1.** `B_- := L ∪ X_-` is Sidon in `[1, ⌊n*/2⌋]`.
`B_+ := U ∪ X_+` is Sidon in `(⌊n*/2⌋, N]`. ✶

*Proof.* All pair-sums in `B_-` are `< n*`: `L + L < n*` by construction;
extras give SAS-unique non-`n*` sums (an extra `x` has `n* − x ∉ A`, so
no extras-involving sum equals `n*`); SAS forbids two distinct sorted
pairs with the same non-`n*` sum. So `B_-` is Sidon. Symmetric for `B_+`.
This formalization is straightforward via `r1_general_multiplicity_bound`
applied to `B_-` (whose pair-sum multiplicities at every value are `≤ 1`).

## Counting bound from Lemma E1

By Lindström (`SidonIntervalAsymptotic` in Mathlib):

  `|B_-| ≤ √(n*/2)·(1 + o(1))`, `|B_+| ≤ √(N − n*/2)·(1 + o(1))`.

Adding:

  `2r + e = |B_-| + |B_+| ≤ (√(n*/2) + √(N − n*/2))·(1 + o(1)) ≤ √(2N)·(1+o(1))`,

giving `|A| ≤ √2·√N·(1 + o(1))`. **This is the existing `√2` bound** —
the extras-tracked split does not by itself break `√2`.

## Why elementary counting can't push below `√2` (using extras)

The reason is structural. The Cauchy–Schwarz inequality
`√(a) + √(b) ≤ √(2(a + b))` is tight when `a = b`. For `√2` to be beat,
we'd need the asymmetric case (`n* ≠ N`, or unequal-half-sizes) to be
forced. But the extras hypothesis is *additive*, not *positional*: the
constraint `e ≥ 2` shows up as a `+e` on the left side of an inequality
already balanced at `2r`. Subtracting `e` ≥ 2 from `√(2N) − e` does *not*
improve the leading constant; it only changes the additive error.

**Quantitative check.** Suppose `n* = N` (worst case for `√2`). Then
`|B_-| ≤ √(N/2)·(1+o(1))` and `|B_+| ≤ √(N/2)·(1+o(1))`. Achieving
equality requires both `B_±` to saturate Lindström in their respective
intervals. At extremality, `|L| = |U| = r ≈ √(N/2)`, `e ≈ 0` — i.e., the
`√2` corner is *only* achieved at `e = 0`. The constraint `e ≥ 2` should
push us off this corner, but the per-side Sidon bound *averages* over
extras and pair-elements indifferently.

## Three-piece counting (attempted refinement, also vacuous)

Refining: the within-`B_-` sum-set covers `|B_-|(|B_-|+1)/2` distinct
values in `[2, n*]`; within-`B_+` covers `|B_+|(|B_+|+1)/2` in `(n*, 2N]`;
cross sums `B_- × B_+` cover `|B_-|·|B_+| − (r − 1)` distinct values
(`r` diagonal collisions all at `n*`). By SAS, the *total* count is

  `|B_-|(|B_-|+1)/2 + |B_+|(|B_+|+1)/2 + |B_-||B_+| − (r − 1)`
  `= |A|(|A|+1)/2 − (r − 1) ≤ 2N − 1`,

i.e., `|A|² + |A| ≤ 4N − 4 + 2r`. With `r ≤ |A|/2` this is `|A|² ≤ 4N`,
giving `|A| ≤ 2√N` — strictly *worse* than `√2`. Even using
`r ≤ (|A| − e + δ)/2` (subtracting the extras contribution from `r`)
only nudges by `O(e)`, well below the `√2` threshold of `≈ 0.26·√N` of
slack we need to push to `2/√3`.

## R1-gen extraction (Sidon-set extraction, also vacuous)

Applying `r1_general_multiplicity_bound` with `k = r − 1`: we extract a
Sidon `S ⊆ A` with `|S| ≥ |A| − (r − 1)`. The optimal choice removes
`r − 1` pair-half elements (keeping one anchor pair intact), giving
`|S| = |A| − r + 1 = r + 1 − δ + e`. Lindström: `|S| ≤ √N·(1 + o(1))`.

Combined: `r + e ≤ √N·(1+o(1))`, so `|A| = 2r + e − δ ≤ 2(r + e) − e`
`≤ 2√N − 2`. **Worse than `√2`.** No improvement.

## Where the obstruction lies (diagnosis)

The 17 attacks documented in `below-sqrt2.md` all converge on the
same meta-obstruction: SAS bipartite rigidity is *location-sensitive*,
but every elementary technique is *translation-invariant* or
*L²-averaged*. The extras-hypothesis `e ≥ 2` does **not** by itself
add positional information — extras can sit anywhere in `[m, M]`. Two
extras on opposite sides give the same counting constraints as zero
extras with a balanced pair structure.

To get below `√2`, we'd need a *position-sensitive* statement about
where extras live, *and* a counting lemma that uses that position.

## Specific attempts that don't close

1. **Pikhurko-style on `B_- ∪ B_+`.** The cross-sumset density
   profile (Attempt C in `density-profile-attack.md`) gives 1/4 slack
   at the `√2` corner. Adding `e ≥ 2` extras gives an *additional* `+O(e)`
   slack, but the dominant `1/4` slack is unaffected.

2. **R1-gen with anchor pair retention.** Iterate R1-gen carefully:
   remove `r − 1` pair-halves, keep one anchor `(m, M)` and all extras.
   Resulting `S` has `|S| = r + 1 + e − δ` and is Sidon in `[1, N]`. But
   `S` is not concentrated in a half-interval, so Lindström gives `√N`,
   not `√(N/2)`. So `|A| ≤ 2|S| − 2 ≤ 2√N − 2` — vacuous.

3. **R1-gen + half-interval split.** Remove `r − 1 + e_+` elements
   (lower halves of `r − 1` pairs and all upper-extras). Remaining
   `S = L_anchor ∪ L ∪ X_-`, Sidon in `[1, ⌊n*/2⌋]`. `|S| = r + e_-`,
   `|A| = 2r + e − δ`. Bound: `r + e_- ≤ √(n*/2)·(1+o(1))`. With the
   symmetric bound `r + e_+ ≤ √(N − n*/2)·(1+o(1))`, summing recovers
   the original `√2`.

## What is needed to close

A *joint* constraint linking `e_+` and `e_-` to `n*` (e.g., extras
forced asymmetric: `n* ≠ N` when `e ≥ 1`). The R2/R3 results (proved)
say extreme pair is on-axis, but extras *between* the extremes could
live anywhere. No structural lemma in Rigidity.lean rules out
balanced extras.

**Conjecture EX1 (open):** If `A` is SAS with `e(A) ≥ 2` then either
`n* < (1 − δ_0)·N` for some explicit `δ_0 > 0`, or `e_- · e_+ = 0`
(all extras on one side). This would force *asymmetry*, breaking the
`α = β = 1/2` Cauchy–Schwarz equality, and gives an explicit
`C < √2` (depending on `δ_0`).

**Status: open.** EX1 is consistent with all 12 known extremizers
(all of which satisfy `e = 0`, so the hypothesis is vacuous). It is
plausible but I have no proof.

## Conclusion (negative)

I **cannot** prove `|A| ≤ C·√N` for any explicit `C < 2/√3 ≈ 1.155`
under the hypothesis `e(A) ≥ 2` using R1–R4 plus elementary counting.
The bound that follows directly is `C = √2 ≈ 1.414` (no improvement
over the existing conditional `Sqrt2BoundConditional`), and three
distinct refinement attempts (three-piece counting, R1-gen, R1-gen
with anchor retention) all give `C ≥ √2` or worse.

The extras hypothesis `e ≥ 2` is **not** by itself sufficient to break
`√2`. To close, one needs a structural rigidity lemma forcing extras
asymmetry (Conjecture EX1) or a position-sensitive counting argument
beyond the elementary toolkit — see the 17 attack diagnoses in
`below-sqrt2.md`.

## Recommendation to PI

1. **Strategic pivot:** the closure path is via R4 + a *uniqueness*
   theorem (`e(A) = 0` forced for near-extremal SAS), not via an
   `e ≥ 2` bound. The `e = 1` case is also worth investigating: is
   `e(A) = 1` compatible with `|A| ≥ (2/√3 + ε)·√N`?

2. **Empirical check:** before further analysis, search computationally
   for SAS sets with `e ≥ 1` and `|A|` close to `2/√3·√N`. If none
   exist, that's evidence for `e = 0` rigidity. The data in
   `computer-search-report.md` (N = 70..79) and the asymmetric extremizers
   at N = 100, 200 all have `e = 0` — suggesting `e = 0` rigidity is
   the natural form.

3. **No Lean formalization** added at this stage: the elementary
   bound here is strictly worse than the existing
   `strong_almostSidon_card_le_sqrt2_sqrt_of_sidon_interval`, so there
   is nothing to add to `Rigidity.lean`.

## Files

- `/Users/samuelschlesinger/projects/formalization/erdos-problems/Erdos/AlmostSidonSets/Rigidity.lean` (R1–R4, E1–E_anchor, used as input).
- `/Users/samuelschlesinger/projects/formalization/erdos-problems/Erdos/AlmostSidonSets/UpperBound/Sqrt2BoundConditional.lean` (existing `√2` bound).
- `below-sqrt2.md` (17 attack diagnoses; consistent verdict).
- `empirical-invariants-report.md` (12 extremizers all have `e = 0`).
