# Participation from Cardinality: Attack Report

**Date:** 2026-05-22.
**Goal:** Prove the participation hypothesis `n* − m₂ ∈ A` of
`r3_second_extreme_pair` from a cardinality lower bound on `A`.

**Target theorem.** Let `A ⊆ {1, …, N}` be SAS with exception `n*` and
R2 axis `m + M = n*` (R2 plus R1 already give this when an exception
exists and `|A| ≥ 3`). If `n* − m₂ ∉ A`, show `|A| ≤ X(N)` for some
explicit `X(N) < (2/√3)·√N(1 + o(1))`.

**Verdict: open.** I cannot prove `|A| ≤ C·√N` for any explicit
`C < (2/√3) ≈ 1.1547` under the failed-participation hypothesis. The
elementary toolkit (R1-gen, E1, R2, R3, structural split) only gives
`C = √2 ≈ 1.4142`, strictly weaker than the existing
`Sqrt2BoundConditional`. The diagnosis is the same as
`extras-bound-attack.md`: SAS is location-sensitive but the techniques
are L²-averaged.

## Reformulation

By E2 (`e2_pair_element_has_reflection`) and R3, `m₂ ∈ pairElements`
iff `n* − m₂ ∈ A`. So failed participation = `m₂ ∉ pairElements`, i.e.
`m₂` is an "extra" (`m₂ ∈ X := A ∖ P` in the notation of
`extras-bound-attack.md`). The participation question is the
*positional* refinement of the extras question: **does the extra
`m₂` (specifically the second-smallest element) being unpaired force
a stronger bound than a generic extra?**

## Six attempted angles, all fail

### A1. R1-gen + half-interval (the standard split).

`A_- := A ∩ [1, ⌊n*/2⌋]`, `A_+ := A ∩ (⌊n*/2⌋, N]`. Both Sidon
(Structure.lean). Lindström: `|A_-| ≤ √(n*/2)(1+o(1))`,
`|A_+| ≤ √(N − n*/2)(1+o(1))`. Cauchy–Schwarz: `|A| ≤ √(2N)(1+o(1))`.
The "extra m₂" datum adds one element to `A_-`; the upper bounds on
`|A_±|` are unaffected. **Yields C = √2, no improvement.**

### A2. Sidon extraction keeping m₂.

`r := r_A(n*)`. Apply `r1_general_multiplicity_bound` with
`k = r − 1`: extract Sidon `S ⊆ A` with `|S| ≥ |A| − r + 1`. The optimal
removal is `r − 1` lower halves (keep the anchor pair `(m, M)` plus
all extras including `m₂`). Lindström on `[1, N]`: `|S| ≤ √N(1+o(1))`.
Combined: `|A| ≤ √N(1+o(1)) + r − 1 ≤ √N + |A|/2`, giving
`|A| ≤ 2√N(1+o(1))`. **Worse than √2.**

### A3. Three-piece counting.

`A = L ⊔ U ⊔ X`, with `L, U` Sidon (pair halves), `X` extras
including `m₂`. Within-`L`, within-`U`, cross-`LU`, and extras-sums
all distinct (SAS, with `r` collisions at `n*` in `L × U`).
Count distinct sums:
`|L|² + |U|² + 2|L||U| − 2(r − 1) + O(|X|)` ≤ `2N`,
giving `|A|² ≤ 4N + O(|A|)`, so `|A| ≤ 2√N`. **Worse than √2.**

### A4. m₂-sums Sidon-unique angle.

Since `n* − m₂ ∉ A`, none of the `|A| − 1` sums `m₂ + a` equal `n*`
(by R3 + the partner-existence equivalence). All `|A| − 1` sums are
distinct, lying in `[m + m₂, m₂ + M]` ⊆ `[2, 2N]`. Constraint:
`|A| − 1 ≤ 2N`. **Vacuous (gives `|A| ≤ 2N`, not even O(√N)).**

### A5. Specific positional gain from "m₂ is *second* smallest".

If `n* − m₂ ∉ A`, the candidate partner `n* − m₂ ∈ (n*/2, M)` is
missing from `A_+`. So `A_+ ⊆ [⌈n*/2⌉ + 1, N] ∖ {n* − m₂}`, which
gives `|A_+| ≤ ⌊N − n*/2⌋ − 1`. But Lindström already gives
`|A_+| ≤ √(N − n*/2)(1+o(1))`, vastly smaller than the count bound.
The missing point doesn't reduce the Lindström bound asymptotically.
**No improvement.**

### A6. Forcing additional 2-representations.

Hope: if `m₂` is unpaired and `|A|` is large, m₂'s presence forces
some sum to have ≥ 2 representations, contradicting SAS exception
uniqueness (E1 forbids second exceptional value). But m₂ contributes
`|A| − 1` sums; SAS only forbids these from equalling `n*` more than
once (it can equal n* zero times, which is the failure case). No
contradiction from cardinality alone — the "extra" can be absorbed
without creating a second exceptional value.

## Quantitative comparison with the target

For `|A| ≥ (2/√3 + ε)√N ≈ 1.155 √N`, R1-gen gives
`r ≥ (2/√3 − 1)√N ≈ 0.155 √N`. The participation failure removes
one element from `pairElements`, so `|pairElements| = 2r` and
`|A| = 2r + e − δ` with `e ≥ 1`. None of A1–A6 leverages the
*specific positional location* of the extra `m₂` (smallest extra)
in a way that beats the symmetric Cauchy–Schwarz corner.

## Why "m₂" doesn't help over "some extra"

The Cauchy–Schwarz inequality `√x + √(N − x) ≤ √(2N)` is tight
at `x = N/2`. To beat √2 we need to force `x = n*/2` to be
*away* from `N/2`. The participation failure of `m₂` is a constraint
on `A_+` (missing one specific value `n* − m₂`), not on `n*` itself.
The position of `n*` within `[1, 2N]` is determined by the global
structure of `A`, not by where individual extras sit. Even iterating
to second-smallest doesn't constrain `n*` enough.

This is the same meta-obstruction documented in `extras-bound-attack.md`:
SAS bipartite rigidity is *positional*, but every elementary
counting argument is *L²-averaged*.

## Open conjecture (parameter-strengthened)

**Conjecture P1.** If `A` is SAS with `n* − m₂ ∉ A` and `|A| ≥ 3`,
then either (i) `n* ≤ (1 − δ_0) N` for some explicit `δ_0 > 0`, or
(ii) at least one additional "second-level" participation fails
(`n* − m₃ ∉ A` or `n* − M₃ ∉ A`).

If P1 holds with `δ_0 ≈ 1/4`, then in case (i) the asymmetric
Cauchy–Schwarz gives `√(n*/2) + √(N − n*/2) ≤ √2 · √N · √(3/4 + 1/4) =
≈ √(2)·√N`, which is still √2 unless `δ_0` is large enough. To beat
√2 → 2/√3 we need `δ_0 ≈ 0.45`, which is empirically wildly
inconsistent with the data (all known extremizers have `n* ∈ [N, 2N]`).

So Conjecture P1 in the form (i) is *not* the right strengthening
either. The right strengthening must be (ii) iterated participation
failure, but that just defers the question.

## Diagnosis (stall point)

The participation hypothesis sits at the structural-rigidity barrier:
proving it requires a *positional* lemma about where extras live in
SAS sets, of the kind documented as missing in the 17 attacks in
`below-sqrt2.md`. None of R1–R4, E1–E2, structural splits, R1-gen,
Sidon extraction, or three-piece counting yield positional
information about extras.

**Stall constant: C = √2 ≈ 1.4142.** This matches the existing
`Sqrt2BoundConditional`. No `C < √2` is reachable from the failed-
participation hypothesis using existing tools. To break √2 → 2/√3,
a fundamentally new structural input (Conjecture EX1 in
`extras-bound-attack.md`, or a positional rigidity lemma) is needed.

## No Lean formalization added

Every theorem above gives `|A| ≤ C·√N` with `C ≥ √2`, strictly weaker
than the existing conditional `√2` bound in
`Erdos/AlmostSidonSets/UpperBound/Sqrt2BoundConditional.lean`. So
there is no new content to formalize.

## Files referenced

- `/Users/samuelschlesinger/projects/formalization/erdos-problems/Erdos/AlmostSidonSets/Rigidity.lean` (R1–R4, E1, E2, E-anchor; `r3_second_extreme_pair` is the consumer of participation).
- `/Users/samuelschlesinger/projects/formalization/erdos-problems/Erdos/AlmostSidonSets/UpperBound/Sqrt2BoundConditional.lean` (existing `√2` bound).
- `extras-bound-attack.md` — same obstruction for `e ≥ 2`.
- `below-sqrt2.md` — meta-obstruction catalog.
- `second-extreme-report.md` — origin of the participation question.
