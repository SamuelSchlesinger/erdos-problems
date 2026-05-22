# Converse-of-R4 Direct Attack

**Date:** 2026-05-22. **Companion to:** `Erdos/AlmostSidonSets/Rigidity.lean`,
`empirical-invariants-report.md`, `direct-combinatorial-attack.md`,
`below-sqrt2.md`.

## Target

Let `A ⊆ {1,...,N}` be SAS with exception `n*` and multiplicity `r := r_A(n*)`.
Define
```
e(A) := |A| − 2·r + δ_self
```
where `δ_self = 1` iff `∃ c ∈ A, 2c = n*`. By the counting lemma
`pairElements_card_no_self_pair / with_self_pair`, `e(A) = |A| − |pairElements|`,
i.e., `e(A) = |X|` where `X := A \ pairElements(A, n*)` is the set of
**extras** (elements not in any n*-pair).

The R4 theorem in `Rigidity.lean` shows `e(A) = 0 ⟹ A = B ∪ (n*−B)`
(EF form). The converse-of-R4 target is:

> **Target.** `e(A) ≥ 2 ⟹ |A| < (2/√3 − δ)·√N` for some absolute `δ > 0`.

Combined with R4 this closes the empirical observation that all known
extremizers have `e = 0`.

## Setup

Write `n := |A|`, `P := pairElements(A, n*)`, `X := A \ P`, so
`|P| = 2r − δ_self` and `|X| = e`, `n = |P| + e`.

For each extra `x ∈ X`: by definition, `n* − x ∉ A` (else `(min(x, n*−x),
max(x, n*−x))` is an n*-pair containing `x`, so `x ∈ P`, contradiction).
Consequently, for any `a ∈ A`, the sum `x + a ≠ n*`. By SAS, this sum is
**Sidon-unique**.

## Counting the sumset (elementary attempt)

We count distinct sum-values in `[2, 2N]`.

- **Pairs touching X** (unordered, with diagonal `{x,x}`): a pair `{u,v}`
  with `u ∈ X` or `v ∈ X`. Count: `e·(n−e) + e(e+1)/2 = en − e²/2 + e/2`.
  All such pair-sums are Sidon-unique (none equals `n*` by the extras
  property), hence distinct.

- **Pairs within P**: `(n−e)(n−e+1)/2 = |P|(|P|+1)/2`. Distinct sum-values
  among these = `|P|(|P|+1)/2 − (r−1)` (the `r` pairs summing to `n*`
  collapse to one value).

- **Disjointness**: a touching-X sum equals a within-P sum only if the
  shared value has two distinct pair representations, which (since it
  isn't `n*`) violates SAS-uniqueness. Disjoint.

Total: `(n−e)(n−e+1)/2 − (r−1) + en − e²/2 + e/2 ≤ 2N − 1`.

Substituting `|P| = n − e = 2r − δ_self`:

- (no-self-pair) `r = (n−e)/2`. The LHS simplifies to `n²/2 + e/2 + 1`,
  giving
  ```
  n² ≤ 4N − 4 − e.
  ```
- (self-pair) `r = (n−e+1)/2`. The LHS simplifies to `n²/2 + e/2 + 1/2`,
  giving the same bound `n² ≤ 4N − 5 − e` (slightly stronger).

**Numerical check.** At `n = (2/√3)·√N ≈ 1.155 √N`, `n² ≈ 4N/3 ≪ 4N − 4 − e`
for any plausible `e`. So this bound is far above target.

**Verdict.** The elementary sum-counting refinement of `e ≥ 2` reduces the
trivial `n² ≤ 4N` bound to `n² ≤ 4N − 4 − e`, but does *not* tighten the
Lindström `n ≤ √(2N)` half-split bound and certainly cannot reach
`(2/√3) √N`.

## Why this attack stalls

The hypothesis `e ≥ 2` adds **Sidon-uniqueness for sums involving X**, but
this is already implied by SAS (since the only allowed multiplicity-2
value is `n*`, and extras' sums avoid `n*` by construction). The extras
contribute **fewer collisions**, not more constraints.

Concretely: the dominant `√2 √N` upper bound comes from the **Lindström
half-split**
```
|A_-| ≤ √(n*/2) (1 + o(1)),    |A_+| ≤ √(N − n*/2) (1 + o(1)),
|A| ≤ |A_-| + |A_+| + δ_midpoint.
```
Extras are distributed `X = X_- ⊔ X_+` (in the two halves). The reflection
involution `a ↦ n* − a` sends `A_- ∩ P → A_+ ∩ P` bijectively. So
```
|A_-| = (|P| − δ_self)/2 + |X_-|,
|A_+| = (|P| − δ_self)/2 + |X_+|.
```
Both Lindström bounds apply uniformly, giving
```
|P| − δ_self + e ≤ √(2N) + o(√N),
```
i.e., `|A| ≤ √(2N) + δ_self + o(√N)`. Extras enter **additively** in `|A|`
and **additively** on the right-hand side via the half-densities; they
don't tighten the bound. The `e ≥ 2` hypothesis only gives `n² ≤ 4N − 6`,
which is `n ≤ 2√N − O(1/√N)` — still far above `(2/√3)√N`.

## Why "position-sensitive" arguments are what's needed

The two methods above (raw sum count, Lindström half-split) ignore *where*
the extras sit. The actual structural fact, observed empirically: in
extremal EF-like sets, the pair-elements `P` form an EF skeleton
`B ∪ (n*−B)` with `B ⊆ [1, αn*]` for `α ∈ (0, 1/3]`. The "outer"
configuration leaves the middle band `(α n*, n* − α n*)` *empty* in `A`.

If `A` has an extra `x`, then necessarily `x` lies somewhere in
`[1, N] \ A`. For `e ≥ 2`, we'd need to argue that the extras *cannot* fit
into the empty middle band without creating SAS violations with the EF
skeleton — but this requires (a) knowing `P` is approximately EF, which
is `R4` itself, and (b) a position-sensitive argument about extras
violating the gap structure.

**Circularity:** the converse-of-R4 we are trying to prove (`e ≥ 2 ⟹
small`) is essentially equivalent to "any near-extremal SAS set is EF",
which is the full conjecture. The elementary tools — sum counting,
half-Lindström, the Sidon-uniqueness extras give us — re-derive the
known `√2 √N` bound but never narrow it.

## Microscopic improvement (provable but useless)

The strongest *elementary* statement that incorporates `e`:

> **Lemma (Sum-count with extras).** For any SAS set `A ⊆ {1, ..., N}`
> with exception `n*`, no-self-pair, and `e := |A| − 2 r_A(n*) ≥ 0`,
> we have `|A|² ≤ 4N − 4 − e`.

This is **less than `√2 √N`** only when `e ≥ 4N − 2N = 2N`, i.e., never
in the relevant regime. Useless as a path to `2/√3`.

## What about hybrid attacks?

A possibly useful hybrid: combine the **Lindström half-bound** with the
**peel argument** from `direct-combinatorial-attack.md` §2c, exploiting
that extras force off-axis pairs. The peel argument gives
```
|A| ≤ √N + 2(r − 1) + O(N^{1/4}).
```
With `e ≥ 2`, `2r = |A| − e ≤ |A| − 2`, so `r ≤ (|A| − 2)/2`, and
substituting:
```
|A| ≤ √N + |A| − 4 + O(N^{1/4}),
```
which gives `4 ≤ √N + O(N^{1/4})` — vacuous for `N ≥ 16`. The extras
hypothesis dilutes the peel bound rather than strengthening it.

## Verdict

Three independent reductions — raw sum count, half-Lindström, peel — all
fail to leverage `e ≥ 2`. Each derives `(√2 + o(1)) √N` or worse,
**uniformly in `e`**. The user's strategy ("extras introduce extra
Sidon-uniqueness constraints") is correct in spirit but the constraints
are *exactly* what SAS already provides for sums avoiding `n*`. There is
no extractable second-order gain from `e ≥ 2` in elementary counting.

The converse-of-R4 target appears to require a **structural rigidity
argument** at the strength of:

> "any SAS set with `|P| < |A|` and `|A| > (1 + o(1)) √N` has its
> extras forced into geometric positions that violate SAS via long-range
> sum collisions."

This is exactly the Freiman-style global structural argument that
`direct-combinatorial-attack.md` and `below-sqrt2.md` identify as the
remaining open step. The converse-of-R4 reduction does NOT bypass it.

## Empirical sanity check

All 12 known extremizers in `empirical-invariants-report.md` have
`e = 0`. The "extras graph" is empty. So `e ≥ 2` is the *complementary*
regime, where no extremizers live empirically. The conjecture says the
elementary bound `|A| ≤ 2√N` from `n² ≤ 4N − 4 − e` is not anywhere near
sharp for `e ≥ 2`; the true bound should jump down to `(2/√3) √N`. But
no elementary identity exhibits this jump.

## Constants achieved

| Method | Constant |
|--------|----------|
| Raw sum-count with `e ≥ 2` | `≤ 2 − O(1/√N)` |
| Lindström half-split, any `e` | `≤ √2 + o(1)` |
| Peel argument with `e ≥ 2` | dilutes; vacuous |
| **Target** | `≤ 2/√3 − δ` |
| **Achieved** | `≤ √2 + o(1)` (no improvement from `e ≥ 2`) |

## Where the proof stalls — precise statement

The proof stalls at exactly the same point as the 12 attacks in
`below-sqrt2.md`:

> **Stall point.** Knowing `e ≥ 2` provides no elementary additive,
> multiplicative, or counting identity that distinguishes `A` from a
> Sidon set of size `√(2N) + o(√N)`. Every counting argument either
> ignores `e` (Lindström half-split) or absorbs it into a vacuous
> additive constant (`n² ≤ 4N − 4 − e`).

To make progress, one must additionally invoke a global structural
theorem (Freiman-style) that constrains the **positions** of extras in
`[1, N]` — a non-elementary fact equivalent to the full conjecture.

## Lean formalization status

We do not formalize the negative-result lemma `n² ≤ 4N − 4 − e` because
it does not advance the target bound, and the existing `r1_general` bound
in `Rigidity.lean` already subsumes the relevant counting.

The R4 theorem in `Rigidity.lean` (theorem
`r4_full_reflection_under_max_multiplicity`) remains the strongest formal
result in this direction. The converse remains open and equivalent to the
full `#864` conjecture for the strong almost-Sidon notion.

## Tracking

- Status: **closed-negative** (13th attack on the SAS `√2` barrier).
- Constant achieved: unchanged `√2 √N`.
- Salvage: confirms `e = 0` (full reflection) is the *only* obstruction
  separating SAS extremizers from EF, and quantifies that any non-EF SAS
  set has `|A|² ≤ 4N − 6`.
