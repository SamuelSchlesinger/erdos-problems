# Empirical Structural Invariants of SAS Extremizers

**Date:** 2026-05-22
**Companion to:** `computer-search-report.md`, `paper.md`, `below-sqrt2.md`,
`Erdos/AlmostSidonSets/Rigidity.lean`.

## Setup

We re-examine the 12 known extremizing strong-almost-Sidon (SAS) sets:

- N = 70..79 (10 sets, from exhaustive bitfield search; sizes 14).
- N = 100, 200 (2 sets, from asymmetric Erdős–Freud search; sizes 16, 22).

For each extremizer A we compute the structural invariants below
(see `data/analyze_invariants.py`). The motivating question is to identify
**rigidity properties beyond R1 (3-multiplicity at exception) and R2
(extreme-pair sums to exception axis)** that hold across every known
extremizer.

## Computed invariants (per N)

| N | \|A\| | m | M | n* | r(n*) | m+M | R2 | sym | ef_dev |
|---|------|---|---|----|-------|-----|----|----|-------|
| 70 | 14 | 1 | 70 | 71 | 7 | 71 | Y | 14/14 | 0 |
| 71 | 14 | 1 | 70 | 71 | 7 | 71 | Y | 14/14 | 0 |
| 72 | 14 | 1 | 70 | 71 | 7 | 71 | Y | 14/14 | 0 |
| 73 | 14 | 1 | 73 | 74 | 7 | 74 | Y | 14/14 | 0 |
| 74 | 14 | 1 | 73 | 74 | 7 | 74 | Y | 14/14 | 0 |
| 75 | 14 | 1 | 75 | 76 | 7 | 76 | Y | 14/14 | 0 |
| 76 | 14 | 1 | 75 | 76 | 7 | 76 | Y | 14/14 | 0 |
| 77 | 14 | 1 | 75 | 76 | 7 | 76 | Y | 14/14 | 0 |
| 78 | 14 | 1 | 77 | 78 | 7 | 78 | Y | 14/14 | 0 |
| 79 | 14 | 1 | 78 | 79 | 7 | 79 | Y | 14/14 | 0 |
| 100 | 16 | 1 | 94 | 95 | 8 | 95 | Y | 16/16 | 0 |
| 200 | 22 | 1 | 199 | 200 | 11 | 200 | Y | 22/22 | 0 |

`sym` is the count of elements `a ∈ A` such that `n* − a ∈ A` (out of |A|).
`ef_dev` is the symmetric difference `|A △ (B ∪ (n* − B))|` for the greedy
maximal Sidon subset `B ⊆ A ∩ [1, n*/2]`.

## Top empirical invariants

Across all 12 extremizers:

### (1) **Full reflection symmetry: `a ∈ A ⟺ n* − a ∈ A`** — 12/12 (100%)

Every extremizer is closed under the involution `a ↦ n* − a`. In particular
`r(n*) = |A| / 2` — every element pairs with another via the exception axis.

This is the strongest invariant we observe and is the structural content of
the Erdős–Freud (EF) construction.

### (2) **Perfect pair structure: `|A| = 2 r(n*)`** — 12/12 (100%)

Equivalent reformulation of (1): the exception sum value `n*` has multiplicity
exactly `|A|/2`. In other words, `A` decomposes uniquely into `|A|/2`
reflection-pairs through `n*`.

This refines R1 (`r(n*) ≥ 3`) to an *exact* equation for extremizers.

### (3) **`m = 1`** — 12/12 (100%) and **`gap_min = 1`** — 12/12 (100%)

Every extremizer contains 1 (in particular both `1` and `2` for 10/12 of them,
giving `a_2 − a_1 = 1`). This is a "minimum element saturation" property:
the EF construction starts with the densest small-integer Sidon-prefix.

### Secondary invariants (provable rigorously from R1+R2)

- **R3 (second-extreme pair, off-axis uniqueness):** `(m, M_2)` and `(m_2, M)`
  are each the unique sorted-pair representation of their sum.
  - **Proof:** Since `M_2 < M`, we have `m + M_2 < m + M = n*`, so
    `m + M_2 ≠ n*` and by SAS-uniqueness `(m, M_2)` is the unique pair.
    Similarly `m_2 + M > m + M = n*`, so `m_2 + M ≠ n*`, and `(m_2, M)`
    is unique. (Verified 12/12.)

- **Asymmetric exception location:** `|n* − N| ≤ 1` — 11/12 (92%).
  The single exception is `n* ∈ {N − 1, N, N + 1}`. (N=200 is the outlier
  where `n* = N`; the N=100 extremizer has `n* = 95 < N`.)

## Conjectured invariants (provable status)

Based on the data, we conjecture two structural rigidity properties:

### Conjecture S (Full Reflection Symmetry — STRONG):

> For every SAS-extremizer A with exception value `n*`, A is closed under
> the reflection `a ↦ n* − a`, and `r(n*) = |A|/2`.

**Provability status:** Plausibly provable from a sharpened anchor-counting
argument that combines R2 with the SAS-uniqueness constraint:

- **Step 1 (R2 + base):** `m + M = n*`. So `(m, M)` is a reflection pair.
- **Step 2 (R3, proved above):** `(m, M_2)`, `(m_2, M)` are unique pair-sums.
- **Step 3 (sketch, not yet rigorously proven):** Iteratively, the unique
  pair-sums `m + a_k` for `a_k ∈ A` produce `|A|` distinct sum-values, all
  ≤ `m + M = n*`. By a parallel argument from the top (`M + a_k`),
  `|A|` distinct sum-values ≥ `n*`. Counting: `|A + A| ≥ 2|A| - 1`, with
  the extra collision at `n*`. To force reflection, one needs to show
  each `a_k + M` collides with the corresponding `m + a_{|A| - k + 1}`,
  which is exactly the EF reflection identity.

### Conjecture P (provable from R2): `r(n*) ≥ 3` for all SAS-extremizers with `|A| ≥ ⌈2/√3 · √N⌉`.

This is **already proved as R1**.

### Conjecture A (provable, weaker form): `(m, M)`, `(m_2, M)` represent two distinct sum-values

Yes — they obviously do (`m + M ≠ m_2 + M` since `m ≠ m_2`).
Stronger: among the `|A|` sums `{m + a : a ∈ A}`, all `|A|` are distinct (true
by injectivity of `a ↦ m + a`), and all are < `m + M = n*`, EXCEPT for the
extreme one `m + M = n*` itself.

Combined with the analogue from `M + a`, we get `2|A| − 1` distinct sum-values
(after merging the two anchor sums at `m + M = n*`). This is the standard
`|A + A| ≥ 2|A| − 1` from anchor-pair counting.

## New formalizable lemma (R3)

We extract one clean rigorous theorem from the analysis above. It strengthens
R2 by identifying additional unique sorted-pair representations.

**R3 (Off-axis uniqueness for second-extreme pairs).**
Let `A` be a SAS set with `|A| ≥ 3`, exception value `n*`, and `m + M = n*`
(where `m = min A`, `M = max A`). Let `M_2 = max(A \ {M})` be the second-largest.
Then `(m, M_2)` is the unique sorted-pair representation in `A` of the sum
`m + M_2`. Symmetrically with `m_2 = min(A \ {m})`: `(m_2, M)` is the unique
sorted-pair representation of `m_2 + M`.

**Proof.** Since `M_2 < M`, we have `m + M_2 < m + M = n*`, so `m + M_2 ≠ n*`.
The SAS condition allows at most one sum-value with two distinct sorted-pair
representations, and that value is `n*`. So any sum-value `≠ n*` has at most
one sorted-pair representation; in particular `m + M_2` has at most one, which
must be `(m, M_2)`. The other direction is symmetric.  ∎

This is a strict generalization of R2's "uniqueness" branch and clarifies
that the second-extreme pair-sums are *automatically* unique once the
extreme pair sits on the axis.

## What is NOT provable from SAS alone

The full reflection symmetry **does not follow from the SAS axiom alone** —
random non-extremal SAS sets (from `random_restart_results.txt`) systematically
violate it (`dev_best ≥ 3` is common for size `~ 0.85 · |A|_max`). So full
reflection symmetry is a *near-extremality* condition, contingent on the
Freiman-style rigidity conjecture in `below-sqrt2.md`.

## Files

- `data/analyze_invariants.py` — analysis script.
- `empirical-invariants-table.md` — auto-generated per-N table.
- `Erdos/AlmostSidonSets/Rigidity.lean` — formalized R1, R2 (and now R3).
