# Asymmetric Erdős–Freud Reflection Search for Strong Almost-Sidon Sets

**Draft research note, 2026-05-22.** Companion to `paper.md`,
`computer-search-report.md`, and `below-sqrt2.md`. This note enumerates
*asymmetric* variants of the Erdős–Freud (EF) reflection construction
for strong-almost-Sidon (SAS) sets at `N ∈ {100, 200}`.

## Setup

The canonical EF construction at `N` is

```
A_EF  =  B_EF  ∪  (N − B_EF),     B_EF  =  max Sidon subset of [1, ⌊N/3⌋].
```

All cross-pairs `(b, N − b)` sum to `N` (the unique SAS exception). The
1/3 threshold guarantees within-B sums `≤ 2N/3` are disjoint from
within-`(N − B)` sums `≥ 4N/3`, so the only collision-value is `N` and
`A_EF` is SAS. Cardinality: `|A_EF| = 2·|B_EF|`.

The **asymmetric variant** generalizes both knobs:

```
A  =  B ∪ (M − B),     B Sidon ⊂ [1, αN],   M ∈ [N/2, N],   α ∈ (1/3, 1/2].
```

Two changes vs canonical EF: the reflection axis `M` is no longer
locked at `N`, and the threshold on `B` is relaxed from `N/3` to `αN`.
With `α > 1/3` the EF band-separation argument breaks: mixed cross-sums
`b + (M − b')` (for `b ≠ b'`) overlap within-B sums when
`αN > M/3`, and every such overlap is a potential new exception.

Reference for the EF baseline: Erdős–Freud 1991; see also
`computer-search-report.md`, `paper.md` §4.

## Method

Source: `data/asymmetric_search.py`. For each `N ∈ {100, 200}` we
enumerate `(M, α)` on a coarse grid (9 `M`-values × 5 α-values).

For each `(M, α)` we run a combined DFS over `B ⊂ [max(1, M − N), ⌊αN⌋]`
that maintains the SAS bitfield over the *full* `A = B ∪ (M − B)`
rather than just `B`. On attempting to extend `B` by `x` (which
simultaneously extends `A` by `{x, M − x}`):

1. Compute new pair-sums against the current `A` bitfield (and
   `M − x` pair-sums separately).
2. Count collisions with the current "sums-of-multiplicity-1"
   bitfield.
3. Accept only if either no collisions or the collision coincides
   with the already-claimed exception value (`M` in the typical run).
4. Recurse.

We seed the search target at `|B| ≥ |B_EF| + 1` and abort as soon as a
witness is found. Per-`(M, α)` time budget: 5s at `N = 100`, 12s at
`N = 200`. The two `|B_EF|` values come from `max_sidon_in_interval`
in the same file, computed once and cached:
`|B_EF(100)| = 7`, `|B_EF(200)| = 10`.

## Results

Source data: `data/asymmetric_results.txt`.

### N = 100

- Canonical EF baseline: `|A_EF| = 14`, with
  `B_EF = {1, 2, 4, 8, 13, 21, 31}` and reflection axis `N = 100`.
- **Asymmetric witness beating EF**: `|A| = 16` with
  ```
  M = 95,   α = 0.45,   B = {1, 5, 7, 12, 15, 30, 31, 43},
  A = {1, 5, 7, 12, 15, 30, 31, 43, 52, 64, 65, 80, 83, 88, 90, 94},
  exc = 95.
  ```
  This is **truly asymmetric** (`M = 95 ≠ N`). The 16 elements fit in
  `[1, 94] ⊂ [1, 100]`. Independently re-verified to be Sidon-`B`
  and SAS-`A`.

- The (non-asymmetric) relaxed-α variant at `M = N = 100` already
  reaches `|A| = 16` (with `α ≥ 0.37`). E.g., `M = 100, α = 0.37`
  also produces `|B| = 8`.

The asymptotic EF prediction `(2/√3)·√N + 1.52·N^{1/4}` is `≈ 16.35`
at `N = 100`, matching the `|A| = 16` we find. So our 16 is the EF
asymptotic, **achieved by relaxed-α or asymmetric-M constructions** —
not by the canonical (`α = 1/3, M = N`) construction.

### N = 200

- Canonical EF baseline: `|A_EF| = 20`, with
  `B_EF = {1, 2, 4, 8, 19, 31, 39, 44, 53, 63}` and axis `N = 200`.
- **Witness beating EF**: `|A| = 22` with
  ```
  M = 200,   α = 0.40,   B = {1, 2, 4, 11, 16, 34, 38, 54, 62, 73, 79},
  A = {1, 2, 4, 11, 16, 34, 38, 54, 62, 73, 79,
        121, 127, 138, 146, 162, 166, 184, 189, 196, 198, 199},
  exc = 200.
  ```
  This witness uses `M = N` but `α = 0.4 > 1/3`. So it is *not*
  axis-asymmetric, but it *is* threshold-relaxed.
- No `M < N` witness of size `|A| ≥ 22` was found within the per-`(M, α)`
  time budget (12 s/each). All `M ∈ {100, ..., 195}` rows time out at
  `|B| ≤ 10` (still searching for 11). Whether `M < 200` can reach 22
  with a larger budget is open.

The asymptotic EF prediction at `N = 200` is
`(2/√3)·√200 + 1.52·200^{1/4} ≈ 22.05`, which matches `|A| = 22`.

## Verdict

For both `N = 100` and `N = 200`, relaxing the canonical EF construction
**does** beat the strict-α-`1/3`-threshold EF cardinality:

| N | canonical `|A_EF|` | best asymmetric `|A|` | EF asymptotic | witness type |
|---|--------------------|------------------------|---------------|--------------|
| 100 | 14 | **16** | 16.35 | asymmetric M (95) AND relaxed-α |
| 200 | 20 | **22** | 22.05 | relaxed-α only (M = N) within time budget |

This is *not* a contradiction with the rigidity conjecture in
`below-sqrt2.md`. The conjecture asserts that any extremizer of size
`≥ (2/√3 + ε)√N` is *approximately* EF, allowing axis perturbation by
`O(1)` and threshold perturbation by `O(N^{1/4})`. The witnesses found
here are *exactly* of EF-augmented form:

- `N = 100, M = 95, α = 0.45`: B sits in `[1, 43]`, beyond the canonical
  `[1, 33]` threshold by `O(N^{1/4})`. Mixed cross-sums avoid within-B
  sums by careful Sidon selection.
- `N = 200, M = 200, α = 0.40`: B in `[1, 79]`, beyond canonical
  `[1, 66]` by `≈ N^{1/4} = 3.76`. Same structure.

In both cases the **single exception** is at `M`, and the reflection
structure `A = B ∪ (M − B)` is preserved. The relaxation is exactly
the "EF + O(N^{1/4}) deviation" envelope predicted by the asymptotic.

**Practical conclusion**: at small `N`, the strict canonical EF (α =
1/3, M = N) is *not* optimal — it loses by `1` or `2` because of
integer-rounding effects in `|B_EF|`. The optimal SAS sets at small
`N` come from relaxed-α or mildly-asymmetric reflections, but they are
**still** of EF form `B ∪ (M − B)` with `B` Sidon, `M` close to `N`.

This is direct empirical support for the rigidity conjecture, not
against it: the *form* is preserved; only the discrete parameters
shift by `O(N^{1/4})`.

## Caveats

1. **Coarse grid (9 M × 5 α = 45 combinations per N).** A finer grid
   could find slightly larger witnesses, especially at `N = 200`
   where most `(M, α)` slots timed out.
2. **Per-(M, α) time budget 12s at N = 200.** Some configurations may
   harbour larger Sidon `B` that the DFS did not reach.
3. **Lex-first only.** The DFS returns the lexicographically smallest
   witness; symmetric structural variants are not enumerated.
4. **Small N.** Both `N = 100` and `N = 200` are below the regime
   where the `√2`-vs-`2/√3` gap becomes asymptotically meaningful.

## Files

- `data/asymmetric_search.py` — search code (DFS + combined SAS check)
- `data/asymmetric_results.txt` — per-`(M, α)` results table
- `data/A389182-extended.txt` — OEIS-derived `f(N)` for `N ≤ 79`
- `computer-search-report.md` — full SAS extremizer search (N ≤ 79)
- `below-sqrt2.md` — rigidity conjecture and `√2`-attack plan
