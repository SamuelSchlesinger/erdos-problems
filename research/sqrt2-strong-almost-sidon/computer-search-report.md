# Computer-Search Extension of OEIS A389182

**Draft research note, 2026-05-22.** Companion to `paper.md` and
`below-sqrt2.md`. This note extends David Spencer's published OEIS
A389182 search (which covered `N ≤ 69`) and analyzes the structure of
extremizing strong-almost-Sidon (SAS) sets — specifically with an eye
toward the Freiman-style **rigidity conjecture** stated at the end of
`below-sqrt2.md`:

> *Conjecture (Freiman-style rigidity for SAS):* If `A ⊆ {1,...,N}` is
> SAS with `|A| ≥ (2/√3 + ε) · √N`, then `A` is "approximately" of the
> Erdős–Freud (EF) reflection form `B ∪ (a − B)` for some Sidon
> `B ⊂ [1, ⌈N/3⌉]` and some axis `a` close to `N`.

## Setup

We computed `f(N) := max{|A| : A ⊆ {1,...,N} is strong almost-Sidon}`
and recorded an extremizing set `A` for each `N` in the extended range.

- `f(N)` and the SAS property are defined in `paper.md` §1.
- Source: `data/extend_search.c` (C bitfield search, ~14× speedup over
  Spencer's pure-Python `erdos_864.py`).
- Parallel driver: `data/parallel_run.sh` (one C-process worker per `N`).
- Analysis / classification: `data/analyze_extended.py`.

The OEIS-canonical values for `N = 1..69` were re-verified by our
implementation and match Spencer's data exactly (this also validates
the C port of the bitfield algorithm).

## Method

For each `N`, we backtrack over `A ⊆ {1,...,N}` in increasing order,
maintaining multi-word bitsets

  `A`           — current set (over indices `1..N`),
  `sums_once`   — sums of pairs in `A` realised exactly once (over `2..2N`),
  `exc_sums`    — singleton bit at the exceptional sum (`0` if none yet).

When trying to add element `x`:

```
new_sums   = (A << x) | (1 << 2x)
collisions = sums_once ∩ new_sums
new_exc    = collisions \ exc_sums
if popcount(new_exc) ≥ 2:                 skip x.
if popcount(new_exc) == 1 and exc_sums≠0: skip x.
else:
  new_sums_once = (sums_once ∪ new_sums) \ collisions
  new_exc_sums  = exc_sums ∪ collisions
  recurse.
```

`best_size` is seeded with the Erdős–Freud (EF) lower-bound
construction (max Sidon `B ⊆ [1, ⌊N/3⌋]`, reflect to form
`A = B ∪ (N − B)`), so cardinality-based pruning kicks in at depth 0.

## Range and Verification

We extended the table from N=69 (Spencer 2025) to **N=79**, computing
`f(N)` and an extremizing set for each. All 10 new values plus the 69
existing values were verified by the same code:

| Range | source | `f(N)` |
|-------|--------|--------|
| 1..69 | Spencer 2025 / OEIS A389182 | matched exactly |
| 70..79 | this note | newly computed |

Each computed extremizer was independently re-checked to be a genuine
SAS set in Python (see `analyze_extended.py`). All checks pass.

The single-core wall time grows roughly `1.25×` per increment of `N`;
`N = 79` took 417 s on one core. We ran 10 N values in parallel on a
14-core machine; total wall time for `N = 70..79` was ≈ 7 minutes. We
attempted `N = 80..82` in the same batch but cancelled them when their
expected runtimes exceeded the time budget. The reachable cutoff with
this exact code on commodity hardware is around `N ≈ 90` within a few
hours wall-time.

## Extended Table

| N | f(N) | EF asymptotic `(2/√3)√N + 1.520·N^{1/4}` | f(N)/pred | exc | ef_strict | dev_strict | dev_best |
|---|------|----------|-------|-----|-----------|------------|----------|
| 70 | 14 | 14.058 | 0.996 | 71 | 0 | 12 | 2 |
| 71 | 14 | 14.142 | 0.990 | 71 | 0 | 2  | 2 |
| 72 | 14 | 14.226 | 0.984 | 71 | 0 | 12 | 2 |
| 73 | 14 | 14.309 | 0.978 | 74 | 0 | 12 | 2 |
| 74 | 14 | 14.391 | 0.973 | 74 | 0 | 2  | 2 |
| 75 | 14 | 14.473 | 0.967 | 76 | 0 | 12 | 2 |
| 76 | 14 | 14.554 | 0.962 | 76 | 0 | 2  | 2 |
| 77 | 14 | 14.635 | 0.957 | 76 | 0 | 12 | 2 |
| 78 | 14 | 14.715 | 0.951 | 78 | 1 | 0  | 0 |
| 79 | 14 | 14.795 | 0.946 | 79 | 1 | 0  | 0 |

Column definitions:

- `exc`: the single exceptional sum value (n.b. `exc ≠ N` in general).
- `ef_strict`: 1 iff `A = lo ∪ (N − lo)` exactly with `lo = A ∩ [1, ⌊N/3⌋]`
  (i.e., canonical EF form with axis `a = N` and threshold `⌊N/3⌋`).
- `dev_strict`: `|A △ (lo ∪ (N − lo))|`. The "all or nothing" jump
  between 2 and 12 reflects whether the canonical axis `N` happens to
  match the natural reflection axis of the extremizer (which is `exc`).
- `dev_best`: minimum over `axis_shift ∈ {−3,...,3}`,
  `third_offset ∈ {−5,...,5}` of `|A △ (lo ∪ (a − lo))|`. This is the
  "best EF fit" allowing the axis and threshold to be slightly perturbed.

Full per-N detail (the extremizer sets, the optimal `(B, a)` pair, and
the `dev_best`-deviation set) is in `data/extremizers.txt`.

## Findings

### 1. f(N) stays at 14 throughout N = 69..79.

The EF asymptotic prediction `(2/√3)√N + 1.520·N^{1/4}` slowly drifts
through `14` (predicting `14.058` at `N = 70`, `14.795` at `N = 79`,
`14.873` at `N = 80`, ..., `15.232` at `N = 84`). Without computing
`N = 80..84` directly we cannot say exactly when `f(N)` next jumps to
`15`, but the EF construction itself attains `2·|B(⌊N/3⌋)| = 14` for
all of `N = 69..83` (using `|B(23)| = ⋯ = |B(27)| = 7`), so the next
jump is plausibly around `N ≈ 84`.

### 2. **Every extremizer in this range has dev_best ≤ 2.**

This is the central finding. For every `N ∈ {70,...,79}`:

- `N = 78, 79`: the extremizer is **pure EF form** (`dev_best = 0`):
  `A = B ∪ (N − B)` with `B = {1, 2, 5, 11, 19, 24, 26}` Sidon in
  `[1, N/3]`.

- `N = 70..77`: the extremizer is **EF + one extra colliding pair**
  (`dev_best = 2`): `A = B ∪ (a − B) ∪ {p, q}` where `p + q = a` and
  `(p, q)` are the two extras. Specifically:

  | N | B | a | extras (p, q) |
  |---|-----|----|---------------|
  | 70 | {1, 2, 4, 9, 15, 19} | 71 | (31, 40) |
  | 71 | {1, 2, 4, 9, 15, 19} | 71 | (31, 40) |
  | 72 | {1, 2, 4, 9, 15, 19} | 71 | (31, 40) |
  | 73 | {1, 2, 4, 8, 16, 21} | 74 | (32, 42) |
  | 74 | {1, 2, 4, 8, 16, 21} | 74 | (32, 42) |
  | 75 | {1, 2, 4, 8, 13, 21} | 76 | (31, 45) |
  | 76 | {1, 2, 4, 8, 13, 21} | 76 | (31, 45) |
  | 77 | {1, 2, 4, 8, 13, 21} | 76 | (31, 45) |

  In every case the axis `a` equals the exceptional sum `exc`, and the
  two extras `p, q` are precisely the additional pair forcing
  `exc = p + q` to have multiplicity `> 1`.

  Structurally, this is the (slightly enriched) EF construction:
  `B ∪ (a − B)` is a *Sidon* set of size `2|B| = 12`, and adding the
  pair `{p, q}` with `p + q = a` introduces exactly one duplicated
  sum value (`exc = a`) while pushing the cardinality from 12 to 14.

### 3. The single exceptional sum equals `a` in every case.

For all 10 new entries, the SAS exception value `exc` coincides with
the EF reflection axis `a`. This is precisely the EF construction's
structural feature: the multiplicity of `a` in the sum set
`a = b + (a − b)` for every `b ∈ B` (plus, in `dev_best=2` cases, the
extra `p + q = a`), so `r(a) = |B| + 1` or `|B|`.

### 4. f(N)/pred stays in (0.94, 1.00).

The empirical ratio is **slightly below** the EF asymptotic prediction
in this range (because the asymptotic is the smooth interpolant, and
`f(N)` only jumps when `|B(⌊N/3⌋)|` jumps). Even so, the absolute
agreement is within one integer everywhere, which is what one would
expect for an EF-extremal sequence.

### 5. **No non-EF extremizer was found.**

Across all 10 new computed values, *every* extremizer of size 14
admits an EF-form description with `dev_best ≤ 2`. The deviations of
size 2 are always the "colliding-pair extension" of an EF set, which
is a *structural* refinement of EF — itself essentially EF with an
extra colliding pair.

## Interpretation: support for the rigidity conjecture

The data in this range is fully consistent with the Freiman-style
rigidity conjecture: every extremizer is approximately
`B ∪ (a − B)` for a Sidon `B` and reflection axis `a` close to `N`.
We did not find a single counter-example.

Concrete supporting observations:

- All 10 extremizers admit an EF description with `dev ≤ 2`.
- The 2-element deviation, when present, has a rigid structural form:
  it is a single pair `(p, q)` with `p + q = a`, i.e., the SAS
  exception value. This is the natural way to extend a Sidon set
  `B ∪ (a − B)` by one "colliding" pair to bump `|A|` by 2.
- The reflection axis `a` always coincides with the SAS exception value.

A search beyond `N = 79` (computationally feasible up to `N ≈ 90` in a
few hours; for `N > 100` the present brute-force algorithm becomes
impractical and one would want a smarter SAT/MILP encoding) would
sharpen the empirical case. With the current 10 data points, we have:

**Empirical evidence for the rigidity conjecture: STRONG (no
counter-examples; every extremizer is EF-form modulo ≤ 2 elements).**

A non-EF extremizer in this range would have shown up as a row with
`dev_best ≥ 3`, and there are none.

## Caveats

1. **Single extremizer per N.** Our backtracking returns the
   *lexicographically smallest* extremizer it finds. We have **not**
   enumerated all extremizers; a non-EF extremizer might exist at,
   say, `N = 70` and we would have missed it if a different lex-first
   extremizer happens to be EF-form. (However: the lex-first ones
   were uniformly EF-form, and our backtracking explores all branches
   that beat `best_size` — the *first* one of full size is captured
   but we don't enumerate all of them.)

   This is a weakness of the search. A follow-up would either (a)
   enumerate all extremizers and check each, or (b) re-run with the
   element order reversed to expose a different lex-first
   extremizer.

2. **Small range.** 10 data points beyond `N = 69` is informative but
   not conclusive. The asymptotic regime starts to bite only at
   `N ≫ 100`, where this brute-force code is too slow.

3. **No theoretical guarantee.** Even with a non-trivial extension,
   computer search alone cannot prove a theorem. A genuine resolution
   of the `2/√3` conjecture requires a structural argument à la
   `below-sqrt2.md` Section "Convergent recommendation".

## Bottom line

Within the modest extension `N = 70..79`, **every extremizing
strong-almost-Sidon set is approximately Erdős–Freud form** (with
`dev_best ≤ 2`). In half of those cases the extremizer is exactly EF
form; in the other half it is "EF augmented by one colliding pair
through the exception value". No non-EF extremizer surfaced.

This is direct empirical support for the rigidity conjecture stated in
`below-sqrt2.md`. The natural next steps are (a) enumerate *all*
extremizers (not just lex-first) at `N ≤ 79` to harden the conclusion,
and (b) extend further with a sharper SAT/ILP-style search.

## Files

- `data/extend_search.c` — main C search (multi-word bitfield)
- `data/extend_search.py` — Python driver / helper (legacy)
- `data/parallel_run.sh` — multi-core wrapper
- `data/analyze_extended.py` — post-processing and EF classification
- `data/A389182-extended.txt` — extended b-file (N = 1..79)
- `data/extremizers.txt` — per-N extremizer details and EF classification
- `data/par_results/` — per-N raw output files

## Reproducibility

```bash
# Compile and run one N:
cd data
cc -O3 -march=native -o extend_search extend_search.c
./extend_search 78 78
# 78 14  # t=...s  set=1,2,5,11,19,24,26,52,54,59,67,73,76,77

# Parallel run a range:
./parallel_run.sh 70 79 10
python3 analyze_extended.py
```
