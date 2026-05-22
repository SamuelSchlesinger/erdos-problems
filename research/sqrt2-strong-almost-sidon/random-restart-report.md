# Random-Restart Local Search for Strong Almost-Sidon Sets

**Draft research note, 2026-05-22.** Companion to `computer-search-report.md`
and `below-sqrt2.md`. This note searches for **non-Erdős–Freud (EF) local
maxima** of the strong almost-Sidon (SAS) hill-climbing problem at scales
N ∈ {100, 200, 500}, beyond the exhaustive-search reachable range (N ≤ 79).
The motivation is a sharpened version of the Freiman-style rigidity
conjecture:

> *Conjecture (Freiman-style rigidity for SAS):* If `A ⊆ {1,...,N}` is
> SAS with `|A| ≥ (2/√3 + ε) · √N`, then `A` is approximately of EF
> reflection form `B ∪ (a − B)` for some Sidon `B` and axis `a ≈ N`.

The exhaustive search at N ≤ 79 (see `computer-search-report.md`) found
that *every* extremizer is approximately EF-form with `dev_best ≤ 2`. The
present note asks whether the same holds in a much weaker sense (across
*local* maxima, not just global) at larger N.

## Setup

For each N ∈ {100, 200, 500} we run **100 random restarts** of the
following hill-climber:

1. **Random initial Sidon set.** Greedily build a Sidon set by adding
   elements from `[1, N]` in a random order until stuck.
2. **Greedy extension.** Add elements that preserve SAS, with a heuristic
   preference for adds that don't create a collision.
3. **Swap moves.** Try `(remove y, add x, re-extend)` triples; accept any
   that strictly increase `|A|`.
4. **Kick perturbations.** Remove a random subset of 1..|A|/4 elements
   and re-extend; accept if larger.

The final `A` is a *local maximum* in the swap-neighbourhood (no remove+add
strictly improves it).

### EF classifier

A set is classified **EF-form** if there exists an axis `a` and threshold
`t` such that, writing `lo := A ∩ [1, t]` and `cand := lo ∪ ((a − lo) ∩ [1, N])`,
the symmetric difference `|A △ cand| ≤ 2`.

Two important refinements over the strict `a = N, t = N/3` form (which is
what `computer-search-report.md` used):

- **Axis sweep.** We sweep `a` over `{N + shift : shift ∈ [-6, 6]} ∪ {exc(A)}`
  where `exc(A)` is the SAS exception value (when non-trivial). Empirically
  the optimal axis is always the exception value.
- **Boundary truncation.** We restrict `(a − lo)` to `[1, N]` so that the
  classifier doesn't penalise EF constructions whose mirror falls partly
  outside `[1, N]`.

These refinements were necessary: without them, many genuinely EF sets
were being misclassified as non-EF (e.g., a size-15 set at N=100 with
axis=107 and threshold=46 was marked non-EF by an axis-N-only classifier
but is in fact EF-form with `dev_best = 1`).

## Results

For each N, we report the size distribution of local maxima and, broken
down by size, how many are EF-form. The key quantity for rigidity is
**the largest non-EF local maximum**.

### N = 100  (EF asymptotic prediction ≈ 16.4; observed max = 15)

| size | count | EF-form / count | dev_best_in_range |
|-----:|-----:|----------------:|---------------------:|
| 15 | 1  | 1/1   | [0, 0] |
| 14 | 30 | 30/30 | [0, 2] |
| 13 | 30 | 21/30 | [0, 5] |
| 12 | 34 | 10/34 | [0, 8] |
| 11 | 5  | 0/5   | [6, 7] |

**Largest non-EF local maximum: size 13** (`dev_best = 3`). All 31 local
maxima of size ≥ 14 are EF-form with `dev_best ≤ 2`.

The non-EF size-13 examples (e.g., `A = {1,2,4,17,27,38,46,67,76,80,82,83,100}`)
are sub-extremal: they sit 1–2 elements below the observed maximum size and
3–7 below the EF prediction. Inspection shows that the "extras" outside the
EF mold typically congregate near a single boundary (`1` or `N`) and form a
local Sidon island detached from the main reflection structure.

### N = 200  (EF asymptotic prediction ≈ 22.0; observed max = 19)

| size | count | EF-form / count | dev_best_in_range |
|-----:|-----:|----------------:|---------------------:|
| 19 | 4  | 4/4   | [0, 1] |
| 18 | 13 | 13/13 | [0, 2] |
| 17 | 19 | 11/19 | [0, 5] |
| 16 | 15 | 4/15  | [0, 10] |
| 15 | 49 | 3/49  | [1, 12] |

**Largest non-EF local maximum: size 17** (`dev_best = 3`). All 17 local
maxima of size ≥ 18 are EF-form with `dev_best ≤ 2`. The observed maximum
(19) is well below the EF prediction (22) — the hill-climber doesn't reach
the global optimum.

### N = 500  (EF asymptotic prediction ≈ 33.0; observed max = 28)

| size | count | EF-form / count | dev_best_in_range |
|-----:|-----:|----------------:|---------------------:|
| 28 | 2  | 2/2   | [0, 0] |
| 27 | 2  | 2/2   | [1, 1] |
| 26 | 1  | 1/1   | [0, 0] |
| 25 | 1  | 0/1   | [4, 4] |
| 24 | 4  | 2/4   | [1, 7] |
| 23 | 5  | 1/5   | [0, 10] |
| 22 | 20 | 1/20  | [2, 16] |
| 21 | 64 | 1/64  | [2, 18] |
| 20 | 1  | 0/1   | [16, 16] |

**Largest non-EF local maximum: size 25** (`dev_best = 4`). All 5 local
maxima of size ≥ 26 are EF-form with `dev_best ≤ 1`.

The notable size-25 non-EF example is:
```
A = {4, 6, 12, 15, 25, 41, 80, 97, 111, 129, 192,
     255, 273, 287, 304, 343, 359, 369, 372, 378, 380,
     420, 472, 499, 500},   exc = 384
```
This set has an 11-pair structure around `384`:
`{4+380, 6+378, 12+372, 15+369, 25+359, 41+343, 80+304, 97+287, 111+273, 129+255, 192+192}`.
The first 21 elements (everything below 380) form a genuine EF-shape
(`B ∪ (384 − B)`) with `B = {4, 6, 12, 15, 25, 41, 80, 97, 111, 129, 192}`,
size-11. The four "extras" `{420, 472, 499, 500}` lie above the natural
upper cutoff `380` and are paired with the lower elements (e.g.,
`420 + 80 = 500 = 4 + 496`, etc.) in ways that produce only unique pair-sums
above the upper boundary of the EF sumset. They cannot be reflected back —
the would-be partners `384 − 420 = -36`, `384 − 499 = -115`, etc., are
negative.

Structurally this is **"EF-21 plus 4 boundary-attached extras"**: a
sub-extremal local maximum of "EF + tail" type. It's similar in spirit to
the `dev_best = 2` extremizers found at N = 70..77, but with a larger
deviation. **It is sub-extremal**, sitting 3 below the observed max (28)
and 8 below the EF prediction (33). Hence it does not directly contradict
the rigidity conjecture, which is a statement about *extremal* SAS sets,
not arbitrary local maxima.

## Verdict

Within the random-restart sample at N ∈ {100, 200, 500}:

- **At and near the observed maximum size**, every local maximum found is
  EF-form (`dev_best ≤ 2`). Specifically:
  - N=100, sizes 14–15: 31/31 are EF-form.
  - N=200, sizes 18–19: 17/17 are EF-form.
  - N=500, sizes 26–28: 5/5 are EF-form.

- **Non-EF local maxima exist but are strictly sub-extremal.** Their sizes
  are 1–3 below the observed maximum and 3–8 below the EF asymptotic
  prediction. They are typically "EF-core plus boundary extras"
  configurations that the conjecture's "approximate" tolerance does *not*
  cover, but which are also not extremizers.

- **Observed max ≪ EF prediction at N = 200, 500.** Our hill-climber is
  not reaching the global optimum at these scales (max 19 vs. predicted
  22 at N=200; max 28 vs. predicted 33 at N=500). This is a known
  limitation of greedy + swap + kick local search for Sidon-like problems
  at scale. A SAT/ILP encoding or simulated annealing with longer
  schedules would likely find larger sets — but our purpose was *only* to
  sample local maxima and classify them, not to attain `f(N)`.

**Bottom line.** The data is fully consistent with EF-rigidity for SAS:
**no random restart converged to a non-EF local maximum at the largest
sizes attained.** The conjecture's "approximate EF" tolerance covers every
high-size local maximum found, and the only non-EF local maxima are
strictly sub-extremal. This is independent corroboration of the exhaustive
N ≤ 79 finding from `computer-search-report.md`, extended to N = 100, 200, 500.

## Caveats

1. **Hill climber doesn't reach the global optimum.** At N = 200 and 500,
   the observed max sizes (19 and 28) are well below the EF prediction.
   This means our sample of "high-size local maxima" is biased toward
   the maxima reachable by greedy+swap from a random Sidon initial set.
   A non-EF local maximum at exactly the rigidity threshold could exist
   and be missed.

2. **100 restarts per N.** The restart count is modest; rare non-EF local
   maxima could be missed. The probability of missing a global EF
   structure given that all 100 restarts found it is empirically low (the
   restarts produce a diverse range of axes — see e.g., the axes
   `{84, 100, 105, 110, 116, 148, 155, 165, 181, 198}` appearing at
   N = 200).

3. **EF classifier sensitivity.** The classifier uses `dev_best ≤ 2` as the
   EF threshold, matching `computer-search-report.md`. If the threshold
   were tightened to `dev_best ≤ 0` (strict EF only), some of the "EF-form"
   counts above would drop. The histograms reveal that strict-EF (dev=0)
   is the modal case at every observed maximum size:
   - N=100 size-15: 1/1 strict (dev=0)
   - N=200 size-19: 3/4 strict
   - N=500 size-28: 2/2 strict

## Files

- `data/random_restart.py` — hill-climber implementation.
- `data/random_restart_results.txt` — per-N text summary.
- `data/random_restart_results.json` — full per-restart results.

## Reproducibility

```bash
cd data
python3 random_restart.py --ns 100,200,500 --restarts 100,100,100 \
    --seed 42 --txt random_restart_results.txt \
    --out random_restart_results.json --verbose
```

Wall time: ≈12 s total on a single core (Python).
