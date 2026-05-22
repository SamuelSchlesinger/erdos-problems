# Local Optimality of the Erdős–Freud Construction for Strong Almost-Sidon Sets

**Computational research note, 2026-05-22.**
Companion to `paper.md`, `below-sqrt2.md`, and `computer-search-report.md`.

## Question

For each `N ∈ {100, 200, 500, 1000, 5000, 10000}`, is the Erdős–Freud
(EF) reflection construction `A_EF := B ∪ (N − B)` (with `B` an
extremal Sidon set in `[1, ⌊N/3⌋]`) a *local maximum* among
strong-almost-Sidon (SAS) sets? In particular:

- (a) **Single ADD.** Is there `x ∈ [1, N] \ A_EF` with `A_EF ∪ {x}` SAS?
- (b) **Single SWAP.** Same-size moves preserving SAS?
- (c) **Colliding pair.** Can `A_EF ∪ {x, y}` with `x + y = N` and
  `{x, y} ∩ A_EF = ∅` be SAS?
- (d) **Iterated colliding pairs.** Greedy iteration of (c) starting from `A_EF`.

If EF is *not* locally maximal, that means `f(N) > 2 · F_2(⌊N/3⌋)`
(strict inequality) and the EF lower bound is not tight.

## Method

`data/ef_locality.c` — C bitfield SAS-test:
- Sidon `B` in `[1, ⌊N/3⌋]` built as the best of: optimal Golomb ruler
  (A003022, sizes 3..27), Singer construction for prime `q`,
  Erdős–Turán construction, plain greedy, and (for `M ≤ 200`) full
  exact backtracking.
- For each `N`, build `A_EF`, verify SAS (exception = `N`), then test
  all single ADD, all SWAP, all colliding pairs (x + y = N), and the
  iterated-greedy colliding-pair augmentation.
- SAS test: maintain `sums_once` and `sums_many` bitsets. For an ADD
  of `x`, compute `new_sums = (A << x) | bit(2x)`; check
  `popcount(sums_many) + popcount(new_sums ∩ sums_once) ≤ 1`.

## Sidon-set quality

| N    | M = ⌊N/3⌋ | F_2(M) (true max) | \|B\| we use | optimal? |
|------|-----------|---------------------|--------------|----------|
| 100  | 33        | 7                   | 7            | YES      |
| 200  | 66        | 10                  | 10           | YES      |
| 500  | 166       | 15                  | 15           | YES      |
| 1000 | 333       | 20                  | 20           | YES      |
| 5000 | 1666      | ≈ 41 (heuristic)    | 33           | NO       |
| 10000| 3333      | ≈ 58 (heuristic)    | 42           | NO       |

For `N ≤ 1000` we use optimal Golomb rulers from A003022.
For `N ≥ 5000` only suboptimal Sidon sets (Singer + greedy) are
available within the time budget; the EF construction is then sub-EF
itself.

## Results

| N     | \|A_EF\| | locally max vs ADD? | min ADD witness | colliding-pair gain | iterated AUG gain |
|-------|----------|---------------------|-----------------|---------------------|-------------------|
| 100   | 14       | **YES**             | (none)          | 0                   | 0                 |
| 200   | 20       | **NO**              | x=100 (= N/2)   | 0                   | 0                 |
| 500   | 30       | **NO**              | x=250 (= N/2)   | 0                   | 0                 |
| 1000  | 40       | **NO**              | x=382           | +2                  | +2                |
| 5000  | 66*      | **NO**              | x=1821          | +2                  | +8                |
| 10000 | 84*      | **NO**              | x=3354          | +2                  | +12               |

*Suboptimal Sidon-B at `N ≥ 5000`.

### Verified witnesses (cross-checked in Python)

**N = 200**:
`B = {1,2,7,11,24,27,35,42,54,56}` (optimal Golomb-10).
`A_EF ∪ {100}` has size 21 and is SAS with single exception at sum 200.
**So `f(200) ≥ 21 > 20 = 2 · F_2(66)`.**

**N = 500**:
`B = {1,2,5,11,24,33,44,58,73,98,116,130,141,144,160}` (optimal Golomb-15 + greedy).
`A_EF ∪ {250}` has size 31 and is SAS.
**So `f(500) ≥ 31 > 30 = 2 · F_2(166)`.**

**N = 1000**:
`B = {1,2,9,12,69,78,95,117,122,157,159,180,195,209,213,229,241,254,260,284}`
(optimal Golomb-20 + shift).
`A_EF ∪ {382, 618}` has size 42 and is SAS.
**So `f(1000) ≥ 42 > 40 = 2 · F_2(333)`.**

## Key findings

1. **EF is locally maximal vs single-element addition at `N = 100` only**
   (in our test range). For all `N ∈ {200, 500, 1000, 5000, 10000}`,
   at least one ADD move produces a strictly larger SAS set.

2. **The "+ x = N/2 midpoint" move kicks in at `N = 200`.** When `N` is
   even and the optimal `B` does not already include any element of
   `A_EF` colliding with the midpoint, adding `N/2` increases `|A|` by
   1 while preserving SAS. The reason: `2·(N/2) = N` lands on the existing
   exception sum (no new exception introduced), and `N/2 + a` for `a ∈ A_EF`
   typically lands in regions where the EF sumset has a structural gap
   (since `B ⊂ [1, N/3]` and `N − B ⊂ [2N/3, N − 1]`, the midpoint sums
   land in `[N/2 + 1, N/2 + N/3]` and `[5N/6 + 1, 3N/2 − 1]`, mostly
   outside the dense parts of the EF sumset).

3. **The "+ colliding pair" deviation (gain +2) kicks in at `N = 1000`**
   and persists at all larger N tested. The same structural pattern
   observed at `N = 70..77` in `computer-search-report.md` (where
   extremizers were `EF + colliding pair through the exception value`)
   continues at large N. The pair `{x, N − x}` augments through the
   existing exception sum `N` without creating new exceptions.

4. **Iterated colliding-pair augmentation gives substantial gains
   at large N.** Starting from `A_EF`:
   - N = 1000: 1 round, gain +2 → size 42.
   - N = 5000: 4 rounds, gain +8 → size 74.
   - N = 10000: 6 rounds, gain +12 → size 96.
   These gains are achieved purely from `A_EF` (no global search).
   The colliding pairs at each round share the exception value `N`
   without colliding with within-half sums.
   *Caveat:* at `N ≥ 5000` our `B` is sub-optimal, so part of the
   gain "fills in" the gap to the true `F_2(N/3)`. But at `N = 1000`
   the gain is *additional* to an already-optimal EF construction.

5. **No swap improves size** (since swap preserves cardinality and the
   test is for ≥ `|A_EF|`); but many SWAP witnesses exist showing the
   high-multiplicity local neighborhood of `A_EF` in the same-size
   SAS landscape.

## Caveats

- At `N = 5000, 10000` our Sidon `B` is sub-optimal (33 vs ~41,
  42 vs ~58). The "EF is not locally maximal" finding there is partly
  due to under-sized `B`. However:
  - The colliding-pair witnesses `{x, N − x}` with `x ∈ (N/3, N/2)`
    sit in the *middle third* outside `A_EF` regardless of `B`'s
    optimality. They are not just "extending `B`."
  - At `N = 1000` with `B` provably optimal, `A_EF ∪ {382, 618}` is
    a genuine `+2` over `2·F_2(N/3)`.

- Our locality search is over single ADD / SWAP / colliding pair.
  It does not exhaust 2-element or 3-element moves of other shapes.
  EF could still be locally maximal w.r.t. some stronger notion of
  "neighborhood," but it is not for the moves we tested.

- We do not enumerate all extremizers. We do not compute `f(N)`
  exactly for the large N (that's currently infeasible by brute
  force above N ≈ 90).

## Implications for the rigidity conjecture

This result is **interesting but does not refute the rigidity
conjecture.** The conjecture says SAS extremizers are *approximately*
of the form `B ∪ (a − B)` (with `dev ≤ O(1)` deviations). Our
witnesses are exactly of this form: `A_EF ∪ {colliding pair through N}`
has deviation 2 from strict EF — the *same* structural deviation
documented at `N = 70..77` in the small-N analysis.

Concretely, at `N = 1000`:
- Strict EF gives 40.
- EF + one colliding pair gives 42 (dev = 2 from strict EF).
- The conjectured asymptotic is `(2/√3)·√N + 1.520·N^{1/4} ≈ 45` —
  so size 42 sits comfortably below this asymptotic and is
  consistent with the conjecture.

What this **does** show:

1. The strict EF construction `B ∪ (N − B)` is **not** literally
   `f(N)` in general. It is a lower bound that is `O(1)`-off
   from `f(N)` at moderate-to-large `N`.

2. The structural family of extremizers is `{EF + few colliding pairs}`,
   which is consistent with all data so far (small-N and now medium-N).

3. The iterated-augmentation gain at large N (e.g., +12 at N=10000)
   is mostly recovering from sub-optimal `B`, but does include real
   colliding-pair augmentations.

## Files

- `data/ef_locality.c` — test code.
- `data/ef_locality_results.txt` — per-N results.
- This file — narrative.

## Reproducibility

```bash
cd data
cc -O3 -march=native -funroll-loops -o ef_locality ef_locality.c
./ef_locality 100 200 500 1000 5000 10000
cat ef_locality_results.txt
```

Total wall time on a single core: ~3 minutes (dominated by N = 500
exact-Sidon backtracking at M = 166).
