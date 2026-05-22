# Attacking the `√2` Barrier from Above for Strong Almost-Sidon Sets

**Draft research notes, 2026-05-22.** Companion to `paper.md`. This note
plans the genuine open step: pushing below `√2` toward the conjectured
`2/√3 ≈ 1.155 · √N`.

**Background (post-survey update).** A literature survey on 2026-05-22
established two facts:

- The `(√2 + o(1)) · √N` upper bound itself is NOT novel; it was posted
  in essentially identical form by `DesmondWeisenberg` in post #75 of the
  [erdosproblems.com #864 discussion thread](https://www.erdosproblems.com/forum/discuss/864)
  on 11 August 2025.
- The territory *strictly below* `√2` is genuinely open as of survey
  date. No published preprint, journal paper, or forum post pushes the
  upper bound below `√2`. Pikhurko (2006), Vinuesa's school (2009–2026),
  the autoconvolution program (Martin–O'Bryant–Matolcsi–Vinuesa–White,
  most recently arXiv:2210.16437 and arXiv:2508.02803), Cilleruelo–Ruzsa–
  Vinuesa 2010 (arXiv:0909.5024) all study the broader `B₂[g]` class
  with `g ≥ 2`; their bounds (around `1.864 · √(gN)`) do not exploit the
  "single exception" hypothesis. Schoen–Sanders–Croot–Sisask almost-
  periodicity has not been applied to the strong almost-Sidon problem.

The OEIS sequence
[A389182](https://oeis.org/A389182) provides extremizer sizes at small
`N`, and [Tao's GitHub issue 143](https://github.com/teorth/erdosproblems/issues/143)
discusses small-`N` analysis up to `N = 69`.

## Where the `√2` slack lives

The bound `√2 · √N` comes from `√(n*/2) + √(N − n*/2) ≤ √(2N)`,
maximized at `n* = N`. At that point both Sidon halves
`A_- ⊆ [1, N/2]` and `A_+ ⊆ [N/2, N]` simultaneously hit their Lindström
maximum density `√(N/2)`. Two structural facts say this is unlikely:

1. **The construction's `n*` is at the boundary**: Erdős–Freud
   `B ∪ (N − B)` with `B ⊆ [1, N/3]` has `|A_-| = √(N/3)` and
   `|A_+| = √(N/3)`, packed in only the outer thirds; the middle third
   is empty. The Lindström bound `√(half-length)` is NOT attained.

2. **Straddling pairs interfere with within-half sums**: a cross-sum
   `a + b` with `a ∈ A_-`, `b ∈ A_+` lies in `(α, α + N]` where
   `α = ⌊n*/2⌋`. This range overlaps both within-`A_-` sums `[2, 2α]`
   and within-`A_+` sums `(2α, 2N]`. Any cross/within collision (other
   than at `n*`) violates strong almost-Sidon.

The `√2` bound exploits (1) but ignores (2). Below-`√2` attacks must
exploit (2).

## Elementary counting attempts (and why they fail)

Let `L = |A_-|`, `U = |A_+|`, `k = mult(n*)`. Available constraints:

- (Sidon) `L ≤ √(α) · (1 + o(1))`, `U ≤ √(N − α) · (1 + o(1))`.
- (Cross-sum range) `L·U − (k − 1) ≤ N + O(1)` (cross-sums in interval of
  size `N`, all distinct except for `k` colliding at `n*`).
- (Total sums) `L(L+1)/2 + U(U+1)/2 + LU − (k − 1) ≤ 2N − 1` (all pair
  sums distinct in `[2, 2N]` except at `n*`).
- (Pair size) `k ≤ ⌊(L + U)/2⌋ + 1` (each n*-pair uses two elements).

At the worst case `n* = N`, `L = U = √(N/2)`:
- Cross-sum constraint: `L·U = N/2`, allowed range is `N`, so the
  constraint `N/2 − k + 1 ≤ N` is satisfied for any `k ≥ 0` — *vacuous*.
- Total sums: `≈ N/2 + N/2 + N/2 = 3N/2` distinct values needed, but
  range allows `2N`. Vacuous.
- Pair size: `k ≤ √(N/2) + 1` — automatic.

**Conclusion: elementary counting does NOT give below `√2`.** The
overlap-and-distinct-cross-sums idea needs to be combined with a
Fourier-like analysis that tracks *which* values are hit, not just
*how many*.

## Three viable attack lines

### Line 1: Pure Pikhurko-style autocorrelation refinement — **disqualified**

The natural first thought is to redo Pikhurko 2006 (arXiv:math/0309029)
Theorem 2 with the substitution `(r − 1)_+ = (k − 1) · δ_{n*}`. But the
survey identified a fatal obstruction:

> Pikhurko's bound `|A|² ≤ 2N + slack` requires the slack
> `∑ (r(n) − 1)²_+` to be small. For the strong notion, the single
> bad atom contributes `(r(n*) − 1)²` which can be as large as
> `(|A|/2)² ≈ |A|² / 4`. So the slack DOMINATES `|A|²` and the
> inequality becomes vacuous.

In other words: Pikhurko's bound is well-suited to many-but-small
excesses (quasi-Sidon), and ill-suited to a single-but-large excess.
The pure-Fourier method alone cannot beat `√2` here.

This is the asymmetric tradeoff: Pikhurko's argument handles "many
exceptional values each with multiplicity 2" cleanly but loses to a
"single value with potentially large multiplicity." That's the
opposite of what we need.

### Line 1' (the actually most promising): hybrid midpoint × Pikhurko on cross terms

The way through: combine the midpoint split (which neutralizes the bad
atom by isolating it) with Pikhurko's Fourier argument on the
*cross-pair* contributions (which have no bad atom, only "near-Sidon"
behaviour).

Concretely, after the midpoint split:
- `A_-` and `A_+` are each genuinely Sidon (lower-bound-side: Lindström).
- The *cross* pairs `(a, b)` with `a ∈ A_-`, `b ∈ A_+` produce sums in
  the interval `(n*/2, n*/2 + N]`, with multiplicity exactly 1 at every
  value except possibly `n*`.
- The cross-pair sumset is itself "Sidon with the one exception at n*",
  but it is a *bipartite* problem, not a within-half problem.

The cross-pair multiplicity at `n*` is `k := |{a ∈ A_- : n* − a ∈ A_+}|`.
For each cross-sum value `≠ n*`, multiplicity 1. So the autocorrelation
on the cross sumset has the *same* shape as Pikhurko's, but with the
bad atom controlled by the explicit `k`.

**Concrete inequality to try (from survey):**

> `|A| ≤ √(αN) + √((1−α)N) + √((1−α)N) ?`

for a splitting parameter `α < 1/3`, giving roughly `1.36 · √N` at the
optimum. The intuition: a three-piece split (lower-half, upper-half-
below-n*, above-n*) plus careful Cauchy–Schwarz might tighten things.

**Estimated effort:** working through the bipartite Fourier inequality
takes 1–2 weeks. Cleaner if we first verify the elementary three-piece
split numerically against OEIS A389182.

**Best-case outcome:** constant `c ∈ [1.30, 1.40]` per the survey's
estimate. Reaching `2/√3 ≈ 1.155` unconditionally would solve the
problem.

### Line 2: Triple-counting with cross-within compatibility

The cross sums (`a + b` with `a ∈ A_-`, `b ∈ A_+`) and within-`A_-` /
within-`A_+` sums share overlap regions. Each "collision" between a
cross-sum and a within-sum (other than at `n*`) is forbidden by strong
almost-Sidon.

Let `c_-(x)` denote the number of within-`A_-` representations of `x`,
`c_×(x)` the number of cross representations, etc. Then

  `c_×(x) · c_-(x) ≤ 0` for `x ∈ overlap range`, `x ≠ n*`.

In other words: for each `x` in the overlap, EITHER no within-`A_-`
pair sums to `x`, OR no cross pair sums to `x`.

This bipartite-style "compatibility" constraint is a hypergraph-coloring
condition on `(A_-, A_+)`. It limits the joint density of `A_-`, `A_+`
near the overlap region.

**Open**: can this be packaged into a clean inequality? The most natural
form would be a constraint on `∑_x c_-(x) · c_×(x) = 0`, which by
Cauchy–Schwarz lower bounds `∑ c_-² · ∑ c_×²`. This could control
`|A_-|` and `|A_+|` jointly.

**Estimated effort:** 1 week to draft the inequality and check feasibility.

**Best-case outcome:** constant below `√2` only if the cross-within
constraint is genuinely tight at the worst case `n* = N`. Heuristically
it should be tight there (cross-sum range fully overlaps within-sum
ranges), but the magnitude of improvement is unclear.

### Line 3: Direct Fourier / additive energy

Define `f = 1_A`. Then Sidon means `r̂ = |f̂|²` has small "off-diagonal"
mass. Strong almost-Sidon means `r̂` is essentially `|A| · 1_{n=0} +
1_{n ≠ 0} + (k − 1) · (1_{n=n*} − 1_{n ≠ 0})·(...)`. Hmm — Fourier-side
constraints translate to additive-energy bounds, which then via
Schoen–Sanders or Croot–Sisask quasirandomness might yield improved
density bounds.

This is the most powerful in principle but requires the most setup.

**Estimated effort:** 2–4 weeks; depends on what's already in Mathlib /
the literature for the underlying harmonic analysis.

**Best-case outcome:** could potentially get all the way to `2/√3` if a
Plancherel-style identity matches the lower-bound construction exactly.
Realistic outcome: a constant strictly below `√2`, but probably not as
sharp as `2/√3`.

## Recommended sequence (post-survey update)

1. **Confirm small-`N` data first**. Pull OEIS A389182 and check whether
   the asymptotic constant looks like it's closer to `2/√3` or to `√2`
   in the small-`N` regime. If the data trends toward `2/√3`, that's
   evidence the lower-bound construction is tight and the gap closes
   from above. If it trends to some intermediate value, that suggests
   the true constant lies strictly between.
2. **Attempt Line 1'** (hybrid midpoint × Pikhurko on cross terms). The
   three-piece split heuristic should give `[1.30, 1.40]`. This is the
   most realistic concrete target.
3. **Read the key papers in full** before any new calculation:
   - Pikhurko 2006 arXiv:math/0309029 §3 (Fourier proof).
   - Vinuesa thesis (icmat.es/Thesis/CVinuesa.pdf) Ch. 3 on `B₂[g]` as
     `g → 1⁺`.
   - White arXiv:2210.16437 (current autoconvolution constant).
4. **Line 2 as parallel approach**: cross-within compatibility constraint
   might still bind in a non-Fourier way; quick to attempt elementarily.
5. **Line 3 (full Fourier)** as the long-term goal toward `2/√3`.

## Realistic outcomes and risks

| Outcome | Probability | Effect on problem |
|---------|-------------|-------------------|
| Find `c ∈ [1.30, 1.40]` via Line 1' | Moderate | Genuine new partial result, publishable as a short note. |
| Find `c → 2/√3` via Line 3 | Low | Resolves #864 unconditionally. |
| Get stuck, no improvement | Plausible | Confirms gap is structurally hard; honest negative report. |
| Discover prior art for below-√2 we missed | Low | Survey was thorough; possible but unlikely. |

**Greatest risk:** the bipartite Pikhurko adaptation could itself
become technical (Fourier on a non-translation-invariant set), and we
end up with a clean argument that gives `√2 − ε` for some unspecified
`ε`, rather than an explicit constant. That's still a real result but
less satisfying than an explicit `1.36` or similar.

## Empirical evidence (2026-05-22): EF construction is essentially tight

We pulled OEIS [A389182](https://oeis.org/A389182) (69 terms,
`N = 1..69`, computed by David Spencer per
[teorth/erdosproblems issue 143](https://github.com/teorth/erdosproblems/issues/143))
and compared `f(N)` against `2·|B(⌊N/3⌋)|` where `|B(M)|` is the
maximum Sidon-set size in `[1, M]` (OEIS A005282). The gap
`f(N) − 2·B(⌊N/3⌋)` is in `{−1, 0, +1}` for every tested `N`. The
Erdős–Freud reflection construction is essentially tight at small `N`.

The asymptotic of the EF construction itself is
`2·B(N/3) ≈ (2/√3)·√N + (2/3^{1/4})·N^{1/4} ≈ 1.155·√N + 1.520·N^{1/4}`,
which matches the OEIS data essentially exactly:

| N | EF prediction | OEIS f(N) |
|---|---------------|-----------|
| 25 | 9.17 | 9 |
| 49 | 12.11 | 12 |
| 69 | 13.98 | 14 |

The empirical ratio `f(N)/√N` is `1.69` at `N = 69` (much higher than
both `√2 ≈ 1.414` and `2/√3 ≈ 1.155`) — but this is fully explained by
the `N^{1/4}` lower-order term. The asymptotic ratio for the EF
construction only reaches `1.20` at `N = 10⁶` and `1.16` at `N = 10¹⁰`.

**Empirical conclusion: the conjectured constant `2/√3` is strongly
supported.** The lower-bound construction (EF) appears asymptotically
tight; pushing the upper bound below `√2` toward `2/√3` is the right
target, and we should expect that the right answer is `2/√3` (not some
intermediate constant).

See `analyze_oeis.py` for the script and `data/A389182.txt` for the data.

## Structural sketch from the empirical analysis

The empirical tightness of EF suggests a *structural* roadmap. EF has
the form `A = B ∪ (N − B)` with Sidon `B ⊂ [1, N/3]`. That is:

- `A_-` (the lower half) occupies only the first **third** of `[1, N/2]`.
- `A_+` symmetrically occupies the last third of `(N/2, N]`.
- The middle third `[N/3 + 1, 2N/3 − 1]` is empty.

The structural question is: can we prove any maximal `A` must be
concentrated like this?

### Failed attempt: elementary "energy" counting

Parametrize `A_- ⊂ [1, α N]`, `A_+ ⊂ ((1 − β) N, N]` with
`α, β ∈ [0, 1/2]` (the midpoint constraint forces both halves into half
the interval). For Lindström-extremal halves:
`|A_-| ≈ √(αN)`, `|A_+| ≈ √(βN)`. Sumset cardinalities:

- Within-`A_-`: `|A_-|(|A_-|+1)/2 ≈ αN/2` distinct values in `[2, 2αN]`.
- Within-`A_+`: `βN/2` distinct values in `[2(1-β)N, 2N]`.
- Cross: `√(αβ)·N` distinct values in `[(1-β)N, (1+α)N]`.

By strong almost-Sidon, all distinct except at `n*`. So the total
count fits in `[2, 2N]`:

  `αN/2 + βN/2 + √(αβ)·N ≤ 2N`, i.e., `(α + β)/2 + √(αβ) ≤ 2`.

Maximize `√α + √β` subject to this constraint and `α, β ≤ 1/2`:
the constraint becomes `1/2 + √(αβ) ≤ 2`, automatic. So the maximizer
is the corner `α = β = 1/2`, giving `√α + √β = √2`. **The counting
constraint does not bind below `√2`** — it only re-proves the bound we
already have.

### Why naive energy fails

The constraint "sumsets disjoint" treats values as occupying interval
ranges uniformly, but it doesn't capture *which* values are hit.
Within-`A_-` and cross sumsets *could* coexist in the overlap range
`(αN, 2αN]` if their hit-patterns are disjoint at the value level —
not just at the cardinality level. Naive cardinality counting allows
this and gives no improvement.

### Where the 2/√3 must come from

The Erdős–Freud construction's distinctive feature is that **every**
cross pair sums to exactly `n* = N` — i.e., cross sums are *maximally
concentrated*. This forces the within-half sumsets to cover most of
the available range, leaving cross sums no room except at `n*`. The
1/3-restriction of `B` is the consequence.

For a general maximal `A`, cross sums need not concentrate at `n*` —
some may take other values, costing room from the within-half sumsets.
But not all cross-sum values are equally "expensive": those in the
overlap with within-half sumsets are heavily constrained, those
outside are free.

A correct argument should weigh cross-sum values by their position
*relative to* the within-half sumsets, not just by total count. This
is exactly the kind of structural argument Erdős–Freud Lemma 1+3
provides: the within-half sumset has a known *density profile* over
`[2, 2αN]` (uniform asymptotically, density 1/4 in the bulk, lower at
the endpoints).

**The honest attack outline:**

1. Apply Erdős–Freud Lemma 1: for near-extremal `A_-`, the within-`A_-`
   sumset has a specific density profile on `[2, 2αN]`.
2. The cross sumset has its own density profile on `[(1-β)N, (1+α)N]`,
   constrained by the structure of `A_- × A_+`.
3. In the overlap region, the two profiles must be *additively
   disjoint* (their values are different, not just their counts).
4. This is a Plancherel-style constraint on the *Fourier
   transforms* of the sumset indicators. The Pikhurko-style argument
   on the cross-terms is the right vehicle.

This is where the **hybrid midpoint × Pikhurko** approach (Line 1' in
this note) becomes concrete: the cross-term Fourier analysis is what
distinguishes "interval-overlap" from "value-overlap" and yields a
sub-`√2` constant.

**Bottom line on the structural sketch:** we have empirical evidence
that the conjectured `2/√3` is tight, and a clear story for *why*
elementary methods cannot reach it (they treat values as a uniform
resource, missing the position-dependent constraint). Resolving the
gap requires Fourier/density-profile arguments.

## Attack attempts and convergent diagnosis (2026-05-22)

Two Fourier-style attacks attempted in parallel, both negative but
convergent in their diagnosis:

### Attempt A — Pikhurko Theorem 2 on cross-terms
*Detail document: [`pikhurko-adaptation.md`](pikhurko-adaptation.md)*

Adapted Pikhurko's gap-deficit Fourier inequality to the bipartite
cross-pair convolution `f_- * f_+`. Got the explicit constraint
`L · U ≤ ((π+2)²/((π+2)² + 2)) · N ≈ 0.93 · N`. Combined with
Lindström per half (`L² ≤ αN`, `U² ≤ βN` with `α + β ≤ 1`), this
gives `αβ ≤ 0.86`. **Vacuous** — `αβ ≤ 1/4` automatically. No
improvement.

**Quantitative gap diagnosis (key):** to reach `2/√3` from this style
of argument one would need `K < 1/2` (specifically `K = 1/6` gives
exactly `2/√3`); the Pikhurko-cross constraint is `K ≈ 0.93`, **short
by roughly a factor of two**.

**Structural diagnosis:** Pikhurko's inequality is a *gap-deficit*
statement — it converts "sumset has few gaps in its ambient interval"
into a size bound. In the bipartite cross setting the cross-sumset
covers at most `N/2` of an interval of length `N` (since
`L·U ≤ √(αβ)·N ≤ N/2`), leaving `≥ N/2` gaps. With `Θ(N)` gaps the
gap-deficit inequality is vacuous.

### Attempt B — White / CRV autoconvolution at `g → 1⁺`
*Detail document: [`autoconvolution-attack.md`](autoconvolution-attack.md)*

White's Corollary 2 with `g = 1` gives a worse constant than
Lindström (the autoconvolution bound deteriorates as `g → 1⁺`).
CRV stratified form with `l = 2k − 2` extra slack at `n*` has the
`l²` term dominate when `k = Θ(√N)`, also vacuous.

**Structural diagnosis:** autoconvolution methods extract
*L²-averaged* information; the SAS hypothesis is "L^∞ minus one
atom" — these are structurally mismatched. Single-atom strength of
SAS is washed out by L² averaging.

### Convergent recommendation

Both attempts independently arrived at the same path forward:
**value-disjointness / density-profile arguments**, using Erdős–Freud
Lemma 1 (uniform distribution of extremal Sidon sets) and Pikhurko
Lemma 10 (sumset density profile). This is exactly the
"position-dependent constraint" sketched earlier in this note.

The key statement to prove (for `n* = N`, the worst case):

> If `A_-` is an extremal Sidon set in `[1, αN]` with `α > 1/3`, then
> the within-`A_-` sumset has *positive density* in the overlap region
> `(N/2, 2αN]`. Specifically, the density approaches the
> Erdős–Freud value `(some explicit fraction)` as `A_-` approaches
> Lindström extremality. Cross sums in the same region would create
> value-coincidences with within-`A_-` sums, violating SAS.

If this density-positivity can be made quantitative, the argument
forces `α ≤ 1/3` (essentially the Erdős–Freud regime) and yields the
bound `(2/√3 + o(1)) · √N` — closing the problem.

This is Line 2 of the original taxonomy ("triple-counting with
cross-within compatibility") combined with the Erdős–Freud Lemma 1
density profile. The Fourier-energy methods (Lines 1' and 3) are
both *disqualified by their own diagnostics*.

## Tracking

Status: open. Two Fourier attacks closed (negative); next step is
density-profile via Erdős–Freud Lemma 1.

| Date | Event |
|------|-------|
| 2026-05-22 | Notes drafted; survey agent dispatched. |
| 2026-05-22 | Survey complete: `√2` is prior art (DesmondWeisenberg Aug 2025); below-`√2` confirmed genuinely open. |
| 2026-05-22 | OEIS A389182 analysis: EF construction is essentially tight; `2/√3` strongly supported as the asymptotic. |
| 2026-05-22 | Structural sketch via Erdős–Freud Lemma 1 + non-collision constraint outlined; potentially closes the problem. |
| 2026-05-22 | **Attempt A (Pikhurko cross-terms) negative**: short by factor of 2 in the cross-product constraint. Detail in `pikhurko-adaptation.md`. |
| 2026-05-22 | **Attempt B (autoconvolution g→1⁺) negative**: L² methods miss single-atom strength. Detail in `autoconvolution-attack.md`. |
| 2026-05-22 | Both attempts independently recommend density-profile / value-disjointness via Erdős–Freud Lemma 1. This is now the open research direction. |
