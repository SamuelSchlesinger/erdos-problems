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

## Tracking

Status: open. Survey complete 2026-05-22; Line 1' is recommended.

| Date | Event |
|------|-------|
| 2026-05-22 | Notes drafted; survey agent dispatched. |
| 2026-05-22 | Survey complete: `√2` is prior art (DesmondWeisenberg Aug 2025); below-`√2` confirmed genuinely open. Recommended Line 1' (hybrid). |
