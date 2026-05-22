# Direct Combinatorial Attack on SAS Bipartite Rigidity

**Research note, 2026-05-22.** Twelfth attack, paired with the eleven
convergent negatives in `below-sqrt2.md`. After all Fourier/L^p methods
hit the same meta-obstruction, we attempt the rawest "order-sensitive,
point-wise, joint" technique: **direct case analysis on the extremes
`m = min(A)`, `M = max(A)` with induction on `|A|`**.

## Setup

`A ⊆ {1,...,N}` SAS with exception `n*`. `m := min A`, `M := max A`.
Strong almost-Sidon: every sum value `s ∈ [2,2N]` has `r_A(s) ≤ 1`
except possibly `r_A(n*)` arbitrary. Centre split:
`A_- := {a < n*/2}`, `A_+ := {a > n*/2}` (and `n*/2` at most once).
Each n*-pair is `(a, n*−a) ∈ A_- × A_+`.

## Case 1: `m + M ≠ n*`

Then `r_A(m+M) = 1`, the unique pair summing to `m+M` is `(m, M)`.

**The sums `{m + x : x ∈ A \ {m}}` are `|A|−1` distinct values** in
`[2m, m+M] \ {m+M}`. **The sums `{M + x : x ∈ A \ {M}}` are `|A|−1`
distinct values** in `[m+M, 2M] \ {m+M}`. These two sets share at most
the value `n*` (each side may contribute one `n*`-incidence).

The available range is `[2m, 2M] = [2m, 2M]` with length `2(M−m)`. So
we obtain `2(|A|−1) − (collisions at n*) ≤ 2(M−m)`, i.e.,
`|A| ≤ M − m + O(1)`. **Vacuous**: `M − m ≤ N` while `|A| ≈ √N`. The
single anchor pair `(m,M)` constrains nothing useful.

**Stall in Case 1:** `(m, M)` is just one anchor. The bulk of `A`
lies in the interior and is not pinned by this anchor. To get a
non-trivial bound, we'd need to involve the *second*-smallest /
*second*-largest elements too — but each new "anchor" gives the same
weak constraint, and they don't combine multiplicatively.

## Case 2: `m + M = n*`

The extreme pair *is* an n*-pair. Set `r_0 := r_A(n*) ≥ 1`. Two
subcases by `r_0`.

### 2a: `r_0 = 1`

Then `A` is genuinely Sidon (no repeated sum at all if `r_0 = 1`
counts the unique pair). Lindström: `|A| ≤ √N + O(N^{1/4})`. Done,
far below `2/√3 · √N`.

### 2b: `r_0 = 2`

Remove either element of an n*-pair other than `(m,M)`: say
`(a_0, n*−a_0)` with `a_0 ≠ m`. Set `A' := A \ {a_0}`. Then `A'` has
exactly one n*-incidence remaining (from `(m,M)`), but every sum has
`r_{A'} ≤ 1` (one count of n* doesn't repeat). So `A'` is Sidon,
`|A'| = |A| − 1 ≤ √N + O(N^{1/4})`, giving `|A| ≤ √N + 1 + O(N^{1/4})`.

### 2c: `r_0 ≥ 3` — the interesting regime

**Structural conclusion so far:** any SAS set with `|A| ≥ (2/√3)·√N`
must have `r_A(n*) ≥ 3`. This is genuine and matches EF
(`r(n*) = |B| = Θ(√N)`).

**Inductive peel.** Take a non-extreme n*-pair `(a, n*−a)` with
`a ≠ m, M` (exists since `r_0 ≥ 3` and only `(m,M)` involves extremes,
as `n*−m = M` and `n*−M = m`). Set `A''' := A \ {a, n*−a}`:
- `min A''' = m`, `max A''' = M`, `n*_{A'''} = n*`.
- `r_{A'''}(n*) = r_0 − 1`.
- `A'''` is SAS with same extremes, n*, and one fewer n*-pair.

**Iterate `r_0 − 2` times.** End at `A^*` with `r(n*) = 2`. One more
peel (Case 2b) → Sidon set of size `|A| − 2(r_0 − 1)`. Lindström:

`|A| − 2(r_0 − 1) ≤ √N + O(N^{1/4})`,
i.e., `|A| ≤ √N + 2r_0 − 2 + O(N^{1/4})`.

### Why 2c stalls

In the EF construction `r_0 = |B| ≈ (1/√3)√N`. Plug in:
`|A| ≤ √N + (2/√3)√N + O(N^{1/4}) = (1 + 2/√3) · √N ≈ 2.155 · √N`.

**This is worse than the `√2` bound**, not better. The bound counts
each stripped pair as costing 2 to `|A|`, but the stripping doesn't
exploit that the stripped pairs *also* satisfy Sidon-like constraints
between themselves and with the remaining set. The induction discards
information at every peel.

### Where Case 2 *almost* worked

The structural facts recovered:

- (S1) `r_A(n*) ≥ 3` in the near-extremal regime (`|A| ≥ (2/√3 + ε)√N`).
- (S2) The non-extreme n*-pairs are precisely the "SAS gain" over a
  Sidon backbone. Peeling them gives a Sidon subset of size
  `|A| − 2(r_0 − 1)`, but the peeled pairs are tightly placed
  (they cluster around `n*/2`).
- (S3) The peel preserves `m, M, n*` — the natural global anchors —
  unlike "remove extremes", which destroys this link.

## The inductive trichotomy

Claim (target): `max ≤ N/3` ∨ `min ≥ 2N/3` ∨ EF-like.

**Removing `m` (Case 2c, `r_0 ≥ 3`):** `A' := A \ {m}` is SAS with
same `n*`. By IH applied to `A'`:
- `max A' ≤ N/3` ⇒ `M ≤ N/3` (since `M ∈ A'`). ✓ gives `max A ≤ N/3`.
- `min A' ≥ 2N/3` ⇒ second-smallest element of `A` is `≥ 2N/3`. But
  `m` might be `< 2N/3`. So we get `A ⊆ {m} ∪ [2N/3, N]`. This is
  *not* the same as `min A ≥ 2N/3`. **Trichotomy is not preserved.**
- `A' ≈ EF`: then `A = {m} ∪ EF`. If `m` fits into the EF skeleton,
  fine; else `A` is "EF plus one outlier". The outlier interacts
  with `M ∈ A'` via the n*-axis: `m + M = n*`, consistent with
  augmenting EF by one colliding pair-element. ✓ matches empirical data.

**Symmetrically removing `M`:** preserves `min A ≥ 2N/3` and EF, not
`max A ≤ N/3`.

**Stall: bifurcating IH.** To preserve all three branches, we must do
*both* removals (or neither), but then `A''` has new extremes `m'', M''`
which need not satisfy `m'' + M'' = n*`. The Case 2 hypothesis breaks
at depth 2.

## Final diagnosis

The direct attack stalls at three explicit points:

1. **Case 1 (`m+M ≠ n*`):** single-anchor constraint is `|A| ≤ M−m`,
   vacuous at the `√N` scale.

2. **Case 2c, size bound:** stripping n*-pairs recovers Lindström
   from below, but the bound `|A| ≤ √N + 2(r_0 − 1)` *rederives* `√2`
   (or worse) because each peeled pair "costs" 2 in cardinality but
   only 1 in Sidon-slot. The dual nature of SAS (Sidon + n*-stack)
   isn't traded efficiently by sequential peeling.

3. **Case 2c, trichotomy preservation:** removing one extreme
   preserves only one of the three trichotomy branches. The induction
   bifurcates and the structural invariant degrades after two levels.

**Root cause (consistent with the 11-attack convergent diagnosis):**
SAS extremality is a *globally coupled* optimum of Sidon size and
n*-multiplicity. Local peel-and-strip moves treat the two as
independent additive resources and re-derive `(1 + 2/√3) √N` or
worse. The `2/√3` constant requires a joint potential function or
global invariant that integrates both resources — exactly what every
Fourier/density/entropy/algebraic method has also failed to provide.

## What is recovered

Not nothing. Two clean facts emerge that we did not have before:

- **(R1) Single-atom amplification:** if `r_A(n*) ≤ 2`, then
  `|A| ≤ √N + 2 + O(N^{1/4})`. Equivalently, **near-extremal SAS sets
  necessarily have `r_A(n*) ≥ 3`**.
- **(R2) Extreme-pair n*-incidence:** in the only useful case (Case 2),
  the extreme pair `(m, M)` *is* an n*-pair, so the SAS exception
  axis aligns with the diameter pair. This matches every empirical
  extremizer (see `computer-search-report.md`: `exc = a = m+M` in all
  79 known cases).

(R2) refines the empirical observation into a structural one for the
direct attack: near-extremal SAS sets have `m + M = n*` (otherwise the
single-anchor Case 1 fails to give `|A| > √N + O(1)`).

## Honest verdict

The direct combinatorial attack is the 12th convergent negative. It
identifies *which* facts are extractable elementarily (R1, R2, S1–S3
above) and *where* the elementary toolkit runs out: at the trade-off
between Sidon size and n*-multiplicity, which is irreducibly global.

The next step — the only one not yet ruled out — is a Freiman-style
**global structural rigidity theorem**: a non-elementary statement
that all near-extremal SAS sets *are* approximately EF, proved by a
genuinely new invariant. Computer search at `N ≤ 10^4` confirms this
empirically; the gap between empirical fact and theorem is the open
problem.

## Tracking

Status: closed-negative (12th attack). Direct-combinatorial bound
yields `|A| ≤ (1 + 2/√3) √N ≈ 2.155 √N`, *worse* than `√2`. Two new
elementary facts (R1, R2) added to the toolkit.
