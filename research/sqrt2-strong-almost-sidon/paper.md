# An √2 upper bound for strong almost-Sidon sets

**Draft note, 2026-05-22.** Companion to the Lean 4 formalization in
`Erdos/AlmostSidonSets/UpperBound/`.

## Abstract

For a finite set `A ⊆ {1, ..., N}` of positive integers, call `A` **strong
almost-Sidon** if at most one integer admits more than one unordered
representation as `a + b` with `a, b ∈ A`. We prove that every such `A`
satisfies `|A| ≤ (√2 + o(1)) · √N` as `N → ∞`.

Erdős and Freud (1991, *J. Number Theory* **38**, 196–205) observed that
`√2` is the natural barrier for upper bounds on the related but broader
class of *quasi-Sidon* sequences (those with `(1 + o(1)) · binom(k,2)`
distinct pairwise sums); their explicit bound was `(2 + o(1))·√N` with an
unpublished refinement to `1.98·√N`, sharpened by Pikhurko (2006,
arXiv:math/0309029) to `(1.863 + o(1))·√N`. Reducing the quasi-Sidon
constant below `√2 ≈ 1.414` remains open. We show that for the strictly
narrower class of strong almost-Sidon sets — those with at most one
duplicated sum, not merely `o(k²)` many — the `√2` barrier becomes a
theorem. The proof uses Lindström's `1969` Sidon upper bound applied to
each half of the midpoint split around the exceptional value, combined
with the elementary Cauchy–Schwarz inequality `√x + √(N−x) ≤ √(2N)`.

## 1. Definitions and main theorem

Throughout, `A ⊆ ℕ_{≥ 1}` is finite.

**Definition 1.1 (strong almost-Sidon).** `A` is *strong almost-Sidon* if
there is at most one integer `n*` such that `n* = a₁ + a₂ = b₁ + b₂` for
some unordered pairs `{a₁, a₂} ≠ {b₁, b₂}` with `aᵢ, bᵢ ∈ A`. The
exceptional sum `n*` may or may not exist; if it does not, `A` is a
genuine Sidon set.

**Definition 1.2 (Sidon).** `A` is *Sidon* (also called a `B₂`-sequence)
if every integer has at most one such representation.

Equivalently: `A` is Sidon iff for all `a₁, a₂, b₁, b₂ ∈ A` with
`a₁ ≤ a₂` and `b₁ ≤ b₂`, `a₁ + a₂ = b₁ + b₂` implies `(a₁, a₂) = (b₁, b₂)`.

For `A ⊆ {1, ..., N}`, write `|A|` for its cardinality.

**Theorem 1.3 (main).** For every `ε > 0` there is `N₀ ∈ ℕ` such that for
all `N ≥ N₀` and every strong almost-Sidon `A ⊆ {1, ..., N}`:

  `|A| ≤ (√2 + ε) · √N`.

The Lean 4 formalization of this theorem is
`AlmostSidonSets.UpperBound.strong_almostSidon_card_le_sqrt2_sqrt`
in `Erdos/AlmostSidonSets/UpperBound/Sqrt2Bound.lean`.

## 2. The midpoint split

**Lemma 2.1 (midpoint split, Lindström-style).** Let `A ⊆ {1, ..., N}` be
strong almost-Sidon with exceptional value `n*`. Set

  `A₋ := A ∩ {1, 2, ..., ⌊n*/2⌋}`,
  `A₊ := A ∩ {⌊n*/2⌋ + 1, ..., N}`.

Then `A₋` and `A₊` are each genuine Sidon sets, `A = A₋ ⊔ A₊`, and in
particular `|A| = |A₋| + |A₊|`.

*Proof.* For `A₋`: suppose `a + a' = b + b'` with `a, a', b, b' ∈ A₋` and
`{a, a'} ≠ {b, b'}`. Then `a + a' ≤ n*` (since both summands ≤ n*/2)
and `a + a' = b + b'` has multiple representations in `A`, so by strong
almost-Sidon, `a + a' = n*`. With `a, a' ≤ n*/2` and `a + a' = n*`, we
must have `a = a' = n*/2`. Similarly `b = b' = n*/2`. So `{a, a'} = {b, b'} = {n*/2}`,
contradiction. Hence `A₋` is Sidon. Symmetrically, `A₊` is Sidon (sums
of two elements `> n*/2` exceed `n*`, so cannot equal `n*`).

The partition is trivial: every `a ∈ A` satisfies either `2a ≤ n*` or
`2a > n*`. ∎

This lemma is formalized as `exceptionalAt_lowerPart_isSidon` and
`exceptionalAt_upperPart_isSidon` in
`Erdos/AlmostSidonSets/Structure.lean`.

## 3. Lindström's Sidon bound on an interval

**Theorem 3.1 (Erdős–Turán 1941 / Lindström 1969).** Let `A` be a Sidon
subset of an interval `[α+1, α+L] ⊆ ℕ` of length `L ≥ 1`. Then for any
integer `1 ≤ M ≤ L`,

  `M · |A|² ≤ (L + M − 1) · (|A| + M − 1)`.

In particular, taking `M ≈ √L / ε` and `L → ∞`, `|A| ≤ (1 + ε) · √L`.

*Proof sketch.* For `x ∈ [α+1, α+L+M−1]`, write
  `r(x) := |A ∩ [x − M + 1, x]|` (count of A-elements in a length-`M` window
ending at `x`). Two identities:

(i) `∑_x r(x) = M · |A|`, because each `a ∈ A` lies in the windows ending
at `a, a+1, ..., a + M − 1` (`M` choices).

(ii) `∑_x r(x)² ≤ M · |A| + M · (M − 1)` (Sidon). Expand:
  `∑_x r(x)² = #{(a, a', x) : a, a' ∈ A ∩ [x − M + 1, x]} = ∑_{(a,a') ∈ A², |a−a'| < M} (M − |a − a'|)`.
The diagonal `a = a'` contributes `M · |A|`. For each `d ∈ [1, M − 1]`,
the Sidon property forbids more than two ordered pairs `(a, a')` with
`|a − a'| = d` (one positive and one negative difference), so the off-diagonal
sum is at most `∑_{d=1}^{M-1} 2(M − d) = M(M − 1)`.

By Cauchy–Schwarz on `∑_x r(x) · 1`:
  `(∑_x r(x))² ≤ (L + M − 1) · ∑_x r(x)²`.

Substituting (i) and (ii):
  `M² · |A|² ≤ (L + M − 1) · (M · |A| + M · (M − 1))
            = M · (L + M − 1) · (|A| + M − 1)`.

Dividing by `M`: `M · |A|² ≤ (L + M − 1) · (|A| + M − 1)`. ∎

The Lean 4 formalization is in
`Erdos/AlmostSidonSets/UpperBound/SidonInterval.lean`, with the asymptotic
predicate `SidonIntervalAsymptotic` defined in `Sqrt2BoundConditional.lean`.

**Remark 3.2.** Lindström originally stated `|A|² < N + √(4N − 3) + 1` for
Sidon `A ⊆ {1, ..., N}`, giving `|A| ≤ √N + N^{1/4} + 1`. The asymptotic
`(1 + ε)·√L` form above suffices for our application and follows from
Theorem 3.1 with `M = ⌈√L / ε⌉`.

## 4. Proof of the main theorem

*Proof of Theorem 1.3.* Fix `ε > 0`. By Theorem 3.1 with `ε' := ε / (2√2)`,
there is `L₀ = L₀(ε)` such that every Sidon `S ⊆ [α+1, α+L]` with `L ≥ L₀`
has `|S| ≤ (1 + ε') · √L`. For `L < L₀`, the trivial bound `|S| ≤ L` gives
the uniform statement `|S| ≤ (1 + ε') · √L + L₀`.

Choose `N₀` large enough that `2L₀ ≤ (ε/2) · √N` for all `N ≥ N₀` (e.g.,
`N₀ = ⌈(4L₀/ε)²⌉ + 1`).

Let `A ⊆ {1, ..., N}` be strong almost-Sidon with `N ≥ N₀`. Two cases:

**Case 1: A has no exceptional value.** Then `A` itself is Sidon, so by
Theorem 3.1 applied to `[1, N]`:
  `|A| ≤ (1 + ε') · √N + L₀ ≤ √2 · √N + ε' · √N + L₀`
       `≤ √2 · √N + (ε/2) · √N + (ε/2) · √N = (√2 + ε) · √N`,
using `1 ≤ √2` and `2L₀ ≤ (ε/2) · √N`.

**Case 2: A has an exceptional value `n*`.** By Lemma 2.1, `A₋` and `A₊` are
Sidon. Note `n*/2 ≤ N` (since `n* ≤ 2N`). Apply Theorem 3.1's uniform form
to each half:
  `|A₋| ≤ (1 + ε') · √⌊n*/2⌋ + L₀`
  `|A₊| ≤ (1 + ε') · √(N − ⌊n*/2⌋) + L₀`.

Sum and apply the Cauchy–Schwarz inequality `√x + √(N−x) ≤ √(2N)`:
  `|A| = |A₋| + |A₊|`
       `≤ (1 + ε') · (√⌊n*/2⌋ + √(N − ⌊n*/2⌋)) + 2 L₀`
       `≤ (1 + ε') · √(2N) + 2 L₀`
       `= (1 + ε') · √2 · √N + 2 L₀`
       `≤ (√2 + ε/2) · √N + (ε/2) · √N = (√2 + ε) · √N`,
using `(1 + ε') · √2 = √2 + ε/2` (by definition of `ε'`) and again `2L₀ ≤ (ε/2)·√N`. ∎

## 5. Comparison with the literature

The "obvious barrier" of `√2` appears explicitly in Erdős–Freud
(1991, p. 204): *"any improvement in the upper bound of Proposition 1 is
equivalent to the reduction of this coefficient in (37) below √2."* In
their setting (quasi-Sidon sequences with `o(k²)` duplicated sums), `√2`
remains an open target — Pikhurko's `1.863` is the strict improvement
record.

The narrower class of *strong* almost-Sidon sequences (at most ONE
duplicated value) was not analysed for upper bounds in either Erdős–Freud
or Pikhurko, as far as the authors can verify. The construction `B ∪ (N − B)`
from a Sidon `B ⊆ [1, N/3]` (Erdős–Freud 1991, p. 204) yields a strong
almost-Sidon set of size `~ (2/√3) · √N ≈ 1.155 · √N`, which is also the
conjectured optimum (`OptimalUpperBoundConjecture` in our Lean formalization).
Thus Theorem 1.3 narrows the strong-notion gap from `1.863 → √2 ≈ 1.414`
versus the lower bound `2/√3 ≈ 1.155`.

The midpoint-split argument in Section 4 fails for quasi-Sidon sequences
because there is no single value to split around: the `o(k²)` exceptional
sums can be spread arbitrarily.

## 6. Open question

The conjectured tight constant is `2/√3 ≈ 1.155` (Erdős–Freud reflection
construction). Reducing our `√2` to anything strictly below `√2` for the
strong notion is open; the natural approach is a Fourier-style refinement
of the midpoint split that penalises pairs straddling the midpoint, in the
spirit of Pikhurko's autocorrelation analysis. We have not pursued this.

## References

1. P. Erdős and R. Freud, *On sums of a Sidon-sequence*, J. Number Theory
   **38** (1991), 196–205. DOI: 10.1016/0022-314X(91)90080-T.
2. B. Lindström, *An inequality for B₂-sequences*, J. Combinatorial Theory
   **6** (1969), 211–212.
3. P. Erdős and P. Turán, *On a problem of Sidon in additive number theory,
   and on some related problems*, J. London Math. Soc. **16** (1941),
   212–215.
4. O. Pikhurko, *Dense edge-magic graphs and thin additive bases*, Discrete
   Math. **306** (2006), 2097–2107. arXiv:math/0309029.
