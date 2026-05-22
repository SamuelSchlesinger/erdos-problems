# Inductive Lifting / Tensor Amplification for SAS

**Scout note, 2026-05-22.** Can a tensor / lift `A ↦ Ã` amplify SAS
violations, giving an inductive descent below `√2`?

## Setup

`A ⊆ [1, N]` is SAS with single exceptional sum-value `n*` of
multiplicity `k`; size `|A| ≤ c · √N`. Goal: find a lift
`Ã ⊆ [1, Ñ]` with `Ñ = N^{1+δ}`, `|Ã| ≥ |A|^{1+δ'}`, and `Ã` still
SAS. Then SAS at scale `Ñ` gives `|Ã| ≤ c · √Ñ`, hence
`|A|^{1+δ'} ≤ c · N^{(1+δ)/2}`. Compared with the input bound
`|A| ≤ c·√N`, this is *tighter* iff `1+δ' > 1+δ`, i.e., `δ' > δ`.
Iterating drives `c → 1` (or to whatever ratio the lift forces).

## Candidate 1 — Base-`M` Cartesian: `Ã = {a + Mb : a,b ∈ A}`, `M = 2N+1`

`|Ã| = |A|², Ñ ≈ MN ≈ 2N²`.

**Sum decomposition.** `(a₁+Mb₁) + (a₂+Mb₂) = (a₁+a₂) + M(b₁+b₂)`;
since `a₁+a₂ ≤ 2N < M`, the pair `(s_a, s_b)` is recovered from the
sum value. So sum-collisions in `Ã` correspond exactly to pairs of
`Ã`-pairs whose `a`-sum and `b`-sum agree.

**Fatal rectangle obstacle.** For ANY two unordered pairs
`{a,a'},{b,b'} ⊂ A` with `a≠a'` and `b≠b'`, the two `Ã`-pairs
`{(a,b),(a',b')}` and `{(a,b'),(a',b)}` have identical sum
`(a+a') + M(b+b')`. So `Ã` has `Θ(|A|⁴)` colliding unordered pairs at
`Θ(N)` distinct sum-values. `Ã` is nowhere near SAS — it has the entire
A·A "rectangle lattice" of forced collisions.

This is a structural obstruction for *every* Cartesian / product /
direct-sum lift: rectangles in `A × A` are intrinsic to product
structure.

## Candidate 2 — Sidon-encoded lift: `Ã = {a + M·σ(a) : a ∈ A}`

Choose `σ: A → ℤ` so that `σ(A)` is Sidon (e.g., via Singer; possible
since `|A| = O(√N)`, embed into a Sidon set of size `|A|`).

**Sum analysis.** Collision `(a+a') + M(σ(a)+σ(a')) = (c+c') +
M(σ(c)+σ(c'))` forces both coordinates equal; `σ(A)` Sidon ⇒
`{a,a'} = {c,c'}`. So `Ã` IS Sidon (zero exceptions). The original
SAS exception is even resolved.

**No amplification.** `|Ã| = |A|, Ñ ≈ M · max σ ≈ N · |A|² ≈ N²`.
Ratio `|Ã|/√Ñ = |A|/N = c/√N → 0`. The lift loses, not gains.

## Candidate 3 — Two-translate union: `Ã = A ∪ (A + D)`, `D > 2N`

**Cross pairs auto-collide.** `(a, a' + D)` and `(a', a + D)` both sum
to `a + a' + D`. So every cross-sum has multiplicity ≥ 2, giving
`Θ(N)` exceptional sum-values. NOT SAS.

## Candidate 4 — EF reflection: `Ã = A ∪ (M - A)`, `M = 2N+1`

This is the Erdős–Freud move. Within-`A` exception at `n*`; within-
`(M-A)` exception at `2M - n*`; cross-exception at `M` (when `a=a'`,
multiplicity `|A|`).

**Three exception values** unless they coincide. Setting `n* = M`
collapses two, but then `n* = 2N+1` is a sum in `A ⊂ [1,N]` — possible
only if `n* = 2N+1`, the extreme upper case. With `n* = M`, `Ã ⊂
[1, M]`, `|Ã| = 2|A|` (modulo the overlap at `n*/2` if integer).
Ratio: `2|A|/√M = 2c√N/√(2N) = c√2`. *Worse* than the input ratio `c`.

Iterating EF on itself is self-similar — the construction reproduces
itself at the same asymptotic ratio `2/√3`, not amplifying.

## Candidate 5 — Quadratic / Singer lift: `a ↦ a² mod p`

Sends `A` into ℤ_p as a Sidon-like image. Loses the linear-ordering
structure (`n*` no longer a natural sum). The SAS hypothesis is
fundamentally about `a + a'` in ℤ, not `a² + a'²` in ℤ_p; the
quadratic map does not commute with SAS-relevant sums.

## Why every product lift fails: the rectangle theorem

> **Observation.** For any lift of the form
> `Ã = {ϕ(a, b) : (a, b) ∈ S}` with `S ⊆ A × A` and `ϕ`
> "non-degenerate" (the projection to each `A`-factor is
> non-collapsing on `S`), the image `Ã` has `Ω(|S|²)` rectangular
> collisions: for `(a₁,b₁),(a₂,b₂) ∈ S` with `a₁≠a₂, b₁≠b₂`, the
> `Ã`-pairs `{ϕ(a₁,b₁), ϕ(a₂,b₂)}` and `{ϕ(a₁,b₂), ϕ(a₂,b₁)}`
> share their sum whenever `ϕ` is additive in each argument.

So additive product lifts cannot preserve SAS. SAS demands a single
sum-collision; product lifts generate quadratically many.

The Sidon-encoded lift (Candidate 2) escapes this by being a
*graph*, not a product, but then `|Ã| = |A|` — no amplification.

## The fundamental tradeoff

A lift `A ↦ Ã` faces a strict dichotomy:

- **Tight (size `≈ |A|^{1+δ}`)**: requires rectangle-rich structure
  ⇒ generates `Θ(|A|²δ)` exception values ⇒ violates SAS by a lot.
- **Sparse (size `≈ |A|`)**: can be made Sidon but achieves no
  amplification, so no descent.

This dichotomy is structural: SAS is an `L^∞` rigidity hypothesis
(at most one exceptional pair-sum value), and product structures
generate `L²` rectangle energy. The two are incompatible.

## Honest verdict

Inductive lifting / tensor amplification, *in the natural product
form*, does NOT preserve SAS. Every candidate lift either:

1. **Breaks SAS catastrophically** (rectangle collisions, Candidates
   1, 3, 4 with general parameters), or
2. **Loses size** (Candidate 2 graph-Sidon embedding), or
3. **Reproduces the original ratio** without amplifying (Candidate 4
   EF self-reflection, giving `c√2 > c`).

This places lifting in the same family as the eleven prior attacks
catalogued in `below-sqrt2.md`: the obstruction is the same — SAS is
*location-sensitive* `L^∞` rigidity, and every elementary
amplification tool is *translation/product-symmetric* or
*L²-averaged* and cannot exploit the single-atom hypothesis.

**Pragmatic recommendation.** Drop the lifting line. The descent
approach would require finding a non-product lift with both size
amplification and SAS preservation; no such construction is known and
the rectangle theorem above suggests none exists in additive form.
The next substantive direction remains the structural rigidity
conjecture identified in `below-sqrt2.md`.

## Connection to known constructions

The non-amplifying behaviour of EF reflection (Candidate 4) is
consistent with the empirical finding (`computer-search-report.md`,
`asymmetric-report.md`) that the EF construction is *essentially
tight* at all observed scales `N ≤ 10⁴`. If a lift COULD amplify SAS
violations, EF would not be tight — extremizers at scale `N²` would
strictly dominate (EF at `N`)-lifted-to-`N²`. The data shows the
opposite: EF at every scale `N` has size `(2/√3)√N + O(N^{1/4})`,
matching the observed `f(N)` essentially exactly.

In other words: empirical EF tightness is independent evidence that
*no amplifying SAS-preserving lift exists*. This corroborates the
analytical verdict above.
