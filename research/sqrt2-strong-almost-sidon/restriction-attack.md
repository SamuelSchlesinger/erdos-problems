# Restriction / Decoupling Attack on Bipartite SAS Rigidity

**Date:** 2026-05-22. Survey of modern harmonic analysis tools
(Bourgain–Demeter decoupling, discrete Fourier restriction,
Stein–Tomas, Tao–Vu Sidon restriction) applied to the open problem:
prove `α + β < 1` for the midpoint-split halves of any near-extremal
strong almost-Sidon set.

## TL;DR (verdict)

**Restriction/decoupling does NOT, as of the published literature,
provide a bipartite (joint) rigidity statement strong enough to force
`α + β < 1`.** All known discrete restriction theorems for Sidon-type
sets are single-set inequalities. They reprove `|A| ≤ √N (1 + o(1))`
via the L⁴ identity but say nothing about a midpoint split. The single
positive result (Ortega–Prendiville 2021) is per-half rigidity and was
already analyzed in `op-application.md` as insufficient (the 1/4
geometric slack is unaffected).

## 1. What the restriction theorems actually say

### 1.1 Discrete Fourier restriction (Bourgain, 1989; Mockenhaupt–Tao 2004)

For `A ⊆ [N]`, write `f̂_A(θ) = Σ_{a∈A} e(aθ)`. A Sidon set is
characterized by the L⁴ identity
`∫₀¹ |f̂_A(θ)|⁴ dθ = |A|² + 2(|A|² − |A|)/2 = |A|² + (|A|² − |A|)`
(more precisely, `‖f̂_A‖_4^4 = 2|A|² − |A|` since each unordered pair
contributes 2 to the diagonal and the off-diagonal pairs are distinct).
This *is* a restriction estimate: it bounds the L⁴ norm of an
exponential sum supported on `A`.

Bourgain's discrete restriction conjecture (Λ(p) problem) for the
squares gives `‖Σ_{n≤N} a_n e(n²θ)‖_p ≪ N^{1/2 − 1/p}·‖a‖_2` for
`p > 6`. The squares are a B₂[2] (hence almost-Sidon) set, but the
restriction estimate gives only `|A| ≪ N^{1/2 + ε}` per half, which
is weaker than the Lindström bound.

**For our problem:** The L⁴ restriction is *equivalent* to the
within-half Sidon constraint. It contains no bipartite information.

### 1.2 Bourgain–Demeter ℓ² decoupling (2015)

Decoupling for the moment curve `(t, t², …, t^k)` gives the Vinogradov
main conjecture. The relevant statement decomposes
`Σ a_n e(nθ + n²φ + …)` into pieces of length `N^{1/2}` and bounds
their L^p sum by the ℓ²-sum.

There is *no* decoupling theorem for a single arithmetic progression
or a Sidon set: decoupling requires curvature, and a Sidon set
`A ⊆ [N]` is a 1D object (one frequency, just `θ`). The "curvature"
is provided by the moment curve, not by `A`.

**For our problem:** Decoupling does not apply directly. One could
try to lift `A` into `(a, a²) ∈ [N] × [N²]` and use 2D decoupling for
the parabola, but the resulting estimate is equivalent (up to log
factors) to the Sidon condition — no new bipartite information.

### 1.3 Tao–Vu discrete restriction (2006)

Tao–Vu's work on the L² → Lᵖ restriction problem for sparse subsets
of `[N]` shows that if `‖f̂_A‖_p ≪ |A|^{1/2} N^{1/2 − 1/p}` then `A`
behaves "like a random" set. Sidon sets satisfy this with `p = 4`
optimally. But this is again a single-set statement.

### 1.4 Ortega–Prendiville (arXiv 2110.13447, 2021)

The cleanest modern Fourier-uniformity statement: *extremal* Sidon
sets `A ⊆ [N]` (i.e., `|A| ≥ √N − N^{1/4 + o(1)}`) have
`sup_{θ ≠ 0} |f̂_A(θ)| ≪ N^{5/12 + ε}` (and improvements: under
strict extremality the sup is `≪ N^{1/4 + ε}`).

This gives *per-half* rigidity for both `A_-` and `A_+` separately
under extremality. It was already exhausted in `op-application.md`:
it controls G1+G2 (within-half profile) but not G3 (the bipartite
gap).

## 2. Searches conducted (post-2015)

| Query | Findings |
|-------|----------|
| "decoupling Sidon" | No bipartite results. Decoupling = curvature, Sidon = 1D. |
| "restriction theorem Sidon set" | Single-set L⁴ identities; ε-removal for squares (Henriot, Hughes). |
| "Bourgain–Demeter Sidon" | No direct application; Vinogradov uses B_s[g] indirectly via the moment curve. |
| "bipartite Sidon Fourier" | Bi-Sidon (Ruzsa, Pach–Zakharov 2024) = additive+multiplicative, *not* bipartite. False friend. |
| "Tao–Vu Sidon discrete restriction" | Single-set L^p bounds. |
| "Wooley nested efficient congruencing" | Vinogradov-style; concerns the moment curve, not B₂ sets. |

The "Bi-Sidon" of Pach–Zakharov ([2409.03128](https://arxiv.org/abs/2409.03128))
is unrelated: it asks for subsets Sidon under both `+` and `×`, not a
bipartite splitting.

## 3. Why the angle fails structurally

The midpoint-split SAS problem has the following Fourier signature:

  `f̂_-(θ) + e(n*θ/2) · f̂_+(θ) − (cross-collisions at n*)` ≈ extremizer.

The "joint" constraint we want — `α + β < 1` — is an *interval-support*
statement: `A_-` lives in `[1, αN]`, `A_+` lives in `[(1−β)N, N]`. This
is a *physical-space* support constraint, not a Fourier-side curvature
or oscillation condition. Restriction/decoupling theorems convert
support information into Fourier information, but the support condition
"`A_-` and `A_+` lie in two specific intervals" already *is* the Fourier
condition (a modulation/phase factor `e(n*θ/2)`), so no new information
is extracted.

More precisely:
- Restriction: bounds `‖f̂‖_p` given the support of `f` on a curved set.
  Our supports `[1, αN]` and `[(1−β)N, N]` are flat intervals — zero
  curvature, no nontrivial restriction.
- Decoupling: needs curvature to gain. None present.
- Stein–Tomas: same as restriction.

The single piece of harmonic analysis that could in principle give a
joint constraint is a **bilinear / multilinear** restriction theorem
applied to the pair `(f_-, f_+)`. But all multilinear restriction
theorems (Bennett–Carbery–Tao 2006, Guth 2015) require *transversality*
between the supports. The Fourier supports of `f_-` and `f_+` are *both
the full circle T* — they are not transverse on any meaningful
manifold. So multilinear restriction also gives no improvement.

## 4. The decoupling-for-sumsets idea

One concrete idea worth recording: define
`g(θ) = f̂_-(θ) · f̂_+(θ) = Σ_v r_×(v) e(vθ)`
(the cross-pair generating function). SAS implies `r_×(v) ≤ 1` for
`v ≠ n*` and `r_×(n*) = k`. Then
`‖g‖_2^2 = Σ r_×(v)² = (LU − k) + k² = LU + k(k−1)`.

If a decoupling-like inequality gave
`‖g‖_2^2 ≪ N^{?} · (‖f̂_-‖_2 · ‖f̂_+‖_2)^{?}`,
that would couple `L`, `U`, `k`. But `‖f̂_±‖_2^2 = L, U` by Plancherel,
and `g = f̂_- · f̂_+` is just a pointwise product. The only meaningful
inequality is Cauchy–Schwarz:
`‖g‖_2^2 ≤ ‖f̂_-‖_4^2 · ‖f̂_+‖_4^2`,
which gives `LU + k(k−1) ≤ (2L² − L)^{1/2} (2U² − U)^{1/2} ≈ 2LU` —
vacuous (consistent with `k ≤ √(LU/2) ≈ √(N/4)`, which is exactly the
trivial bound).

## 5. Honest verdict

Restriction/decoupling tools, as developed through 2026, do *not*
provide a bipartite rigidity theorem for SAS sets. The technical
reason is that:

1. SAS gives an L^∞-minus-one-atom Fourier signature, while
   restriction/decoupling extract L^p (averaged) information.
2. The bipartite splitting condition is a physical-space support
   statement on flat intervals — no curvature, no gain from
   restriction theorems.
3. Bilinear/multilinear restriction needs transversality; our two
   halves share the same frequency space (no transversality).

This converges with the conclusions of the five previous attacks
(Attempts A–D2 in `below-sqrt2.md`): all per-half Fourier methods
exhaust at √2 because they cannot see the *joint* constraint.

**The path forward is not harmonic-analytic.** It is structural:
a Freiman-style rigidity theorem for SAS extremizers (cf. the
"Conjecture (Freiman-style rigidity for SAS)" in `below-sqrt2.md`).
Harmonic analysis can be a *tool* inside such a rigidity proof
(e.g., Ortega–Prendiville–style equidistribution per half), but it
cannot replace the structural input.

**Risk of a hidden win:** Bourgain–Demeter–Guth-style "discrete
decoupling at scale `N^{1/2}`" inequalities have *not* been
specifically applied to the bipartite SAS problem. A novel
adaptation might still yield something, but no published preprint
points in that direction. Estimated probability of a positive result
in this angle: **< 10%**.

## 6. References (key)

- Ortega–Prendiville, *Extremal Sidon sets are Fourier uniform*,
  arXiv:2110.13447 (2021/2023 JTNB). Per-half rigidity, exhausted.
- Bourgain–Demeter, *The proof of the ℓ² decoupling conjecture*,
  Annals of Math. 182 (2015). No bipartite application.
- Bourgain, *On Λ(p)-subsets of squares*, Israel J. Math. 67 (1989).
  Single-set discrete restriction.
- Pach–Zakharov, *Ruzsa's problem on Bi-Sidon sets*, arXiv:2409.03128.
  "Bi-Sidon" = additive+multiplicative, not bipartite (false friend).
- Henriot, *Restriction estimates of ε-removal type for kth-powers
  and paraboloids*, Math. Ann. 374 (2019). Discrete restriction
  techniques; single-set.
- Fraser–Rakhmonov, *L^p averages of the discrete Fourier transform*,
  arXiv:2510.13483 (2025). Sidon application is again single-set.
