# Algebraic Number Theory Attack on Bipartite SAS Rigidity

**Date:** 2026-05-22. Companion to `below-sqrt2.md` and `op-application.md`
(the precise diagnostic identifying *bipartite rigidity* — a joint
`(A_-, A_+)` constraint forcing `α + β < 1` — as the missing ingredient).

**Scope.** Can the algebraic-NT toolkit OpenAI used for the planar
unit-distance lower bound (Motifs M1–M6 in
`../openai-motifs-tier1/motifs/index.md`) be re-used to prove the
conjectured bipartite rigidity of SAS extremizers?

**Bottom line.** *Very unlikely.* All four angles in the prompt fail for
the same root reason: they produce or constrain *multiplicative* objects,
while bipartite rigidity is a purely *additive* assertion about integer
coordinates in `[1, N]`. The documented "clean negative transfer" for the
construction side
(`../openai-motifs-tier1/sidon-almost/motif-transfer.md`) carries over to
the rigidity side; the mismatch is *worse* here because rigidity asks not
just for the right cardinality but for a positional constraint.

A modest exception (§5): a 2D Minkowski-style argument in `ℤ × ℤ`
*could* express the bipartite constraint, but the relevant theorem is
elementary convex-body Minkowski; the algebraic-NT toolkit adds nothing.

---

## 1. The target

> **Bipartite Rigidity (BR).** There exist `α, β ≥ 0` with `α + β < 1`
> such that every SAS `A ⊆ {1, ..., N}` with `|A| ≥ (2/√3 + ε)·√N`
> satisfies `A_- ⊆ [1, αN]` and `A_+ ⊆ ((1−β)N, N]`.

Key features: **(F1)** joint, not per-half (`α = β = 1/2` would only give
`√2`); **(F2)** purely additive in `ℤ ∩ [1, N]`.

## 2. Angle 1 — CM embedding of SAS sets

**Pitch.** Reverse OpenAI's M1+M2: embed `A ↪ K = L(i)` so the SAS
hypothesis becomes a Galois-orbit constraint.

**Verdict: no.** Three blockers:

1. *No natural CM embedding.* `A ⊂ ℤ` has no multiplicative structure;
   any embedding `A → \mathcal{O}_K` is either trivial (`a ↦ a·1`, CM
   structure invisible) or auxiliary (`a ↦ a + ζ_p`, the SAS hypothesis
   becomes meaningless in `K`).

2. *Reflection symmetries don't match.* EF construction is involutive
   under `x ↦ N − x`; CM units are involutive under complex conjugation
   `c : K → K`. The two involutions live on different objects, no
   compatible embedding.

3. *Per-projection bound* (`cm-seed-construction.md` §2): every
   `ℚ`-linear projection of unit-norm CM elements lies in a bounded
   interval `[-2f, 2f]`, **independent of `N`**. So an SAS extremizer's
   image under any rational projection cannot span `[1, αN] ∪ ((1−β)N, N]`.

## 3. Angle 2 — S-unit equation at the exceptional value

**Pitch.** At `n*`, SAS has `k` representations `n* = a_i + b_i`. Apply
Evertse–Schlickewei finiteness for `x + y = n*` with `x, y` in a
finitely generated multiplicative subgroup.

**Verdict: no, same root cause.** The Evertse–Schlickewei theorem
([Evertse–Schlickewei–Schmidt 2002](https://www.jstor.org/stable/3062130))
bounds solutions in `(K^×)^2` ranging over a *multiplicative* group
`Γ ⊂ K^×` of finite rank: `≤ 2^{15(s+1)}` with `s = rank Γ`.

SAS's `a_i + b_i = n*` has `a_i, b_i` in an *additive* finite set
`A ⊂ ℤ`. `A` is not a finitely generated multiplicative subgroup of any
nontrivial number field. Exponentiating (`e^a + e^b = e^{n*}`) destroys
the integer structure SAS depends on.

The closest legitimate S-unit application is Evertse–Györy's
exponential-Diophantine work, which requires genuine multiplicative
variables; SAS has none.

## 4. Angle 4 — Class group pigeonhole

**Pitch.** The `2^m / h(K)` pigeonhole (M1) is the engine of OpenAI's
proof; attach `(A_-, A_+)` to a class group and re-apply.

**Verdict: no.** Class groups parametrize *ideals mod principal*. SAS is
a single integer set, not a system of `2^m` ideals. One could *force* an
analogue (attach an ideal `\mathfrak{P}_{(a,b)}` to each pair
`(a, b) ∈ A_- × A_+` with `a + b = n*`), but the resulting "relation
among pairs" would be ideal-product principality — a multiplicative
relation — while SAS demands a single additive equation `a + b = n*`.
Class pigeonholing is silent on additive structure.

## 5. Angle 3 — Lattice/Minkowski in `ℤ × ℤ` (partial salvage)

**Pitch.** Treat `(a, b) ∈ A_- × A_+ ⊂ ℤ²` as a 2D lattice problem.
Along the anti-diagonal `a + b = n*` there are `k` points; elsewhere
at most 1 per anti-diagonal.

**Verdict: lattice methods can express the constraint, but the relevant
theorem is elementary 2D Minkowski, not M5+M6.**

Concrete attempt:
- `S = A_- × A_+ ⊂ [1, αN] × [(1−β)N, N]`, `|S| = |A_-|·|A_+|`.
- SAS anti-diagonal: `|A_- + A_+| ≥ |S| − (k − 1)`.
- `A_- + A_+ ⊆ [(1−β)N + 1, (1+α)N]`, length `(α + β)N`.
- Hence `|A_-|·|A_+| ≤ (α + β)N + k`.

Combined with `|A_-|·|A_+| ≤ √(αβ)·N` (Sidon per-half):

  `√(αβ)·N ≤ (α + β)N + k`.

For `k = O(√N)`, this is *automatically satisfied* (LHS ≤ N/2,
RHS ≥ N for any `α + β ≥ 1/2`). **No bipartite constraint emerges.**

This is the same elementary collapse as in `below-sqrt2.md` and the
"1/4 slack at α = β = 1/2" of `op-application.md`. 2D Minkowski adds
nothing.

**M5 transferred?** M5's exponential gain requires `f → ∞` (number
field degree). In our 2D setting `f = 1`; the "torus averaging" is
trivial counting. **No exponential lift.**

## 6. Structural diagnosis

| Feature | OpenAI motifs | SAS bipartite rigidity |
|---|---|---|
| Operation | Multiplicative (norms, ideal products) | Additive (sums in ℤ) |
| Ambient | High-degree CM field, lattice in `ℂ^f` | `ℤ ⊂ ℝ`, interval `[1, N]` |
| Asymptotic parameter | Degree `f → ∞` | Cardinality `N → ∞` |

The OpenAI proof exploits all three (high `f` gives room for
class-pigeonhole, multiplicative norm-1 gives constraint, lattice
embedding gives output). BR negates all three: `f = 1`, additive, fixed
interval. Every motif degenerates.

**The "1/4 slack" obstruction is geometric, not statistical.**
(`density-profile-attack.md`.) At `α = β = 1/2` the value-disjointness
slack `1/4` arises because within-half sumsets cover only the bulk of
their range, not the endpoints — a *geometric* feature of integer
intervals. Algebraic-NT methods do not interact with the geometry of
`ℤ ∩ [1, N]` in a way that would close this slack.

## 7. Where could algebraic methods plausibly help?

- **Singer/Bose seeds via M4 + Dirichlet.** Lower-bound side only,
  already constant-tight at `2/√3`. No bearing on BR (BR is upper-bound).
- **Davenport/L-function on `A_- + A_+`?** Long shot with no clear
  technical foothold — cross-sumsets are combinatorial in `ℤ`, not
  attached to any modulus.

## 8. Recommendation

**Do not pursue algebraic-NT methods for SAS bipartite rigidity.** The
right toolkit is Fourier-analytic (Ortega–Prendiville's per-half Fourier
uniformity, Eberhard–Manners's positional rigidity conjecture, White's
autoconvolution uniqueness). The `op-application.md` diagnostic
identifies bipartite rigidity as the missing piece, and the relevant
near-misses (`rigidity-survey.md` §A) are uniformly Fourier-flavoured.

The algebraic-NT toolkit's only legitimate role in #864 remains the
Singer-seed lower bound, already optimal.

## Confidence

**Very unlikely** that any algebraic-NT method yields bipartite rigidity
for SAS. Negative transfer documented for construction side; rigidity
side inherits the same mismatch with no relieving factor.
