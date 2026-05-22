# Entropy / Information-Theoretic Attack on the SAS √2 Barrier

**Date: 2026-05-22.** Research scout note. Companion to `below-sqrt2.md`,
`pikhurko-adaptation.md`, `autoconvolution-attack.md`, `density-profile-attack.md`,
`op-application.md`.

**Verdict at a glance: NO.** Entropy methods are structurally mismatched to
the SAS hypothesis for the same reason L² autoconvolution methods are
(Attempt B). Entropy is averaged log-information; SAS strength lives in a
single atom. The mismatch is even sharper than L²: entropy is convex and
concentrates information across the support, blurring the n* singularity by
construction. Sections below give the prior art, the inequalities we tried,
and the precise diagnostic.

## 1. Prior entropic work surveyed

| Source | Topic | Relevance to SAS |
|---|---|---|
| Tao (2010, *Sumset and inverse sumset theory for Shannon entropy*) | Establishes entropy↔cardinality dictionary: H(X) ↔ log|A|, sumset inequalities have entropy analogues. | Foundational. Encodes the same information as cardinality bounds; cannot extract SAS-specific content. |
| Tao (2009 blog, "Entropy Plünnecke–Ruzsa") | H(X+Y₁+…+Y_m) ≤ H(X) + Σ log K_i when each H(X+Y_i) ≤ H(X) + log K_i. Submodularity: H(X+Y+Z) + H(Y) ≤ H(X+Y) + H(Y+Z). | Submodularity is the only joint constraint on triples, but at m=2 it degenerates. |
| Kontoyiannis–Madiman (2014, IEEE Trans. Inf. Theory) | Differential-entropy versions of Ruzsa, Plünnecke, BSG. | Continuous analogue; no extra structural information for discrete SAS. |
| Goh (arXiv:2406.18798, 2024) | "Entropic additive energy" `Δ(X,Y) := 2H(X,Y) − H(X+Y)`. Small-Δ regime corresponds to Sidon-like behaviour. | Closest to our setting. For Sidon: H(X+Y) ≈ H(X) + H(Y), so Δ ≈ 0 and the inequalities saturate, giving no slack. |
| Madiman (CUHK 2013 slides; Madiman–Wang) | Upper bounds for entropies of sums; entropic doubling constant. | Establishes `H(X+X') − H(X) ≥ ½ log K` for doubling K; for Sidon, this just says K = |A|/2. |
| Gowers Lent 2025 lecture notes (Naylor scribe) | Shearer, Bregman, entropy in additive combinatorics. | Pedagogical; no result specifically targeting B₂[g] with g→1⁺. |
| Razborov-style entropic flag algebra | Asymptotic graph density. | Wrong category. No mechanism for the additive structure of SAS. |
| Tao (2022 blog, "Notes on inverse theorem entropy") | ε-entropy of seminorms for inverse theorems. | Different ε-entropy. No SAS application. |

**Bottom line of survey:** There is NO prior work on entropic bounds for
B₂[g] sets in the regime `g → 1⁺`. The whole field of entropic additive
combinatorics is uniformly **dual to cardinality estimates** — every
entropy inequality has a set-cardinality shadow proved by Ruzsa/Plünnecke
and vice versa. So entropy cannot extract MORE information than the
corresponding cardinality argument (which we have already exhausted in
Attempts A, B, C).

## 2. Tao-style entropic argument we attempted

Let `X ∼ Uniform(A_-)`, `Y ∼ Uniform(A_+)`, independent. Then:

- `H(X) = log L`, `H(Y) = log U` where `L = |A_-|`, `U = |A_+|`.
- The cross sumset has cardinality `|A_- + A_+| = LU − (k − 1)` (SAS forces
  cross-sums distinct except at `n*` with multiplicity `k`).
- Therefore `H(X + Y) ≤ log(LU − (k − 1)) = log L + log U + log(1 − (k−1)/(LU))`.

The entropic additive energy is
```
Δ_cross := H(X) + H(Y) − H(X + Y) ≥ −log(1 − (k − 1)/(LU))
                                  ≈ (k − 1)/(LU)   for small k/(LU).
```
This says Δ_cross is **tiny** — at most O(1/√N) for `k = O(√N)` and
`LU = Θ(N)`. The cross-pair behaves like an honest Sidon pair in the
entropy sense: SAS contributes a vanishing correction.

**This is precisely the L² problem again.** Entropy averages
log-multiplicity over the sumset; the single bad atom contributes only
`(k − 1) · log k / |A_- + A_+|` to the entropy deficit, which is `O(log
N / √N) → 0`. The SAS hypothesis becomes invisible in the entropic
inequality.

## 3. Submodularity and chain-rule attempts

Define a third random variable `Z = X + Y`. Submodularity gives
```
H(X + Y + Z) + H(Y) ≤ H(X + Y) + H(Y + Z),
```
but with `Z := X + Y` this collapses to `H(2X + 2Y) + H(Y) ≤ H(X+Y) +
H(X + 2Y)`, which involves multiplicative-2 dilations of `A_-` — those
dilations are not constrained by SAS at all. **Submodularity fails to
yield a joint (L, U) bound.**

Alternative: take `Z` independent of `X, Y` and uniform on a structured
set (e.g., `A_- ∪ A_+`). Then the inequality holds but only mixes the
two halves, again leaving no joint multiplicity constraint at `n*`.

The chain-rule `H(X, Y) = H(X) + H(Y | X)` for independent `(X, Y)` just
gives `H(X, Y) = log L + log U` — pure cardinality.

## 4. Why entropic methods cannot break √2 here

The diagnostic is structurally identical to attempt B but quantitatively
sharper:

**(E1) L¹/L² mismatch.** Entropy is `−Σ p log p`; the SAS feature is a
single atom of mass `k/(LU) = O(1/√N)`. Its entropy contribution is
`(k/(LU)) · log(LU/k) = O((log N)/√N) → 0`. Entropy doesn't see it.

**(E2) Submodular slack saturates at Sidon.** For independent uniform X,
Y on `A_±` (each Sidon), `H(X+Y) = log(LU − O(k)) ≈ log L + log U`. The
entropy chain-rule inequality `H(X+Y) ≤ H(X) + H(Y)` is essentially
tight. There is no slack to exploit a joint (L,U) bound.

**(E3) Goh's Δ is too small.** Even the most modern entropic additive
energy doesn't separate "Sidon" from "SAS with bad atom of size √N":
both have Δ = O(1/√N · log N). The two are indistinguishable
information-theoretically.

**(E4) Equivalence to cardinality.** Tao's dictionary is *exact*: every
entropy inequality on independent uniform random variables on sets is
a cardinality inequality on the underlying sets. We already exhausted
cardinality inequalities in Attempts A and B. Hence entropy cannot win
where cardinality lost.

## 5. The single non-equivalent corner — and why it still fails

Entropy CAN be slightly more powerful than cardinality when we use
**non-uniform** distributions. For instance, take X distributed on
`A_-` with extra weight near the n*/2 boundary (matching the
EF-construction concentration). Then `H(X) < log L`, but `H(X + Y)`
might receive a corresponding boost from concentrated overlap.

We checked: this only ever loses, because non-uniform X has H(X) ≤
log L by Jensen, and the SAS constraint on H(X+Y) is the same
cardinality bound regardless of the distribution shape. Any
non-uniformity hurts strictly. **No improvement.**

## 6. Honest verdict

**Maybe-no, leaning hard no.** Entropy methods would give a NEW bound
only if SAS had a **non-cardinality-shadow** consequence (e.g., a
genuinely information-theoretic structural constraint that doesn't
follow from sumset-cardinality estimates). The SAS hypothesis is a
pointwise L^∞ constraint on the representation function `r_A(n)`. It
cannot be reformulated as a moment or entropy statement without losing
information.

The bipartite rigidity we need — `α + β < 1` for the half-densities
of `A_±` — is a **geometric** constraint about set placement, not an
information-theoretic one. The closest entropic statement would be
something like `H(X) + H(Y) − H(X+Y) ≥ c` for some bipartite constant
`c`, but every such Δ-style inequality vanishes for Sidon-like
configurations.

**Sketch of what WOULD work entropically (and why we don't have it):**
A "joint Sidon defect" inequality of the form
```
H(X + Y) ≥ H(X) + H(Y) − f(joint placement of A_±)
```
where `f(.)` is small only when `(A_-, A_+)` are geometrically
compatible (the EF configuration). No such inequality is known, and
the obstruction is the same as for cardinality: pointwise placement is
not visible to averaged quantities. This is consistent with the
meta-finding in `below-sqrt2.md` §"Three negative attacks" — all
*averaging-style* attacks fail for the same structural reason.

## 7. What entropy methods could help with (negative directions)

Entropy methods are a good fit for problems that ALREADY have an
energy/L² flavour, or for proving inverse theorems where one wants to
trade compactness for structure. SAS rigidity is neither: it is a
pointwise-extremal additive geometry problem. So entropy methods are
correctly diagnosed as **the wrong tool** here. The right tools (per
the convergent diagnosis in `below-sqrt2.md`) involve Freiman-style
rigidity / inverse theorems for additive sets — which are themselves
notoriously hard.

## 8. Recommendation

Add entropy methods to the list of **Fourth Attempt: closed negative.**
The diagnosis matches B (L² autoconvolution) and is now confirmed by
the survey of all known entropic Sidon-style inequalities.

No further entropy-method work on this problem is recommended. The
genuine direction remains: Freiman-style structural rigidity for SAS
extremizers, as outlined at the end of `below-sqrt2.md`.

## References

- Tao, T. (2010). *Sumset and inverse sumset theory for Shannon entropy*.
  Combin. Probab. Comput. 19. arXiv:0906.4387.
- Tao, T. (2009 blog). "An entropy Plünnecke–Ruzsa inequality."
  https://terrytao.wordpress.com/2009/10/27/
- Kontoyiannis, I.; Madiman, M. (2014). "Sumset and inverse sumset
  inequalities for differential entropy." IEEE Trans. Inf. Theory.
  arXiv:1206.0489.
- Goh, M.K. (2024). *On an entropic analogue of additive energy*.
  arXiv:2406.18798.
- Madiman, M.; Marcus, A.; Tetali, P. (2012). "Entropy and set
  cardinality inequalities."
- Gowers, W.T. (2025). *Entropy Methods in Combinatorics*. Lecture
  notes (Naylor scribe), Lent 2025.
- Zhao, Y. (2024). *Probabilistic Methods in Combinatorics*, Ch. 10
  (Entropy). https://yufeizhao.com/pm/10.pdf

| Date | Event |
|------|-------|
| 2026-05-22 | Entropy-method survey + diagnosis: negative. No bipartite rigidity available. |
