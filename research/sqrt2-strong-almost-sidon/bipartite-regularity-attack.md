# Bipartite Regularity Attack on Strong Almost-Sidon

**Scout note, 2026-05-22.** Companion to `below-sqrt2.md`. Investigates
whether Szemerédi-style or sparse regularity for bipartite graphs can
force a below-`√2` upper bound for SAS sets.

## Setup

After the midpoint split `A = A_- ⊔ A_+` with `A_- ⊆ [1, n*/2]`,
`A_+ ⊆ (n*/2, N]` (assume `n* = N` for the worst case), define the
**SAS collision graph** `G = (A_-, A_+; E)`:

  `(a, b) ∈ E ⟺ a + b ≠ n*` AND (`a + b ∈ A_- + A_-` OR `a + b ∈ A_+ + A_+`).

That is, `(a,b)` is an edge iff the cross-sum `a + b` coincides with a
within-half sum value somewhere, and it is not the legal exception
axis `n*`.

## Key observation: G is edge-free (almost)

By SAS, every pair-sum `≠ n*` has multiplicity exactly 1. So any value
`v ≠ n*` is hit by at most one pair (within or cross). Consequently:

> **Lemma 1.** `G` has NO edges. The only nontrivial bipartite
> structure is the "n*-graph" `G_* := {(a, b) ∈ A_- × A_+ : a + b = n*}`,
> a perfect matching on a subset of `A_- ∪ A_+`.

So the SAS condition is *exactly* "the cross-collision graph `G` is
empty, except for the matching `G_*`." This is a very stringent
combinatorial constraint but it's expressed as edge-absence, not as
edge-density.

## Szemerédi regularity application — vacuous

Szemerédi's regularity lemma partitions `V(G)` into ε-regular cells and
extracts a reduced graph whose densities approximate `G`. Two issues
make this useless here:

1. **`G` has zero density.** With `|A_-|, |A_+| = O(√N)` and `|E(G)| = 0`,
   the bipartite density `d(A_-, A_+) = 0`. Every regularity partition is
   trivially ε-regular with all densities `0`. The reduced graph is
   empty. No information extracted.

2. **`G_*` is a matching, not a graph with positive density.** Even if
   we re-target regularity at `G_*`, the density is `|G_*| / (|A_-| · |A_+|) ≤
   1/min(|A_-|, |A_+|) = O(1/√N)`, far below any `ε > 0` threshold.

Classical Szemerédi regularity is fundamentally a **dense-graph tool**
(densities of order Ω(1)); SAS lives in the sparse regime where it has
nothing to say.

## Sparse regularity (Conlon–Fox–Sudakov / Kohayakawa–Rödl)

Sparse regularity rescales densities by a global parameter `p` (the
"ambient density"), and works for graphs with `|E| = Θ(p · n²)` when
`p ≫ n^{-c}`. To apply:

- Set ambient density `p` = density of `G` viewed inside the *cross-sum
  collision pattern*. Even loading `G_*` (the matching) plus `G` (the
  collisions, which is empty), total `|E| / (|A_-| |A_+|) = O(1/√N)`.
- Sparse regularity requires `p^{-1} = O(n^c)` for some `c < 1`. Here
  `n = √N` and `p^{-1} = √N`, so `c = 1`. We sit exactly at the
  **threshold** where sparse regularity is conjectured but not known to
  give useful information.

**Conclusion.** Sparse regularity (Conlon–Fox 2014, *Combinatorica*)
gives counting lemmas only for `p ≫ n^{-1/Δ}` for `Δ`-bounded subgraph
counts. For matchings (Δ = 1) the threshold is `p ≫ n^{-1}`, exactly
our regime — borderline. Even when applicable, the conclusion is a
counting statement (number of subgraphs) not a *location* or *size*
statement on `A_±`. We get no help.

## Bipartite Plünnecke–Ruzsa

Plünnecke–Ruzsa: `|A_- + A_+| ≤ K · |A_-|` implies `|n·A_- − m·A_+| ≤
K^{n+m} · |A_-|`. Apply to SAS:

- `|A_- + A_+|` = number of distinct cross-sums. By SAS, all cross-sums
  are distinct (except the matching `G_*` collapsing onto `n*`). So
  `|A_- + A_+| = |A_-| · |A_+| − (|G_*| − 1) ≥ |A_-||A_+| - |A_-|`.
- `K = |A_- + A_+| / |A_-| ≥ |A_+| − 1`.

With `|A_+| ~ √N`, the doubling constant `K ~ √N` is HUGE. Plünnecke
output `|n A_- − m A_+| ≤ K^{n+m} |A_-|` becomes `≤ N^{(n+m)/2} √N`,
which is vacuous (the ambient interval has size `O(N)`).

**Plünnecke is the wrong tool: it controls `K`-doubling sets; SAS sets
have maximally *anti*-doubling cross-sums (`K ≈ √N`, not `K = O(1)`).**

## Bipartite expansion / Zarankiewicz

Could `G_*` (a matching of size `k`) be forced to be small? Zarankiewicz
`z(m, n; 2, 2)` bounds `K_{2,2}`-free bipartite graphs; with no edges
this is automatic. The matching `G_*` is `K_{2,2}`-free trivially, so
Zarankiewicz `≤ m + n` is vacuous (`k ≤ |A_-| + |A_+| ~ 2√N`).

## Why the bipartite framing fails

The SAS condition translates to "bipartite graph `G` is empty except for
a matching." The information content is **purely structural** — there
ARE no edges to count, regularize, or expand. All graph-theoretic
machinery for bipartite graphs counts/regularizes edges; with zero
edges these tools yield zero information.

The matching `G_*` itself is constrained:
- `|G_*| = k`, the multiplicity at `n*`.
- `2k ≤ |A_-| + |A_+|` (each matched pair uses one vertex from each side).

Both already-known facts. Bipartite regularity tells us nothing new.

## The structural takeaway

Bipartite regularity reproduces — at best — the **edge-counting**
constraint `L · U − (k − 1) ≤ N`, which is the same vacuous inequality
diagnosed in `below-sqrt2.md`. The location-sensitive structure (within-
sumsets and cross-sumsets share a *range overlap*; SAS forces value-
disjointness in that overlap) is invisible to bipartite graph theory,
which only sees `(A_-, A_+, E)` and not the ambient interval `[1, N]`.

This is the **twelfth attack** to fail with the same diagnosis: SAS
rigidity requires a *positional* / *value-level* tool, not a
*combinatorial* / *cardinality-level* one. Bipartite regularity is
firmly in the cardinality camp.

## Conclusion

Bipartite regularity (Szemerédi, sparse, Frieze–Kannan), bipartite
Plünnecke–Ruzsa, and Zarankiewicz all fail to give below-`√2` for SAS,
for the same root reason: they count edges or measure densities, but
the SAS edge set (in the natural collision graph) is empty by
hypothesis, and the auxiliary matching `G_*` is already captured by
elementary counting. None of these tools sees the ambient interval
structure where the `2/√3` rigidity lives.

**Verdict: bipartite regularity is not a viable attack route.** Logged
as attack #12 on the meta-obstruction list. Genuine progress still
requires a positional Freiman-style rigidity theorem (cf. main note).
