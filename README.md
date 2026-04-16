# Erdős Problems in Lean 4

Formal proofs of partial results for open [Erdős problems](https://www.erdosproblems.com/)
in Lean 4 with Mathlib. We are not just stating conjectures — we are proving
structural theorems, density bounds, and cross-problem connections.

## Problems

| # | Problem | Key Results |
|---|---------|-------------|
| [89](https://www.erdosproblems.com/89) | Distinct distances in the plane | Statement formalized; distance-set monotonicity, vanishing for sets of size at most one, positivity for sets of size at least two, and the trivial quadratic upper bound |
| [242](https://www.erdosproblems.com/242) | Erdős-Straus conjecture | All cases except primes p ≡ 1 (mod 24) |
| [282](https://www.erdosproblems.com/282) | Greedy Egyptian fractions with restricted denominators | Statement formalized; unique minimal greedy choice, monotone remainder bounds, one-step termination for every unit fraction `1/n` with `n ∈ A`, and in particular termination of every odd unit fraction on the odd numbers |
| [152](https://www.erdosproblems.com/152) | Isolated sums of Sidon sets | Value-truncation stability; fast-growth sequences have infinitely many isolated sums; explicit finite obstruction family with empty lower-isolated region |
| [156](https://www.erdosproblems.com/156) | Small maximal Sidon sets | Finite statement formalized; maximal extensions exist in every interval; every positive strong-gap prefix extends to a maximal set (in particular `{1,4,…,4^m}`); maximality forces elementary obstruction cover; direct cubic lower bounds `N ≤ |A| + |A|^2 + |A|^3` and `N ≤ 3|A|^3`; packaged existence with the coarse `N^{1/3}` lower bound |
| [864](https://www.erdosproblems.com/864) | Almost-Sidon sets with one exceptional sum | Statement formalized; structural midpoint split into two genuine Sidon halves; Erdős-Freud reflected-Sidon construction formalized; if `B ⊆ {1,…,⌊N/3⌋}` is Sidon then `B ∪ {N-b : b∈B}` is almost Sidon in `{1,…,N}` with cardinality `2|B|`, and every repeated two-sum is forced to be `N`; explicit `4^i` seed family packaged as size-`2(m+1)` examples |
| [313](https://www.erdosproblems.com/313) | Primary pseudoperfect numbers | Statement formalized; successor-prime extension; examples 2, 6, 42, 1806; every example > 2 is pseudoperfect |
| [364](https://www.erdosproblems.com/364) | Consecutive powerful triples | Statement formalized; no four consecutive powerful numbers; any hypothetical triple starts in residue classes `7`, `27`, or `35 mod 36`; verified no starts below `1000000` |
| [Erdős-Moser](https://en.wikipedia.org/wiki/Erdos-Moser_equation) | Power-sum Diophantine equation | `k=1` uniqueness, odd-exponent exclusion (`Odd k ∧ 1<k` gives no solutions), reduction of all non-classical cases to even branch (`Even k ∧ 10 ≤ k`), no solutions for `k=2..8`, modular obstructions (`m ≡ 0/3 mod 4`; odd `k` gives `m ≡ 0 mod 3` and `m ≡ 0/3 mod 12`; odd `k≥3` gives `m ≡ 0 mod 8` and `m ≡ 0 mod 24`; mod-5 split: `k ≡ 1 (mod 4)` gives `m ≡ 0/3 mod 5`, `k ≡ 3 (mod 4)` gives `m ≡ 0 mod 5`, `k ≡ 2 (mod 4)` gives `m ≡ 0 mod 5`; `k ≡ 2 (mod 6)` gives `m ≡ 0 mod 7`; `k ≡ 2 (mod 10)` gives `m ≡ 0 mod 11`; `k ≡ 2 (mod 12)` gives `m ≡ 0 mod 35`, `m ≡ 0 mod 13`, hence `m ≡ 0 mod 455`, and with mod-4 gives `m ≡ 0/35 mod 140` and `m ≡ 0/455 mod 1820`; `k ≡ 2 (mod 60)` gives `m ≡ 0 mod 5005`, and with mod-4 gives `m ≡ 0/15015 mod 20020`; with odd `k≥3`, this yields `m ≡ 0/48 mod 120` in the `k ≡ 1` branch and `m ≡ 0 mod 120` in the `k ≡ 3` branch), bounded certificate (`m≤150`,`k≤25`) |
| [302](https://www.erdosproblems.com/302) | Unit fraction triples | Cambie 5/8 lower bound, van Doorn 9/10 upper bound |
| [327](https://www.erdosproblems.com/327) | Unit fraction pairs | Master characterization `pair_n_cn_iff` |
| [301](https://www.erdosproblems.com/301) | Unit fraction sum-free sets | Upper half construction, bridge to #302, multiplier-fiber reduction, pseudoperfect/divisor obstruction bridge to #470 |
| [470](https://www.erdosproblems.com/470) | Weird numbers | Benkoski-Erdős, infinitude, Egyptian fraction bridge |
| [474](https://www.erdosproblems.com/474) | Pair-colorings of the plane on uncountable sets | Statement formalized; monotonicity under enlarging the ambient set, one-color case, and color-merging reduction from `l` colors to any smaller positive `k` |
| [893](https://www.erdosproblems.com/893) | Divisors of Mersenne numbers | Statement formalized; positivity of each divisor-count term, exact successor recurrence, monotonicity of partial sums, and the lower bound `f(n) ≥ n` |
| [950](https://www.erdosproblems.com/950) | Reciprocal sums over prime gaps | Statement formalized; nonnegativity, exact vanishing for `n = 0, 1, 2`, and the first positive lower bound coming from the prime `2` |

## Building

```sh
lake build
```

Requires Lean 4.27.0 and Mathlib. The project is maintained without `sorry`.

## Project Structure

```
Erdos/
  Common/                  -- Shared infrastructure (packing bounds, p-adic signatures)
  DistinctDistances/       -- #89: distinct distances determined by finite planar sets
  ErdosMoser/              -- Erdos-Moser equation: sum_{i=1}^{m-1} i^k = m^k
  ErdosStraus/             -- #242: 4/n = 1/x + 1/y + 1/z
  AlmostSidonSets/         -- #864: almost-Sidon sets with one exceptional sum
  ConsecutivePowerful/     -- #364: consecutive powerful triples
  GreedyEgyptian/          -- #282: restricted greedy Egyptian fractions
  MaximalSidonSets/        -- #156: small maximal Sidon subsets of {1, ..., N}
  MersenneDivisorSums/     -- #893: divisor sums over 2^k - 1
  PlanePairColorings/      -- #474: colorings of plane pairs on uncountable sets
  PrimaryPseudoperfect/    -- #313: sum of prime reciprocals equals 1 - 1/m
  PrimeGapHarmonic/        -- #950: reciprocal sums over prime gaps
  SidonSumsets/            -- #152: isolated sums in Sidon sumsets
  UnitFractionTriples/     -- #302: 1/a = 1/b + 1/c avoidance
  UnitFractionPairs/       -- #327: (a+b) | ab avoidance
  UnitFractionSets/        -- #301: 1/a = Σ 1/bᵢ avoidance
  WeirdNumbers/            -- #470: abundant but not pseudoperfect
```

Each problem directory follows the same progression: `Statement.lean`
formalizes definitions, subsequent files build up partial results, and
cross-problem connections live in dedicated bridge files (e.g.,
`EgyptianBridge.lean` connecting #470 with #301).

## Workflow

The project follows an iterative four-phase process described in
[WORKFLOW.md](WORKFLOW.md):

1. **Statement** — formalize the problem, cross-check with
   [erdosproblems.com](https://www.erdosproblems.com/)
2. **Known territory** — prove well-known cases to build infrastructure
3. **Novel attempt** — push beyond the literature
4. **Assessment** — document results and obstructions, then iterate or
   move on

Every theorem must pass the quality gate: no `sorry`, clean `lake build`,
doc-comments explaining the mathematics, and a proof structure a
mathematician can follow.

## Potentially Novel Results

Most of this project formalizes known results from the literature. A few
results may be new — see the
[Novelty Assessment](LITERATURE.md#novelty-assessment) in LITERATURE.md
for the full classification. Highlights:

- **Cambie 5/8 construction does NOT lift to sum-free sets** (#301 vs #302):
  the identity 1/15 = 1/36 + 1/45 + 1/60 sits inside the Cambie set,
  proving a structural gap between triple-free and sum-free avoidance.
- **Star neighborhood bounds** (17/18, 11/12 for #302): intermediate
  density bounds via a hitting-set argument on {2d, 3d, 4d, 6d, 12d},
  a different technique from van Doorn's S+T family approach.

## Documentation

- [LITERATURE.md](LITERATURE.md) — living document tracking papers,
  techniques tried and to-try, cross-cutting observations, novelty
  assessment, and a prioritized queue of next formalizations. This is
  where mathematical ideas are evaluated for feasibility before any Lean
  code is written.
- [REFERENCES.md](REFERENCES.md) — formal bibliography organized by
  problem number. Citation keys (e.g., `[BE74]`, `[Fr93]`) are used for
  traceability between the bibliography and the Lean source, where
  author names appear in doc-comments.
- [WORKFLOW.md](WORKFLOW.md) — the iterative problem-selection and proof
  process, including proof standards, the quality gate, and literature
  maintenance procedures.

## Proof Standards

1. No `sorry` — every proof is complete
2. No `native_decide` on unbounded domains
3. No custom axioms beyond Lean's kernel
4. Mathlib-compatible naming and tactic style
5. Reviewer-ready doc-comments on every theorem

## AI Assistance

This project is developed with the assistance of AI (Claude by Anthropic).
Problem selection, proof strategy, and all mathematical reasoning are
human-directed; Claude assists with Lean 4 formalization, tactic
engineering, and code generation. Every theorem is verified by the Lean
type-checker — the proofs are machine-checked regardless of how they were
authored.
