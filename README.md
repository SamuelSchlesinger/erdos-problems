# Erdős Problems in Lean 4

Formal proofs of partial results for open [Erdős problems](https://www.erdosproblems.com/)
in Lean 4 with Mathlib. We are not just stating conjectures — we are proving
structural theorems, density bounds, and cross-problem connections.

## Problems

| # | Problem | Key Results |
|---|---------|-------------|
| [242](https://www.erdosproblems.com/242) | Erdős-Straus conjecture | All cases except primes p ≡ 1 (mod 24) |
| [Erdős-Moser](https://en.wikipedia.org/wiki/Erdos-Moser_equation) | Power-sum Diophantine equation | `k=1` uniqueness, no solutions for `k=2..7`, modular obstructions (`m ≡ 0/3 mod 4`; odd `k` gives `m ≡ 0 mod 3` and `m ≡ 0/3 mod 12`), bounded certificate (`m≤150`,`k≤25`) |
| [302](https://www.erdosproblems.com/302) | Unit fraction triples | Cambie 5/8 lower bound, van Doorn 9/10 upper bound |
| [327](https://www.erdosproblems.com/327) | Unit fraction pairs | Master characterization `pair_n_cn_iff` |
| [301](https://www.erdosproblems.com/301) | Unit fraction sum-free sets | Upper half construction, bridge to #302 |
| [470](https://www.erdosproblems.com/470) | Weird numbers | Benkoski-Erdős, infinitude, Egyptian fraction bridge |

## Building

```sh
lake build
```

Requires Lean 4.28.0 and Mathlib. All 8000+ compilation jobs succeed
with zero `sorry`.

## Project Structure

```
Erdos/
  Common/                  -- Shared infrastructure (packing bounds, p-adic signatures)
  ErdosMoser/              -- Erdos-Moser equation: sum_{i=1}^{m-1} i^k = m^k
  ErdosStraus/             -- #242: 4/n = 1/x + 1/y + 1/z
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
