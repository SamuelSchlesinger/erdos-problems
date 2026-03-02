# Erdős Problems in Lean 4

## Project Goal

Formalize and **prove** open Erdős problems (or novel partial results) in Lean 4
with Mathlib. We are not just stating conjectures — we are attempting to solve them.

## Proof Standards

Every theorem in this project must satisfy:

1. **No `sorry`** — every proof must be complete
2. **No `native_decide` on unbounded domains** — `native_decide` is acceptable only
   for finite, small computations (e.g., checking a specific numeric identity)
3. **No `Decidable.decide` abuse** — don't use decidability instances to smuggle in
   unverified computation
4. **No axioms beyond Lean's core** — `Classical.choice`, `propext`, `Quot.sound`,
   and function extensionality are fine (they're in Lean's kernel). Don't add custom
   axioms.
5. **Mathlib-compatible style** — follow Mathlib naming conventions and tactic style
6. **Reviewer-ready** — a mathematician should be able to read the Lean proof and
   reconstruct a valid paper proof from it. Use doc-comments to explain the
   mathematical idea behind each theorem.

## Workflow

See WORKFLOW.md for the iterative problem-selection and proof process.

## Structure

```
Erdos/
  Common/                -- Shared infrastructure (packing bounds, p-adic signatures)
  ErdosStraus/           -- #242: Erdős-Straus conjecture (4/n = 1/x + 1/y + 1/z)
  UnitFractionTriples/   -- #302: 1/a = 1/b + 1/c avoidance (density bounds)
  UnitFractionPairs/     -- #327: (a+b) | ab avoidance (master characterization)
  UnitFractionSets/      -- #301: 1/a = Σ 1/bᵢ avoidance (bridge to #302)
  WeirdNumbers/          -- #470: abundant but not pseudoperfect
```

Each problem directory follows the same progression: `Statement.lean` formalizes
definitions, subsequent files build up partial results, and cross-problem
connections live in dedicated bridge files.
