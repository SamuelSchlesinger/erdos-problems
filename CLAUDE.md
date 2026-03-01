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
  ErdosStraus/           -- Problem 242: Erdős-Straus conjecture
    Statement.lean       -- Conjecture statement
    EvenCase.lean        -- Proof for even n
    Mod4Eq3.lean         -- Proof for n ≡ 3 (mod 4)
    Mod4Eq1.lean         -- Proof for n ≡ 1 (mod 4) subcases
    Main.lean            -- Combined results
  Common/                -- Shared lemmas (Egyptian fractions, etc.)
```

## Current Problem: #242 (Erdős-Straus)

For every n > 2, there exist distinct positive integers x < y < z such that
4/n = 1/x + 1/y + 1/z.

Status: OPEN. We are attempting a novel proof.
