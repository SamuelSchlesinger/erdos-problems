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

## Golfing & verification lessons

When simplifying/golfing proofs, verification gaps have bitten us — follow these:

1. **`lake env lean <file>` and the LSP do NOT run the `linter.style.longLine`
   (100-char) style linter.** That linter is set in the lakefile's leanOptions and
   fires only during a full `lake build`. So collapsing `:= by exact <term>` onto one
   line can silently push it past 100 chars and pass per-file checks while failing the
   real build.
2. **Always finish an edit/golf pass with a full `lake build`, capturing the COMPLETE
   log** — do not pipe through `tail` (it truncates and hides warnings). Redirect to a
   file and grep it.
3. **Before trusting per-file checks, scan the diff for added long lines.** For each
   `+` line in `git diff --unified=0`, flag `len(body) > 100` (unicode-aware). This
   catches longLine regressions across all files at once.
4. **Fix a longLine regression by breaking after `:=`** and putting the proof term on
   the next indented line — this keeps the golf (no `by exact`) while staying ≤100.
5. **Distinguish new from pre-existing warnings:** a warning is only a regression if its
   line is in the diff. Warnings on files untouched by the pass are pre-existing.
6. **Dropping `:= by exact t` → `:= t` can trigger the `unusedVariables` linter** when
   the term contains an unused lambda binder (e.g. `fun p hp =>` with `p` unused), which
   the surrounding tactic block had suppressed. `lake env lean` *does* catch this one —
   revert such collapses (or underscore-prefix the binder).
7. **`rw [h]; exact x` → `rwa [h]` only when `x` is a bare local hypothesis** — applied
   lemmas, projections, and anonymous constructors break `rwa`'s trailing `assumption`.

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
