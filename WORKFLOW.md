# Workflow: Solving Erdős Problems in Lean 4

## Problem Selection Criteria

1. **Open** — the problem (or the specific case we target) is unsolved
2. **Concrete attack plan** — we have a specific mathematical idea to try
3. **Lean-amenable** — the relevant mathematical objects exist in Mathlib,
   or can be defined cleanly without massive library extensions

## Iterative Process

### Phase 1: Statement
- Formalize the problem statement in Lean 4
- Verify it matches the statement on erdosproblems.com
- Cross-reference with google-deepmind/formal-conjectures if available

### Phase 2: Known Territory
- Prove the "easy" cases that are well-known in the literature
- This builds infrastructure (helper lemmas, definitions) we'll need later
- Also serves as a sanity check on our formalization

### Phase 3: Novel Attempt
- Identify the boundary of what's known
- Formalize our attack strategy as intermediate lemmas
- Attempt the proof, iterating on the mathematical ideas
- If stuck, consider: alternative parametrizations, reductions, computational search

### Phase 4: Assessment
- If we proved something new: clean up, document, prepare for review
- If stuck: document what we tried, what obstructions we hit, and either
  push further or move to a different problem

## Quality Gate

Before marking any theorem as "done":
- [ ] No `sorry` anywhere in the file or its dependencies
- [ ] `lake build` succeeds with no warnings
- [ ] Doc-comments explain the mathematical content
- [ ] A human can follow the proof structure
