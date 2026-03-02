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

### Phase 5: Literature & References

After proving a new result, maintain the project's documentation:

1. **Cite sources in doc-comments** — use author names inline (e.g.,
   "Benkoski-Erdős", "Cambie", "van Doorn") matching REFERENCES.md entries.
   File-level headers use `Reference: URL` (singular). See existing files
   for the conventions.
2. **Update REFERENCES.md** — if the proof relies on a paper or contribution
   not already listed, add a `[KEY]` entry in the appropriate problem section.
3. **Update LITERATURE.md** — mark the result as DONE in the active queue
   and add it to the completed table.
4. **Classify novelty** — add the result to the Novelty Assessment section
   of LITERATURE.md. Is it a formalization of a known result, or potentially
   new? If uncertain, mark it "Possibly novel" and note what literature
   search was done.
5. **Reclassify when needed** — if a result previously marked "Novel" or
   "Possibly novel" is later found in the literature, move it to "Known"
   and add the reference.

## Quality Gate

Before marking any theorem as "done":
- [ ] No `sorry` anywhere in the file or its dependencies
- [ ] `lake build` succeeds with no errors
- [ ] **Linter clean** — no warnings from `lake build` in modified files.
  Common fixes: `simp` → `simp only [...]`, unused variables → prefix with `_`,
  `native_decide` → only for small finite computations (and acknowledge the warning).
- [ ] Doc-comments explain the mathematical content
- [ ] A human can follow the proof structure
- [ ] Sources are cited in doc-comments and REFERENCES.md
- [ ] Result is classified in LITERATURE.md (novelty assessment)
