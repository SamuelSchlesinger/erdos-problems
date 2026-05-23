# WIP attempts that did not build (2026-05-23)

These were in the working tree at session shutdown but had build errors. They
are preserved here for later repair.

## `AbcConditional.lean`

Conditional finiteness of consecutive powerful triples assuming abc. 468 lines.
Errors at build time:

- L76 type mismatch
- L83 unsolved goals
- L97–99 unexpected syntax (likely a misplaced `from`)
- L179 stuck typeclass instance problem
- L288, L290, L292 unknown constant `UniqueFactorizationMonoid.Nat.radical_pos`
  (the correct name in Mathlib is probably `radical_pos` without the
  `UniqueFactorizationMonoid.Nat.` prefix)
- L308, L313 "no goals to be solved"

The decomposition `powerful_iff_eq_square_mul_cube` and `radical_sq_dvd_of_powerful`
look like the natural targets to land first.

## `PrimaryPseudoperfect-Examples.patch`

87-line patch adding examples to `Erdos/PrimaryPseudoperfect/Examples.lean`.
Errors at L133:48 and L155:49 (unsolved goals — likely arithmetic verification
of a reciprocal sum that needs `norm_num`-style closure or a missing case).

## `MaximalSidon-T0-broken.patch`

244-line attempt at the T0 sharper cubic bound for problem #156
(`midpoint_obstruction_count_bound`, `sumDiff_obstruction_count_bound`,
`obstruction_cover_implies_sharper_bound`). Build fails with ~8 errors
beginning at L71 (application type mismatch), L120 (unsolved goals),
L166–171 (more type mismatches in what looks like a `⟨...⟩` for `Eq.refl`),
and similar lower-down. Likely needs the existing `IsSidonFinset` API
re-traced — the patch author was approximating signatures that don't quite
match.

## `AlmostSidon-SidonInterval-broken.lean`

327-line attempt to formalise the Lindström / KST Sidon-interval bound
`|A| ≤ (1 + ε)√L` for problem #864. Build fails with 10+ errors clustered
around L66–127: repeated `rcases` failures on `Quot.lift` / `Multiset`
arguments, several `simp made no progress`, and several malformed
`⟨...⟩` notations. The agent appears to have mis-typed the project's
`IsSidon` predicate (probably wrote it over a `Multiset` when the project
uses a `Finset`-pair characterisation). Needs a re-read of the project's
own `IsSidon` definition before the proofs will type-check.

## Resurrection

Apply with `git apply research/wip-2026-05-23/PrimaryPseudoperfect-Examples.patch`,
move `AbcConditional.lean` back to `Erdos/ConsecutivePowerful/`, register it in
`Erdos.lean`, and fix the errors above.
