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

## Resurrection

Apply with `git apply research/wip-2026-05-23/PrimaryPseudoperfect-Examples.patch`,
move `AbcConditional.lean` back to `Erdos/ConsecutivePowerful/`, register it in
`Erdos.lean`, and fix the errors above.
