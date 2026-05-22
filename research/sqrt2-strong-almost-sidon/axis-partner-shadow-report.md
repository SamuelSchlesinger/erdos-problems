# Axis-Partner Shadow Lemma

**Date:** 2026-05-22.
**Status:** Formalized and machine-checked in
`Erdos/AlmostSidonSets/Maximality.lean`.

## Goal

Start the local-replacement attack suggested by the R4 characterization:
if an extremal strong almost-Sidon set has an unpaired element `x`, then its
missing reflection `y = n* - x` should be blocked by a concrete local
obstruction. The hope is that these blockers eventually overconstrain any
near-extremizer with extras.

## New definition

```lean
def IsMaximalAlmostSidonInInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  AlmostSidonInInterval A N ∧
    ∀ x ∈ ground N, x ∉ A → ¬ AlmostSidonFinset (insert x A)
```

This is the direct analogue of maximal Sidon-ness, but for the strong
almost-Sidon predicate in `{1, ..., N}`.

The file also defines cardinality extremality and proves the bridge:

```lean
theorem IsCardinalityMaximalAlmostSidonInInterval.isMaximal
```

So the shadow lemma applies to actual extremizers of `f(N)`, not merely to
sets that are locally maximal under insertion.

## Main lemma

For a maximal almost-Sidon set `A` with existing exception `nstar`, every
missing point `y ∈ {1, ..., N} \ A` has an off-axis shadow:

```lean
theorem maximal_missing_point_has_shadow
    {A : Finset ℕ} {N nstar y : ℕ}
    (hmax : IsMaximalAlmostSidonInInterval A N)
    (h_exception : HasTwoSumReprs A nstar)
    (hyN : y ∈ ground N) (hyA : y ∉ A) :
    (∃ b ∈ A, ∃ c ∈ A, 2 * y = b + c ∧ 2 * y ≠ nstar) ∨
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, y + a = b + c ∧ y + a ≠ nstar
```

The specialization

```lean
theorem maximal_missing_reflection_has_shadow
```

applies this to a missing reflection `y = nstar - x`.

The same content is also packaged in set-valued form:

```lean
def insertionShadowFinset (A : Finset ℕ) (nstar y : ℕ) : Finset ℕ

theorem maximal_missing_point_shadow_nonempty
theorem maximal_missing_reflection_shadow_nonempty
theorem cardinalityMaximal_missing_reflection_shadow_nonempty
```

Here `insertionShadowFinset A nstar y` is
`({2y} ∪ (y + A)) ∩ ((A + A) \ {nstar})`.

## Interpretation

If maximality blocks insertion of `y`, then insertion must create a new
repeated sum at some value different from the original exception. Since `A`
was already almost-Sidon, that new off-axis collision cannot be entirely old.
It also cannot use `y` on both sides, because two sorted pairs with the same
sum and a common distinguished element are equal. Thus one side is an old
pair from `A`, while the new side is either:

1. the self-pair `y + y`, or
2. a translate `y + a` with `a ∈ A`.

This is the first reusable formal version of the "axis-partner shadow":
a missing reflection must lie in the translate-shadow of the old pair-sum
set, away from the exception axis.

## What It Buys

This does **not** close the `√2 → 2/√3` gap by itself. It converts the
unknown "why is `n* - x` absent?" into a concrete certificate:

`insertionShadowFinset A nstar y` is nonempty, i.e.
`{2y} ∪ (y + A)` intersects `(A + A) \ {n*}`.

That is position-sensitive in a way the earlier energy/counting attacks were
not. The next possible step is to count shadows for many missing reflections
and show they cannot all be distinct or consistently placed in a near-EF
configuration.

## Follow-up Formal Lemmas

The same file now also formalizes the first two refinements of the shadow
certificate.

### Self-shadow descent

For extras, define the paired-element set by `pairElements A nstar` as in R4.
If `x ∈ A` is extra and `y` is its missing reflection (`x + y = nstar`), then
a self-shadow blocker `b + c = 2y` cannot have both endpoints paired:

```lean
theorem selfShadow_forces_extra_endpoint
```

The proof reflects `(b, c)` across the exception axis. If both endpoints were
paired, the reflected pair would be an old representation of `2x`, colliding
off-axis with `(x, x)`. R3 forces the reflected pair to equal `(x, x)`, hence
`b = c = y`, contradicting `y ∉ A`.

The useful descent corollary is:

```lean
theorem selfShadow_highExtra_descends
theorem leastExtra_no_high_selfShadow
```

So the least extra in the high region `2y < x` cannot be blocked by the
self-shadow branch.

### Translate-shadow crowding

The translate branch is packaged as a sorted witness:

```lean
def TranslateShadow (A : Finset ℕ) (nstar y a b c : ℕ) : Prop
```

and R3 gives the core injectivity statement:

```lean
theorem translateShadow_same_value_forces_same_oldPair
```

Two translate shadows with the same value must hit the same old sorted pair.
For missing reflections this yields:

```lean
theorem reflectionTranslate_equalOffset_distinctOldPair_false
theorem reflectionTranslate_sameValue_forces_anchor_order
theorem reflectionTranslate_noAnchorDifference_disjoint
```

This isolates the remaining escape hatch: different missing reflections can
share a translate value only through the same old pair and a matching anchor
offset `a₁ + x₂ = a₂ + x₁`.

The paired-anchor branch is now substantially sharper:

```lean
theorem translateShadow_endpoint_not_pairElements
theorem translateShadow_forces_oldPair_endpoints_extra
theorem unpairedAnchor_translateShadow_moves_to_distinct_extra
theorem translateShadow_pairedAnchor_endpoint_not_pairElements
theorem translateShadow_pairedAnchor_forces_oldPair_endpoints_extra
theorem translateShadow_contains_x_with_pairedAnchor_gives_selfShadow
theorem leastHighExtra_translateShadow_pairedAnchor_avoids_x
theorem leastHighExtra_translateShadow_pairedAnchor_ascends
theorem leastHighExtra_forces_larger_extra
```

In fact, for any translate shadow of a missing reflection, both old-pair
endpoints are extras. The proof reflects a paired endpoint across the exception
axis and uses R3 on the resulting old off-axis collision; the only possible
equalities force either the anchor to be `x` or the paired endpoint to be the
missing point `y`. The paired-anchor lemmas are now special cases used for
ascent. For a least high extra, a paired-anchor translate shadow cannot contain
`x`; it must ascend to a strictly larger extra. If the anchor is not paired, the
anchor itself is a strictly larger extra because `a = x` would put `y + a` back
on the exception axis. Thus any least high extra in a maximal set forces a
larger extra.

The extra set is now packaged as

```lean
def extraElements (A : Finset ℕ) (nstar : ℕ) : Finset ℕ
```

with finset/cardinality consequences:

```lean
theorem reflection_not_mem_of_extra
theorem minExtra_high_forces_larger_extraElement
theorem leastHighExtra_not_greatestExtra
theorem uniqueExtra_not_high_missingReflection
theorem extraElements_card_le_one_not_high_missingReflection
```

So a high in-range missing reflection requires at least two extras.

The unique-extra middle-band escape is also isolated:

```lean
theorem uniqueExtra_translateShadow_forces_selfPair
theorem uniqueExtra_maximal_missingReflection_shadow_shape
theorem uniqueExtra_noSelf_maximal_missingReflection_translate_selfPair
theorem uniqueExtra_maximal_missingReflection_has_selfShadow
theorem uniqueExtra_maximal_missingReflection_has_paired_selfShadow_endpoint
theorem uniqueExtra_maximal_missingReflection_exact_pairEndpoints
```

In words: if there is only one extra `x`, then any translate shadow for its
missing reflection has the exact form `y + a = x + x` with paired anchor `a`.
Reflecting that paired anchor gives a self-shadow, and maximality pins a
paired endpoint `d` with `x + d = 2y`; its reflected anchor `a` satisfies
`y + a = 2x` and `a + d = n*`. Thus the unique-extra case is no longer an
arbitrary middle escape but an exact paired-endpoint configuration.

### All-high collapse

The high-band escape has now collapsed in a stronger way. The arithmetic
helpers

```lean
theorem high_reflection_mono_right
theorem reflection_ground_mono_right
theorem extraElements_empty_of_every_extra_has_larger
```

package monotone movement on the exception axis and the finite-chain
contradiction. More importantly, the all-extras-high regime is impossible as
soon as one extra has an in-range missing reflection:

```lean
theorem allExtrasHigh_maximal_missingReflection_false
theorem not_allExtrasHigh_of_maximal_missingReflection
theorem exists_extra_not_high_of_maximal_missingReflection
theorem exists_middle_extra_of_maximal_missingReflection
```

Maximality first forces an unpaired-anchor translate shadow. If all extras are
high, the translate arithmetic says an extra anchor must have a paired endpoint;
but the endpoint-reflection lemma says no translate-shadow endpoint for a
missing reflection can be paired. Consequently any maximal counterexample with
an in-range missing reflection must contain a low/middle extra, or an extra
whose reflection escapes the exception axis.

## Empirical Shadow Certificates

The companion script

```text
research/sqrt2-strong-almost-sidon/data/shadow_certificates.py
```

classifies missing reflections by blocker type. Current output:

| cohort | sets | sets with missing | missing y | in range | self | translate | both | none | out |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| known extremizers | 12 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| target max sample N81-100 | 32 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| target one-below N81-100 | 670 | 118 | 118 | 100 | 0 | 0 | 42 | 58 | 18 |
| random/local top | 55 | 14 | 19 | 8 | 0 | 1 | 7 | 0 | 11 |

The important distinction is that arbitrary one-below witnesses have many
unblocked missing reflections, while top local samples have none in range.
That supports focusing on local maximality/cardinality extremality rather than
near-cardinality alone.

## Next Targets

1. **Low/middle extra analysis.** The all-high escape is gone. The remaining
   sharp gap is to exploit the forced low/middle extra from
   `exists_middle_extra_of_maximal_missingReflection`, or show that axis
   overflow is too expensive in a near-extremizer.

2. **Translate escape closure.** Rule out or charge the same-pair/equal-offset
   configuration `a₁ + x₂ = a₂ + x₁` for many missing reflections.

3. **Unique-extra exact endpoint.** Use
   `uniqueExtra_maximal_missingReflection_exact_pairEndpoints` to attack the
   exact equations `x + d = 2y`, `y + a = 2x`, and `a + d = n*`. This is the
   observed one-extra escape in the local samples.

4. **Multi-shadow counting.** For cardinality extremizers, apply the shadow
   lemma to every missing reflection of every extra and try to force two
   shadows to collide off-axis.

## Verification

`lake build Erdos.AlmostSidonSets.Maximality` passes with the new shadow
refinements. A full `lake build Erdos` may include unrelated in-progress work
from other agents, so the target-module build is the relevant check here.
