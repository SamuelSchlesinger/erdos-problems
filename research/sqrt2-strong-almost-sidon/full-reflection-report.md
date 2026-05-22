# R4: Full Reflection Symmetry under Maximum Multiplicity

## Headline result

Let `A` be almost-Sidon with exception value `nstar`. Define
`r := |sumReprsFinset A nstar|` (the number of sorted-pair representations
of `nstar` in `A`). Under the empirically-observed "saturation" hypothesis
`2 r ≈ |A|`, every element of `A` is reflection-symmetric about `nstar/2`:

```
∀ a ∈ A,  nstar - a ∈ A.
```

This is the Erdős–Freud form `A = B ∪ (nstar − B)` with
`B = A ∩ [0, nstar/2]`.

## Theorem (Lean, `r4_full_reflection_under_max_multiplicity`)

```lean
theorem r4_full_reflection_under_max_multiplicity
    (A : Finset ℕ) (hA : AlmostSidonFinset A)
    {nstar : ℕ} (h_exception : HasTwoSumReprs A nstar)
    (h_max_mult :
      (¬ HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card) ∨
      (HasSelfPair A nstar ∧ 2 * (sumReprsFinset A nstar).card = A.card + 1)) :
    ∀ a ∈ A, nstar - a ∈ A
```

The hypothesis is split into two cases by a self-pair indicator:

- **No-self-pair case** (`HasSelfPair A nstar` is false): the multiplicity
  must satisfy `2 r = |A|`. Each `nstar`-pair contributes 2 distinct
  elements, so `|pairElements| = 2 r = |A|`.
- **Self-pair case** (some `c ∈ A` has `2c = nstar`): the unique self-pair
  `(c, c)` contributes only 1 element, so `|pairElements| = 2r − 1 = |A|`,
  i.e. `2 r = |A| + 1`.

## Proof structure (formalised in `Rigidity.lean`)

1. `pairElements A nstar` is defined as the union of fst- and snd-images
   of `sumReprsFinset A nstar`.
2. `pairElements_subset`: `pairElements A nstar ⊆ A`.
3. `pairElements_has_reflection`: every `x ∈ pairElements A nstar` has
   `nstar − x ∈ A` (uses `e2_pair_element_has_reflection`).
4. `pairElements_card_no_self_pair`: when no self-pair exists, the fst-
   and snd-image-injectivity argument (using `e1_distinct_pairs_disjoint`)
   yields `|pairElements| = 2 r`.
5. `pairElements_card_with_self_pair`: in the self-pair case the analogue
   gives `|pairElements| + 1 = 2 r`.
6. Under the saturation hypothesis, the inclusion
   `pairElements ⊆ A` becomes an equality by cardinality, so every
   `a ∈ A` is in `pairElements` and has its reflection.

## Erdős–Freud decomposition (`r4_ef_decomposition`)

```lean
theorem r4_ef_decomposition ... :
    let B := A.filter (fun a => 2 * a ≤ nstar)
    A = B ∪ B.image (fun a => nstar - a)
```

This produces the explicit `B ⊆ [0, nstar/2]` such that `A = B ∪ (nstar−B)`,
matching the canonical Erdős–Freud construction.

## Connection to empirical invariants

The `empirical-invariants-report.md` records that all 12 known SAS
extremizers (N = 70..79 from exhaustive search; N = 100, 200 from
asymmetric search) satisfy:

- **Exact half-multiplicity**: `2 r_A(nstar) = |A|` (no self-pair) or
  `2 r_A(nstar) = |A| + 1` (self-pair). This is exactly the disjunctive
  hypothesis of `r4_full_reflection_under_max_multiplicity`.
- **Full reflection symmetry**: `a ∈ A ↔ nstar − a ∈ A`. This is the
  conclusion of `r4_full_reflection_under_max_multiplicity`.

R4 therefore formalises the implication "saturation ⇒ full reflection
symmetry" as a clean counting argument, and the EF decomposition is the
explicit structural witness.

## Status

- Proved in Lean (no `sorry`, no `native_decide`, no custom axioms).
- `lake build Erdos.AlmostSidonSets.Rigidity` succeeds cleanly.
- New code: ~440 lines added to `Erdos/AlmostSidonSets/Rigidity.lean`,
  including 4 new public theorems
  (`pairElements_subset`, `pairElements_has_reflection`,
  `pairElements_card_no_self_pair`,
  `pairElements_card_with_self_pair`,
  `r4_full_reflection_under_max_multiplicity_no_self_pair`,
  `r4_full_reflection_under_max_multiplicity_self_pair`,
  `r4_full_reflection_under_max_multiplicity`,
  `r4_ef_decomposition`)
  plus a decidable `HasSelfPair` predicate.

## Next step

The remaining structural question is to **prove the saturation
hypothesis** for genuine SAS extremizers, i.e. show that
`|A| > Sidon(N) + 1` already forces `2 r_A(nstar) ∈ {|A|, |A|+1}`. The
current `r1_general_multiplicity_bound` gives the lower direction
(`r ≥ (|A| − Sidon(N)) / 2`); pinning down the upper direction would
close the loop and reduce SAS-extremality to Sidon-extremality on the
sub-image `B ⊆ [0, nstar/2]`.
