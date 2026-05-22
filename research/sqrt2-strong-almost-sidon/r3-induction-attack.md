# R3-Inductive Attack on Full Reflection

**Date:** 2026-05-22. Companion to `second-extreme-report.md`,
`full-reflection-report.md`, `multiplicity-lowerbound-attack.md`.

## Goal

Prove from **R2 + R1-generalized alone** (no participation hypothesis) that
every near-extremal SAS set `A` with `|A| ≥ (2/√3 + ε)·√N` is fully
reflection-symmetric about `n*/2`, i.e. `n* − a ∈ A` for every `a ∈ A`.

## The proposed inductive step

For `i ≥ 1`, let `A^{(i)} = A \ {m₁, M₁, …, m_i, M_i}` where `(m_k, M_k)` are
the first `i` extreme pairs of `A^{(k-1)}`. Suppose the first `i` extreme
pairs are all on the `n*`-axis (`m_k + M_k = n*` for `k ≤ i`).

**Induction step.** Show that `(m_{i+1}, M_{i+1})`, the extreme pair of
`A^{(i)}`, also satisfies `m_{i+1} + M_{i+1} = n*`.

## Case analysis

### Case 1: `n*` is still an exception of `A^{(i)}`

`A^{(i)}` is SAS (sub-set of SAS is SAS — `AlmostSidonFinset.erase` iterated).
If the multiplicity at `n*` in `A^{(i)}` is `≥ 2`, then `n*` is still the
unique exception of `A^{(i)}`. Multiplicity dropped by exactly `i` (E1
disjointness: each removed pair `(m_k, M_k)` is a sorted `n*`-pair, and the
pairs are disjoint by `e1_distinct_pairs_disjoint`). So
`r_{A^{(i)}}(n*) = r_A(n*) − i`.

**Condition:** `r_A(n*) − i ≥ 2`, i.e., `i ≤ r_A(n*) − 2`.

Under this condition, apply R2 to `A^{(i)}`: `m_{i+1} + M_{i+1} = n*`. Done.

### Case 2: `n*` is no longer the exception in `A^{(i)}`

This occurs at `i = r_A(n*) − 1` (residual multiplicity 1). Then `A^{(i)}` is
Sidon (no value has ≥ 2 reps). The extreme pair `(m_{i+1}, M_{i+1})` of a
Sidon set is unconstrained — it need not lie on the `n*`-axis. Induction
**fails** at this boundary.

## Maximum reach of the induction

The induction succeeds for `i ≤ r_A(n*) − 2`. By R1-gen + Lindström
(`r1_general_multiplicity_bound`, the (L0) bound):

```
r_A(n*) ≥ |A| − √N + O(N^{1/4})  =  (c − 1)·√N + O(N^{1/4}),
```

where `|A| = c·√N`. For `c = 2/√3`, this is `≈ 0.155·√N`. We can therefore
peel at most `≈ 0.155·√N` extreme pairs and still have R2 to lean on.

After the maximum peel `i* = r_A(n*) − 2`, we have removed `2 i* ≈ 0.31·√N`
elements, all on the `n*`-axis. Remaining: `|A| − 2 i* ≈ 0.85·√N` elements
in `A^{(i*)}`, with `n*`-multiplicity exactly 2. The `0.85·√N` elements
beyond the peeled pairs are **not** forced onto the `n*`-axis by this
argument.

## What the induction does NOT give

Full reflection requires `2 r_A(n*) ≥ |A| − δ` (R4 hypothesis), i.e.,
`r_A(n*) ≥ |A|/2 ≈ 0.577·√N` at `c = 2/√3`. The induction only verifies
`m_k + M_k = n*` for `k ≤ r_A(n*) − 2 ≈ 0.155·√N`, so it only **witnesses**
`r_A(n*) − 2` pairs on the axis. This is a tautology: each peeled pair *was*
a multiplicity contribution to `n*` to begin with.

In particular, the iteration does **not** generate new representations of
`n*`; it only confirms that the existing `n*`-pairs are extreme-pairs in
the nested sequence. We learn nothing about the elements of `A` that are
not in any `n*`-pair (the "non-pair" set `Q = A \ pairElements`, with
`|Q| = |A| − 2 r_A(n*) ≈ 0.85·√N`).

## Why iterating R1-gen on `A^{(k)}` doesn't tighten

Restart of (L0) on `A^{(k)}`: since `A^{(k)}` is SAS,
`r_{A^{(k)}}(n*) ≥ |A^{(k)}| − √N + O(N^{1/4})`.
With `|A^{(k)}| = |A| − 2k` and `r_{A^{(k)}}(n*) = r_A(n*) − k`, this gives
`r_A(n*) − k ≥ |A| − 2k − √N + O(N^{1/4})`, i.e., `r_A(n*) ≥ |A| − k − √N`,
which is **weaker** than (L0) for any `k ≥ 0` and saturates at `k = 0`.
The peel cannot bootstrap.

Pushing all the way to `k = r_A(n*) − 1` (Sidon residue) gives the
**Lindström** bound `|A| − 2(r_A(n*) − 1) ≤ √N + O(N^{1/4})`, i.e.,
`r_A(n*) ≥ (|A| − √N)/2 + O(N^{1/4})`. This is **half** of (L0). See Angle
3 in `multiplicity-lowerbound-attack.md`.

## The precise missing input

The induction succeeds for `i ≤ r_A(n*) − 2 ≈ 0.155·√N` but stops there.
For the full reflection conclusion, we would need **one of**:

**(M1) [Multiplicity boost]** A lower bound `r_A(n*) ≥ |A|/2 + O(1)` —
exactly the R4 saturation hypothesis. This is the *open* problem;
`multiplicity-lowerbound-attack.md` documents that no elementary angle
reaches this from `c < 2`.

**(M2) [Non-pair participation]** A proof that *every* element of `A` (not
just those in `n*`-pairs) is reflected: `q ∈ A \ pairElements ⇒ n* − q ∈ A`.
This is *equivalent to* full reflection (since `pairElements` is already
reflection-closed by E2), hence circular.

**(M3) [Strong off-axis Sidonicity]** A bound forbidding the non-pair part
`Q = A \ pairElements` from forming an off-axis Sidon structure of size
`> √N − r_A(n*)`. Combined with R3 (off-axis unique reps), this would
collapse `|Q| ≤ √N − r_A(n*)`, giving `|A| ≤ √N + r_A(n*)`, i.e.,
`r_A(n*) ≥ |A| − √N` — which is **just (L0)**. No win.

**(M4) [Sharper R3-second-extreme without participation]** Replace the
participation hypothesis `n* − m₂ ∈ A` in `r3_second_extreme_pair` by a
cardinality hypothesis `|A| ≥ √N + 2` (or similar). This is *strictly
stronger than R3-second-extreme*, but if achievable would let us run the
induction without the participation gating. Status: **open**. The bracket
proof of `r3_second_extreme_pair` *requires* an `n*`-pair anchor; without
participation there is no anchor to feed into `r3_nonextreme_pair_in_second_bracket`.

## Verdict

The R3-inductive attack **does not close the gap to full reflection** from
R2 + R1-gen alone. The induction is valid up to `i = r_A(n*) − 2`, but
`r_A(n*)` is *not large enough* (≈ 0.155·√N versus the needed ≈ 0.577·√N).
The argument essentially re-derives the (L0) lower bound on `r`, which is
provably tight within peel-style reasoning (see Angles 1–6 of
`multiplicity-lowerbound-attack.md`).

**Precise additional input identified:**
> Either (a) an unconditional removal of the participation hypothesis
> `n* − m₂ ∈ A` in `r3_second_extreme_pair` (an open structural question
> equivalent to the EF-rigidity conjecture for second-extreme elements),
> or (b) a quadratic-in-|A| lower bound on `r_A(n*)`, which is unavailable
> by Cauchy–Schwarz below `c = 2`.

Neither is reducible to R2 + R1-gen alone; both require new global input
(Freiman-style rigidity, Eberhard–Manners-style restricted-product
structure, or a localised energy-method gain that the current SAS
support-size estimates cannot supply).

## No Lean changes

No new theorem is added: the inductive step is *provable* (it follows from
R2 applied to `A^{(i)}` once SAS preservation under pair-erasure is
established), but the maximum reach `i ≤ r_A(n*) − 2` is the bottleneck.
Formalising the inductive lemma would simply restate `r1_general_multiplicity_bound`
+ R2 in a recursive form without strengthening the conclusion.

## References

- `Erdos/AlmostSidonSets/Rigidity.lean` — R2 (`r2_extreme_pair_on_exception_axis_or_unique`),
  R3-second-extreme (`r3_second_extreme_pair`), R1-gen
  (`r1_general_multiplicity_bound`), E1 disjointness
  (`e1_distinct_pairs_disjoint`), R4 family (`r4_full_reflection_*`).
- `research/sqrt2-strong-almost-sidon/multiplicity-lowerbound-attack.md` —
  proof that no elementary angle pushes `r` past `(c − 1)·√N`.
- `research/sqrt2-strong-almost-sidon/second-extreme-report.md` — the
  participation hypothesis in R3-second-extreme.
- `research/sqrt2-strong-almost-sidon/full-reflection-report.md` — the
  R4 saturation hypothesis equivalence to full reflection.
