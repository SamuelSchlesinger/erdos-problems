# Sharpening the Multiplicity Lower Bound for SAS Sets

**Research note, 2026-05-22.** Companion to `multiplicity-cardinality-report.md`.
Attempts to push the current bound
`r_A(n*) ≥ |A| - √N + O(N^{1/4})` (from `r1_general_multiplicity_bound`
together with Lindström) up to the R4-applicable threshold
`r_A(n*) ≥ |A|/2` at `|A| = (2/√3)·√N`.

## Notation

`A ⊆ [1,N]` SAS with exception `n*`, `r = r_A(n*)`, `|A| = c·√N`.
`r1_general_multiplicity_bound` plus Lindström give
**(L0)**  `r ≥ |A| - √N + O(N^{1/4}) = (c − 1)·√N + O(N^{1/4})`.

R4 requires `2r ≥ |A|`, i.e., `r ≥ (c/2)·√N`. At `c = 2/√3 ≈ 1.155`,
(L0) gives `0.155·√N` while R4 requires `0.577·√N`. Gap factor ≈ 3.7×.

## Angle-by-angle analysis

### Angle 1: Iterated removal + Ortega–Prendiville on the Sidon residue

After removing one element from each of the `r − 1` non-canonical n*-pairs,
the residue `B' = A \ {removed}` has `|B'| = |A| − (r − 1)` and is Sidon
(no value retains ≥ 2 representations after the surgery).

Lindström alone gives `|B'| ≤ √N + O(N^{1/4})`, which is the source of (L0).

**Ortega–Prendiville (Theorem 1.2, 2023).** Any Sidon `B' ⊆ [N]` with
`|B'| ≥ √N/100` satisfies `‖1̂_{B'} − (|B'|/N)·1̂_{[N]}‖_∞ ≪ |B'|·N^{−1/12}`.

**Consequence.** For any sum value `n`, `r_{B'}(n) ≤ |B'|²/N + O(|B'|·N^{−1/12})`
uniformly in `n`. For `|B'| = O(√N)`, this is `O(1) + O(N^{5/12})`.

**Catch.** This bound is `O(N^{5/12})`, *much larger* than the constant we
need. Fourier-uniformity does not directly drive `r_{B'}(n^*)` below 1; it
only says representations are *globally* distributed, with a power-saving
error that is too weak to prevent one specific value from accumulating
`O(N^{5/12})` representations. This is consistent with `B'` Sidon (≤ 1
representation) — the Ortega–Prendiville bound is just very loose for
Sidon sets, since it is tuned for `B_2[g]` regimes.

**Verdict.** Angle 1 + OP **does not improve (L0)**. The residue is already
Sidon by construction; the Fourier rigidity simply confirms (rather than
sharpens) Lindström.

### Angle 2: Multi-value multiplicity

SAS forbids two values from both having ≥ 2 representations, so the
single-value hypothesis in (L0) is already tight in the multi-value sense.
**No improvement available** — every other `n ≠ n*` has multiplicity
exactly 1 (when the diagonal `(a,a)` rep counts as 1).

### Angle 3: Remove whole pairs (cost 2, gain 1 in multiplicity)

Peel `r − 2` non-extreme n*-pairs (each removal: 2 elements, multiplicity
drops by 1). Residue `A^{(r-2)}` is SAS with `r_{A^{(r-2)}}(n*) = 2`.
One more peel (the Case 2b reduction) loses one more element to give a
Sidon set of size `|A| − 2(r−1)`. Lindström:

`|A| − 2(r − 1) ≤ √N + O(N^{1/4})`, i.e., `r ≥ (|A| − √N)/2 + O(N^{1/4})`.

**This is strictly worse than (L0)** by a factor of 2. Angle 3 loses the
"each new representation costs *one* element" disjointness from E1; pair
removal double-counts the cost.

### Angle 4: Reverse R4

R4 says: if `2r ≥ |A|` (with self-pair correction), then `A` is fully
reflective about `n*/2`. Equivalently, the *contrapositive*: if `A` is not
fully reflective, then `r < |A|/2`.

**This is an upper bound on `r`**, not a lower bound. Angle 4 thus gives
no direct help; instead, it tells us *what happens if* we close the gap:
if we can establish `r ≥ |A|/2`, then R4 hands us full reflection.
The goal is a lower bound, and angle 4 cannot supply one.

### Angle 5: Energy / Cauchy–Schwarz on `r_A`

Worked out in the prompt and re-verified here:

`(∑ r_A(n))² ≤ |supp(r_A)| · ∑ r_A(n)²`.
For SAS: `∑ r_A(n) = |A|(|A|+1)/2 = s`, `∑ r_A(n)² = s − r + r²`,
`|supp(r_A)| = s − r + 1 ≤ 2(M − m) + 1 ≤ 2N − 1`.

Plugging `|supp(r_A)| ≤ 2N − 1`:
`s² ≤ (2N − 1)(s + r² − r)`, so
`r² ≥ s²/(2N − 1) − s + r ≈ c⁴N/8 − c²N/2`.

**Vacuous** unless `c⁴/8 > c²/2`, i.e., `c² > 4`, i.e., `c > 2`. Useless
in the regime `c ∈ [1, √2]` where the question lives.

Plugging the *actual* `|supp(r_A)| = s − r + 1`:
`s² ≤ (s − r + 1)(s + r² − r)`
which simplifies to `0 ≤ sr² − 2sr − r³ + 2r² + s − r`,
a self-consistency identity (tautologically true for `r ∈ [1, |A|]`).

**Verdict.** C–S on the multiplicity function gives no information until
`|A| > 2√N`, far above the relevant regime.

#### Angle 5b: Localised C–S with interval bound `|supp| ≤ 2(M − m) + 1`

If `M − m = α·√N` is small, we get `r² ≥ s²/(2α√N) − s ≈ c⁴N^{3/2}/(8α) − c²N/2`.
This is *strong* (gives `r ≳ c²√N/√(8α)`) provided `α = o(√N)`.

**But** for a Sidon set in `[1,N]` with `|A| = c√N`, the standard packing
argument gives `M − m ≥ |A|²/2 = c²N/2`, so `α ≥ c²√N/2` — i.e., `α` is
*not small*, it is of order `√N`. Plugging `α = c²√N/2` back:
`r² ≥ c⁴N^{3/2}/(8 · c²√N/2) − c²N/2 = c²N/4 − c²N/2 = −c²N/4`. Vacuous.

The interval-bound refinement of C–S coincides with the trivial bound at
the SAS extremal density.

### Angle 6: Other lower bounds

I tried three additional ideas.

**6a. Counting non-pair elements.** The pair elements `P ⊆ A` form
`|P| = 2r − [self-pair]` distinct elements (by E1). The non-pair elements
`A \ P` have `|A \ P| = |A| − 2r + δ` for `δ ∈ {0, 1}`. These contribute
to no multi-rep at `n*`, hence each sum `x + y` with `x ∈ A \ P, y ∈ A`
is unique. But this is *consistent* with `r` arbitrary, and the only
deducible inequality is `2r − δ ≤ |A|`, i.e., **upper bound** `r ≤ |A|/2`.
No lower bound emerges.

**6b. Reflection-respecting Lindström.** The reflection map
`σ: a ↦ n* − a` fixes `P` (by E2) and may or may not fix elements of
`A \ P`. If we count the orbit space `A/σ`, we get `|A/σ| = r − [self] + |A \ P| / [orbit size]`.
The reflected set `σ(A \ P)` is disjoint from `A \ P` (else those would
be pair elements of `n*`), and `σ(A) ⊆ [1, n* − 1]`. So
`|A ∪ σ(A)| ≤ n* ≤ 2N`. But `|A ∪ σ(A)| = |P| + 2|A \ P| = 2|A| − |P|`.
Hence `2|A| − |P| ≤ 2N`, i.e., `|P| ≥ 2|A| − 2N`. For `|A| ≤ √N`, this is
trivially negative. **Vacuous.**

**6c. Sumset growth in the non-pair part.** Let `Q = A \ P`. Then
`Q + A ⊆ [2, 2N]` and `|Q + A| ≥ |Q| + |A| − 1` (Freiman lower bound).
For `|Q| = |A| − 2r`, this gives `|Q + A| ≥ 2|A| − 2r − 1`. Combined with
`|Q + A| ≤ 2N − 1`: `r ≥ |A| − N`. **Vacuous** for `|A| < N`.

The sumset growth `|Q + A|` could in principle be larger than `|Q| + |A| − 1`
(Plünnecke / Freiman 3k-4 type), but we have no algebraic structure on
`Q ∪ A` to extract it.

## Summary of bounds

| Angle | Lower bound on `r` | Effective at `c = 2/√3 ≈ 1.155` | Improvement over (L0)? |
|-------|---------------------|--------------------------------|------------------------|
| (L0) [current] | `(c − 1)·√N + O(N^{1/4})` | `0.155·√N` | baseline |
| 1 (OP rigidity) | (L0) | `0.155·√N` | no |
| 2 (multi-value) | n/a | – | no |
| 3 (whole-pair peel) | `(c − 1)/2 · √N` | `0.077·√N` | **worse** |
| 4 (reverse R4) | n/a (upper bound) | – | no |
| 5 (C–S energy) | `√(c⁴/8 − c²/2)·√N` | imaginary (vacuous) | no |
| 5b (localised C–S) | vacuous at SAS extremality | – | no |
| 6a (non-pair count) | n/a (upper bound) | – | no |
| 6b (reflection union) | vacuous | – | no |
| 6c (sumset growth) | vacuous | – | no |

## Where the argument *is* sharp

The (L0) bound `r ≥ |A| − √N + O(N^{1/4})` is **provably sharp up to lower-order
terms** in two senses:

(i) Each removal in the inductive peel of `r1_general_multiplicity_bound`
    strips exactly one rep and exactly one element, by E1 disjointness.
    This is a *tight* one-for-one trade: there is no slack to recover.

(ii) The Sidon residue achieves Lindström tightly (Singer-difference-set
    construction), and the surgery preserves Sidon-extremality. So the
    sequence `A ↦ B' ↦ Singer-like` is rate-optimal.

## Why the bound stalls below `|A|/2`

The fundamental obstruction: the (L0) bound trades **multiplicity for
*Sidon size***, but the gap we need to close trades multiplicity for **|A|**.
At `|A| = c√N`, even if `B'` is Lindström-extremal at `√N`, we recover
only `r ≥ (c−1)√N`. To reach `r ≥ (c/2)√N` we would need:

`(c − 1)·√N ≥ (c/2)·√N`, i.e., `c ≥ 2`.

So **(L0) alone reaches R4's threshold only at `|A| ≥ 2√N`**, far above
the `(2/√3)√N` benchmark. The structural gap is precisely the missing
factor of ~1.7 in `|A|`, equivalent to needing a quadratic-in-`|A|`
lower bound on `r`, not linear-in-`|A|`. 

No elementary angle produces a quadratic bound. Cauchy–Schwarz (the
natural source of quadratic bounds) becomes vacuous below `c = 2` because
the support `|A + A|` is *too large* relative to `N` — there is no
concentration to exploit.

## Conclusion

**The best provable lower bound is (L0)**: `r ≥ |A| − √N + O(N^{1/4})`,
already formalised as `r1_general_multiplicity_bound` plus a Lindström
plug-in. None of angles 1–6 yields an asymptotic improvement in the
regime `c ∈ (1, 2)` where the open question lives.

The shortfall to the R4 threshold (`r ≥ |A|/2`) is fundamental: closing
it requires a *quadratic* lower bound on `r` (i.e., `r ≳ |A|^2/(2N) · √N`),
which cannot come from peel-style arguments (which give only linear
trades) nor from L²-energy (which is vacuous below `|A| > 2√N`).

This is consistent with the diagnosis in `direct-combinatorial-attack.md`:
the `√2`-barrier is a globally coupled obstruction that local
multiplicity-vs-cardinality trades cannot bridge. The path forward (per
`rigidity-survey.md`) is a Freiman-style global rigidity theorem.

**No new Lean theorem.** The Lean infrastructure
(`r1_general_multiplicity_bound`) already captures the best elementary
lower bound on `r`; nothing in angles 1–6 sharpens it.

## Files referenced

* `Erdos/AlmostSidonSets/Rigidity.lean` — `r1_general_multiplicity_bound`
  (lines 469–537), `e1_distinct_pairs_disjoint` (217–258), R4 family
  (1199–1290).
* `research/sqrt2-strong-almost-sidon/multiplicity-cardinality-report.md`
  — the (L0) report.
* `research/sqrt2-strong-almost-sidon/direct-combinatorial-attack.md`
  — diagnosis of the `2/√3` versus `√2` gap.
* `research/sqrt2-strong-almost-sidon/rigidity-survey.md` —
  Ortega–Prendiville and Eberhard–Manners adaptation discussion.
