# Generalized R1: Multiplicity / Cardinality Tradeoff

**Research note, 2026-05-22.** Formal extension of R1 from "at most two
representations" to the general "at most `k + 1` representations" regime.
Implemented in `Erdos/AlmostSidonSets/Rigidity.lean` as
`r1_general_multiplicity_bound`.

## Statement (Lean)

```lean
theorem r1_general_multiplicity_bound
    (A : Finset ℕ) (hA : AlmostSidonFinset A) (k : ℕ)
    (h_atMost : ∀ n, ¬ HasKPlusOneSumReprs A n (k + 1)) :
    ∃ S ⊆ A, IsSidonFinset S ∧ A.card ≤ S.card + k
```

Here `HasKPlusOneSumReprs A n k` is defined as
`k + 1 ≤ (sumReprsFinset A n).card`, so the hypothesis
`¬ HasKPlusOneSumReprs A n (k + 1)` says that the value `n` has at most
`k + 1` sorted-pair representations in `A`. The conclusion: there is a
Sidon subset `S ⊆ A` losing at most `k` elements of `A`.

## Specializations

* **`k = 0`**: hypothesis is "at most 1 rep per value", i.e. `A` is Sidon
  outright; conclusion is `S = A` and `|A| ≤ |S|`.
* **`k = 1`**: at most 2 reps per value (matches the
  classical *almost-Sidon* regime); we lose at most 1 element to obtain a
  Sidon set. This is exactly R1.
* **`k = 2`**: at most 3 reps per value; lose at most 2 elements.
* **`k = r - 1`**: if the exception multiplicity `r = r_A(n*)` is bounded
  by `r`, we lose at most `r - 1` elements.

## Consequence (paper form)

Combining with the Lindström-style Sidon interval bound
`|S| ≤ √N + O(N^{1/4})` (for any Sidon `S ⊆ [1, N]`):

> If `A ⊆ [1, N]` is almost-Sidon with `r_A(n) ≤ k + 1` for every `n`,
> then `|A| ≤ √N + O(N^{1/4}) + k`.

**Contrapositive.** Any almost-Sidon set with `|A| > √N + O(N^{1/4}) + k`
has some value with `r_A(·) ≥ k + 2`. Specializing `k = r_0 - 1`: at the
SAS extremality threshold `|A| ≈ (2/√3)√N`, the exception multiplicity
satisfies `r_A(n*) = |A| − (√N + O(N^{1/4}))`, recovering the asymptotic
linear-in-`|A|` lower bound from the direct-combinatorial attack
(`direct-combinatorial-attack.md`, S1–S3).

## Proof idea

The proof is by induction on `k`.

* **Base `k = 0`**: hypothesis says no sum value has 2 representations, so
  `A` is Sidon by `isSidonFinset_of_no_twoSumReprs`. Take `S = A`.

* **Step `k → k + 1`**: there are two cases.
  - If the stricter bound (at most `k + 1` reps) also holds, apply the IH.
  - Otherwise, some value `n*` attains the *maximal* multiplicity `k + 2`.
    Pick any representing sorted pair `(a, b)`. Remove `a` from `A`.
    The almost-Sidon property is preserved
    (`AlmostSidonFinset.erase`), and the multiplicity at `n*` drops by
    *exactly one* — because the pair `(a, b)` is the unique sorted pair
    in `sumReprsFinset A n*` containing `a` (distinct sorted pairs with
    the same sum share no elements: `e1_distinct_pairs_disjoint`).
    Hence `A.erase a` satisfies the inductive hypothesis (at most
    `k + 1` reps per value). Apply IH and lift: `|A| ≤ |S| + k + 1`
    becomes `|A| − 1 ≤ |S| + k`, i.e. `|A| ≤ |S| + (k + 1)`.

The key combinatorial fact powering the induction is the
*non-overlap of distinct sorted pairs with the same sum*: if
`(a, b), (c, d)` both sort-sum to `n` and they share any element, then
`(a, b) = (c, d)`. This is recorded as `e1_distinct_pairs_disjoint`
(elsewhere in `Rigidity.lean`) and is used implicitly when we observe
that erasing `a` removes *exactly one* pair from
`sumReprsFinset A n*`.

## Verification of the proof sketch

The sketch in the prompt claimed: "pairs share no elements except in the
diagonal case". In fact, for sorted distinct pairs summing to `n`, even
the diagonal case `(c, c)` cannot share an element with any other pair:
if `(a, b) ≠ (c, c)` and `a + b = c + c = n`, the only way to share an
element is `a = c` or `b = c`, which by the sorted-pair forcing
(`a ≤ b`, `c ≤ d = c`) collapses to `(a, b) = (c, c)`. So the
disjointness is unconditional.

The proof in `r1_general_multiplicity_bound` uses this implicitly: in
the case-split on `n = nstar`, we observe that the pair `(a, b)` is in
`sumReprsFinset A nstar` but not in `sumReprsFinset (A.erase a) nstar`
(because `a` is no longer in `A.erase a`), giving a *strict* drop in
multiplicity. By the antisymmetry of `≤`, the IH-derived inequalities
collapse to a contradiction in the `n = nstar` branch.

In the `n ≠ nstar` branch: if `(sumReprsFinset (A.erase a) n).card ≥
k + 2` and `n ≠ nstar`, then `A` had ≥ 2 reps at both `n` and `nstar`,
violating the almost-Sidon uniqueness axiom.

## Files

* `Erdos/AlmostSidonSets/Rigidity.lean`:
  - `sumReprsFinset` — finset of sorted-pair representations of `n` in `A`.
  - `HasKPlusOneSumReprs A n k` — `k + 1 ≤ (sumReprsFinset A n).card`.
  - `hasTwoSumReprs_iff_two_le_card` — bridges with the existing
    `HasTwoSumReprs` predicate.
  - `AlmostSidonFinset.erase` — almost-Sidon is closed under `erase`.
  - `isSidonFinset_of_no_twoSumReprs` — no 2-rep ⟹ Sidon.
  - `sumReprsFinset_erase_subset` — sub-monotonicity under `erase`.
  - **`r1_general_multiplicity_bound`** — the main theorem.

## What remains

This is a *purely structural* lemma: it converts a multiplicity hypothesis
into a cardinality bound modulo a Sidon-subset bound. To extract a
*numerical* upper bound `|A| ≤ √N + k + O(N^{1/4})`, one needs to combine
with `UpperBound/SidonInterval.lean` (Lindström). This bridge is not
included here but is a one-liner once the asymptotic Sidon bound is
plugged in.

The theorem does **not** close the `√2`-barrier conjecture by itself: at
the conjectural threshold `|A| ≈ √2 · √N`, the multiplicity `r_A(n*)`
must already be of order `(√2 − 1) · √N`, far from the `O(1)` regime
where this elementary bound bites. But it is a genuine **quantitative**
upper bound on the multiplicity-cardinality tradeoff in the regime where
both `|A|` and `r_A(n*)` are simultaneously controlled.
