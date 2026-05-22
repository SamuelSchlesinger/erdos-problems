# R3: Second-Extreme Pair Reflection — Report

**Date:** 2026-05-22.
**Status:** Formalized and machine-checked in `Erdos/AlmostSidonSets/Rigidity.lean`.

## Context

R2 (already in `Rigidity.lean`) says: for an SAS set with an exception
value `n*`, the extreme pair `(min A, max A)` either satisfies
`min A + max A = n*` (the "axis") or is the unique sorted-pair
representation of its sum. Empirically (OEIS A389182 + exhaustive search
up to `N = 79`) **every** SAS extremizer is of the Erdős–Freud form
`A = B ∪ (n* − B)` for a Sidon `B`, so `min A + max A = n*` always holds
and elements come in reflection pairs about `n*/2`.

The natural question: does this reflection structure extend to the
*second*-extreme pair `(m₂, M₂)`?

## Main theorems (added to `Rigidity.lean`)

We assume `|A| ≥ 3` and the R2 axis `m + M = n*` throughout. Let
`m₂ := min'(A \ {m})`, `M₂ := max'(A \ {M})`.

1. **`r3_nonextreme_pair_in_second_bracket`** — *Bracket lemma.*
   Every sorted `n*`-pair `(c, d) ≠ (m, M)` satisfies `m₂ ≤ c` and
   `d ≤ M₂`. Non-extreme `n*`-pairs are confined to the "second-extreme
   bracket" `[m₂, M₂]`. *Proof:* immediate from
   `e_anchor_nonextreme_pairs_interior`: `m < c < d < M` plus
   `m₂ = min(A \ {m})`, `M₂ = max(A \ {M})`.

2. **`r3_second_min_reflection_bounded`** — *Reflection bound.*
   If `n* − m₂ ∈ A`, then `n* − m₂ ≤ M₂` (and `m < n* − m₂ < M`).
   *Proof:* the sorted pair built from `(m₂, n* − m₂)` is non-extreme,
   so the bracket lemma applies. A short cardinality argument
   (`|A| ≥ 3`) rules out `m₂ = M`.

3. **`r3_second_extreme_pair`** — *Main theorem.*
   If both `n* − m₂ ∈ A` and `n* − M₂ ∈ A`, then `m₂ + M₂ = n*`.
   *Proof:* From (2) applied to `m₂`: `n* ≤ m₂ + M₂`. For the reverse,
   set `s := n* − M₂ ∈ A` and apply the bracket lemma to the sorted pair
   built from `(M₂, s)`:
   - If `M₂ ≤ s`: bracket gives `s ≤ M₂`, hence `s = M₂` and
     `n* = 2 M₂`. Then `n* − m₂ ≤ M₂` forces `M₂ ≤ m₂`; combined with
     `m₂ ≤ M₂` from `m₂ ∈ A \ {M}`, we get `m₂ = M₂ = n*/2`.
   - Otherwise `s < M₂`: bracket gives `m₂ ≤ s = n* − M₂`, so
     `m₂ + M₂ ≤ n*`.
   In both cases `m₂ + M₂ = n*`.

## What the hypothesis means

The "participation" hypotheses `n* − m₂ ∈ A` and `n* − M₂ ∈ A` are
**provably true** in the Erdős–Freud construction (since
`A = B ∪ (n* − B)` is closed under `x ↦ n* − x`). They are also
verified empirically on all 12 known extremizers (`N ≤ 79`, `N = 100`,
`N = 200`).

The hypothesis is *strictly weaker* than full EF symmetry: it only asks
about two specific elements. The conclusion `m₂ + M₂ = n*` is then
forced — i.e., the *second-extreme pair lies on the same axis as the
extreme pair*.

## Why we do not get unconditional R3

Without the participation hypotheses, we cannot rule out a hypothetical
SAS extremizer in which (say) `n* − m₂ ∉ A`: in that case the bracket
argument has no anchor to apply to. Such a configuration is empirically
absent from all known extremizers, but proving its absence is the
content of the broader Erdős–Freud rigidity conjecture itself.

## Verification

`lake build Erdos.AlmostSidonSets.Rigidity` passes. `#print axioms`
yields only `propext`, `Classical.choice`, `Quot.sound` — Lean's
kernel axioms. No `sorry`, no `native_decide`.

## Files changed

- `Erdos/AlmostSidonSets/Rigidity.lean` — appended new section
  "R3 (second-extreme reflection axis)" with the three theorems above.

## Next steps

- The natural follow-up is to *remove* the participation hypothesis by
  showing it follows from `|A|` being near-extremal. The expected
  argument: if `n* − m₂ ∉ A`, the SAS surplus at `n*` is too small to
  reach `(2/√3 + ε)√N`. This connects to R1 (`r1_general_multiplicity_bound`).
- Iterate to `m₃, M₃, …`: under participation hypotheses for the `k`-th
  extreme pair, `mₖ + Mₖ = n*` should follow by the same bracket
  argument applied to `A.erase m` ∪ `A.erase M` recursively.
