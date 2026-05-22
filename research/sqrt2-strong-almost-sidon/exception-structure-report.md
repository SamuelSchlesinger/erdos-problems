# Exception-Element Structure in Strong Almost-Sidon Sets

**Research note, 2026-05-22.** Scout report on structural facts about the
elements occurring in representations of the exceptional sum value `n*`
of a strong almost-Sidon (SAS) set `A`. Paired with the R1-generalisation
scout (which strips one element per pair to recover a Sidon backbone).

## Setup

Let `A ⊂ {1,...,N}` be SAS with exception `n*`, and let `k := r_A(n*)`
denote the number of distinct sorted unordered representations
`(a_i, b_i)` with `a_i ≤ b_i` and `a_i + b_i = n*` (`i = 1,...,k`).
Write `m := min A`, `M := max A`. Existing facts:

- **R1** (formalised): if `k ≤ 2`, then `A` minus one element is Sidon.
- **R2** (formalised): if `k ≥ 2`, then either `m + M = n*` or `(m, M)`
  is the unique sorted-pair representation of `m + M`.

## Candidate lemmas analysed

### E1 — Disjoint-pair structure (NEW, formalised)

**Statement.** Two distinct sorted pairs `(a₁, a₂)` and `(b₁, b₂)`
summing to the same value `n` use four pairwise-distinct elements:
`{a₁, a₂} ∩ {b₁, b₂} = ∅`.

**Proof sketch.** Cancellation. If `a₁ = b₁` then `a₂ = n - a₁ = b₂`,
contradicting distinctness. The cross-coincidences `a₁ = b₂` and
`a₂ = b₁` force the sorted-order constraint to collapse, again giving
equality of the pairs.

**Status:** No hypothesis on `A`; even the SAS structure is not needed.
This is the foundational cancellation underlying both R1 and R2's
case analyses. *Not* covered by R1-generalised: R1 only needs *one*
element distinct, not all four.

**Lean theorem name:** `e1_distinct_pairs_disjoint`.

**Corollary (E1 set-level):** The 2k elements involved in the k pairs at
`n*` are pairwise distinct, except for the case `n* = 2c` for some `c ∈ A`,
in which exactly one pair is the "self-pair" `(c, c)` and contributes only
one element. (This case is automatically excluded by sortedness combined
with `a_i < b_i` for distinct sorted pairs — by E1, a self-pair `(c, c)`
must be the unique pair at `n*`, not a member of a larger collection.)

### E2 — Reflective structure (NEW, formalised)

**Statement.** If `a + b = n*` with `a, b ∈ A`, then `b = n* - a`.

**Status.** Trivial arithmetic, but spelled out for readability. The
k pairs at `n*` are therefore precisely the elements
`{a_i, n* - a_i : i = 1..k}`. The set of pair-elements is *reflection-
symmetric* about `n*/2`.

**Lean theorem name:** `e2_pair_element_has_reflection`.

### E3 — Mixed (strip-both) ⇒ Sidon (subsumed)

**Statement.** Removing all 2k pair-elements gives a Sidon set of size
`|A| - 2k` (or `|A| - (2k - 1)` if `n* = 2c`).

**Status.** Strictly weaker than R1-generalised, which strips only
`k - 1` elements (one per non-anchor pair) and produces a Sidon set of
size `|A| - (k - 1)`. R1-generalised yields the bound `|A| ≤ √N + k - 1
+ O(N^{1/4})`; E3 yields the worse `|A| ≤ √N + 2k + O(N^{1/4})`.

**Verdict:** Not formalised — superseded.

### E4 — Quantitative version of E3 (subsumed; same as above)

Same verdict as E3.

### E_anchor — Anchor-confinement of non-extreme n*-pairs (NEW, formalised)

**Statement.** Suppose `|A| ≥ 2`, `A` is almost-Sidon with exception
`n*`, and `m + M = n*` (the R2-axis case). For *any* sorted n*-pair
`(a, b)` (i.e., `a, b ∈ A`, `a ≤ b`, `a + b = n*`):

> either `(a, b) = (m, M)`, **or** `m < a` and `b < M`.

That is: the anchor pair `(m, M)` is the *unique* n*-pair using either
extreme; every other n*-pair lies strictly in the open interval
`(m, M)`.

**Proof sketch.** Apply E1 to `(m, M)` vs `(a, b)`: distinct sorted pairs
with the same sum `n*` are element-disjoint, so `a ≠ m`, `b ≠ M`.
Combine with the trivial `m ≤ a` and `b ≤ M` to get the strict
inequalities.

**Lean theorem name:** `e_anchor_nonextreme_pairs_interior`.

**Why this is a *new* structural fact:** R1-generalised tells us *size*
bounds (counting). R2 tells us the *extreme pair* is on the exception
axis. E_anchor combines them into a *positional* statement: the
exception axis is "anchored" by `(m, M)`, and all other excitation lives
*strictly interior* to the diameter. This is precisely the
"concentration around `n*/2`" structural signal that the
Ortega–Prendiville Fourier-uniformity strategy ultimately wants to
exploit (see `rigidity-survey.md`, Section C, step 4): the non-extreme
n*-pairs cluster *strictly* between `m` and `M`, not at the boundary.

In the EF reflection construction with `B ⊂ [1, N/3]` and
`A = B ∪ (n* - B)`, the anchor pair `(m, M)` is precisely
`(min B, n* - min B)`, and every other n*-pair `(b, n* - b)` has
`min B < b < n* - min B`, so the lemma matches the empirical extremiser.

### E5 — Arithmetic-progression density of n*-pairs (deferred)

**Statement (hypothetical).** Sort the n*-pairs by first coordinate:
`a_1 < a_2 < ... < a_k`. Then the gaps `a_{i+1} - a_i` are bounded
above by `O(√N / k)`, with equality near EF.

**Status.** Not proved; corresponds to the second Sidon-extraction layer
(if the `a_i`'s clustered too tightly, they'd violate the Sidon
property of `A \ {b_i's}`). This requires using the Sidon-bound for the
"`a`-side" `{a_1, ..., a_k}` as a subset of `[1, n*/2]`. Pursuing E5
would require a finer count than R1-generalised.

**Verdict:** Open; promising but not within the 30-call budget.

## Summary of additions

Three new Lean theorems added to `Erdos/AlmostSidonSets/Rigidity.lean`:

1. `e1_distinct_pairs_disjoint` — distinct sorted same-sum pairs are
   element-disjoint. Unconditional. Foundational.
2. `e2_pair_element_has_reflection` — partners in an n*-pair are
   reflections about `n*/2`. Trivial but clarifying.
3. `e_anchor_nonextreme_pairs_interior` — under R2's axis condition,
   non-anchor n*-pairs are strictly interior to the diameter `(m, M)`.
   Combines E1 + R2 into a positional rigidity.

All proofs are elementary (`omega`, `le_antisymm`, finset min'/max'
basics) and unconditional in the sense of requiring no Sidon-bound
input.

## Verdict on the scout question

> Is there a NEW structural theorem about elements in n*-pairs that's
> NOT subsumed by R1-generalised?

**Yes:** `e_anchor_nonextreme_pairs_interior` (E_anchor) is a genuinely
new *positional* statement that R1-generalised does not give. It states
that the SAS surplus over Sidon is structurally *interior* to the
diameter pair — exactly the structural ingredient one needs as an
input to a Freiman-style rigidity attack.

`e1_distinct_pairs_disjoint` and `e2_pair_element_has_reflection`
are foundational hygiene: they make explicit the cancellation and
reflection facts already implicit in R1, R2, and the direct-combinatorial
attack, and provide a clean Lean-level API for any future SAS structural
work.

The R1-generalised counterpart (strip `k - 1` elements, get Sidon) and
E3 (strip 2k, get Sidon, weaker) are *counting* statements, while
E_anchor is a *positional* statement. They are complementary, not
overlapping.
