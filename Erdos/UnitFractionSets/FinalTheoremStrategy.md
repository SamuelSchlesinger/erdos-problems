# Problem #301 Final Theorem Strategy

Goal: prove the conjectural upper bound

```text
for every epsilon > 0, f(N) <= (1/2 + epsilon) N for all sufficiently large N.
```

Equivalently, every sum-free `A subset {1, ..., N}` must omit at least
`(1/2 - o(1))N` integers. The upper-half construction gives the matching lower
bound, so the whole problem is to force this omission density.

## Current Position

- Public baseline: van Doorn's `25/28 + o(1)` upper bound.
- Formalized project bound: **`163/195 + o(1)`** via the dense `{2:4,3:3,5:2}`
  signature grid (`DenseTemplate.lean`, `sum_free_dense_template_163_195_bound`),
  improving the earlier `145/168` same-signature gadget
  `{2,3,4,5,6,10,12,15,20,30,60}` (`UpperBound.lean`).
- Distance to the final theorem:
  - `145/168` forces omitted density `23/168`, about `27.4%` of the required
    `1/2` omission mass.
  - `163/195` forces omitted density `32/195`, about `32.8%` of the required
    `1/2` omission mass.
- **Open frontier (Phase 3):** measure whether the same-signature template
  family stalls strictly above `1/2`. The LP integrality gap is already visible
  — per-row fractional-matching values fall well short of the integral deficits
  (worst row `7.67` vs `13`) — and the local hitting numbers far exceed the
  upper-half trace, suggesting disjoint same-signature packing cannot reach
  `1/2` on its own. Run the grid sweep + LP duals to confirm, then pivot to the
  overlap-aware / splitting-reservoir routes.

## Core Proof Campaign

### Phase 1: Bank the Next Concrete Improvement

- [x] Build a generic weighted/parametric certificate bridge.
- [x] Add exact multiplier-template search to `scripts/weighted_sumfree_lp.py`.
- [x] Rediscover the formalized `145/168` grid with the search script.
- [x] Find the `{2:4,3:3,5:2}` grid with candidate upper bound `163/195`.
- [x] Compress the raw `2,980` identities to a `219`-witness prefix certificate.
- [x] Move the `163/195` candidate into a new Lean file, separate from
  `UpperBound.lean`.
- [x] Prove the required p-adic signature separation for the 23 multipliers.
- [x] Prove a generic replay theorem for finite branch certificates.
- [x] Generate and independently verify a compressed branch certificate for the
  219-witness dense template.
- [x] Add a smaller vertex-cover lower-bound certificate route and verify the
  compressed dense certificate with `27,578` nodes in the largest row.
- [x] Prove the finite prefix-hitting theorem over `Fin 23`. (Done via a bitmask
  branch search `maskSearch` on `List`/`Nat` data — faster and lighter than the
  cover-certificate route, which proved unnecessary. `Finset` is confined to the
  proof layer through the structural bridge `maskOfList_eq_maskOfFn_toFinset`.)
- [x] Package the resulting finite theorem as a disjoint-gadget packing bound
  (`sum_free_dense_template_163_195_bound`, nineteen bands).
- [x] Record the asymptotic calculation yielding `163/195 + o(1)`
  (`dense_template_density_calculation`).

### Phase 2: Make Certificates Data-Driven

The `145/168` proof is bespoke. The final theorem cannot be. We need a reusable
Lean theorem of the form:

```text
finite multiplier identities
+ p-adic signature separation
+ prefix hitting or weighted-load certificate
+ signature-density estimate
=> explicit asymptotic upper-density bound.
```

- [x] Define a reusable multiplier-template structure in Lean.
- [x] Prove a generic scaled-identity obstruction theorem for arbitrary template
  data.
- [x] Prove a generic prefix-hitting-to-gadget-cardinality theorem.
- [x] Prove a generic branch-certificate-to-prefix-hitting theorem.
- [x] Prove a generic cover-lower-certificate-to-prefix-hitting theorem, with a
  compact DAG adapter for generated data.
- [ ] Prove a generic p-adic signature disjointness theorem from valuation
  residues.
- [ ] Prove or isolate the asymptotic density lemma for classes
  `v_p(a) == 0 mod q_p`.
- [ ] Make new constants mostly data plus finite verification.

### Phase 3: Mine the Limiting Pattern

Finite constants are useful only if they reveal a family approaching `1/2`.

- [ ] Extend the search script to sweep grids under state caps and emit a ranked
  table of candidate asymptotic constants.
- [ ] Add LP-dual output: for each strong grid, record a small obstruction
  explaining why the constant is or is not improving.
- [ ] Track whether the best same-signature constants appear to approach `1/2`
  or stall above it.
- [ ] If they approach `1/2`, conjecture a parametric family of grids and local
  hitting numbers.
- [ ] If they stall, use the dual obstruction to identify the missing global
  ingredient.

### Phase 4: Prove a Parametric Family

The final theorem should come from a family indexed by a scale parameter `R`,
not from one large certificate.

Target shape:

```text
for every eta > 0, choose a finite template T_eta such that
every sum-free A omits at least (1/2 - eta)N integers.
```

- [ ] State the parametric template theorem cleanly in Lean.
- [ ] Identify the mathematical pattern behind the searched grids.
- [ ] Prove the local obstruction for all templates in the family.
- [ ] Prove the density calculation tends to `1/2`.
- [ ] Combine the family theorem with the upper-half construction to obtain
  `f(N) = (1/2 + o(1))N`.

## Parallel Final-Theorem Route: Splitting Repeated Denominators

The Erdős site notes that if repeated denominators are allowed on the right-hand
side, the threshold is already `1/2`, essentially by divisibility. The final
proof may come from converting repeated-denominator obstructions into distinct
Egyptian identities using density.

Potential theorem:

```text
dense A above density 1/2 + epsilon
=> many repeated-denominator divisibility obstructions
=> enough splitting reservoir inside A
=> one distinct-denominator identity 1/a = sum 1/b_i.
```

Checklist:

- [x] Formalize the repeated-denominator `1/2` obstruction as a clean theorem.
  Done in `SplittingReduction.lean`: `card_gt_half_implies_dvd_pair` proves that
  any `A ⊆ {1,…,N}` with `|A| > ⌈N/2⌉` contains a divisor pair `a ∣ b`, `a < b`
  (largest-odd-divisor injection `ordCompl[2]` + pigeonhole; axiom-clean). This is
  the "with repeats, threshold is `1/2`" core.
- [x] Define a splitting reservoir: elements of `A` usable to replace repeated
  denominators by distinct unit fractions. Done in `SplittingReduction.lean`:
  `card_disjoint_divisor_pairs_quant` proves `A ⊆ {1,…,N}` contains
  `≥ (|A| − ⌈N/2⌉)/2` pairwise-disjoint divisor pairs (the reservoir), in the
  encoding `(S, g)` (small elements `S` + injective partner map `g`). The
  factor `1/2` is the cost of disjointness; an adversarial review killed the
  naive `|A| − ⌈N/2⌉` claim (false: a single odd-part chain has only `⌊|A|/2⌋`
  disjoint pairs). Axiom-clean.
- [ ] Prove small local splitting lemmas, then parameterize them. (The atomic
  one is done: `not_sum_free_contains_a_2a_3a_6a` in `MultiplierFiber.lean` —
  `{a,2a,3a,6a} ⊆ A ⇒ ¬SumFree` via `1/a = 1/2a+1/3a+1/6a`. Remaining: BOUNDED
  in-`A` splits converting a reservoir pair into a scaled Egyptian partition —
  the Bloom-type wall.)
- [ ] Search for finite splitting templates analogous to the multiplier
  certificates.
- [ ] Compare the splitting route against the template-packing route.

### Reduction-layer finding (2026-06-16): the naive reduction is circular

`SplittingReduction.lean` also pins down what the splitting route's analytic
hypothesis must look like. The clean, *non-vacuous* density-triggered form

```text
DensityForcesRep N :=
  ∀ A ⊆ Icc 1 N, ⌈N/2⌉ < |A| → ∃ a ∈ A, ∃ nonempty S ⊆ witnessPool A N a,
    ∑_{b∈S} 1/b = 1/a
```

is **logically equivalent** to the #301 upper bound itself — both directions are
proved (`sumFree_card_le_half_under_R` and `upperBound_implies_DensityForcesRep`).
So a hypothesis strong enough to drive the reduction in one step is just a
restatement of the goal; discharging it *is* solving the problem. An adversarial
review also found that the earlier "for every `a` with nonempty tail there is a
representation" form is **vacuity-inducing** (it plus `SumFree` forces `|A| ≤ 1`),
because it asserts exactly the configuration `SumFree` forbids. Lesson: the
genuine work is not a clean logical reduction but the *constructive* splitting
argument (Lemma 1 → bounded in-`A` splits → Bloom-type reservoir filling), and the
honest interface (`witnessPool`, `poolRep_contradicts_sumFree`,
`DensityForcesRep`) isolates exactly the Bloom–Mehta analytic content that remains.

## Immediate Next Actions

1. [x] Create `Erdos/UnitFractionSets/DenseTemplate.lean`.
2. [x] Import the common packing infrastructure.
3. [x] Encode the 23 multipliers for the `{2:4,3:3,5:2}` grid.
4. [x] Prove the p-adic signature separation and dense gadget disjointness.
5. [x] Add the 219-witness compressed certificate generated by:

```bash
python3 scripts/weighted_sumfree_lp.py \
  --template-moduli 2:4,3:3,5:2 \
  --max-rhs-size 6 \
  --template-compress \
  --emit-template /tmp/dense_163_195_template.json
```

6. [x] Prove the generic branch-certificate replay theorem in
   `TemplateSchema.lean`.
7. [x] Verify the compressed dense branch certificate:

```bash
python3 scripts/weighted_sumfree_lp.py \
  --branch-cert-from-template /tmp/dense_163_195_template_compressed.json \
  --verify-branch-certificate /tmp/dense_branch_certificate_compressed.json
```

8. [x] Add the smaller cover-certificate generator/checker:

```bash
python3 scripts/weighted_sumfree_lp.py \
  --cover-cert-from-template /tmp/dense_163_195_template_compressed.json \
  --verify-cover-certificate /tmp/dense_cover_certificate_compressed.json
```

9. [ ] Emit the cover certificate as Lean DAG data, prove the finite prefix
   theorem, then build the disjoint-gadget global theorem.

## Coordination Notes

- Keep #470 edits out of this campaign while another agent is active there.
- Prefer adding new #301 files over bloating `UpperBound.lean` further.
- Avoid full-project builds when a targeted build proves the changed files.
- Any finite computation used in Lean must stay on bounded finite types such as
  `Fin 23`; no unbounded `native_decide`.
