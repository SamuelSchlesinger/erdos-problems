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
- Formalized project bound: `145/168 + o(1)` via the same-signature
  multiplier gadget `{2,3,4,5,6,10,12,15,20,30,60}`.
- Best current searched candidate: `163/195 + o(1)` from the denser
  `{2:4,3:3,5:2}` p-adic signature grid.
- Distance to the final theorem:
  - `145/168` forces omitted density `23/168`, about `27.4%` of the required
    `1/2` omission mass.
  - `163/195` forces omitted density `32/195`, about `32.8%` of the required
    `1/2` omission mass.

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
- [ ] Prove the finite prefix hitting certificate over `Fin 23`.
- [ ] Package the resulting finite theorem as a disjoint-gadget packing bound.
- [ ] Record the asymptotic calculation yielding `163/195 + o(1)`.

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

- [ ] Define a reusable multiplier-template structure in Lean.
- [ ] Prove a generic scaled-identity obstruction theorem for arbitrary template
  data.
- [ ] Prove a generic prefix-hitting-to-gadget-cardinality theorem.
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

- [ ] Formalize the repeated-denominator `1/2` obstruction as a clean theorem.
- [ ] Define a splitting reservoir: elements of `A` usable to replace repeated
  denominators by distinct unit fractions.
- [ ] Prove small local splitting lemmas, then parameterize them.
- [ ] Search for finite splitting templates analogous to the multiplier
  certificates.
- [ ] Compare the splitting route against the template-packing route.

## Immediate Next Actions

1. [x] Create `Erdos/UnitFractionSets/DenseTemplate.lean`.
2. [x] Import the common packing infrastructure.
3. [x] Encode the 23 multipliers for the `{2:4,3:3,5:2}` grid.
4. [x] Prove the p-adic signature separation and dense gadget disjointness.
5. [ ] Add the 219-witness compressed certificate generated by:

```bash
python3 scripts/weighted_sumfree_lp.py \
  --template-moduli 2:4,3:3,5:2 \
  --max-rhs-size 6 \
  --template-compress \
  --emit-template /tmp/dense_163_195_template.json
```

6. [ ] First prove the finite prefix theorem. Only then build the disjoint-gadget
   global theorem.

## Coordination Notes

- Keep #470 edits out of this campaign while another agent is active there.
- Prefer adding new #301 files over bloating `UpperBound.lean` further.
- Avoid full-project builds when a targeted build proves the changed files.
- Any finite computation used in Lean must stay on bounded finite types such as
  `Fin 23`; no unbounded `native_decide`.
