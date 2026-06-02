# Permutations avoiding monotone arithmetic progressions (Erdős #195 / #196 / #197)

A formalized study, in Lean 4 + Mathlib, of the Davis–Entringer–Graham–Simmons (1977)
circle of problems on permutations of ℕ/ℤ avoiding monotone arithmetic progressions.
Source files: `Erdos/PermutationMonotoneAP/`. Running research log: `notes.md`.

All theorems below compile in the project's pinned Mathlib and are **axiom-clean**
(`propext`, `Classical.choice`, `Quot.sound` only — no `sorry`, no custom axioms,
no `native_decide`).

## The problems

A set `S ⊆ ℕ` is **3-free** if it admits an enumeration `e : ℕ ≃ S` (each element listed
once) with **no monotone 3-term AP**: no positions `i<j<k` whose values `e i, e j, e k`
form an AP with `e j` the value-midpoint.

- **#197** (Erdős–Graham partition): can `ℕ = A ⊔ B` with both parts 3-free?
- **#196** (ℕ): must every permutation of ℕ contain a monotone **4**-AP?
- **#195** (ℤ): is the largest always-present monotone-AP length `k* = 3` or `4`?

Density parameters: `α(3) = sup` of upper densities of 3-free sets, `β(3) = sup` of lower
densities. **#197 has answer NO if `α(3) + β(3) < 1`** (since a partition forces
`upperDensity A + lowerDensity B = 1`). Conjecture (LeSaulnier–Vijay): `α(3)=1/2`,
`β(3)=1/4`. **No nontrivial upper bound on `α(3)` or `β(3)` is known** (even `β(3)<1` is open).

## What is formalized

| File | Content |
|---|---|
| `Statement.lean` | `HasMonotoneAP`, `IsFree`; DEGS base case `hasMonotoneAP_three` (every permutation of ℕ has a monotone 3-AP) |
| `Forcing.lean` | ~9 structural results: AP-containment forcing, subset-closedness, affine images, residue-class self-similarity (`apRestrict`), `isFree_three_of_no_threeAP` |
| `Density.lean` | natural density framework; `upperDensity A + lowerDensity Aᶜ = 1`; the LV reduction `α(3)+β(3)<1 ⟹ ¬#197` and its conditional resolution |
| `VanDerCorput.lean` | the van der Corput (bit-reversal) order is a strict total order on ℕ with **no monotone 3-AP** (`vdc_middle_not_between` + order axioms) |
| `Construction.lean` | **`α(3) ≥ 1/4`**: a fully formalized positive-density 3-free set (the LV construction) |
| `Reflection.lean` | the reflection leak at records; record values are 3-AP-free; **the conditional reduction of `β(3)<1`** |
| `Descent.lean` | **rank descent** + **no infinite doubling orbit** — the first ω-essential consequence |
| `Dyadic.lean` | **#196 layer**: k-generic affine invariance `HasMonotoneAP (c+a·g) k ↔ HasMonotoneAP g k`; the **dyadic 4-AP reduction** `isFree_four_dyadicRestrict`; `Erdos196Avoidable ↔ ¬Erdos196 ↔ IsFree univ 4`. Plus `vdc_no_monotone_fourAP` (vdc avoids 4-APs) in `VanDerCorput.lean` |
| `OddDifference.lean` | **#196 odd-difference layer (LeSaulnier–Vijay 2011) + Adenwalla reduction, formalized**: `exists_perm_no_oddDiff_mono4` — explicit permutation of `ℕ` (`g(3k)=4k, g(3k+1)=4k+2, g(3k+2)=2k+1`) with **no monotone 4-term AP of odd common difference**, via property (P) `odd x before even y ⟹ y>2x`. Bridge `oddDiffSafe_oddAvoiderInv` to the `Compactness.lean` socket (meets `OddDiffSafe N` ∀N, bound `≤2v`). Plus the **dyadic reduction towards Adenwalla Thm 4**: `AvoidV2 σ k` (avoid 4-APs with diff not divisible by `2^k`), `avoidV2_succ` (the reduction: (P) + both dyadic children avoid `2^k`-indivisible ⟹ avoids `2^(k+1)`-indivisible), and `adenwalla_of_hasPMerge : HasPMerge → ∀k ∃ G, AvoidV2 G k` — reducing Adenwalla's theorem (axiom-clean) to one (unproved) merge hypothesis. Plus the **quantifier-swap characterisation**: `mono4_free_iff_forall_avoidV2` (a fixed order is `AvoidV2` at all `k` ⟺ avoids every 4-AP) and `erdos196Avoidable_iff_exists_injective_avoidV2_all` (**#196-NO ⟺ `∃ G, Injective G ∧ ∀ k, AvoidV2 G k`**), exhibiting the open content as the swap `(∀k ∃G) ⟹ (∃G ∀k)` against Adenwalla's `∀k ∃G` |
| `Compactness.lean` | **#196 finitary bridge**: `exists_finiteFeasible_iff_avoidable` — a 4-AP-avoiding permutation of ℕ exists **iff** some uniform bound `f` makes every initial segment `[0,N)` 4-AP-free-orderable with `σ v ≤ f v` (König's lemma + rank-compression). Plus the **drift lemma** `unbounded_displacement_of_avoiding`: every 4-AP avoider has unbounded displacement (`f v − v → ∞`) |
| `Unavoidability.lean` | **#196 impossibility (YES) direction, sub-lemma (b)**: `hasMonotoneAP_three_dvd` — every permutation of ℕ has a monotone **3**-AP whose common difference is a nonzero multiple of any prescribed `M` (the DEGS argument run inside one residue class mod `M`); `hasMonotoneAP_three_pow_two` specialises to `2^k ∣ d`, giving monotone 3-APs of **arbitrarily high 2-adic valuation**. This is the "scale-controlled DEGS" hinge that an impossibility argument needs to escalate past Adenwalla's bounded-`v₂` regime. (`hasMonotoneAP_three` is the `M=1` case.) |

### Headline results

1. **A positive-density 3-free set exists** (`Construction.exists_isFree_upperDensity_pos`):
   there is `S` with `IsFree S 3` and `upperDensity S ≥ 1/4`. So **`α(3) ≥ 1/4 > 0`**. This is,
   to our knowledge, the first formalization of the LeSaulnier–Vijay lower bound. The set is
   `S = ⋃ₖ [2qₖ, 3qₖ−1]` (`qₖ₊₁ = 3qₖ−1`), enumerated block-by-block in van der Corput order;
   3-freeness combines `threeAP_same_block` (every 3-AP stays in one block) with
   `vdc_middle_not_between` (vdc scrambles within-block APs).

2. **A formalized reduction of `β(3) < 1`** (`Reflection.lowerDensity_le_of_records_dense`):
   if a 3-free enumeration has records (left-to-right maxima) of temporal rank `t ≥ c·value`
   infinitely often (`c>0`), then `lowerDensity S ≤ 1 − c/2 < 1`. The reflection leak
   (`reflection_leak`: a record of value `M`, rank `t`, forces `t` missing points in `(M,2M]`)
   is the engine. So `β(3)<1` reduces to a **uniform lower bound on record ranks**; the
   hypothesis is non-vacuous (the LV extremizer satisfies it with `c≈1/6`).

3. **No infinite doubling orbit** (`Descent.no_infinite_doubling_orbit`): with `a = e₀`, rank
   strictly descends along `x ↦ 2x−a`, so `S` contains no full orbit `{a+2ᵏ(x−a)}`. The first
   result here that essentially uses the ω order type (false for finite sets).

## The frontier: why the upper bound resists (a barrier map)

The crux — `α(3) ≤ 1/2`, `β(3) ≤ 1/4`, or even `β(3) < 1` — is **open and resists every
standard method**. We attacked it from six angles (explore + adversarial verification) and
ruled five out *with precise mechanisms*:

- **Finite-window methods can't work in principle**: every *finite* set is 3-free-orderable
  (van der Corput). Any density bound must use the infinite ω-structure essentially. This
  kills flag-algebra/permuton SDPs and finite Fourier ("ordered Roth" is false for finite sets).
- **2-adic self-similarity recursion** is vacuous: the dyadic-average recursion is the identity
  map `α ↦ ½(α+α)=α`, and is in fact 3-freeness-blind; the LV set is a self-similar fixed point.
- **Ergodic / Furstenberg correspondence** is blind: the LV set has upper **Banach density 1**,
  and 3-freeness is a property of an *enumeration* not detectable from the subshift of `1_S`.
- **The reflection leak** (record or interior, single- or multi-scale) cannot close the bound:
  a small element `y < V/2` deferred to last has all reflections inside `[0,V]` (no leak) — so
  density can be deferred "for free", and the leak vanishes.
- **Rank descent** (the natural global potential) is only a density-0 obstruction, and it
  *confirms* rather than refutes the adversary's "early-placed = large" structure.

**Synthesis.** The obstruction lives in the **global ω-order type**, not in additive structure:
the 3-APs only *supply* betweenness constraints; the entire difficulty is whether a density-δ
betweenness structure is realizable as an ω-well-order. Every density / measure / partition /
permuton / energy tool is structurally blind to this. A genuinely non-local tool (infinitary
Ramsey, or a global potential strong enough to see density — which rank descent is not) would
be needed. This is, we believe, exactly why the problem has stood since 1977.

## Problem #196 / #195 (the 4-AP question): reframing + barrier

A separate sub-study (`Dyadic.lean` + `notes.md` PROBING LOGs 13–17) attacked the open 4-AP
question via the `2ᵏ`-divisible case. Key outcomes:

- **Clean reframing.** A monotone 4-AP with `2ᵏ | d` lies in one residue class mod `2ᵏ` and
  rescales to an *odd*-difference 4-AP (`isFree_four_dyadicRestrict`). And the vdc/bit-reversal
  *dense* order has **no** monotone AP of any length `≥ 3` (`vdc_no_monotone_fourAP`: no monotone
  3-AP ⟹ no monotone 4-AP). So **#196 ⟺ realize a 4-AP-free order at order type ω** — the
  obstruction is purely order-type, not additive. (`Erdos196Avoidable ↔ IsFree univ 4`.)
- **The finitary bridge (`Compactness.lean`, NEW).** The order-type-ω requirement is now made
  *construction-ready*: `exists_finiteFeasible_iff_avoidable` proves `Erdos196Avoidable` is
  **equivalent** to a purely finitary statement — `∃ f, FiniteFeasible f`, i.e. a single uniform
  displacement bound `f` under which every initial segment `[0,N)` admits an injective 4-AP-free
  order with `σ v ≤ f v`. König's lemma threads the finite orders and rank-compression forces
  order type ω; the reverse uses `f = g.symm`, so the reduction loses nothing. **Resolving #196
  (NO direction, k\*=3) reduces to exhibiting one explicit `f` with `FiniteFeasible f`** — no
  infinitary reasoning remains. The SAT evidence (PROBING LOG 15) suggests `f v = 2 v + 6`.
- **Drift is forced (`Compactness.lean`, NEW).** `unbounded_displacement_of_avoiding`: any
  4-AP avoider `g` has unbounded displacement — for every `C` some value sits `> C` from its
  position. So the bridge's `f` must satisfy `f v − v → ∞` (it cannot be `id` or near-`id`) while
  keeping each value at a finite position. This is the precise, formalized statement of the
  ω-vs-additive tension a #196 construction must resolve (the on-paper Drift Lemma, now in Lean).
- **The wall (numerically pinned).** The unique order killing all monotone APs is vdc
  (recursive evens-first), which is *dense* (displacement `≈ N`, not ω). Every ω-izing
  modification — interval blocks (DEGS), self-similar merges — reintroduces monotone 4-APs,
  flooring at longest monotone AP `= 4`. DEGS reach 5-AP-avoidance (type ω); Adenwalla reach
  4-AP-avoidance for differences of *bounded* `v₂`; the open content is *all scales at once*,
  which requires a non-uniform/"fractal" coupling outside every natural family tried.
- **Evidence for the answer.** Three independent SAT probes (initial-segment placement;
  `rank(v) ≤ 2v+6` feasible to `N=64`; emergent relaxed self-similarity) plus the failure of
  every forcing mechanism for NO point firmly to **#196 = YES / #195 `k* = 3`** — but no
  explicit type-ω construction was found (it is the genuine 50-year frontier).

## Status

- **#197 lower bounds**: `α(3) ≥ 1/4` formalized.
- **#197 upper bounds** (`α(3)≤1/2`, `β(3)<1`): **open**; `β(3)<1` reduced to a record-rank bound; barrier map shows it is a global ω-order-type problem.
- **#196/#195**: **open** (confirmed: erdosproblems.com/196). The open content is precisely avoiding
  monotone 4-APs over **all 2-adic valuations of the common difference at once**. Each *fixed* valuation
  bound is solved in the literature: **odd difference** (LeSaulnier–Vijay 2011) and **difference not
  divisible by `2^k`** for each `k` (Adenwalla). Formalized this circle:
  - `exists_finiteFeasible_iff_avoidable` (proved, both directions, lossless) reduces #196 to one explicit
    uniform `f` with `FiniteFeasible f`. The drift lemma forces *that* `f` (`= g.symm`) to diverge from
    `id`. The dyadic socket's `OddDiffSafe` obligation is, *heuristically*, the LV layer: the **single-order**
    fact `oddDiffSafe_oddAvoiderInv` (any `N`, bound `≤ 2v`) is proved, but the socket needs `OddDiffSafe`
    of the **recursively merged parent at every stage**, which is *not* discharged by the single order —
    "faithful / loses no slack" is an informal judgement, not a theorem.
  - **`exists_perm_no_oddDiff_mono4`** (`OddDifference.lean`): the LeSaulnier–Vijay odd-difference theorem,
    via an explicit closed-form permutation + property (P). Strongest KNOWN partial result on #196.
  - **Adenwalla Thm 4 (bounded `v2`), reduced to one merge lemma**: the dyadic reduction `avoidV2_succ`
    and capstone `adenwalla_of_hasPMerge` formally reduce "for each `k`, a permutation avoiding 4-APs
    with difference not divisible by `2^k`" to a single merge hypothesis `HasPMerge` (`∀ k, ∃ G, …`).
    `HasPMerge` is **unproved in Lean**; an explicit recursive deadline-merge avoids all `v2(d) < k` APs in
    *external* SAT/Python probes up to `k = 6`, but no Lean proof exists, and (as `notes.md` PROBING LOG
    21–22 records) the per-`k` output is a rank function, **not** the global ω-bijection the bridge consumes.
  - **The quantifier swap, pinned in Lean** (`erdos196Avoidable_iff_exists_injective_avoidV2_all`,
    `mono4_free_iff_forall_avoidV2`): a single fixed order avoiding `2^k`-indivisible-difference 4-APs at
    *all* scales `k` is the same as avoiding *every* 4-AP (any `d>0` has `2^d ∤ d`), so
    **#196-NO ⟺ `∃ G, Injective G ∧ ∀ k, AvoidV2 G k`**. Adenwalla (`adenwalla_of_hasPMerge`) gives the
    **swapped** `∀ k, ∃ G, AvoidV2 G k` (a different order per scale). The open content of #196 is exactly
    this `(∀ k ∃ G) ⟹ (∃ G ∀ k)` swap; the drift lemma is why no compactness bound threads the per-scale
    orders. A scale-`j` AP rescales to an odd-difference AP in class `a mod 2^j`, and the scale-`j`
    (P)-orders impose conflicting magnitude orderings (nested keys leak at `v2=2`; matches Adenwalla
    bounded-`v2`): resolvable for *fixed* `k` (geometric/deadline merge), open across all scales — the
    50-year wall, not yet broken in either direction.
  - **Impossibility (YES) direction, a ladder** (`Unavoidability.lean`): an impossibility proof must
    (1) use the ω order-type essentially (finite/dense orders are 4-AP-free-orderable), (2) escalate the
    dyadic scale unboundedly (each fixed scale is refuted by Adenwalla), and (3) cut off at length 4
    (DEGS build a 5-AP-free ω-permutation). Steps: **(a)** [proved] DEGS — a monotone 3-AP always exists;
    **(b)** [**proved now**] `hasMonotoneAP_three_dvd` / `hasMonotoneAP_three_pow_two` — monotone 3-APs of
    *arbitrarily high* `2`-adic difference-valuation always exist (DEGS run inside a residue class), the
    hinge between (a) and the scale-escalation in (2); **(c)** [open, the crux] some such high-scale 3-AP
    has an un-tuckable completion, forcing a monotone 4-AP. A natural reformulation for (c): `f` avoids
    monotone 4-APs ⟺ every monotone 3-AP has both completions placed in its interior — impossibility is
    that this completion web has no ω-solution.
- ~280 theorems across 11 files, all axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only);
  full project builds green. (Note: the construction-side socket tower in `Compactness.lean` is exploratory
  scaffolding — ~14 `finiteFeasible_of_child_*` constructors + ~18 `erdos196Avoidable_of_child_*` wrappers,
  each conditional on an undischarged merge step; the load-bearing reduction is the iff + drift + the
  quantifier-swap characterisation above.)
