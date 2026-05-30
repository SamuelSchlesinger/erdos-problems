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
- **#196/#195**: **open**; reframed as "4-AP-free order of type ω", evidence for YES, the all-scales construction is the frontier.
- ~24 theorems across 8 files, all axiom-clean; full project builds green.
