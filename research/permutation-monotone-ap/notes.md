# Research Notes: Permutations Avoiding Monotone Arithmetic Progressions

**Long-haul target.** Resolve one of the genuinely-open Erdős problems
**#195, #196, #197** (Davis–Entringer–Graham–Simmons 1977 circle), or make
substantial formalized partial progress. Chosen after an exhaustive triage of
all ~293 open formalized Erdős problems (see "Why this target" below).

Working dir for Lean: `Erdos/PermutationMonotoneAP/` (to be created).
This file is the durable anchor — update it every session.

---

## The precise definition (matches google-deepmind/formal-conjectures)

`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`:

```
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)
```

So for `f : ℕ → ℕ` (or `ℤ → ℤ`) viewed as a SEQUENCE (position ↦ value),
`HasMonotoneAP f k` means: there exist **strictly increasing positions**
`i_0 < i_1 < ... < i_{k-1}` whose **values** `f(i_0), ..., f(i_{k-1})` form a
`k`-term arithmetic progression (a list `[a, a+d, ..., a+(k-1)d]`, d ≠ 0 for a
permutation since values are distinct).

Equivalent reading (for a permutation π of ℕ): a `k`-term value-AP
`{a, a+d, ..., a+(k-1)d}` is "monotone" iff its elements appear in **monotone
order of position** — i.e. positions `π⁻¹(a), π⁻¹(a+d), ...` are increasing
(matching increasing value) or decreasing. AVOIDING monotone k-APs = the
permutation "scrambles" every k-term AP so its elements are never in monotone
position order.

Note: the *positions* need NOT be in AP — only strictly increasing. Only the
*values* form an AP.

## The three problems (exact formalized statements)

- **#195** (`f : ℤ ≃ ℤ`): `k* := sSup {k | ∀ f : ℤ ≃ ℤ, HasMonotoneAP f k}`.
  Known `3 ≤ k* ≤ 4` (Geneson: `≤ 5`; Adenwalla: `≤ 4`). **OPEN: is k* = 3 or 4?**
  i.e. is there `f : ℤ ≃ ℤ` with NO monotone 4-AP?
- **#196** (`f : ℕ ≃ ℕ`): **OPEN: must every permutation of ℕ contain a monotone
  4-AP?** Equivalently: is there a permutation of ℕ avoiding monotone 4-APs?
- **#197** (partition): **OPEN: can ℕ be partitioned into `A ⊔ B` such that each
  part can be enumerated (bijection `ℕ ≃ A`, `ℕ ≃ B`) avoiding monotone 3-APs?**

All three are tagged `@[category research open]` in formal-conjectures and
`open` in the teorth/erdosproblems community DB (last_update 2025-08-31).

## State of the art (literature)

- **Davis, Entringer, Graham, Simmons (1977)**, "On permutations containing no
  long arithmetic progressions":
  - Constructed a permutation of ℕ (the positive integers) avoiding monotone
    **5-term** APs.
  - Constructed a *doubly-infinite* permutation (ℤ-indexed) avoiding monotone
    **4-term** APs.
  - (Folklore/likely) every permutation of ℕ contains a monotone **3-AP** — this
    is WHY #197 must split into two parts.
- **Geneson (2019)**, "Forbidden arithmetic progressions in permutations of
  subsets of the integers", Discrete Math.: permutation of ℤ avoiding monotone
  **6-APs** (gives `k* ≤ 6`), among other results on subsets.
- **Adenwalla (2022/2024)**, arXiv:2211.04451 (+ generalisation arXiv:2302.09662),
  "Avoiding Monotone Arithmetic Progressions in Permutations of Integers",
  Discrete Math. 2024:
  - Permutation of ℤ avoiding monotone **5-APs** ⟹ `k* ≤ 4`.
  - For each `k ≥ 1`, a permutation of ℕ avoiding monotone **4-APs with common
    difference not divisible by `2^k`**. (PARTIAL — the hard remaining case is
    4-APs whose common difference is divisible by high powers of 2.)
  - Density-type results `β_{ℤ+}(4)=1`, `β_ℤ(3) ≥ 3/10`, `β_ℤ(4)=1`,
    `α_ℤ(4)=1` (need to pin exact meanings from the paper).
  - Structure of permutations of `[1,n]` avoiding length-3 monotone APs **mod n**.

**The crux / known barrier.** The 4-AP question (#195 for ℤ, #196 for ℕ) is the
boundary. Adenwalla handles differences not divisible by `2^k`; the obstruction
is differences `d` divisible by large powers of 2. Believed answer is not
settled in my reading — NEEDS VERIFICATION (read the papers' "open problems").

## Why this target (triage summary, 2026-05-28)

Surveyed all ~293 open Erdős problems formalized in formal-conjectures, cross-
referenced status in teorth/erdosproblems. Ruled out:
- Analytic-NT / asymptotic / density / limsup problems (not formalizable by me):
  e.g. #9 (positive density, Pan got N^{1-ε}), #11 (squarefree+2^k, tied to
  Wieferich primes), #66, #893, #950, etc.
- Covering-system problems (#203, #273, #1113): computed that the natural
  coverings DON'T exist — for #203, small-`⟨2,3⟩ mod q` primes have incompatible
  orders (huge tori) while order-compatible primes have `⟨2,3⟩` too big to reach
  density 1. #1113 ties to Fermat primes. #273 (p≥5) excludes moduli 2,3.
- Independence/ZFC problems: #474 ("not provable"), #598, etc.
- Famous-hard: #20 sunflower, #52 sum-product, #89 distances, #242, #470, #701.

The permutation cluster won on: genuinely open, **concrete & construction-shaped**
(a YES is an explicit permutation → formalizable), recent partial progress to
build on, clean Lean objects (`ℕ ≃ ℕ`, AP predicates), and fits the repo's
additive-combinatorics theme.

## Attack plan (living)

Phase 0 — Understand (current):
- [ ] Read DEGS 1977, Geneson 2019, Adenwalla 2022 carefully; extract exact
      constructions and the precise open gap + believed answer.
- [ ] Computational search on finite prefixes: greedily/ILP build permutations of
      `[1,N]` avoiding monotone 4-APs (and 3-APs for #197) to feel the obstruction
      and look for a pattern that extends to ℕ.

Phase 1 — Framework (Lean):
- [ ] `Statement.lean`: port `HasMonotoneAP`, `IsAPOfLength` (list version), and
      the three problem statements (match formal-conjectures exactly).
- [ ] Basic theory: monotonicity, reduction lemmas, "block construction" lemma
      (if a permutation is built from finite blocks with a gap condition, bound
      the AP length crossing blocks).

Phase 2 — Known territory (valuable regardless):
- [ ] Formalize "every permutation of ℕ has a monotone 3-AP" (if true) — clean.
- [ ] Formalize a DEGS-style construction (e.g. doubly-infinite avoiding 4-APs,
      or ℕ avoiding 5-APs). First formal proof of any of these is a contribution.

Phase 3 — Novel attempt (the resolution):
- [ ] #197 first (likely most tractable / least attacked): explicit partition +
      enumerations avoiding monotone 3-APs, with a clean correctness proof.
- [ ] #196 / #195: the 4-AP question. Either a full ℕ/ℤ construction, or a
      forcing proof that every permutation has a monotone 4-AP.

## Key mathematical observations (running log)

- Avoiding monotone 3-APs in a SET-enumeration: for every AP {a,a+d,a+2d} inside
  the set, the middle term a+d must be positioned first or last among the three
  (not in the middle). van der Waerden ⟹ ℕ can't be 2-colored 3-AP-free, so in
  #197 the parts DO contain 3-APs; the enumeration must scramble them.
- Heuristic difficulty: a random perm of [1,N] has ~N²/72 monotone 4-APs, so an
  avoiding permutation is highly structured. 5-APs are easier (~N²/... fewer with
  the 1/60 monotone-fraction), which is why DEGS got 5 but 4 is open.
- Base-2 structure of the barrier (Adenwalla) suggests constructions via binary
  representations / bit operations handle odd-ish differences but not 2^k | d.

- **Convention equivalence.** Two conventions exist: (A, the Lean def) "increasing
  positions, values form an AP"; (B, classical DEGS) "positions form an AP, values
  monotone". π satisfies A ⟺ π⁻¹ satisfies B. Since #195/#196 quantify "∃ permutation
  avoiding ...", the two conventions give EQUIVALENT existence questions (pass to
  inverse). So literature results transfer, and we can use the Lean def (A) freely.

- **CRUX: ℤ vs ℕ is an order-type question, NOT a finite obstruction.** A linear
  order on the values, restricted to {1,…,M}, gives a permutation of [M]; a monotone
  4-AP there lifts to one in the whole order. Restriction (perm of [M+1] → perm of
  [M]) makes "[M]-permutations avoiding monotone 4-APs" a finitely-branching tree.
  KEY CONSEQUENCE: by König, IF avoiders of [M] exist for all M THEN an avoiding
  *countable linear order* exists — but its order type need not be ω. DEGS realized
  type ℤ (doubly-infinite). So:
    * Finite [M]-avoiders exist for ALL M (they're restrictions of the DEGS ℤ-avoider).
      ⟹ a finite "every perm of [M] has a monotone 4-AP" obstruction does NOT exist,
      so brute finite search will NOT prove "every perm of ℕ forced".
    * #196 (ℕ = order type ω) is STRICTER than ℤ: it asks whether the avoiding order
      can be ONE-SIDED (well-ordered by position, type ω) rather than two-sided (ℤ).
      This is the real content and why ℕ is harder than ℤ. Adenwalla's restricted-
      difference ℕ results attack exactly this "folding to one-sided" problem.
  ⟹ Strategy implication: don't hunt for a finite forcing obstruction for ℕ-4-APs;
  instead study whether the ℤ-construction can be folded to ω, or find a one-sided
  obstruction specific to type ω. For #195 (ℤ) the question is whether type ℤ avoids
  4-APs (DEGS doubly-infinite suggests possibly YES ⟹ k*=3) — VERIFY what DEGS's
  doubly-infinite construction's order type is (ℤ-indexed positions? then it may
  already answer #195). THIS NEEDS CAREFUL READING of DEGS — could be that #195 is
  "morally known" via DEGS and the formalization is the contribution, OR there's a
  gap. Top-priority verification.

## Computational findings (running log)

- 2026-05-28: Backtracking search (`/tmp/apsearch2.py`) confirms monotone-4-AP-
  avoiding permutations of `[n]` exist for all `n` tested (1..13+), as predicted by
  the order-type insight. Lex-min avoiders: n=11 `[1,2,4,3,8,6,9,11,10,7,5]`,
  n=12 `[1,2,4,3,8,6,10,7,5,11,12,9]`, n=13 `[1,2,4,3,8,6,10,7,5,11,13,12,9]`.
  IMPORTANT: these are NOT prefix-consistent across n (n=11 ≠ prefix of n=12),
  reconfirming finite existence does NOT yield an ω-sequence directly. Recurring
  motif `1,2,4,3,8,6,...` (roughly: low evens/odds interleaved) worth analyzing —
  smells like a base-2 / bit-structured construction.

## Immediate next actions (Phase 0 continued)
1. Read the ACTUAL papers (DEGS 1977; Adenwalla arXiv:2211.04451 PDF; Geneson
   arXiv:1803.06334) for: exact constructions, the precise order-types (does DEGS's
   doubly-infinite avoider settle #195 for ℤ?), and the explicitly-stated open
   problems / believed answers. (Top priority — resolves whether #195 is "morally
   known".)
2. Run the REAL #196 probe: greedy/backtracking infinite extension over ℕ that
   FORCES small values to appear (so it's an ω-permutation, not drifting to ∞), and
   see if it's sustainable + what pattern emerges. Contrast with a free extension.
3. For #197: confirm computationally that a single ℕ-enumeration can't avoid
   monotone 3-APs, then search for a 2-partition + enumerations that do.
4. Begin `Erdos/PermutationMonotoneAP/Statement.lean` (port defs).

## DECISIVE LITERATURE FINDINGS (2026-05-28) — full state of the art

Sources read: Geneson (arXiv:1803.06334), Adenwalla (arXiv:2211.04451),
LeSaulnier–Vijay (arXiv:1004.1740, full text in /tmp/lv.txt), DEGS (Acta Arith 34, 1977).

**Definition (settled).** A permutation a₁,a₂,… of a set S "avoids monotone k-APs"
= no subsequence (increasing positions) of length k whose values form a k-term AP
(equivalently an increasing OR decreasing k-AP appears as a subsequence). Matches Lean.

**DEGS clean proof that every permutation of ℕ has a monotone 3-AP** (formalizable,
~5 lines): let a₁ be the first term; let k be least with aₖ > a₁ (exists). Then
2aₖ − a₁ > aₖ > a₁ and it is NOT among positions 1..k (those values are ≤ a₁ except
aₖ itself, and 2aₖ−a₁ ≠ aₖ). So it appears at a position > k. Hence (a₁, aₖ, 2aₖ−a₁)
is an increasing 3-term AP at increasing positions = monotone 3-AP. ∎
(For a SUBSET S this breaks iff 2aₖ−a₁ ∉ S — which is exactly why subsets can be 3-free.)

**LeSaulnier–Vijay constructions (formalizable):**
- α(4)=1, β(4)≥1/3: S^{(a)} = ⋃_{i≥0}[a·2^i, a·2^{i+1}] each block internally 3AP-free-
  permuted, concatenated; 4-free. d̄=a/(a+1)→1, d_=1/(a+1).
- α(3)≥1/2, β(3)≥1/4: p₀=1,q₀=2; pₖ=2q_{k-1}, qₖ=3q_{k-1}−1; Tₖ=[pₖ,qₖ];
  T=⋃Tₖ enumerated τ₀τ₁τ₂… (each τₖ a 3AP-free perm of the finite block Tₖ). T is 3-free.
  d̄(T)=1/2, d_(T)=1/4. (3-free because: cross-block increasing AP forces x₃≥2x₂⟹x₁≤0;
  same-block x₂,x₃ with earlier x₁ forces x₂−x₁ ≥ q_{k-1} > block-length > x₃−x₂.)
- Finite recurrence M(2n)≥2M(n)², M(2n+1)≥2M(n)M(n+1): concatenate a 3AP-free perm of
  evens {2,..,2n} with one of odds {1,..,2n-1}; works because the two ENDS of any 3-AP
  share parity, so an odd-difference 3-AP has its middle in the opposite parity block.

**α/β framework.** d̄,d_ = upper/lower density. α(k)=sup d̄(S), β(k)=sup d_(S) over
k-free S. Known: α(k)=β(k)=1 for k≥5; α(4)=1, β(4)≥1/3; α(3)≥1/2, β(3)≥1/4.

**THE BARRIERS (why all three are frontier-hard):**
- **#195 (ℤ) / #196 (ℕ): the 4-AP question.** ∃ permutation of ℤ (resp ℕ) avoiding
  monotone 4-APs? OPEN. Adenwalla: ℤ avoids 5-APs; ℕ avoids 4-APs with common difference
  not divisible by 2^k (for each fixed k). Barrier = differences divisible by high powers
  of 2 (the 2-adic depth / order-type obstruction). No construction and no forcing proof.
- **#197 (Erdős–Graham partition).** NO iff α(3)+β(3) < 1. LeSaulnier–Vijay conjecture
  α(3)=1/2, β(3)=1/4 (⟹ NO), but **could not even prove β(3) < 1**. So NO nontrivial
  UPPER bound on α(3) or β(3) is known — that is the entire open content. The YES
  direction needs a 3-free set of lower density ≥ 1/2 with 3-free complement (beating
  their 1/4), which they believe impossible.

**vdc insight (mine, formalizable, but does NOT resolve anything).** The van der Corput
(bit-reversal) order r(n)=reverse-binary∈[0,1) makes EVERY 3-AP's middle r-extreme
(0 bad up to N=2048; clean proof: at the lowest differing bit v=v₂(d), middle has the
opposite bit and that bit dominates in r). BUT r is a DENSE (ℚ-type) order, not a
permutation (type ω) — exactly the order-type gap. Confirms why discrete orders fail.

## HONEST ASSESSMENT (2026-05-28)
Full resolution of any of #195/#196/#197 requires breaking a known barrier with NO
existing partial upper bound (4-AP question; or α(3)≤1/2 / β(3)<1). This is genuine
research frontier. Realistic deliverables I can FULLY prove & formalize:
  (1) DEGS: every permutation of ℕ has a monotone 3-AP (clean).
  (2) LV constructions α(3)≥1/2, β(3)≥1/4, α(4)≥1−ε, etc. (first formal treatment).
  (3) The α+β<1 ⟹ ¬#197 reduction.
  (4) vdc dense-order avoidance.
These are NOVEL FORMALIZATIONS (not in Mathlib/repo) but are "known" mathematics, not
a resolution of the open conjecture. Resolving the open conjecture itself: low odds.

## PROGRESS LOG
- 2026-05-28: `Erdos/PermutationMonotoneAP/Statement.lean` created & builds clean.
  Defs `HasMonotoneAP` (positions = StrictMono ℕ→ℕ, values form AP over ℤ), `IsFree`,
  `Erdos196`, `Erdos197`. **`hasMonotoneAP_three` PROVED** (DEGS base case: every
  permutation of ℕ has a monotone 3-AP), axiom-clean (propext, Classical.choice,
  Quot.sound only). First formalization of this cluster. Wired into Erdos.lean.
  NOTE: this is KNOWN mathematics, NOT the open conjecture.
- 2026-05-28: `Erdos/PermutationMonotoneAP/Forcing.lean` builds clean, axiom-clean.
  **`hasMonotoneAP_three_of_containsAP`** + **`not_isFree_three_of_containsAP`** PROVED:
  a 3-free set contains NO infinite arithmetic progression (the key structural necessary
  condition; strengthens DEGS). Direct argument: among AP elements pick the enumeration-
  earliest `i_a`, then earliest `j>i_a`; element `2j−i_a` is forced later ⟹ monotone 3-AP.
  Wired into Erdos.lean. Two genuine theorems now formalized for this cluster.
- 2026-05-28: `Erdos/PermutationMonotoneAP/Density.lean` builds clean, axiom-clean.
  Natural density layer (`countMem` via `Set.ncard`, `densityRatio`, `upperDensity`,
  `lowerDensity`). **`upperDensity_add_lowerDensity_compl`** (general: `d̄(A)+d_(Aᶜ)=1`)
  and **`not_erdos197_of_density_bounds`** PROVED: the LeSaulnier–Vijay reduction —
  IF `∀ 3-free S, upperDensity S ≤ uA` and `∀ 3-free S, lowerDensity S ≤ uB` with
  `uA+uB<1`, THEN ¬Erdos197. This is the precise open target (prove the density upper
  bounds; conjecturally uA=1/2, uB=1/4). Used `liminf_const_sub`. Wired into Erdos.lean.
  THREE theorems now formalized for the cluster (DEGS + structural + reduction).
- 2026-05-28: `Erdos/PermutationMonotoneAP/VanDerCorput.lean` builds clean, axiom-clean.
  **`vdc_middle_not_between`** PROVED: the van der Corput (reverse-binary) order `vdcLt`
  makes every 3-AP `x,x+d,x+2d` have its middle `≺`-extreme — i.e. the vdc linear order
  on ℕ has NO monotone 3-AP. Clean 2-adic proof (`ap_bits`: at lowest set bit v of d,
  endpoints share bit v, middle is flipped; `vdcLt` decided by lowest differing bit).
  This is the engine for within-block scrambling in positive-density 3-free constructions.
  (vdc is a DENSE order, not ω — so doesn't alone give an ω-3-free permutation.)
  FOUR theorems now formalized: DEGS + structural + density-reduction + van der Corput.

## CURRENT STATE SUMMARY (first formalization of #195/196/197 cluster)
Files in `Erdos/PermutationMonotoneAP/`: Statement, Forcing, Density, VanDerCorput.
All build, axiom-clean (propext/Classical.choice/Quot.sound), wired into Erdos.lean,
full `lake build` green. The OPEN conjecture (#197 needs density UPPER bounds α(3)≤1/2
etc.; #195/196 the 4-AP question) remains open — frontier, documented barriers.
Next candidate work: (a) positive-density 3-free construction (LV's T using vdc blocks)
→ formalize α(3)≥1/2 / β(3)≥1/4 (lower bounds; substantial: needs the union-of-blocks
Equiv); (b) keep attacking upper bounds (open); (c) documentation (LITERATURE/REFERENCES).

## ATTACK LOG (for future sessions — avoid repeating these dead ends)

User directive (2026-05-28): "Keep attacking, accept the odds" — genuine multi-session
research attempt at the open conjecture, formalizing partial results as we go.

**Reformulation.** `S` 3-free ⟺ ∃ bijection (well-order) `ρ : S → ℕ` (the enumeration
ranks) s.t. every 3-AP `{x,y,z}⊆S` (y the value-middle) has `ρ(y)` rank-EXTREME (not
strictly between `ρ(x),ρ(z)`). DEGS = no such ρ exists for `S = ℕ`.

**Attack 1 (rank well-foundedness / infinite descent).** ρ-min element `m₀`: for `y∈S`,
`y>m₀`, if `2y−m₀∈S` then `ρ(2y−m₀)<ρ(y)`. So `S` cannot contain a full orbit
`{m₀+2^k(y−m₀):k≥0}` (infinite ρ-descent, impossible). ⟹ for every odd `u`, infinitely
many `j` with `m₀+2^j u ∉ S`. BARRIER: these orbits are exponentially sparse; a density-0
complement can hit each i.o. — no density bound. (Generalizes the well-foundedness obstruction.)

**Attack 2 (pair-counting).** For `x<y∈S` with `ρ(x)<ρ(y)`: `2y−x∉S` (forced). Gives
~`|S∩[1,V]|²/4` forced-missing points in `[1,2V]`. BARRIER: heavy COLLISIONS among the
`2y−x` (≤ 2V distinct possible), so no contradiction. This collision phenomenon is exactly
why dense 3-free sets exist; any density upper bound must control collisions (additive-energy
style), which is the real (open) difficulty.

**Attack 3 (construction optimization — can we beat α(3)=1/2 / β(3)=1/4?).** For an
interval-block set `⋃[p_k,q_k]` (blocks in order, each internally 3AP-free), the binding
3-freeness constraint is preventing **APs across THREE different blocks** (e.g. 0,2,4 ⊂
evens — the case that kills constant-gap constructions). Preventing it forces consecutive
gaps to grow ⟹ geometric growth ⟹ density ≤ 1/2 (upper), matching LV. So LV's bounds look
optimal for interval constructions; beating them (toward #197-YES) needs a genuinely
non-interval construction (parity-mixed? 2-adic?). I could not find one this session.

**Net:** all three standard angles hit the known barriers (sparse orbits / additive collisions
/ geometric-growth). The open content (an upper bound on α(3),β(3), or a denser construction)
genuinely needs a new idea, consistent with LV being unable to even show β(3)<1.

## PROBING LOG 2 (2026-05-28, "keep probing for new ideas")

New theorems added (`Forcing.lean`, verified, green):
- `isFree_three_missesAP_infinite`: a 3-free set misses infinitely many terms of
  EVERY infinite AP (else it contains a tail = infinite AP).
- `isFree_three_compl_infinite`: a 3-free set is co-infinite (weakest rung toward β(3)<1).

New STRUCTURAL IDEAS probed (genuine, some formalizable; none cracks the bound yet):
- **Subset-closedness**: any subset of a 3-free set is 3-free (restrict the enumeration).
  Clean math; Lean needs subsequence→Equiv reindexing (`Nat.nth` on the position set).
  Generalizes the structural lemma. FORMALIZABLE (medium), good foundational lemma.
- **Self-similarity**: for a 3-free `S` and any AP `P={c+a·i}`, `S∩P` is 3-free *inside*
  `P≅ℕ`. ⟹ density of `S` in EVERY residue class ≤ α(3); an extremal 3-free set has
  density α in every class (self-similar). Didn't yield the bound (consistent with a
  self-similar extremizer), but a strong structural constraint.
- **Run / recursive-zigzag**: within any maximal run of consecutive integers ⊆ S, the
  enumeration must be a local-extremum-everywhere "zigzag", and recursively zigzag at
  every 2-adic scale = exactly the vdc structure. So finite runs are fine (vdc); the
  density bound is forced by GLOBAL/large-d APs, not local — confirming the difficulty
  is the additive (no-infinite-AP / 2-adic-depth) structure, not local.
- **Energy/collision (refined Attack 2)**: forced-missing points `{2y-x}` form `2S−S`;
  a bound needs `|2S−S|` large, but the adversary order maximizes collisions and dense
  sets have high additive energy → fights the bound. This is THE obstruction; an
  unconditional bound likely needs real additive-combinatorics (Fourier/energy increment).
- **ℤ-case (#195)**: k* ∈ {3,4} hinges on the SAME 4-AP question; the vdc engine is
  ℕ-specific (bit-reversal), so ℤ needs a different idea. No easier than #196.

HONEST: after two rounds of probing (6+ distinct angles), the unconditional density
upper bound (the open content of #197, and the 4-AP question for #195/196) resists all
elementary attacks — matching the literature (LV couldn't show even β(3)<1; Adenwalla
stuck at the 2^k barrier). A breakthrough needs genuine additive-combinatorial machinery.

## PROBING LOG 3 (2026-05-28) — subset-closedness + affine invariance DONE

Two more theorems formalized (`Forcing.lean`, verified, axiom-clean, full build green):
- **`isFree_three_of_subset`**: any infinite subset of a 3-free set is 3-free
  (restrict the enumeration; via `Nat.nth` reindexing of the position set). Foundational
  downward-closure lemma — gives the structural results uniformly.
- **`isFree_three_affine_image`**: the affine image `{c + a·t : t ∈ T}` (a≥1) of a 3-free
  `T` is 3-free (the map `t ↦ c+a·t` is an order/AP-iso; carry the enumeration via
  `Equiv.Set.image`). Rigorous form of the SELF-SIMILARITY probing idea: 3-freeness is
  translation/dilation invariant. Combined with subset-closedness ⟹ a 3-free set is
  3-free inside every AP ⟹ density ≤ α(3) in every residue class.

Cluster now = 10 theorems (DEGS base case; structural: containsAP/missesAP/co-infinite/
univ/subset/affine; density: reduction + conditional resolution; engine: van der Corput).

The frontier (unconditional density bound α(3)≤1/2 etc.) STILL resists — self-similarity
(now rigorous) shows extremizers are self-similar but doesn't bound α (the bound needs the
additive INTERACTION across classes, not per-class structure). Confirmed again.

## PROBING LOG 4 (2026-05-28) — self-similarity COMPLETE

Two more theorems (`Forcing.lean`, verified, axiom-clean, full build green):
- **`isFree_three_of_affine_image`**: converse affine invariance (image 3-free ⟹ source
  3-free; pull back the enumeration along the affine bijection).
- **`isFree_three_apRestrict`**: SELF-SIMILARITY — `S` 3-free ⟹ `{i | c+a·i ∈ S}` is 3-free
  (when infinite). Proof: `affine-image({i|c+a·i∈S}) = S∩AP ⊆ S` is 3-free (subset-closed),
  then converse affine. ⟹ a 3-free set has density ≤ α(3) in every residue class mod a.

**Cluster = 12 theorems.** Structural framework essentially complete:
- base case: DEGS (`hasMonotoneAP_three`)
- structural (Forcing.lean): containsAP, missesAP-infinite, co-infinite, univ-not-free,
  subset-closed, affine-image (both dirs), apRestrict (self-similarity)
- density (Density.lean): `d̄(A)+d_(Aᶜ)=1`, reduction, conditional resolution
- engine (VanDerCorput.lean): vdc has no monotone 3-AP

Frontier (unconditional α(3)≤1/2) STILL open — self-similarity (now fully rigorous) shows
extremizers are self-similar (density α in every class) but the bound needs the additive
INTERACTION across classes, which all elementary angles fail to capture.

## PROBING LOG 5 (2026-05-28) — van der Corput order theory COMPLETE

`VanDerCorput.lean` now fully characterizes the vdc order (verified, axiom-clean):
- `vdcLt_irrefl`, `vdcLt_trans` (only `propext`!), `vdcLt_total`, `vdcLt_trichotomous`:
  vdc is a STRICT TOTAL ORDER on ℕ. Together with `vdc_middle_not_between`:
  **ℕ admits a strict total (dense) order with no monotone 3-term AP.** Clean complete
  story (and the prerequisite for sorting finite sets by vdc = the within-block scrambler).

Framework is now very comprehensive (≈13 named theorems):
- Statement: HasMonotoneAP/IsFree defs + DEGS base case.
- Forcing: containsAP, missesAP-∞, co-infinite, univ-not-free, subset-closed,
  affine-image (both dirs), apRestrict (self-similarity).
- Density: `d̄(A)+d_(Aᶜ)=1`, LV reduction, conditional resolution of #197.
- VanDerCorput: no-monotone-3-AP + strict-total-order (irrefl/trans/total/trichotomous).

## PROBING LOG 6 (2026-05-28) — no-3AP lemma + Thue–Morse observation

- **`isFree_three_of_no_threeAP`** (Forcing.lean, verified): a 3-AP-free infinite set is
  3-free (vacuously). Establishes `IsFree _ 3` is inhabited (e.g. powers of two). Enumeration
  via `Denumerable.ofEncodableOfInfinite` + `classical`.

- **NEW PROBING IDEA — the self-similar #197 partition is THUE–MORSE.** A #197 partition
  `ℕ = A ⊔ B` (both 3-free) is self-reducing: by `apRestrict`, `A∩evens` and `B∩evens`
  partition the evens (≅ℕ) into two 3-free sets, etc. — so a solution exists at every scale.
  Imposing the natural self-similar fixed point `A∩evens = 2A`, `A∩odds = 2B+1` forces (by
  unfolding the binary recursion) `χ_A(n) = χ_A(n/2) XOR bit₀(n) = parity of popcount(n)`.
  So the canonical self-similar candidate is `A = {n : even popcount}` (Thue–Morse), density 1/2.
  ⟹ **"Is Thue–Morse 3-free?" ⟺ essentially "β(3) ≥ 1/2" ⟺ #197 = YES** (with `B` the odd-
  popcount set). LV conjecture β(3)=1/4 ⟹ Thue–Morse NOT 3-free. Evidence for NO: the natural
  recursive enumeration `A = (enum 2A) ++ (enum 2B+1)` is a concatenation of two INFINITE
  sequences — not a valid ω-enumeration (order-type obstruction, same as DEGS). But a cleverer
  ω-enumeration isn't ruled out, so INCONCLUSIVE. Worth: a concrete candidate to attack
  (prove Thue–Morse not 3-free → strong evidence #197=NO; or 3-free → resolves #197=YES).
  DEGS-style forcing fails on A (the AP-completions `2y−x` are often outside A = even-popcount),
  which is exactly why A *might* be 3-free — genuinely open which way.

## ★ MILESTONE (2026-05-29) — POSITIVE-DENSITY 3-FREE SET FORMALIZED (α(3) ≥ 1/4) ★

`Construction.lean` is COMPLETE (verified, axiom-clean {propext,Classical.choice,Quot.sound},
full build green, 8616 jobs). First formalization of the LeSaulnier–Vijay lower bound.
Headline theorems:
- `isFree_S : IsFree S 3` — the LV set `S = ⋃ₖ [2qₖ, 3qₖ−1]` (qₖ₊₁=3qₖ−1) is 3-free.
- `upperDensity_S_ge : 1/4 ≤ upperDensity S`; `upperDensity_S_pos : 0 < upperDensity S`.
- `exists_isFree_upperDensity_pos : ∃ T, IsFree T 3 ∧ 1/4 ≤ upperDensity T`.
Architecture: `threeAP_same_block` (every 3-AP stays in one block) + within-block vdc
RANK (`cntIn` = #{w∈block : vdcLt w v}, a bijection block_k→[0,qₖ) since vdcLt is a strict
total order) + cumulative `C k = Σ_{j<k} qⱼ` ⟹ global `rank : ↥S ≃ ℕ` (Equiv.ofBijective).
3-freeness: a monotone 3-AP in `enum` ⟹ same block ⟹ position-order = vdc-order ⟹ the AP
middle is vdc-middle, contradicting `vdc_middle_not_between`. Density: block k (qₖ elts) sits
below 3qₖ+1, ratio ≥ qₖ/(3qₖ+1) ≥ 1/4 i.o., so limsup ≥ 1/4 (`le_limsup_of_frequently_le`).
This is the LOWER-BOUND side of the #197 density framework (α(3) ≥ 1/4 > 0). The matching
UPPER bound (α(3) ≤ 1/2, β(3) ≤ 1/4) remains the open frontier (see Density.lean reduction).

## PROBING LOG 7 (2026-05-29) — CONSTRUCTION started: key lemma DONE

`Construction.lean` created (verified, axiom-clean, full build green):
- `q` recurrence (q₀=2, qₖ₊₁=3qₖ−1), `q_ge_two`, `q_strictMono`, `q_mono`.
- `inBlock n k := 2qₖ ≤ n ≤ 3qₖ−1`; `S := {n | ∃k, inBlock n k}` (LeSaulnier–Vijay set).
- `block_le_of_lt`: value order ⟹ block-index order.
- **`threeAP_same_block`** (THE KEY LEMMA): every 3-AP `x<y<z` (x+z=2y) of `S` lies in
  one block. Slick LV argument: (a) if y,z in different blocks then z ≥ 2y ⟹ x=2y−z ≤ 0,
  contra x≥4; (b) if y,z share block k but x earlier, then x ≤ qₖ < qₖ+1 ≤ x=2y−z, contra.
  IMPORTANT FINDING: naive power-of-2 blocks FAIL (non-adjacent cross-block 3-APs exist);
  the ratio-3 recurrence qₖ₊₁=3qₖ−1 is *exactly* what makes z≥2y work. Aligned power-of-2
  blocks give density 0. So [2qₖ,3qₖ−1] (size qₖ, positive density) is necessary, which
  forces vdc-RANK-COUNTING (not bit-reversal) for the within-block order.

REMAINING for the construction (the enumeration + density):
- block k has exactly qₖ elements (`Nat.card_Icc`); blocks disjoint; S infinite.
- `cnt v := |{w ∈ block(v) : vdcLt w v}|` is a bijection block_k → [0,qₖ) (rank in the
  vdc strict total order: injective via `vdcLt`-transitivity subset argument + card).
- `C k := ∑_{j<k} qⱼ`; `rank v := C(blockOf v) + cnt v` is a bijection ↥S ≃ ℕ.
  e := (Equiv.ofBijective rank).symm. IsFree via threeAP_same_block + vdc_middle_not_between:
  a monotone 3-AP in e ⟹ values same block ⟹ position-order=vdc-order ⟹ magnitude-middle
  is vdc-middle, contradicting vdc_middle_not_between (it's vdc-extreme). Density positive
  (qₖ≈c·3ᵏ, Σ_{j≤k}qⱼ ≈ (3/2)qₖ, S∩[0,3qₖ] density ≈ 1/2).

## PROBING LOG 8 (2026-05-29) — ATTACK B (2-adic self-similarity recursion) is a DEAD END

Goal was α(3) ≤ 1/2 via the parity split E=S∩2ℕ, O=S∩(2ℕ+1); E/2,(O−1)/2 each 3-free
(`isFree_three_apRestrict`, formalized). RESULT: the recursion is provably VACUOUS.

(1) 3-APs classify by parity of common difference d (verified):
    - d EVEN ⟹ all three terms same parity ⟹ AP lives in E or in O ⟹ recurse into E/2,(O−1)/2.
    - d ODD ⟹ endpoints share parity, MIDDLE has OPPOSITE parity ("cross" AP). Cross constraint
      (placement rule): for even midpoint 2a, its odd reflection-pair {2a−d,2a+d} (in (O−1)/2-coords
      b,c with b+c=2a−1) must be on the SAME temporal side of 2a; symmetric for odd midpoints.
(2) EXACT density identity (formalizable, trivial parity bijection of [0,2M)):
      countMem(S,2M) = countMem(E/2,M) + countMem((O−1)/2,M)
      ⟹ densityRatio(S,2M) = ½(dr(E/2,M)+dr((O−1)/2,M))
      ⟹ upperDensity(S) ≤ ½(upperDensity(E/2)+upperDensity((O−1)/2)).
(3) Recursion: with IH upperDensity(child) ≤ α, get F(α)=½(α+α)=α. IDENTITY MAP. No contraction,
    no fixed-point pin-down. Same vacuity for the β-direction (β ≤ ½(β+α) ⟺ β ≤ α, trivial) and
    for ANY modulus m (F(α)=(1/m)(mα)=α — partition-averaging is intrinsically lossless).

WHY (the failure mode the task warned of is REALIZED): the PROVEN-3-free LV set S_LV=⋃[2qₖ,3qₖ−1]
has BOTH children jointly extremal — numerically (to N=30M) upperDensity(E/2)=upperDensity((O−1)/2)
=1/2 AND lowerDensity(E/2)=lowerDensity((O−1)/2)=1/4, i.e. each child is an affine COPY of S_LV
(E/2,(O−1)/2 are again interval-block sets with the same geometric-3 growth). So S_LV is a 2-adic
SELF-SIMILAR FIXED POINT; the cross constraints carry ZERO density deficit (δ=0). Verified: LV's
actual block-lockstep enumeration satisfies all 13.6M cross constraints in [0,5e4] with 0 violations.
STRUCTURAL CAUSE: the 2-adic split sends ~half the 3-AP constraints to "cross" but they are EQUALLY
numerous and EQUALLY strong as within-parity ones (cross/within ratio → 1); the split relabels
constraints without relaxing them. CAVEAT learned: the converse gluing S=2A∪(2B+1) of two
independent 3-free A,B is NOT auto-3-free in ω — cross-block odd-d APs (e.g. (11,20,29), d=9) need
the children's block phases aligned; finite concat is auto-OK (LV recurrence M(2n)≥2M(n)M(n+1)) but
ω needs phase-compatible block structure. This phase-coupling is the only real "teeth" and it is an
order-type/phase constraint, NOT a density deficit (LV-aligned children glue back to density 1/2).

SALVAGE (formalizable byproduct, TRUE but non-bounding): `countMem_two_mul`,
`densityRatio_two_mul`, `upperDensity_le_half_add` (the exact halving identity + ≤-corollary).
Nice infrastructure linking `apRestrict` to `Density.lean`; does NOT advance the bound.

DO-NOT-REPEAT: parity/modulus self-similarity recursion for an upper bound on α(3)/β(3). The
extremizer is self-similar at every scale, so any per-scale partition-averaging reproduces α exactly.
A bound must use a NON-self-similar functional (additive energy of 2S−S; or a global ω/order-type
invariant), not the residue-class decomposition.

## PROBING LOG 9 (2026-05-29) — ATTACK C: reflection leak FORMALIZED; β(3)<1 REDUCED to a record-rank bound

Goal: β(3)<1 via the reflection leak (at each new-maximum/record placement M at rank t,
the t reflections {2M−p : p∈Pₜ} ⊆ Sᶜ∩(M,2M], so t ≤ |Sᶜ∩(M,2M]|).

FORMALIZED (`Reflection.lean`, builds clean, axiom-clean {propext,Classical.choice,Quot.sound},
full build green 8617 jobs, wired into Erdos.lean):
- `IsRecord e t` (left-to-right maximum); `isRecord_zero`; `rank_le_record_value` (t ≤ e t).
- **`reflection_avoids_of_record`**: the pointwise leak 2M − e s ∉ S for s<t (M=e t a record).
- **`reflection_leak`**: t ≤ ncard(Sᶜ ∩ Ioc M (2M)). The quantitative core (the LV "z≥2y" mechanism).
  Verified numerically against the LV construction: every record's reflected prefix lands in the gap.
- `record_rank_le_countMem_compl`: t ≤ countMem Sᶜ (2 e t+1) (countMem form).
- `exists_record_value_gt`: records have arbitrarily large value (argmax-over-prefix is a record).
- **`recordValues_no_threeAP`** (NEW, clean): the set of RECORD VALUES is 3-AP-free. Reason: records
  in rank order are increasing in value, so a 3-AP among record-values would be a monotone 3-AP.
  ⟹ (via Roth, prose) the NUMBER OF DISTINCT RECORD VALUES below M is o(M) — i.e. the record INDEX is
  sparse. (This does NOT bound the record RANK t; see ★ below. The two are decoupled.)
- **`lowerDensity_le_of_records_dense`** (conditional, sharp): if ∃ᶠ records with rank t ≥ c·(e t) (c>0),
  then upperDensity Sᶜ ≥ c/2, so lowerDensity S ≤ 1−c/2 < 1. Via `le_limsup_iff'` + c·E/(2E+1)→c/2.

★ STATUS — β(3)<1 is REDUCED, not "out of reach" (CORRECTED after adversarial verification). ★
The explorer first concluded "leak inherently o(N) ⟹ β(3)<1 out of reach" via a RANK-vs-INDEX
CONFLATION; the verifier refuted it by direct LV simulation. The correction:
(a) The leak strength at a record is the TEMPORAL RANK t (`reflection_leak`: t ≤ |Sᶜ∩(M,2M]|). Roth (via
    `recordValues_no_threeAP`) bounds only the record INDEX i = #{record values ≤ M} = o(M). t and i are
    DIFFERENT, DECOUPLED counts; "index sparse" does NOT imply "rank small". The o(N) claim was a non-sequitur.
(b) MEASURED on the LV extremizer (to 44291 elts): record rank ratio t_i/M_i ∈ [0.168, 0.379] (mean ~0.21),
    BOUNDED BELOW — does NOT decay — while index ratio i/M_i → 0.0006. LV record ranks are t ≍ value, so LV
    SATISFIES the hypothesis with c ≈ 1/6 (yielding lowerDensity ≤ 0.92, consistent with LV's true 1/4). The
    conditional bound is NON-VACUOUS.
(c) So β(3)<1 REDUCES to a clean ORDER-TYPE lemma: a UNIFORM c>0 lower bound on limsup_records (rank/value),
    over EVERY 3-free enumeration. The final implication is ALREADY FORMALIZED. Genuinely open: can an
    adversary build a density-→1 3-free set whose late records all have rank o(value) (a "sparse rightward
    skeleton")? — i.e. can such a skeleton coexist with the dense interior placements needed for high density?
    The same ω-vs-finite gap as DEGS, localized to the record-rank profile. Neither built nor ruled out here.

DEAD-END byproducts from the same fan-out (all adversarially verified):
- ATTACK B (2-adic self-similarity recursion): VACUOUS. The dyadic-average recursion is F(α)=½(α+α)=α
  (identity), and is 3-freeness-BLIND (holds for random sets). LV is an exact self-similar fixed point (both
  children at upper 1/2, lower 1/4). Partition-averaging over any modulus is intrinsically lossless. Byproduct:
  the halving identity countMem(S,2M)=countMem(E/2,M)+countMem(O',M) (clean infra). Any bound needs a
  NON-self-similar functional. [task #7]
- ATTACK D (flag algebra / permuton): NO for the naive single-window SDP — [0,N) is window-3-free-orderable
  (vdc), so SDP optimum = 1 (the finite-orderability trap exactly). Density is CROSS-SCALE (dilation x→2x);
  needs a dilation-equivariant 2-adic/log-scale limit object, not a scale-invariant permuton.
- ATTACK E (ergodic / Furstenberg): NO-GO. (I) Furstenberg runs on upper BANACH density and LV has Banach
  density 1 (full-run blocks) ⟹ measure-1 system, blind. (II, the real obstruction) 3-freeness is a property
  of an ENUMERATION (well-order of type ω) NOT determined by the subshift of 1_S (two enumerations of the same
  S give the same subshift), so the rank is not a cocycle; correspondence erases exactly the order type.
- ATTACK A (structure-vs-randomness): random pole (random rank ⟹ 1/3 of 3-APs monotone) and smooth pole
  (monotone rank ⟹ ALL monotone) proven; both force the rank onto the 2-adic/vdc fractal. But the leak is
  NECESSARY-yet-INSUFFICIENT for α≤1/2: upperDensity ≤ ½ + ½·limsup G_x/x with G_x/x ≈ 0.2–0.33 on LV (deferred
  sub-x elements), so the single-record inequality is wrong-scaled for α. Needs amortized multi-scale energy +
  a bespoke 2-adic inverse theorem (not in the literature).

META-LESSON (unifying thread): the obstruction is ORDER-TYPE ω, and every density/measure/partition/permuton
tool (B, D, E) is blind to it — the extremizer is "maximally nice" (Banach density 1, self-similar fixed point)
exactly where those tools look. The ONLY surviving handle is the reflection leak (C), because it is order- AND
scale-sensitive (not partition-averaged, not window-normalized). Live paths: the record-rank lower bound (C),
and/or an additive-energy increment on the 2S−S reflection collisions (A).

## PROBING LOG 10 (2026-05-29) — chasing the C reduction; precise frontier of the reflection leak

Target: a universal c>0 with "records of rank t ≥ c·value i.o." for every 3-free enum ⟹ β(3)<1.
Two findings that PIN DOWN the frontier (and show the pure leak cannot close β<1):

1. NAIVE LEMMA IS FALSE. {2ⁿ} is 3-AP-FREE (verified in Lean: x+z=2y with x<y<z among powers of 2 is
   impossible — 2-adic valuation clash), so EVERY enumeration of it is 3-free. Enumerated increasingly,
   eₜ=2ᵗ: every element a record, Mᵢ=2ⁱ at rank tᵢ=i, so limsup(rank/value)=limsup i/2ⁱ=0. NO c works.
   ⟹ the record-rank hypothesis is NOT automatic; the reduction is genuinely DENSITY-CONDITIONAL. The
   correct target is exactly "no 3-free set has lowerDensity 1" = the open β(3)<1 (LV couldn't prove it).

2. SHARPEST LEAK, AND WHY IT STALLS. General (non-record) leak: at any time t, m=eₜ, with a=#placed below m,
   b=#placed above m (a+b=t), reflecting the a lower ones through m lands a points in (m,2m], each
   already-placed-above (≤b) or in Sᶜ ⟹ **|Sᶜ∩(eₜ,2eₜ]| ≥ a−b = t − 2·#{s<t : eₛ>eₜ}**. (Record case b=0
   recovers reflection_leak.) THE WALL: a density→1 set can have SUPERLINEAR running max Rₜ/t→∞ ({2ⁿ}
   already witnesses Rₜ/t→∞ for a 3-free enum). Then every record has rank t=o(value) ⟹ leak ≥t is
   o(value), diluted to density 0; and at interior placements b≥t/2 ⟹ t−2b≤0, leak VACUOUS. Whether
   Rₜ/t→∞ can coexist with lowerDensity→1 IS β(3)<1's hard case. The pure reflection count provably does
   not decide it — same wall as LV/Attack A/C-verifier.

CONCLUSION (honest): the reflection leak is a DEAD END for β(3)<1 by itself, for a precise reason (the
−2b penalty / the superlinear-max regime that the count cannot see). The missing input is genuinely
additive-combinatorial — control the COLLISIONS among the forced completions {2y−x : x,y∈S placed} = the
additive energy / |2S−S| structure of the interior reflections — or a direct order-type/Ramsey
impossibility for an ω-well-order of a density→1 set. This is the LV-hard frontier; not closed here.
DO-NOT-REPEAT: pure record/leak counting for β(3)<1 (now pinned as provably insufficient, not just "hard").

## PROBING LOG 11 (2026-05-29) — additive-energy frontier: attacked; precise NEGATIVE + reframing

Attacked the additive-energy frontier (the "what's needed" from logs 9–10) for α(3)≤1/2 / β(3)<1.
Two concrete energy formulations; BOTH fail, for precise (Lean-checked) reasons:

1. FINITE-WINDOW ENERGY ("ordered Roth"). 3-free ⟺ for every 3-AP (m−d,m,m+d)⊆S,
   (σ(m)−σ(m−d))·(σ(m)−σ(m+d)) ≥ 0 (midpoint rank not strictly between ⇔ equal-sign rank-gaps),
   so #monotone-3-APs = #{negative terms} = 0. An "ordered Roth" (dense ⟹ positive fraction of 3-APs
   midpoint-between, under ANY order) would bound density by Fourier/energy — but it is FALSE for finite
   sets: vdc orders any finite A at density 1 with ZERO midpoint-between 3-APs. No finite ordered Roth ⟹
   finite-window energy/Fourier is killed by vdc (the finite-orderability trap, same wall as flag-algebra D).

2. CROSS-SCALE LEAK ENERGY. Sharpest leak (any placement, m=eₜ, a/b = #placed below/above m):
   |Sᶜ∩(m,2m]| ≥ a−b. Telescoping across octaves WOULD give δ≤1/2 IF octave-records were placed
   "on schedule" (rank≈density·value). FAILS by FREE DEFERRAL (Lean-verified mechanism): place a SMALL
   element y<V/2 LAST in [0,V]. Its rightward reflections 2y−p (p<y placed) satisfy 2y−p<V (stay in
   placed territory [0,V], no leak); and the would-leak reflections y+d>V need d>V−y>y ⟹ partner y−d<0∉S
   (don't exist). So deferring small elements creates ZERO complement; the leak vanishes there. Hence the
   leak — record or interior, single- or multi-scale — cannot force the bound.

REFRAMING (the genuine insight): EVERY consequence of the LOCAL placement rule — reflection leak,
finite-window energy, order-type centroid/DEGS trap — is provably INSUFFICIENT for α≤1/2 / β<1. The
rightward "escape" cost IS the leak (fails by free deferral); leftward/interior placements give only
satisfiable temporal constraints (no complement). So the real obstruction is GLOBAL ω-ORDER-TYPE
satisfiability — "can a density-δ AP-betweenness structure be realized as an ω-well-order with every
3-AP midpoint extreme?" — which is NOT an additive-energy statement and NOT local. The additive structure
only SUPPLIES the betweenness constraints; the hardness is purely the ω-realizability. This is, I believe,
exactly why LV (and the field) are stuck: #195–197 is an infinitary / order-type problem wearing
additive-combinatorics clothing. A non-local tool (infinitary Ramsey, or a global potential invisible to
finite windows) is needed; not in hand, and beyond a session.

DO-NOT-REPEAT (frontier): additive energy / Fourier / leak-counting / partition-averaging / permuton /
ergodic for α≤1/2 or β<1 — ALL reduce to the leak (free-deferral) or to a false finite ordered-Roth
(vdc). The open content is genuinely global-ω-order-type. Status: FRONTIER MAPPED; bound not closed.

## PROBING LOG 12 (2026-05-29) — sought a GLOBAL POTENTIAL; formalized rank descent (first ω-essential result)

The frontier analysis said: the missing tool is a GLOBAL invariant invisible to finite windows. The
natural candidate is THE RANK ITSELF (well-order of type ω, no infinite descent). Made it bite via
infinite descent and FORMALIZED it (`Descent.lean`, builds green, axiom-clean {propext,Classical.choice,
Quot.sound}):
- **`rank_descent`**: for a 3-free enum with a:=e 0 (global rank-min), x∈S, x>a, 2x−a∈S ⟹ rank(2x−a) <
  rank(x). (AP (a,x,2x−a) has midpoint x; a rank-min ⟹ x rank-max ⟹ 2x−a precedes x.)
- **`no_infinite_doubling_orbit`**: iterating T(x)=2x−a (Tᵏx = a+2ᵏ(x−a)) strictly DESCENDS ranks while
  in S; ℕ has no infinite descent ⟹ S contains NO full doubling orbit {a+2ᵏ(x−a)}. This is the FIRST
  result in the whole project that ESSENTIALLY uses the ω order type (false for finite enums, invisible to
  any finite window). The right TYPE of object.

HONEST LIMIT: it is only a DENSITY-0 obstruction. The orbits {a+q·2ᵏ} (q odd) partition (a,∞), each
exponentially sparse; descent ⟹ each has ∞-many Sᶜ-gaps, but the gaps can sit at large k (outside any
window), so NO lower bound on Sᶜ density follows. Worse, descent CONFIRMS the adversary's structure rather
than contradicting it: orbit-tops (large values) get LOW rank ⟹ "early-placed = large" = the
superlinear-max / sparse-rightward-skeleton behaviour that already defeats the leak. Using non-min base
points e_j fails (only e_0 is unconditionally rank-min, giving clean descent). Combining descent + leak:
no gain (both align with early=large). So a DENSITY-STRENGTH global potential remains elusive — matching
the field's impasse. Descent is the cleanest ω-essential artifact, but not the bound.

NET (whole investigation): α(3)≥1/4 constructed+formalized; β(3)<1 reduced to a record-rank lower bound
(formalized implication); 5 attack families ruled out with precise mechanisms; rank descent formalized as
the first ω-essential consequence. The remaining gap (α≤1/2, β<1) is a genuine global-ω-order-type problem
with no known tool — a natural, honest stopping point. ~21 theorems, all axiom-clean.

## PROBING LOG 13 (2026-05-29) — PIVOT to #196/#195 (the 4-AP question); 2^k-divisible case fan-out

New target (after consolidating #197 work): the 4-AP question. #196: does a permutation of ℕ avoiding
monotone 4-APs exist? (Believed YES.) Adenwalla 2022 builds one avoiding 4-APs of difference NOT divisible
by 2^k (each fixed k); the OPEN barrier is differences with unbounded v₂(d) — the 2^k-divisible case.

★ CLEAN REFRAMING (recovered from Phase-1 fan-out; the key clarification) ★
View a permutation as a LINEAR ORDER (well-order, type ω) on ℕ. "Avoid monotone 4-AP" = no value-4-AP is
order-monotone.
- **A 4-AP-free order EXISTS densely**: the vdc/bit-reversal DENSE order has NO monotone 3-AP
  (`vdc_middle_not_between`), hence NO monotone k-AP for ANY k≥3 (a monotone 4-AP contains a monotone 3-AP).
  [This resolves a Phase-1 agent contradiction: vdc DOES avoid 4-APs; the "vdc fails for 4-APs" claim was wrong.]
- So **the ONLY obstruction to #196 is realizing a 4-AP-free order as TYPE ω** (vdc is dense — infinite
  descending chains 2,4,8,…). SLACK vs #197: a type-ω 4-AP-free order MAY contain monotone 3-APs (3-AP-free
  ω is impossible by DEGS; 4-AP-free ω is the open question).
- **DEGS (type ω, proven)**: doubly-exponential blocks B_k=[s_k, s_k+2^(2^k)−1], vdc within, avoids monotone
  5-APs. Interval-block methods have a PROVABLE **5-FLOOR** ("1+2+2": ≤2 AP-terms per vdc block + cross-block
  count caps longest monotone AP at 5). To reach 4 you MUST go beyond interval blocks.

★ THE 2-ADIC REDUCTION (heart of the barrier) ★
A monotone 4-AP v,v+d,v+2d,v+3d with 2^k|d lies in ONE residue class mod 2^k (all ≡v) and rescales (/2^k)
to an ODD-difference 4-AP. So: an order avoids ALL monotone 4-APs IFF every residue class mod 2^j (rescaled)
avoids ODD-difference monotone 4-APs, for all j. ⟹ #196 reduces to a SELF-SIMILAR (2-adic) order avoiding
odd-difference 4-APs at all scales at once. Adenwalla = bounded v₂ (finitely many scales) via a residue-mod-2
INTERLEAVING; the BARRIER: the even-class descent loses the interleaving. Odd-d 4-APs alternate parity
(terms 0,2 one parity; 1,3 the other) — the interleaving must scramble that.

FORMALIZABLE WINS (recovered; being banked in Phase 2):
- The project's self-similarity machinery is **k-GENERIC** (not 3-specific): the function-level affine
  invariance `HasMonotoneAP (c + a·g) k ↔ HasMonotoneAP g k` (fwd all k; bwd needs k≥2) re-proves
  subset/affine/apRestrict for any k. Self-similarity "costs nothing in k".
- The dyadic 4-AP reduction (residue-class containment + odd rescale). Cleanest target: `IsFree (univ) 4`
  (= `Erdos196Avoidable` = `¬Erdos196`).
- DEGS-5 is formalizable by swapping LV widths q_k → 2^(2^k) in Construction.lean + the 1+2+2 counting lemma
  (would be the first formalization of DEGS's 5-AP construction).

PROCESS NOTE: Phase-1 workflow lost its structured output (schema-forced output choked after long runs; the
numerics agent self-deadlocked polling background jobs). Phase-2 fix: plain-text returns, synchronous
time-boxed numerics. Findings above recovered from agent transcripts.

CRUX for Phase 2: build a type-ω, 2-adically self-similar order on ℕ avoiding monotone 4-APs (break the
interval-block 5-floor using the 3-AP slack) — or prove the all-scales self-similar fixed point is obstructed.

## NEXT IDEAS
- **Finish the construction enumeration** (cnt bijection + rank bijection + IsFree + density).
  The within-block vdc-rank bijection is the crux; prove directly (filter-subset + card) to
  avoid packaging vdc as a `LinearOrder`.
- Frontier: additive-energy / Fourier increment on `2S−S` collisions (genuine research).
- Additive-energy / Fourier control of the `2y−x` collisions (Attack 2) → maybe α(3)<1.
- Non-interval (parity-recursive / 2-adic) constructions for the lower bound (Attack 3).
- Formalize the LV constructions + the `α+β<1 ⟹ ¬#197` reduction (framework for the attack).

## Open verification TODOs
- [ ] Confirm exact DEGS results (ℕ vs ℤ vs doubly-infinite; which length for which
      domain). The web summaries were slightly inconsistent — read the actual paper.
- [ ] Confirm believed answers / open-problem statements in Adenwalla's paper.
- [ ] Re-confirm none of #195/#196/#197 was resolved 2024–2026.

## ATTACK A (2026-05-29) — structure vs randomness dichotomy: MAPPED + NEGATIVE result on RL

Convention (verified by simulation, /tmp/probe_fix.py): monotone 3-AP <=> value-midpoint a+d is
the ORDER-MEDIAN (rank between the two endpoints). 3-free = ZERO monotone. Equivalently (clean):
3-free <=> every value-3-AP has its midpoint placed temporally FIRST or LAST (rank-extreme).

THREE FRAGMENTS PROVEN & COMPILE (axiom-clean; /tmp/attackA_all.lean):
- RANDOM POLE (median_trichotomy + median_exclusive): among 3 distinct ranks EXACTLY one is the
  strict median. => MonoCount = #{3-APs: midpoint is rank-median}. Random rank => each element is
  median w.p. 1/3 => fraction 1/3 of 3-APs monotone (verified 0.333). So pseudorandom rank forces
  >0 monotone APs. The U^2/Fourier inverse needed: control of the "order-indicator" s(u,v)=1[v before u];
  MonoCount = sum_AP [a+b-2ab] with a=s(mid,left),b=s(mid,right). UNCONDITIONAL increment NOT obtained.
- SMOOTH POLE (smooth_pole): if rank is monotone in value (e.symm monotone) then EVERY value-3-AP is
  monotone (midpoint at median position). Verified: identity/reverse/x^2 profiles => 100% monotone.
  CLEAN unconditional theorem.
- SYNTHESIS core (reflection_leak): at a new-max placement x=e(t) (all earlier < x), every reflection
  2x-p (p=e(s), s<t) must avoid S. => |S^c cap (x,2x)| >= t.

DECISIVE NEGATIVE FINDING (the real contribution): the reflection leak ALONE does NOT prove
alpha(3) <= 1/2, even granting order-type omega. Exact accounting (/tmp/probe_iterate.py):
  RL at record x  =>  A(2x) <= x + G_x,  where G_x := #{y<x : y in S, y placed AFTER x}.
  => upper density <= 1/2 + (1/2) limsup_{records} G_x / x.
The whole gap is the lemma "G_x = o(x) along records" (no positive fraction of sub-x elements is
deferred past a record). THIS FAILS FOR LV ITSELF: in the LV extremizer G_x/x ~ 0.2-0.33 at block-end
records (the within-block vdc order defers ~25% of sub-x elements past the record), yet LV has density
exactly 1/2 (because 2x lands in the inter-block GAP). Certified RL bound for LV oscillates in
[0.5, 1.5], NEVER converging to 1/2 (/tmp/probe_RL_actual.py). CONCLUSION: the factor-2 reflection is
NECESSARY but the naive "leak at records" is NOT SUFFICIENT; the bound is wrong-scaled. A correct proof
must combine the leak at MANY records/scales with the deferred-element constraints those G_x elements
themselves later incur — i.e. an amortized/energy argument, not a single-record inequality.

FINITE-ORDERABILITY TRAP re-confirmed sharply: vdc orders [0,2^k) 3-freely at density 1, but the
vdc-rank of a FIXED value changes with k (value 2 has rank 1,2,4,8,16 in windows k=2..6) => vdc is the
DENSE dyadic order, NOT a single bijection to N. The omega obstruction = "no single rank realizes the
window-orders simultaneously". Greedy single-omega-order builds get stuck at 2^k sparse sets (density->0).

INTERVAL-BLOCK OPTIMALITY (numerics, /tmp/probe_union.py): over all gapped interval-block + vdc-within
constructions, max density = exactly LV's ~1/2 (params f=0.5 blocksize, g=2.0 gap = LV). Denser => not
3-free (cross-block z>=2y fails). Strong support for alpha(3)=1/2 but ONLY for interval constructions.

WHICH INVERSE THEOREM: the U^2 (Fourier/Roth) inverse is the natural tool for the random pole, but the
escape (vdc) is a 2-adic/bit-reversal object that U^2 does NOT see as "structured" in the usual sense
(vdc-rank as [0,1)-valued is a bracket/2-adic phase, not a single linear phase e(xi x)). So the needed
object is a BESPOKE 2-ADIC INVERSE THEOREM: "a bijective rank S->N avoiding the median-event on all
3-APs must be a 2-adic (bit-reversal-graded) order", which DOES NOT EXIST in the literature and would
have to be invented. Even granting it, the density-1/2 conclusion needs the omega-truncation argument
that the RL fails to supply cleanly (see negative finding). Net viability of Attack A as stated: LOW-MODERATE.

## PROBING LOG 14 (2026-05-29) — #196/#195 IMPOSSIBILITY ATTACK: calibrated refutation; YES is the right bet

Phase: attack the OPPOSITE direction (is every type-ω order FORCED to contain a monotone 4-AP?),
exploiting the all-scales 2-adic reduction. Verified everything synchronously (no `timeout` binary on
this macOS; used in-Python wall-clock guards, bounded N). Sources re-read in full: Adenwalla 2211.04451
(extracted to /tmp/adenwalla.txt) and LeSaulnier–Vijay 1004.1740 (/tmp/lv.txt).

★ LITERATURE RE-CONFIRMED ★ #196/#195 (length-4) OPEN as of Adenwalla 2024 (his Question 1 verbatim:
"Do there exist permutations of the positive integers or the integers that avoid 4-APs? ... it seems
some new techniques will need to be applied"). DEGS built a DOUBLY-INFINITE (type ℤ-ish, two-sided)
4-AP-free perm of ℕ — NOT type ω. So the order-type obstruction is the genuine, acknowledged content.

★ EXACT LV ODD-DIFFERENCE CONSTRUCTION (the base case) — REBUILT & VERIFIED (/tmp/lv_exact.py, lv_verify.py) ★
σᵢ = 3AP-free perm of the 2ⁱ consecutive EVENS {(4ⁱ+2)/3, …, (4ⁱ⁺¹−4)/3};
πᵢ = 3AP-free perm of the 2^{i−1} consecutive ODDS {(4ⁱ+2)/6, …, (4ⁱ⁺¹−6)/6};
order = σ₁π₁σ₂π₂σ₃π₃⋯  (TYPE ω — finite blocks listed in order). KEY INVARIANT (verified 0 violations
/ 444k samples): if odd x precedes even y then 2x−y<0. ⟹ NO odd-difference monotone 4-AP (longest
odd-d monotone AP = 3, measured; 0 odd-d 4-APs for all start<2000). So ODD-d 4-AP-avoidance IS
ACHIEVABLE IN TYPE ω. THIS IS DECISIVE for the diagonal question (below).

★ THE DIAGONAL FORCING HAS NO FOUNDATION (the main impossibility finding) ★ /tmp/diagonal_logic.py
Geneson's Thm 5 (proven): every perm of ℕ has a 3-AP with diff divisible by k, for all k. Its engine is
the SELF-REDUCTION: the multiples-of-k subsequence /k is a perm of ℕ ⟹ has a 3-AP (DEGS base) ⟹ pulls
back. Trying the SAME for 4-APs: "multiples-of-k /k is a perm of ℕ ⟹ has a 4-AP" — but "every perm of ℕ
has a 4-AP" IS #196. **CIRCULAR.** The 3-AP diagonal bites only because DEGS (3-AP forcing) is a THEOREM.
The 4-AP diagonal would need a base case "every type-ω order has an ODD-d 4-AP" — and that base case is
**FALSE** (LV above). So there is NO seed for an all-scales diagonal forcing. The all-scales 2-adic
reduction is SELF-REFERENTIAL for 4-APs (#196 ⟺ #196 one scale down), not an independent obstruction.

★ THE 2^k BARRIER, MADE PRECISE (/tmp/barrier_analysis.py) ★ Adenwalla Thm 4 (n=2^k): residue-mod-2^k
INTER-class interleaving kills 4-APs with d not divisible by 2^k. The remaining (d divisible by 2^k)
4-APs live in ONE residue class mod 2^k; rescaling that class /2^k, the INDUCED order is a plain
interval-block order (the inter-class interleaving is GONE) — which has the 5-floor (measured 5–6, NOT
≤3). To break the next scale you must interleave by parity WITHIN each class = use n=2^{k+1}, a globally
different construction (different scaling/residue count). The k-constructions are mutually incompatible;
a single value n has ONE rank. THIS is "the even-class descent loses the interleaving", confirmed.

★ LV IS NOT SELF-SIMILAR (/tmp/selfsim_test.py, verify_4ap.py) ★ LV's order restricted to EVENS,
rescaled /2, HAS an odd-d monotone 4-AP: explicitly the evens 2,4,6,8 have LV-ranks 0,1,3,5 (strictly
increasing) = a monotone 4-AP of (original) difference 2. LV only ever promised ODD-d avoidance; the
even-class descent fails. So LV alone does NOT solve #196 — exact failure exhibited.

★ WHY 3-AP-free ω is IMPOSSIBLE but 4-AP-free ω is OPEN — the order-type distinction (/tmp/omega_distinction.py
+ adversarial.py, with a SELF-CORRECTION) ★ Let a = rank-min (rank 0), orbit Oₑ={a+iₑ}.
- 3-AP-free: Oₑ must avoid monotone 3-APs in BOTH directions; T(x)=2x−a gives a SINGLE strictly
  rank-descending chain a→2a... wait, descends — no infinite descent in ω ⟹ contradiction (DEGS /
  Descent.lean's `no_infinite_doubling_orbit`). Cap = 2, AND a single monotone chain.
- 4-AP-free: Oₑ must avoid monotone 4-APs ⟹ longest monotone run ≤ 3, in EITHER direction. ADVERSARIAL
  CORRECTION (caught an overclaim of mine): I first said "only the increasing direction is banned from
  a"; but the orbit minus a must ALSO be 4-AP-free among itself, so pure descent (decreasing 4-run) is
  ALSO banned. The honest statement: the orbit just has to be a 4-AP-free SUB-ORDER = the SAME problem
  recursed one scale down (self-similar). The cap is 3 (with slack: 3-runs allowed) and the descent can
  RESET — so there is NO infinite-descent contradiction. The DEGS potential (rank descent) that kills
  3-AP-free ω structurally FAILS for 4-AP-free ω, for this precise reason. No Ramsey/Erdős–Szekeres
  forcing either: an infinite increasing(value,rank) subsequence can be AP-free (e.g. powers of 2).

★ "DRIFT IS FORCED" — a clean PROVEN lemma (Sub-claim A, /tmp/drift.py) ★ If an order has BOUNDED
displacement (|rank(n)−n| ≤ C for all n), then for any AP with common difference d > 2C the terms are
placed in value-order = strictly increasing rank = MONOTONE, giving arbitrarily long monotone APs.
⟹ ANY 4-AP-free type-ω order MUST have UNBOUNDED displacement. (Verified: C=4 order has longest mono
AP = 75, all from d=4.) This is the rigorous quantification of "type ω forces drift" — but it is
NECESSARY-only: unbounded (yet finite-per-element) displacement is exactly what Adenwalla-window
avoiders have (displacement growing with the window's k), and whether a SINGLE coherent ω profile
realizes all scales is the open content. Drift does NOT force a 4-AP; it forces unbounded drift.

★ KÖNIG-TREE STATUS (re-confirmed) ★ Finite all-scales 4-AP avoiders of [1,N] EXIST for every N
(Adenwalla Thm 4 with 2^k > N/3 ⟹ on [1,N] every d<2^k is "not divisible by 2^k" ⟹ ALL 4-APs avoided
on the window). [My ad-hoc single-interval Adenwalla code gave 5–6 because it doesn't faithfully
reproduce his OVERLAPPING [aⁱ,aⁱ⁺ⁿ) interleaving — the THEOREM is what guarantees the window avoiders.]
So #196 is EXACTLY the 3-AP situation: avoiders exist at every finite level (a finitely-branching tree
⟹ an avoiding LINEAR ORDER exists by König), and the entire question is whether the order type can be ω.
For 3-APs the answer is NO (DEGS forcing). For 4-APs the forcing mechanism PROVABLY does not transfer.

═══ HONEST VERDICT (task part 3) ═══
1. Is there a forcing that every type-ω order has a monotone 4-AP? — NO viable one found, and a precise
   reason it should NOT exist: (a) the all-scales diagonal is self-referential (needs an odd-d 4-AP
   base case that LV REFUTES); (b) the rank-descent potential that kills 3-AP-free ω only caps the
   orbit at 3 with resettable slack for 4-APs (no infinite descent); (c) no Ramsey/E–S forcing (sparse
   increasing sets are AP-free). Every forcing fragment that WORKS for 3-APs has a concrete 4-AP escape.
2. Drift: type ω FORCES unbounded displacement (PROVEN, clean). It does NOT force a 4-AP — unbounded
   finite displacement is consistent with avoidance (Adenwalla windows realize it per-scale).
3. Does Adenwalla make YES overwhelmingly likely? — YES, this is the calibrated bet. Adenwalla covers
   every BOUNDED band of scales (d not divisible by 2^k, ANY k) in type ω; the ONLY gap is gluing all
   k simultaneously, an order-type/phase-coherence problem with NO impossibility obstruction (the two
   candidate obstructions — diagonal forcing and rank-descent — both PROVABLY fail for 4-APs). The
   problem is "wearing additive clothing": it is a Π⁰-style coherence/realizability question, the SAME
   flavor as 3-APs but with the unique forcing lever removed. Believed answer YES (#195 k*=3) is well
   supported; impossibility is REFUTED at the level of every known forcing tool. Not closed (the
   coherent all-scales ω construction is genuinely unbuilt), but the weight of evidence is firmly YES.

CONSTRUCTION TARGET (most promising, for a future YES attempt): a single ω order whose restriction to
every residue class mod 2^j, rescaled, is AGAIN such an order AND parity-splits (LV-invariant) at its
top scale — i.e. a TRUE self-similar fixed point of the LV mechanism, with the block scalings chosen so
the per-scale geometric layouts are mutually compatible (the phase-coherence the 2-adic reduction needs).
The obstruction to naive recursion: full recursion = sort by v₂(n) = ∞-many ∞-classes concatenated = NOT
ω (same wall as vdc). The 3-AP SLACK (3-runs allowed at each scale) is the room that vdc/DEGS-5 don't use
— a working construction must spend exactly the slack to keep displacement finite-per-element at all
scales. This is the precise crux; unbuilt here, but un-obstructed.

## ★ PROBING LOG 16 (2026-05-29) — ADENWALLA 2^k MECHANISM RECONSTRUCTED; the all-scales diagonal CONFLICT pinned ★

Task: extend Adenwalla (bounded v₂) to ALL scales (the actual #196/#195 4-AP question), or find the precise
two-scale conflict. READ the actual paper (arXiv:2211.04451 v7, /tmp/adenwalla.txt) — Theorem 4 reconstructed
& VERIFIED numerically (/tmp/adenwalla_thm4b.py: 0 violations for n=2 AND n=4, ~5000 values each).

ADENWALLA THEOREM 4 (exact). For n=2^k, a≥3: blocks Xᵢʲ = a 3-AP-free perm of {x≡j mod n : x∈[aⁱ,aⁱ⁺¹)}.
S = perm of [1,n] avoiding 3-APs MOD n (exists iff n=2^k; the vdc/bit-reversal residue order works). Listing R:
initial row of n blocks (octave 0, residues in S-order), then rows t=1,2,…; row t lists blocks
(octave e = tn−p, residue Sₚ) for p=0..n−1 — a DESCENDING octave staircase (e: tn,tn−1,…,(t−1)n+1) paired
against the residue order S. PROOF that R breaks every 4-AP with d≢0 mod n: REACH BOUND — for an increasing
4-AP m₁<m₂<m₃<m₄, m₄ = m₁+3d < 3m₂ (since m₁≥1), and m₂∈octave e₂ ⟹ m₄<3·aᵉ²⁺¹≤aᵉ²⁺² ⟹ **m₂,m₃,m₄ sit in at
most 2 consecutive octaves {e₂,e₂+1}** (m₁ free, lower); RESIDUE ARGUMENT — the staircase forces the residues
of m₂,m₃,m₄ to appear in increasing S-index l₁<l₂<l₃; d≢0 mod n ⟹ 3 distinct residues forming an AP mod n;
S avoids 3-APs mod n ⟹ contradiction. ∎

(1) THE RESOURCE CONSUMED PER SCALE k: a 3-AP-free-mod-2^k residue order S_{2^k} COUPLED to a descending
octave staircase of ROW-LENGTH 2^k. R_{2^k} breaks ALL scales 0,1,…,k−1 at once (verified v₂(d)<k ⟹ broken).
So low scales are NOT the problem — one big modulus does them all; the diagonal only needs modulus→∞ as VALUES
grow, to catch ever-higher scales.

(2) DIAGONAL ATTEMPT + THE EXACT CONFLICT. Two assets are genuinely compatible:
   - FACT 1 (verified): "all evens before all odds" breaks EVERY odd-difference AP of length ≥3 (odd-d AP
     alternates parity p,1−p,p,1−p ⟹ ranks low,high,low,high — never monotone). This is the v₂=0 breaker.
   - FACT 2 (verified k=1..5): the vdc residue orders are NESTED — S_{2^{k+1}} restricted to even residues, /2,
     EQUALS S_{2^k}. So the residue half of the staircase telescopes perfectly across scales. NO conflict there.
   THE CONFLICT IS THE OCTAVE BACKBONE (FACT 3, verified):
   - ω order-type REQUIRES the octave backbone to be (roughly) ASCENDING — each value finitely many
     predecessors. A modulus-INDEPENDENT ascending octave order makes the construction LEAK cross-octave APs
     at EVERY scale (/tmp/fixed_octave_order.py: 15 violations, scales 0,1,2 — e.g. (5,7,9,11) d=2 monotone),
     because later AP terms land in higher octaves ⟹ ranks ascend ⟹ monotone. Within-octave scrambling can't
     catch a cross-octave AP.
   - Breaking scale k REQUIRES Adenwalla's octave↔residue COUPLING = a DESCENDING run of length 2^k. But a
     single octave order cannot be a descending-run staircase for two different lengths: mod-2 gives octave
     order [2,1,4,3,6,5,…] (runs of 2), mod-4 gives [4,3,2,1,8,7,6,5,…] (runs of 4). These DISAGREE — mod-2
     puts octave 1 BEFORE 3 (different runs [2,1],[4,3]); mod-4 puts 3 BEFORE 1 (same run [4,3,2,1]).
     12 such clashes on octaves 1..8. Confirmed at the integer level: Adenwalla R₈ vs R₄ have 1640 order
     inversions on shared values (/tmp/redesign_staircase.py), concentrated at far-apart octaves with equal
     residue mod 4 — the row-grouping length, not the residue order, is what's irreconcilable.

(3) NO CLEAN SELF-SIMILAR FIXED POINT (this session). Every consistent (modulus-stable, ω) variant LEAKS:
   - telescoping modulus that doubles between octave-regimes with empty-octave GAPS (so reach-2 APs can't
     straddle a doubling) STILL leaks (/tmp/final_creative.py, 407k values): residual violations are EXACTLY
     at scales j ≥ k of each regime's fixed modulus 2^k. A finite regime of modulus 2^k breaks only scales <k;
     any AP of scale j≥k living inside it survives. So a fixed modulus is never enough, and modulus→∞ re-invokes
     the run-length conflict (the octave backbone can't change row-length coherently).
   THE PRECISE TWO-SCALE CONFLICT (deliverable): scales k and k+1 demand octave row-lengths 2^k and 2^{k+1};
   the corresponding descending-run octave orders DISAGREE on the relative order of octaves that lie in the same
   2^{k+1}-run but different 2^k-runs (witness: octaves 1 vs 3 for k=1). Equivalently — the ONLY octave order
   simultaneously presenting nested descending runs of EVERY length 2^k is the full bit-reversal (vdc) order on
   the octave index, which is DENSE (not ω: a fixed octave has ∞-many vdc-predecessors). So: {ω order type} ∧
   {Adenwalla residue-staircase mechanism at all scales} are INCOMPATIBLE on the octave backbone. This is the
   2-adic barrier made precise — exactly the place Adenwalla's paper says "some new techniques will be needed."

HONEST VERDICT: the natural diagonalization of Adenwalla's mechanism CANNOT close #196 — proven (numerically +
structurally) to hit the run-length/ω conflict. This does NOT prove #196 is NO (the residue staircase is only
ONE sufficient mechanism; FACT 1+2 show the residue side telescopes, so a NON-staircase octave coupling that is
ω AND catches cross-octave APs at unbounded scale is not ruled out — it would have to abandon the
"ascending-octave or descending-run" dichotomy, e.g. exploit the 3-AP slack). NEW ASSET for future: the vdc
residue nesting (FACT 2) + the tight 2-octave reach (m₂,m₃,m₄ within 2 consecutive octaves) — these are the
clean ingredients a future construction can build on. Scripts: /tmp/adenwalla_thm4b.py (Thm 4 verified),
/tmp/fixed_octave_order.py (ω-backbone leaks), /tmp/redesign_staircase.py (R₄/R₈ inconsistent),
/tmp/final_creative.py (telescope leaks at scale≥k), /tmp/consolidate.py (3 facts).
DO-NOT-REPEAT: diagonalizing Adenwalla's descending-run staircase to all scales (pinned: run-length conflict
vs ω). A YES needs a genuinely different octave-coupling that is ω and scale-unbounded.

## PROBING LOG 15 (2026-05-29) — #196 CONSTRUCTION crux: SAT-based omega-feasibility (NEW, decisive numerics)

Phase: build an explicit type-omega 2-adic self-similar order avoiding monotone 4-APs (or pin the
obstruction). Synchronous numerics only (SIGALRM guards in /tmp/tlimit.py; no `timeout` binary on macOS).
Framework /tmp/lib.py (key->order, longest-AP, has_4ap, omega rank-stability). SAT via pysat Glucose3
(order vars b(u,w)=u-before-w + transitivity + 4-AP clauses both directions; cross-verified vs brute force
/tmp/c41_verify_sat.py — encoding CORRECT).

CONSTRUCTION FAMILIES TESTED (all FAIL to reach zero 4-APs while omega; abundant 4-APs at all v2 scales):
- Differing-bit selectors (compare m,n at a chosen differing bit): ONLY min(=vdc, dense not-omega, 0 APs)
  and max(=identity, omega, all APs) are TRANSITIVE. All "in-between" selectors (second-lowest,
  highest-isolated) are NON-TRANSITIVE (1200+ violations N=32) — `sorted` artifacts, DEAD END. [/tmp/c9]
- Fully-self-similar shuffles (order = fixed merge string s of two copies evens=2*O, odds=2*O+1):
  EXHAUSTIVE over periodic s up to period 8 — ZERO are 4-AP-free (floor 4; best omega ones admit the
  d=1 AP 0,1,2,3). Non-periodic s (Thue-Morse, ruler) WORSE (6-8). PROVEN-numerically floor: a single
  fixed-merge self-similar order has longest-AP >= 4. [/tmp/c12,c13,c15]  DO-NOT-REPEAT: single fixed
  merge string.
- Scale-varying recursive merges (TM-shifted, vdc-level, biased-TM): biased-TM is omega (rank(1)=2 stable)
  with the FEWEST odd-d 4-APs of any omega construction (~383 vs 5461 identity) but still NONZERO. [/tmp/c38]
- Closed-form omega keys: Gray code / inverse-Gray (igray) cut odd-d 4-APs ~15x (363 on [0,512)) and is
  omega — best closed form — but nonzero. msb-then-vdc-of-rest, lazy-bit-reversal, interleave: all nonzero
  abundant. [/tmp/c19,c31]
- Magnitude-band [2^k,2^{k+1}) + evens-first/vdc within: WORSE (7). Geometric ratio-2 bands bad. [/tmp/c5]
- Doubly-exp interval blocks + vdc: 5-floor REconfirmed (witness d=2 = cross-block). Alternating reversal
  -> longest-run 4 but still 427 odd-d 4-APs. Uniform tiling of any fixed within-block scramble: terrible
  (lined-up blocks, AP=24). [/tmp/c3,c4,c14,c30]

★ KEY NEW DECISIVE RESULTS (SAT, the real contribution of this log) ★
1. FACT 1 reconfirmed: "all evens before all odds" kills odd-d (v2=0) monotone APs of length>=3 (longest
   odd-d run = 2), BUT globally => rank(1)=N/2 -> infinity = NOT omega (= the vdc wall, c1). The razor:
   evens-before-odds breaks odd-d 4-APs but destroys omega; the 3-AP SLACK (3-runs allowed) is the only room.
2. ★ THE 2-ADIC/COMPACTNESS DISTINCTION MADE PRECISE (why #196 is genuinely open) ★ A 4-AP-free TOTAL
   ORDER on N EXISTS by compactness/Konig (finite avoiders exist at every N: vdc-restricted-to-[0,N) is one,
   verified). vdc itself is such an order. But TYPE-OMEGA is NOT a closed/finitary condition — so compactness
   does NOT deliver an omega avoider. THIS is the entire content of #196. Confirmed: greedy "extend finite
   order preserving relative order" CHAINS DIE (stuck at 24 though fresh [0,28) exists, c34) — paths in the
   Konig tree can be finite; existence of an infinite (omega) path is exactly the open question.
3. ★ DRIFT LEMMA quantified by SAT (min uniform max-displacement of a 4-AP-free order of [0,N)) ★:
   N: 12 16 20 24 28 32 36 40   -> min-max-disp: 2 4 4 5 6 7 8 10. GROWS (confirms displacement->inf, the
   drift lemma) at rate ~N/4-N/5 (roughly linear). Linear growth is FULLY CONSISTENT with type omega (finite
   displacement per element); does NOT obstruct. [/tmp/c28b,c32]
4. ★ OMEGA SURROGATE FEASIBLE TO N=64 (the most YES-leaning evidence) ★: a 4-AP-free order of [0,N) with
   rank(v) <= 2v+6 for ALL v (= genuine type-omega profile, linear displacement) is FEASIBLE for every N
   tested up to 64 (c40). Tighter: rank<=1.5v+4 ok to 40; rank<=1.3v+4 ok @32 fails @40; min linear slope
   (add=6) crept 1.0(N<=32)->1.2(N=40) — borderline whether a clean LINEAR-displacement omega order exists
   or displacement must be slightly super-linear. Either way an omega avoider is strongly plausible.
5. ★ EMERGENT RELAXED SELF-SIMILARITY ★ The SAT omega-optimal orders are NOT exactly self-similar, but
   their even-residues/2 and odd-residues/2 orders are NEARLY IDENTICAL 4-AP-free orders (e.g. both start
   7,9,8,0... at N=48, c39). I.e. when FORCED omega, the solver spontaneously produces orders where both
   residue classes rescale to (almost) the same 4-AP-free order — exactly the relaxed self-similarity the
   2-adic reduction asks for. Encouraging for YES.

VERDICT (this log): No explicit closed-form/simple-recursive omega 4-AP-free construction found (consistent
with the literature; problem open). BUT three independent SAT probes (initial-segment placement always = m;
omega surrogate rank<=2v+6 feasible to N=64; emergent relaxed self-similarity) all lean #196 = YES, with the
honest caveat that finite-N feasibility cannot certify the infinite (omega) limit — the same compactness gap
that IS the open problem. Best explicit omega candidate so far: inverse-Gray-code order (igray, 15x fewer
odd-d 4-APs than identity, omega) — a good SEED for a future SAT-guided incremental construction.
DO-NOT-REPEAT: single-fixed-merge self-similar shuffles (floor 4, exhaustively checked); non-transitive
differing-bit selectors; uniform-tiled interval blocks. Scripts: /tmp/c*.py.

## PROBING LOG 17 (2026-05-29) — direct (non-workflow) testbench; THE WALL confirmed by hand

After the workflows, reproduced the landscape from scratch (own checker /tmp/ap4*.py). The recursive
even/odd merge family makes the wall explicit (N=256):
- `block` = recursive evens-first = **vdc**: 0 monotone 4-APs, longest monotone AP = 2 (no 3-AP either!),
  but maxdisp ≈ N (value 1 deferred to ~N/2) ⟹ NOT type ω.
- `even_first` interleave = identity (10795 4-APs).
- Every ω-izing merge modification (`alt_pp`, `alt_level`, `reflect_odd`) reintroduces 4-APs, FLOORING at
  longest monotone AP = 4 (alt_pp: 687 4-APs, maxdisp ≈ N/2).
ONE-LINE WALL: the unique order with 0 monotone APs is vdc (recursive evens-first) = dense, NOT ω; every
displacement-bounding (ω-izing) modification reintroduces monotone 4-APs (floor 4). The 3-AP slack is NOT
enough within the natural merge/interval-block families. Displacement-bounded backtracking (rank≤2v+c) with
greedy/urgency heuristics fails to find the SAT-certified N=64 witness (bad heuristic, not infeasibility) —
the witness's structure resists a closed form. CONCLUSION: #196's explicit type-ω 0-4AP construction lies
outside all natural self-similar/block families; it is the genuine open frontier (YES well-supported by the
SAT evidence + no surviving forcing for NO). CONSOLIDATED here.

## PROBING LOG 18 (2026-05-30) — #196 COMPACTNESS BRIDGE completed to an iff + DRIFT LEMMA formalized

Phase: consolidate the #196 reduction into a tight, formalized, construction-ready statement.
Lean: `Erdos/PermutationMonotoneAP/Compactness.lean` (now built, axiom-clean: propext/Classical.choice/
Quot.sound only).

★ FINITARY CHARACTERISATION (the headline) ★ `exists_finiteFeasible_iff_avoidable`:
  `Erdos196Avoidable ↔ ∃ f : ℕ→ℕ, FiniteFeasible f`,
where `FiniteFeasible f := ∀ N, ∃ σ, InjOn σ [0,N) ∧ (∀ v<N, σ v ≤ f v) ∧ ¬HasMono4 σ N`. Forward
direction (was already there): König's infinity lemma threads the finite bounded orders into a global
σ : ℕ→ℕ, then σ-rank compresses it to a genuine permutation of order type ω inheriting 4-AP-freeness.
REVERSE direction (added this session): given an avoider g, take f = g.symm; each [0,N) is ordered by
g.symm itself (injective, meets the bound with equality, 4-AP-free since g is) — so the reduction is
EXACT, no slack. NET: **#196 (NO / k*=3) ⟺ exhibit ONE explicit uniform bound f with FiniteFeasible f.**
The infinitary/order-type content is fully discharged by the bridge; only a finitary construction remains.
(SAT evidence from LOG 15: f(v)=2v+6 is the candidate — feasible to N=64.)

★ DRIFT LEMMA, now in Lean ★ `unbounded_displacement_of_avoiding`: every 4-AP avoider g has UNBOUNDED
displacement — ∀C ∃v, C < |g.symm v − v|. Proof (clean, reuses the new helper
`hasMonotoneAP_four_of_positions`): if |g.symm v − v| ≤ C for all v, the AP 0,d,2d,3d with d=2C+1 has
each term's position within C of its value and gap d>2C, so positions strictly ascend ⟹ a monotone
4-AP. Contrapositive gives the result. CONSEQUENCE: the bridge's f must satisfy f(v)−v→∞ (cannot be id
or near-id) while keeping each value at a FINITE position — the precise ω-vs-additive tension, formalized.

Helper added & reused: `hasMonotoneAP_four_of_positions` (4 strictly-ascending positions whose g-values
form an AP ⟹ HasMonotoneAP g 4); the sign of the AP is carried by d', so it serves both the increasing
and decreasing cases of the reverse bridge AND the drift lemma.

STATUS: #196 is now construction-ready in the repo. The remaining diff to a resolution is a single
`FiniteFeasible f` term — i.e. the genuine open all-scales construction (LOGs 16/17 barrier stands: no
NATURAL closed form realises it; the run-length/ω conflict in the Adenwalla staircase is the wall). No
new construction attempted this session; the contribution is the tight finitary reduction + drift necessity.
DO-NOT-REPEAT unchanged. NEXT options logged for the user: (a) formalize Adenwalla Thm 4 (bounded-v₂
avoidance, the strongest KNOWN partial result — real, completable); (b) SAT-guided hunt for an explicit
FiniteFeasible f (high-risk, = the open frontier); (c) formalize "finite avoiders exist unbounded" to
isolate that the uniform bound is the entire difficulty.

## ★ PROBING LOG 19 (2026-05-30) — LITERATURE SETTLED + LeSaulnier–Vijay ODD-DIFFERENCE THEOREM FORMALIZED (explicit closed form) ★

Phase: stop circling the recursive socket; settle the literature, formalize the strongest KNOWN
partial result, and pin the open frontier precisely.

### Literature (decisive, from the actual papers this session)
- **Erdős #196 is GENUINELY OPEN** (erdosproblems.com/196; confirmed). The open content is *exactly*
  avoiding monotone 4-APs over **all 2-adic valuations of the common difference simultaneously**.
- **LeSaulnier–Vijay 2011** (arXiv:1004.1740, Thm 2): there IS a permutation of ℕ⁺ avoiding all monotone
  4-APs with **odd** common difference. **Adenwalla** (arXiv:2211.04451, Thm 4): for each `k`, a
  permutation avoiding 4-APs with difference **not divisible by 2^k**. So every FIXED 2-adic-valuation
  bound is achievable; only the all-scales coupling is open. DEGS/Geneson/Adenwalla reach 5-AP avoidance
  (type ω). 3-APs are unavoidable. 4 is the boundary.
- **Consequence for the repo:** the `OddDiffSafe` socket in `Compactness.lean` is *exactly* the LV / n=2
  layer of the dyadic recursion. The literature confirms the socket is FAITHFUL — it loses no slack:
  the per-level odd-difference obligation is the (solved) LV layer, and the uniform-bound coupling across
  all dyadic scales is the (open) frontier. The socket is neither too strong nor too weak.

### The LV mechanism, distilled to ONE property
LV's whole odd-difference argument rests on:
> **Property (P):** whenever an odd value `x` appears before an even value `y`, then `y > 2x`.
(P) ALONE kills every odd-difference monotone 4-AP (both directions), by pure arithmetic: the 4 terms of
an odd-`d` AP alternate parity, so an adjacent odd-before-even pair exists; (P) turns monotonicity of the
positions into `v < 0`. The internal order of LV's geometric blocks is IRRELEVANT — only (P) matters.

### NEW: explicit closed-form realization (cleaner than LV's geometric blocks)
The permutation (sequence `g n` = n-th value), in blocks of three:
```
g(3k) = 4k,   g(3k+1) = 4k+2,   g(3k+2) = 2k+1     →  0,2,1,4,6,3,8,10,5,12,14,7,…
```
with inverse (position function) `σ v = 3·(v/2)+2` (v odd), `3·(v/4)+(v%4)/2` (v even). Equivalently it is
the order by the injective key `key(n)=2n` (n even) `/ 4n+1` (n odd): then odd-before-even ⟺ `4x+1<2y`
⟺ `y>2x` = (P). Verified to N=6000: bijection, (P) holds, no odd-diff monotone 4-AP, `σ v ≤ 2v` (linear,
type ω).

### FORMALIZED (Lean, axiom-clean: propext/Classical.choice/Quot.sound only)
`Erdos/PermutationMonotoneAP/OddDifference.lean` (built green; wired into `Erdos.lean`):
- `oddAvoider : ℕ ≃ ℕ` — the explicit permutation above (`toFun`/`invFun` with omega-verified inverses).
- `oddAvoiderInv_propP` — property (P).
- `no_oddDiff_mono4` — the arithmetic core: (P) ⟹ no odd-difference monotone 4-AP (4-case parity analysis).
- `HasMonotoneAPOddDiff` + `hasMonotoneAP_four_of_oddDiff` (odd-diff AP ⟹ AP, so `Erdos196Avoidable` ⟹ this).
- **`exists_perm_no_oddDiff_mono4` : ∃ g : ℕ ≃ ℕ, ¬ HasMonotoneAPOddDiff (g)** — the LV theorem.
- Bridge to the socket: **`oddDiffSafe_oddAvoiderInv (N) : OddDiffSafe oddAvoiderInv N`** for ALL N, with
  `oddAvoiderInv_le : oddAvoiderInv v ≤ 2*v`. So the socket's single-scale `OddDiffSafe` + linear-bound
  obligation is unconditionally, globally met; the residual difficulty is ONLY the recursive coupling.

### The open frontier, pinned crisply (why the full problem resists)
A 4-AP with `v2(d)=j` rescales (repo's `isFree_four_dyadicRestrict`) to an **odd**-difference 4-AP inside
residue class `a mod 2^j`. So #196-avoidable ⟺ a single ω-order whose EVERY dyadic class (rescaled) is
odd-difference-safe. The LV/(P) order solves the `j=0` class. To also solve `j=1` one needs property
`(P_1)` on the rescaled even subsequence — but `(P_0)`'s order is *magnitude-primary*, which already fully
commits the order within each parity class, leaving no freedom to install `(P_1)`. **The scales impose
conflicting magnitude-orderings.** Computationally: nested-LV keys kill `v2 = 0,1` then leak at `v2 = 2`
(exactly Adenwalla's bounded-`v2` phenomenon); self-similar single-merge-word orders (Thue–Morse, paper-
folding, etc.) all retain small-`d` 4-APs. This is a precise restatement of the 50-year wall — NOT closed.
(Avoidance ≠ property (P), so this conflict does NOT prove impossibility either; #196 stays open both ways.)

STATUS: #196 unresolved (open). Delivered: the strongest KNOWN partial result (LV odd-difference)
formalized via a clean explicit permutation, axiom-clean, plus a faithful bridge to the `Compactness.lean`
socket. NEXT (real, completable): formalize Adenwalla Thm 4 (bounded-`v2`, general `k`) by nesting the
(P)-key over the lowest `k` bits with geometric magnitude gaps. DO-NOT-REPEAT: single fixed merge word
(fails small `d`); magnitude-primary keys cannot install higher-scale (P) (the all-scales conflict).

## ★ PROBING LOG 20 (2026-05-30) — ADENWALLA Thm 4: clean recursive construction VERIFIED + dyadic reduction FORMALIZED ★

Phase: go after Adenwalla's Theorem 4 (for each k, a permutation of ℕ avoiding monotone 4-APs with
common difference NOT divisible by 2^k; k=1 = LV, done in LOG 19).

### Clean recursive construction (verified k≤6)
A 4-AP with v2(d)=j<k rescales (Dyadic.isFree_four_dyadicRestrict) to an ODD-difference 4-AP inside a
dyadic subsequence at depth j. So it suffices to make every dyadic subsequence (down to depth k) a
property-(P) order. Recursion:
  O_0 = increasing;  O_k = (P)-MERGE of [evens ordered by O_{k-1} on v/2] and [odds ordered by O_{k-1}
  on (v-1)/2], where the merge emits each odd u only AFTER all evens w≤2u ("deadline merge").
Verified (/tmp/merge196/recmerge.py): O_k is a permutation, satisfies full (P), kills exactly all
v2(d)<k monotone 4-APs (first survivor at d=2^k), linear-in-value displacement (ratio grows ~ with k).
The deadline merge provably realizes the HasPMerge spec (verify_pmerge.py): even-child order = H,
odd-child order = H, property (P). NOTE: O_k has NO clean closed form (unlike k=1) — the odd-residue
values place linearly but even residues recurse; the merge is genuinely non-scalar (no single key K(n)
can order evens both by H AND cross-compare to odds by value — that is the all-scales tension, here
finite/bounded so resolvable, but not by a closed form).

### FORMALIZED (Lean, OddDifference.lean, axiom-clean; full project builds green)
The DYADIC REDUCTION — the mathematical core — is now formal and complete (no sorry):
- `AvoidV2 σ k` := ∀ a d, 0<d → ¬(2^k ∣ d) → ¬ Mono4 σ a d   (avoid 4-APs, diff not div by 2^k).
- `avoidV2_zero` — vacuous base (2^0=1 divides all d).
- **`avoidV2_succ`** — THE REDUCTION: (σ kills odd-diff APs) ∧ AvoidV2 (evenChild σ) k ∧
  AvoidV2 (oddChild σ) k ⟹ AvoidV2 σ (k+1). Proof: even-diff d=2q AP rescales via
  `mono4_evenChild_iff`/`mono4_oddChild_iff` to a child AP with ¬(2^k∣q); odd-diff handled by (P).
- `avoidV2_oddAvoiderInv_one` — the explicit LV order (LOG 19) realizes the base case k=1.
- `mono4_iff_of_lt_iff` — Mono4 depends only on the induced strict order.
- **`adenwalla_of_hasPMerge : HasPMerge → ∀ k, ∃ G, AvoidV2 G k`** — Adenwalla Thm 4 by induction on k,
  CONDITIONAL on `HasPMerge` (∀ H, ∃ G with both dyadic children reproducing H's order + property (P)).
  `HasPMerge` is exactly the deadline-merge spec, verified to be realizable.

NET: Adenwalla's Theorem 4 is now CONSTRUCTION-READY — fully reduced (in Lean, axiom-clean) to the single
lemma `HasPMerge`, i.e. an explicit type-ω bijection for the (verified) deadline merge. The remaining
formal step is that merge bijection (no clean closed form ⟹ needs the deadline bookkeeping or an abstract
locally-finite-poset → ω order-embedding; ~substantial, a clean next chunk). DO-NOT-REPEAT: clean scalar
key for general k (provably impossible — evens can't be ordered by H AND value simultaneously); level-key
works but via the residue/3-AP-mod-2^k argument (different, also substantial), NOT via property (P).

---

## 2026-05-30 — SLACK-GROWTH probe (ramsey/impossibility vector; #196 finite-feasibility)

Question (compactness framing): avoidable ⟺ ∃ f with FiniteFeasible(f) (σ[v] ≤ f(v) ∀N). Test
the sharpest fixed family f(v)=2v+C. Define wall(C) = largest N admitting a monotone-4-AP-free
order of [0,N) with σ[v] ≤ 2v+C. Machine-verified (TWO independent solvers: z3 boolean ORDER
encoding with PbLe deadline + pysat Cadical153 with seqcounter cardinality — they AGREE):

  wall(0) = 44   (N=44 SAT witness saved; N=45,46,47,48 UNSAT)
  wall(1) = 72   (N=72 SAT; N=73 UNSAT)  [z3-order took 155s on the N=73 UNSAT, pysat 50s]
  wall(2) ≥ 80   (N=80 SAT verified; exact wall not pinned — SAT near wall is the slow part)

⇒ needed_slack(N) := min{C : N ≤ wall(C)} is STRICTLY INCREASING and (each wall finite) UNBOUNDED.
⇒ NO fixed affine f(v)=2v+C is finite-feasible. The avoider (if any) needs f growing faster than
2v+O(1). Data consistent with wall(C) ≈ 28C+44 ⟹ needed_slack(N) ≈ (N−44)/28 — slow LINEAR growth
(NOT bounded, but also NOT explosive). This neither proves nor disproves #196: a super-constant but
e.g. linear-slack f (f(v)=2v+εN-ish, or f(v)=(2+δ)v, or f(v)=2v+c·log) is NOT ruled out and remains
the live candidate for an avoider. So this is a NEUTRAL/structural result: it kills the "fixed 2v+C"
hypothesis (SAT had found 2v+6 feasible to N=64, but that is NOT a uniform-over-N bound) and pins the
required growth rate to between ω(1) and O(N) additive slack.

Key correction to prior lore: σ[v] ≤ 2v (ZERO slack beyond doubling) is full-4-AP-free-feasible all
the way to N=44 — the recmerge O_k displacement-ratio explosion (2→3.7→30→164→…) is a SUBOPTIMAL
ARTIFACT of that construction, not a forced wall (z3/pysat find C=0 orders recmerge misses, e.g. the
N=44 witness has 73 property-(P) violations — it does NOT use odds-before-evens).

Scripts (re-runnable, ~1min): /tmp/merge196/vRAMSEY_FINAL.py (re-verifies all 5 facts via pysat),
vRAMSEY_pysat_check.py (the CDCL order+cardinality encoding), vRAMSEY_sat.py (z3 order encoding),
witness /tmp/merge196/vRAMSEY_witness_N44_C0.json.

## ★ PROBING LOG 21 (2026-05-30) — SYSTEMATIC ADVERSARIAL FAN-OUT (29 agents): impossibility machine-closed, sharp dichotomy, the v2>=5 wall isolated ★

Phase: ultracode multi-agent fan-out (14 attack vectors x adversarial verifier + synthesis), all claims
machine-verified via a shared tested library /tmp/merge196/shared.py (fast monotone-4-AP detection +
z3/CP-SAT feasibility). Decisive, honest map of Erdos #196.

### Verdict: weakly YES-avoidable, NOT resolved. The open difficulty is now precisely isolated.

IMPOSSIBILITY IS MACHINE-CLOSED (3 reproduced impossible-vectors): no finite forcing argument can work.
The naive DEGS 3-AP->4-AP extension fails on the concrete avoider rank=(1,2,0,3,6,5,4) of [0,7) (4th
term turns back). The forced-precedence digraph has ZERO edges forced in all 4-AP-free orders for
N=5..9, and #(4-AP-free orders) grows super-exponentially (564,3336,22266,168864,1307470,11066766 for
N=6..11; log2(#)/N rises 1.52->2.13). => any unavoidability proof MUST invoke the type-omega/uniform
regime, not finite order/sign structure.

SHARP DICHOTOMY (verified 5 ways: allscalesP, geonest, deadlimit, levelword, numtheory):
- Orders avoiding ALL 4-APs (all-scales-(P) greedy; deadline diagonal O_{ceil log2 N}; vdC; Calkin-Wilf)
  are NOT type-omega. Quantified: the all-scales (P) poset is ACYCLIC (N<=4096, mutually consistent)
  and its greedy extension kills all 4-APs to N=16384, BUT the transitive forced down-set ds(3)/N->1/2
  is a POSET INVARIANT (rank[3] >= |ds(3)| in EVERY linear extension; verified across 5 extensions),
  so NO extension is type-omega. Identical failure mode to van der Corput.
- Type-omega orders (bounded displacement) ALL leak at exactly (a,d,v2)=(0,2^j,j). The LV/(P) order
  (rank[v]=3(v//2)+2 odd, 3(v//4)+(v%4)//2 even) kills all v2=0 with clean bound rank[v]<=1.5v+0.5;
  first 4-AP (0,2,1). recmerge O_k kills v2<k but displacement ratio blows up 2,3.7,29.8,205.9,455,591.

PROPERTY (P) IS SUFFICIENT-NOT-NECESSARY (refute-meta, reproduced): z3 found 2v+6-bounded 4-AP-free
orders VIOLATING (P) in 84 (N=32) to 169 (N=40) places. => the divergence of all (P)-based
constructions is an artifact of an over-strong strategy; a non-(P) avoider is not excluded. THE
poset-invariant obstruction is a barrier to the (P) APPROACH, NOT to #196.

THE WALL, isolated: a monotone 4-AP with v2(d)=j needs N>=3*2^j. ALL prior SAT stalled at N<=72 =>
provably blind past v2=4 => only re-certified Adenwalla's bounded-k. The genuine open content (all
scales) lives at N>=96 (v2=5), untested until now.

### NEW CP-SAT data (ortools installed; /tmp/merge196/cpsat.py) — first probes into v2>=5:
4-AP-free order with sigma[v]<=2v+C: SAT-clean at N=48(C=6), N=64(C>=12), N=96(C=40 in 2s; C<=20
UNKNOWN/25s), N=128(C=40 UNKNOWN/45s). => minimal slack slack2(N) GROWS with N (consistent with
"no fixed 2v+C works for all N"). Growth RATE = the decisive open quantity (log => YES plausible;
fast/divergent-for-a-fixed-value => NO). Deep-phase workflow launched to pin it + chase 2 construction
leads (non-(P) witness mining; position-unit deadline poset with bounded down-sets).

### Lean status (scratch, not yet wired; project build green, 8621 jobs):
adenwalla_of_hasPMerge + erdos196Avoidable_of_finiteFeasible axiom-clean (type-omega bijection DONE
via rank/ncard). Agents added scratch/OmegaBijection.lean (exists_orderMatching_equiv, axiom-clean,
reusable value->position omega-enumeration) and scratch/ScratchMerge.lean (noOddDiffMono4_of_pProperty
axiom-clean; ONE sorry at line 165 = hasPMergedOrder). CAVEAT: HasPMerge's output is a per-k family,
NOT one global omega-order; the right interface is "one injective sigma, finite down-sets, forall k
AvoidV2 sigma k" feeding erdos196Avoidable_of_finiteFeasible. The all-scales coupling is upstream of
the bijection. DO-NOT-REPEAT: value-magnitude (P) deadlines (force divergent down-sets); single fixed
self-similar word; scalar key for general k; depth-grows-with-magnitude self-similar (limits to vdC).

## ★ PROBING LOG 22 (2026-05-31) — DEEP v2>=5 PROBE (11 agents, CP-SAT + pysat Kissat/CaDiCaL): slack ladder pinned; solution isolated to its infinitary core ★

Phase: deep-probe workflow into the v2>=5 wall (first time N>=96 reached) with proven UNSAT lower bounds.

### slack2(N) PINNED (machine-proven UNSAT + verified SAT witnesses)
slack2(N) := min over monotone-4-AP-free bijections of [0,N) of max_v (sigma[v]-2v) (= min C with a
feasible sigma[v]<=2v+C order):
```
 N      32  40  44  48  64  80  84  88  96
 slack2  0   0   0   1   1   2   2   2  {2,3}
```
- Jumps 0->1 in (44,46], 1->2 in (64,80]; UNSAT lower bounds reproduced on CaDiCaL195 AND Kissat404
  (e.g. N=48 C=0 UNSAT 0.25s, N=64 C=0 UNSAT 0.49s — fast, genuine, NOT timeouts).
- slack2(96)=2 or 3: C=3 SAT verified (witness wslacklaw_witness_N96_C3.json, 4-AP-free, max-excess=3);
  C=2 sits EXACTLY at the SAT phase transition — UNKNOWN across CaDiCaL(38min)/Kissat(28min)/CP-SAT(901s).
  The decisive open cell. (CP-SAT proven too weak here; pysat order-encoding is the authoritative prover.)
- slack2 is PROVABLY non-constant + non-decreasing (= FiniteFeasible.mono). Growth law UNDETERMINED: log
  fit (~1.5 log2 N) and shallow-linear (~0.04 N) are statistically indistinguishable on 3 distinct
  values; both predict the 2->3 jump near N in [111,137].

### Decisive interpretations (VERIFIED)
- **FiniteFeasible(2v+0) and FiniteFeasible(2v+1) are FALSE** (slack2(46)>=1, slack2(80)=2). First hard
  refinement of the candidate bound. (Machine-proven; NOT cheaply formalizable — UNSAT needs SAT-scale
  search, decide over [0,46) orders is infeasible, native_decide banned.)
- **FiniteFeasible(2v+6) is NEITHER proven nor refuted**: max proven slack2 = 2 <= 6, fully consistent
  with the Lean target being TRUE. Refuting needs some N with slack2(N)>=7 (extrapolated N in [189,546]).
- **The wall is barely touched**: v2=5 APs (d=32) need N>=97 (0 at N=96, 16 at N=112); d=16 (v2=4) is the
  binding scale at N=96. So even N=96 mostly re-tests Adenwalla's regime; the genuine all-scales content
  starts at N>=112 and is beyond current solver reach.
- **minpos is degenerate (==0)**: each fixed value can individually be placed FIRST (min rank[3]=0 thru
  N=96), and {0..11} pack into the first 12 positions at N=96 (excess 0). So front-crowding is an ARTIFACT
  of the (P)/recmerge constructions, NOT of the problem. (Mild YES-evidence.) The binding is the JOINT
  packing, attained at small values (v=1 or 4), not any single value diverging.

### Constructions: ALL leak (verified)
recmerge deadline-merge O_e (only all-scale order) avoids all 4-APs to N=16384 but rank[3]=2^(e-1)+e-1
(exact closed form, verified N=256..8192) -> rank[3]/N->1/2 -> NOT type-omega. Position-unit relaxed
poset (bounded ds(3)=3) CANNOT block APs (fails for all j,c tested). Bounded multiplicative odd-boost
insufficient: B*(64)<=4 but B*(96)>10 (B=4,6,8,10 all genuine INFEASIBLE). Tight C=3 witnesses are
adaptive non-self-similar packings (vdC-like front scramble per block) with NO clean closed form.

### THE SOLUTION, ISOLATED
Erdos196Avoidable <=> exists an infinite type-omega 4-AP-free permutation <=> exists uniform f with
FiniteFeasible f (formalized iff). Finite SAT CANNOT settle this (needs the infinite object; can only
refute specific f). Verified state: impossibility machine-closed at the finite level; every natural
construction family exhausted; the governing quantity (joint front-packing slack over the 2v baseline)
grows GLACIALLY (still <=3 at N=96), consistent with — but not proving — a uniform-f YES. Net lean:
WEAKLY YES-AVOIDABLE, unresolved. A resolution requires genuinely INFINITARY methods (an explicit
adaptive construction, or an infinitary impossibility argument) — the 50-year frontier, now boxed in
precisely. DECISIVE OPEN COMPUTATION (if pursued): slack2(112,C=2) via cube-and-conquer/DRAT on an
uncontended machine. Lean assets intact + axiom-clean: LV (k=1), Adenwalla reduction (avoidV2_succ,
adenwalla_of_hasPMerge), compactness bridge. scratch/{OmegaBijection(reusable, clean), ScratchMerge
(1 sorry = the per-k merge, NOT on the critical path since HasPMerge's per-k interface is mis-shaped)}.

## ★ PROBING LOG 23 (2026-06-01) — QUANTIFIER-SWAP characterisation formalised; construction re-probe reproduces the wall (no advance) ★

NEW LEAN (axiom-clean, builds green):
- `mono4_free_iff_forall_avoidV2 (G)` : `(∀ a d, 0<d → ¬ Mono4 G a d) ↔ ∀ k, AvoidV2 G k`. For ONE fixed
  order, killing every `2^k`-indivisible-diff 4-AP at all k = killing every 4-AP (any d>0 has `2^d ∤ d`,
  so scale k=d suffices; no padicVal needed). Axioms: propext, Quot.sound only.
- `forall_not_hasMono4_iff (G)` : `(∀ N, ¬ HasMono4 G N) ↔ (∀ a d, 0<d → ¬ Mono4 G a d)`.
- **`erdos196Avoidable_iff_exists_injective_avoidV2_all`** : `Erdos196Avoidable ↔ ∃ G, Injective G ∧ ∀ k,
  AvoidV2 G k`. Sets the open content next to `adenwalla_of_hasPMerge : HasPMerge → ∀ k, ∃ G, AvoidV2 G k`
  — #196-NO is the SAME statement with the quantifiers swapped: `(∀ k ∃ G) ⟹ (∃ G ∀ k)`. The `Injective`
  hypothesis is tight (constant G vacuously satisfies `∀k AvoidV2` but yields no permutation; the forward
  map produces an injective witness). This is, to date, the cleanest Lean statement of "all scales at once".
- Refactor: reverse-bridge core extracted as `not_hasMono4_symm_of_avoiding` (reused by the iff above +
  `exists_finiteFeasible_of_erdos196Avoidable`, −25 LOC of duplication).
- Housekeeping: socket tower wrapped in two labelled `section ConstructionTargets` blocks (purely
  organisational, names still global); RESULTS.md overclaims fixed ("exactly the LV layer" → heuristic;
  "Adenwalla verified realizable / checked to k=6" → external SAT, HasPMerge unproved in Lean); stale
  "~42 theorems" → ~280.

CONSTRUCTION RE-PROBE (did NOT close #196; reproduced PROBING LOG 22's wall, did not advance it):
- LV `oddAvoiderInv` has an even-diff 4-AP at values 0,2,4,6 (positions 0,1,3,4) — confirms it is the k=1
  layer only, as expected.
- Greedy lexicographically-least 4-AP-free sequence avoids all 4-APs but DEFERS small values indefinitely
  (value 3 unplaced through 120 positions) → unbounded displacement = the drift lemma in action; it is NOT
  a bounded-f order.
- z3 (int+Distinct encoding) confirms FiniteFeasible(2v+6) per-N SAT to N≥48, then times out (UNKNOWN, not
  UNSAT) — strictly weaker than LOG 22's CaDiCaL/Kissat order-encoding (N=96, slack2 pinned). The z3
  witnesses are unstructured (displacement −26..+17, no self-similarity) — no recursive pattern to lift to
  a global order. Net: the construction route remains alive-but-unconstructed; closing it needs the same
  infinitary object LOG 22 isolated. No new ground gained on the construction side this session.

## ★ PROBING LOG 24 (2026-06-02) — IMPOSSIBILITY DIRECTION opened: sub-lemma (b) "scale-controlled DEGS" PROVED ★

Pivot from the construction (NO) side to the impossibility (YES) side, and mapped what such a proof must
establish: three sanity gates — (1) use ω essentially (finite + dense vdc are 4-AP-free-orderable),
(2) escalate the dyadic scale (every fixed scale is refuted by Adenwalla), (3) cut off at length 4 (DEGS
build a 5-AP-free ω-permutation). Any natural argument violates one and is refuted by a known construction.

Reformulation (elementary, not yet formalized): `f` avoids monotone 4-APs ⟺ every monotone 3-AP in `f` has
**both completions tucked into its interior** (forward completion before the last term's position, backward
completion after the first term's). Since DEGS makes 3-APs unavoidable, impossibility = this completion web
has no ω-solution. Bootstraps from the proven base case, so it's "force one more term," not "from scratch".

LADDER: (a) [proved] DEGS, a monotone 3-AP exists. (b) [PROVED NOW] monotone 3-APs of arbitrarily high
2-adic difference-valuation exist. (c) [open, the crux] some high-scale 3-AP has an un-tuckable completion.

### (b) formalized — `Erdos/PermutationMonotoneAP/Unavoidability.lean` (axiom-clean, builds green)
- `hasMonotoneAP_three_dvd (f : ℕ ≃ ℕ) (M) (0<M)` : ∃ monotone 3-AP with `M ∣ d`, `d ≠ 0`.
- `hasMonotoneAP_three_pow_two (f) (k)` : ∃ monotone 3-AP with `2^k ∣ d`, `d ≠ 0`.
- Proof = the DEGS argument run inside the residue class of `f 0` mod `M`: `b` = first value `> f 0` and
  `≡ f 0 (mod M)`; reflection `m = 2b − f 0 ≡ f 0 (mod M)` is forced later by the same prefix counting;
  `(f 0, b, m)` is a monotone 3-AP with `M | (b − f 0)`. `hasMonotoneAP_three` is the `M = 1` case.
- Empirically (LV avoider): residue-DEGS yields exactly `(0, 2^k, 2^{k+1})` for every k≤8 — clean.
- Axioms: propext/Classical.choice/Quot.sound only. Sanity gates: (b) passes gate 1 (uses DEGS = an
  ω-statement; breaks for dense orders, which have no monotone 3-AP at all) and delivers gate 2.

NEXT (c): the genuine content — show the completion web is over-determined. Needs either a global potential
that "sees density" (strengthening rank-descent, currently only density-0) or a partition-regularity theorem
for AP-completions on ω-well-orders. A concrete intermediate: bound how early all completions of the forced
high-scale 3-APs must sit, and derive a packing contradiction. Direction still genuinely open (SAT leans NO).

## ★ PROBING LOG 25 (2026-06-02) — DEAD END: the packing/quantitative-(b) route to (c) is BLOCKED ★

Probed the "quantitative (b) ⟹ finite packing contradiction" sub-step (bound how early completions must
sit, pigeonhole them). **It cannot work, and the block is a theorem we already have:**
`finite_initial_segments_vdc_orderable : FiniteOrderable4` — every finite `[0,N)` is 4-AP-free-orderable
with NO displacement bound (vdc). So the *unbounded* completion web is satisfiable on every finite value
set; a packing/counting argument is inherently finite, hence can never contradict it. Any "how early must
completions sit" bound has slack for every N.

- The ONLY finite contradictions live in the *bounded* problem (`slack2(N) > C` = UNSAT cell), and those
  refute one fixed `f = 2v+C`, not the `∀ f` statement #196 requires. So no fixed-bound packing reaches #196.
- Crude empirical confirmation (cadical witnesses, completion-web metric): forward completions number
  far fewer than positions (ncompletions ≈ 36–64 vs N = 48–80), fit comfortably, no bottleneck, for tight
  (C=slack2) AND loose (C=20) bounds. (Metric was degenerate at small P; the decisive argument is the
  theorem, not the measurement.)

SHARPER SYNTHESIS: `FiniteOrderable4` is the SINGLE linchpin making #196 infinitary from BOTH sides —
construction side (no finite construction; must supply a uniform ω-bound `f`) AND impossibility side (no
finite obstruction; any impossibility proof is irreducibly infinitary). Same theorem blocks finite methods
in both directions. DO NOT re-attempt finite packing/counting for (c). The only remaining lever for (c) is
genuinely infinitary (density-seeing global potential, or order-completion partition regularity) — the
50-year frontier, no foothold found. #196 push stopped here; sub-lemma (b) banked as the session's gain.
