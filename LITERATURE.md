# Literature Review & Ideas

This document tracks papers, techniques, and ideas relevant to our Erdős problem
formalizations, along with notes on how they performed when we attempted to
execute on them in Lean.

---

## Problem #242: Erdős-Straus (4/n = 1/x + 1/y + 1/z)

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Mordell 1967 | Polynomial identities covering all n except {1,121,169,289,361,529} (mod 840) |
| Schinzel 1956 | **Fundamental limitation**: no polynomial identity system can cover quadratic residue classes; n ≡ 1 (mod m) is never eliminable |
| Vaughan 1970 | Exceptions up to N are O(N^{3/4}); exceptional set has density 0 |
| Elsholtz-Tao 2013 ([arXiv:1107.1010](https://arxiv.org/abs/1107.1010)) | Solution count: N log²N ≪ Σ f(p) ≪ N log²N · log log N. Uses Bombieri-Vinogradov. Type I/II classification |
| Salez 2014 ([arXiv:1406.6307](https://arxiv.org/abs/1406.6307)) | Verified to 10^17 using 7 modular equations |
| Bloom-Elsholtz 2022 ([survey](https://www.nieuwarchief.nl/serie5/pdf/naw5-2022-23-4-237.pdf)) | Comprehensive survey placing E-S in Egyptian fraction context |
| Bradford 2024 ([arXiv:2403.16047](https://arxiv.org/abs/2403.16047)) | One-dimensional reduction: solutions ↔ divisors of x² satisfying modular equations |
| Ghermoul 2025 ([arXiv:2508.07383](https://arxiv.org/abs/2508.07383)) | Four multivariable polynomial families; one covers all primes to 1.2×10^10 |
| Pomerance-Weingartner 2025 ([arXiv:2511.16817](https://arxiv.org/abs/2511.16817)) | For general m/n conjecture: n_m ≥ exp(m^{1/3+o(1)}) — the 4/n case is special |
| Mihnea-Bogdan 2025 ([arXiv:2509.00128](https://arxiv.org/abs/2509.00128)) | Verified to 10^{18} + empirical f(p) data |
| Bradford 2026 ([arXiv:2602.11774](https://arxiv.org/abs/2602.11774)) | **Claims full proof** (unverified preprint) via greedy + Type I/II |

**Why the p ≡ 1 (mod 24) barrier is fundamental**: Schinzel's theorem *proves*
that no finite system of congruence-based polynomial identities can eliminate
quadratic residue classes. Since 1 is a QR mod every m, the class n ≡ 1 is
unreachable by congruence methods. Any complete proof must use deeper arithmetic.

**Why the circle method fails here**: f(p) ~ log²(p) on average — far too sparse
for Hardy-Littlewood. Unlike ternary Goldbach (polynomial growth of representations),
there is essentially no margin.

### Ideas Tried

- **Case splitting by residue classes**: Proved all cases except primes p ≡ 1 (mod 24).
  Capstone: `reduction_to_primes_1_mod_24`.
- **Factorization witnesses via core_identity**: Successfully handled mod-24 subcases.
  Each identity is a polynomial identity verifiable by `ring`.
- **Prime factor ≡ 3 (mod 4)**: Leveraged divisibility to reduce composite cases.

### Ideas To Try

- **Additional Salez-type modular identities**: could narrow from mod 24 to mod 840
  or mod 27720. Won't complete the proof but makes the remaining set sparser.
  Each identity is `ring`-verifiable. **Formalizable: YES, but diminishing returns.**
- **Bradford's one-dimensional reduction**: The 2026 proof has a CRITICAL GAP
  (Schinzel barrier). The core divisor-of-x² step is not self-contained.
  **Status: NOT VIABLE without breakthroughs.**
- **Elsholtz-Tao Type A/B classification**: restructures the solution space; might reveal
  new identities within p ≡ 1 (mod 24). **Moderate formalization effort.**
- **Identity registry with coverage tracking**: Create a structure representing a modular
  identity (modulus conditions, explicit formulas for (x(n),y(n),z(n)), validity theorem,
  coverage class), plus a "coverage combiner" that mechanically proves "covered outside
  these residue classes." Makes adding identities from literature or search cheap, and
  gives a mechanically checked "remaining exceptional set" statement. Doesn't bypass
  Schinzel, but makes last-mile modular work scalable.
  **Formalizable: YES, engineering-heavy. LOW PRIORITY given #242 is wrapped up.**
- **Formal connection #242 → #302**: ✓ FORMALIZED in `ErdosStraus/TripleBridge.lean`.
  Every Erdős-Straus solution 4/n = 1/x + 1/y + 1/z rearranges to 1/a = 1/y + 1/z
  (a unit fraction triple) when (4x−n) | nx. Even case produces consecutive triples.

---

## Problem #152: Isolated Sums of Sidon Sets

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Sárközy-Sós 1994 | Finite Sidon-set problem: isolated elements of `A + A` must grow with `|A|` |

The finite theorem is naturally about *cardinality truncations* of Sidon sets.
For the infinite problem, value truncation is a cleaner interface: if an
isolated sum lies strictly below the value cutoff, then later elements cannot
create neighboring sums there.

### Ideas Tried

- **Value-truncation stability**: ✓ **DONE** (`SidonSumsets/Stability.lean`).
  For any `A ⊆ ℕ` and `N ≤ M`, every isolated sum `s < N` of
  `(A ∩ [0,N]) + (A ∩ [0,N])` remains isolated in
  `(A ∩ [0,M]) + (A ∩ [0,M])` and in the full sumset `A + A`.
- **Strategy packaging**: ✓ **DONE** (`infiniteConjecture_of_lowerIsolated_strategy`).
  Any proof that every infinite Sidon set has arbitrarily large lower-isolated
  witnesses along value truncations immediately yields the infinite conjecture.
- **Fast-growth subclass theorem**: ✓ **DONE** (`SidonSumsets/FastGrowth.lean`).
  If `u` satisfies `2u_n + 1 < u_{n+1}` and `u_0 > 0`, then each doubled term
  `2u_n` is isolated in the sumset of `range u`, already below the next value
  cutoff `u_{n+1}`. Hence `range u` is Sidon and has infinitely many isolated
  sums. This proves the infinite conjectural conclusion for a concrete infinite
  class.
- **Finite obstruction family**: ✓ **DONE** (`SidonSumsets/Obstructions.lean`).
  The naive finite strengthening is false. For each `m`, the explicit finite
  Sidon set `{0, 1} ∪ {obstructionSeq m + obstructionSeq i | i ≤ m}` has no
  lower-isolated sums below the cutoff `2 * obstructionSeq m`.

### Ideas To Try

- **Lower-half finite bound**: prove that for Sidon `A ⊆ [0,N]`, the number of
  isolated sums `s < N` in `A + A` tends to infinity with `N`. This is stronger
  than the already-solved finite problem because the witnesses are stable under
  extending the set. **Formalizable: YES, high priority.**
- **Retarget the ESS94 argument**: revisit the finite proof and force the
  isolated sums it produces into the stable lower region rather than allowing
  them anywhere in `A + A`. **Moderate formalization effort.**
- **Extremal search**: computationally search for Sidon sets in `[0,N]` that
  minimize lower-isolated sums. This could distinguish a true obstruction from
  an artifact of standard constructions like Mian-Chowla. **Good search task.**

---

## Problem #156: Small Maximal Sidon Sets

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Sárközy-Sós 1994 | Original finite maximal-Sidon question |
| Ruzsa 1998 | Maximal Sidon subset of `{1, ..., N}` with size `≪ (N log N)^{1/3}` |

Problem #156 is closely related to #152, but the finite maximality question has
its own natural language: rather than asking for isolated sums, one asks for a
small Sidon set whose complement is completely blocked from further Sidon
extension. The basic obstruction mechanism is elementary: if `x` cannot be
adjoined, then inserting `x` would create either a midpoint collision
`a + b = 2x` or a sum-difference collision `x + c = a + b`.

### Ideas Tried

- **Finite statement formalization**: ✓ **DONE** (`MaximalSidonSets/Statement.lean`).
  We formalized finite Sidon subsets of `{1, ..., N}`, maximality in the
  interval, and a cubic-form statement of the conjecture
  `|A|^3 ≤ C N`.
- **Maximal extension existence**: ✓ **DONE** (`MaximalSidonSets/Existence.lean`).
  Every Sidon subset of `{1, ..., N}` extends to a maximal Sidon subset of the
  same interval. In particular, maximal Sidon sets exist for every `N`.
- **Explicit geometric seed**: ✓ **DONE** (`MaximalSidonSets/ExplicitSeeds.lean`).
  The finite progression `{1, 4, 4², ..., 4^m}` is Sidon and, whenever
  `4^m ≤ N`, extends to a maximal Sidon subset of `{1, ..., N}`. This gives a
  concrete family of maximal sets with a certified sparse core.
- **Generic strong-gap seed extension**: ✓ **DONE** (`MaximalSidonSets/ExplicitSeeds.lean`).
  More generally, every finite prefix of a positive strong-gap sequence extends
  to a maximal Sidon subset of any interval containing its last term. This
  exposes a clean structural bridge from the fast-growth machinery developed for
  problem #152 to the maximal-extension setting of #156.
- **Elementary obstruction framework**: ✓ **DONE** (`MaximalSidonSets/Statement.lean`).
  We introduced midpoint and sum-difference candidate families, together with
  the obstruction-cover hypothesis that every outside point of `{1, ..., N}` is
  captured by one of these elementary candidates.
- **Maximality ⇒ obstruction cover**: ✓ **DONE** (`MaximalSidonSets/Maximality.lean`).
  Expanding the failure of Sidon after inserting an outside point `x` and
  splitting on where `x` appears in the equal-sum witness shows that every
  genuinely maximal Sidon set satisfies the elementary obstruction-cover
  hypothesis.
- **Easy cubic lower bound**: ✓ **DONE** (`MaximalSidonSets/ElementaryBound.lean`).
  Under the obstruction-cover hypothesis, we proved
  `N ≤ |A| + |A|^2 + |A|^3`, the standard coarse counting inequality behind
  the lower bound `|A| ≫ N^{1/3}` for maximal Sidon sets.
- **Direct maximal-set bound**: ✓ **DONE** (`MaximalSidonSets/Maximality.lean`).
  Combining maximality ⇒ obstruction cover with the counting lemma yields the
  direct bounds `N ≤ |A| + |A|^2 + |A|^3`, and for `N ≥ 1` also
  `N ≤ 3|A|^3`, for every maximal Sidon subset `A ⊆ {1, ..., N}`.
- **Packaged finite existence theorem**: ✓ **DONE** (`MaximalSidonSets/Maximality.lean`).
  For every `N ≥ 1`, there exists a maximal Sidon subset `A ⊆ {1, ..., N}`
  with `N ≤ 3|A|^3`. This bundles the extension-existence theorem with the
  direct cubic lower bound into a single finite result.

### Ideas To Try

- **Sharpen the counting**: replace the crude `|A|^2 + |A|^3` bound by a more
  faithful count of actual obstructions, with the goal of recovering the exact
  easy lower bound from the folklore argument.
- **Import Ruzsa's construction**: formalize the `≪ (N log N)^{1/3}` upper
  bound or a simplified precursor construction.

---

## Problem #864: Almost-Sidon Sets with One Exceptional Sum

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Freud 1991 | Lower-bound construction by doubling a Sidon set `B ⊆ [1, N/3]` with its reflection `N - B` |
| Erdős 1992 | Problem statement source cited on erdosproblems.com |

This problem asks for the largest `A ⊆ {1, ..., N}` for which there is at most
one integer admitting more than one sorted representation `n = a + b` with
`a ≤ b` and `a, b ∈ A`. The natural lower-bound mechanism is to start from a
genuine Sidon set in the lower third and reflect it across `N`; all cross
pairs then sum to the central value `N`, while the lower-third and upper-third
bands remain separated enough to block any other repeated sum.

### Ideas Tried

- **Finite statement formalization**: ✓ **DONE** (`AlmostSidonSets/Statement.lean`).
  We formalized the interval model `{1, ..., N}`, the predicate saying a value
  has two distinct sorted two-term representations, the finite almost-Sidon
  condition, and the asymptotic upper-bound conjecture
  `|A| ≤ ((2 / sqrt 3) + o(1)) N^{1/2}`.
- **Midpoint structural split**: ✓ **DONE** (`AlmostSidonSets/Structure.lean`).
  If every repeated sum of `A` is forced to equal `n`, then the lower half
  `A ∩ [1, ⌊n/2⌋]` and the upper half `A ∩ [⌊n/2⌋+1, ∞)` are both Sidon, and
  they partition `A`. This is the right first reduction for future upper-bound
  arguments.
- **Reflected-Sidon construction**: ✓ **DONE** (`AlmostSidonSets/Construction.lean`).
  If `B ⊆ {1, ..., ⌊N/3⌋}` is Sidon, then
  `A = B ∪ {N - b : b ∈ B}` is almost Sidon in `{1, ..., N}`.
  The formal proof isolates the geometric separation between the lower-third
  base and the reflected copy, proves the two pieces are disjoint and have the
  same cardinality, and then shows that every repeated sorted two-sum in `A`
  is forced to be the central value `N`. Hence `|A| = 2|B|`.
- **Explicit geometric seed family**: ✓ **DONE** (`AlmostSidonSets/ExplicitSeeds.lean`).
  Specializing the construction to the Sidon seed `{1, 4, 4², ..., 4^m}`
  gives explicit almost-Sidon subsets of `{1, ..., N}` of size exactly
  `2(m + 1)` whenever `4^m ≤ ⌊N/3⌋`.

### Ideas To Try

- **Import explicit Sidon families**: combine `doubledFinset_almostSidonInInterval`
  with any formalized family of large finite Sidon sets to get concrete lower
  bounds for problem #864 immediately.
- **Asymptotic packaging from optimal Sidon bounds**: formalize the standard
  implication "Sidon sets of size `(1+o(1)) sqrt M` in `[1,M]` imply almost-Sidon
  sets of size `(1+o(1)) (2 / sqrt 3) sqrt N` in `[1,N]`" by taking
  `M = ⌊N/3⌋`.
- **Upper-bound side**: look for an elementary counting argument that exploits
  the existence of at most one repeated sum more efficiently than the raw
  Sidon-set bound. The lower-bound construction is now in place, so the next
  real mathematical work is on the converse direction.

---

## Problem #327: Unit Fraction Pairs ((a+b) | ab)

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Graham 1980 | Original problem statement |
| van Doorn (erdosproblems.com) | Upper bound f(N) ≤ (25/28+o(1))N |
| SAT solver computations (SharkyKesa) | Densities ~0.705 for N ≤ 5000 |
| Adenwalla (erdosproblems.com) | Positive answer to Q1 ⟹ negative answer to Q2 |

**Van Doorn's 25/28 argument**: Uses disjoint "star" neighborhoods S_a = {2a, 3a, 4a, 6a, 12a}
indexed by a = 8^b · 9^c · d with gcd(d,6)=1. Each S_a forces ≥2 omissions from any
pair-free set. The disjointness comes from unique factorization. Our `pair_n_cn_iff`
theorem already provides the exact forbidden-pair characterization needed.
**Formalizable: YES, high priority.**

**Computational data suggests true density is ~0.7**, well above 1/2. If this persists,
the conjecture f(N) = (1/2+o(1))N would be *false*, and the second question (does
avoiding (a+b)|2ab force o(N)?) becomes the interesting one.

**Triage update (2026-03-05):** no published upper bound better than `25/28`
was found in our latest scan (including erdosproblems + recent arXiv pointers).
So #327 currently looks like an *optimization* program on top of the existing
van Doorn framework, not a theorem-import opportunity.

### Ideas Tried

- **Odd numbers are pair-free**: Proved, gives f(N) ≥ ⌈N/2⌉. Parity obstruction:
  odd+odd = even, odd·odd = odd, so even cannot divide odd.
- **GCD classification**: Full parametric characterization via `sum_dvd_gcd_of_pair`.
- **Master constraint `pair_n_cn_iff`**: (n, cn) pair ⟺ (c+1) | n. Very powerful.
- **Forbidden pair families**: (3m,6m), (4m,12m), (10m,15m) all proved.

### Ideas Tried (continued)

- **Van Doorn's 25/28 upper bound**: ✓ **DONE** (VanDoorn.lean). Two-family approach:
  S-family {3a,6a} and T-family {4a,12a} parameterized by VDParam (3|v₂(a), Even v₃(a)).
  Disjointness via (v₂ mod 3, v₃ mod 2) signatures: all four multipliers {3,6,4,12}
  have distinct signatures (0,1), (1,1), (2,0), (2,1). Density 3/7 gives 25N/28.
  **Matches the best known upper bound for #327.**
- **Pair gadget mining update (2026-03-04)**: Expanded `scripts/gadget_mine.py`
  to search overlapping family combinations (`--max-families`, `--connected-only`).
  Best local pattern found for pairs is a triangle gadget on multipliers {1,r,s}
  with edges (1,r), (1,s), (r,s), forcing τ/|G| = 2/3 (e.g. {1,2,3}).
  Formalized the missing edge criterion in Lean:
  `pair_2n_3n_iff` and the derived constraints
  `pair_free_double_triple_not_div5`, `triangle_pairs_of_dvd60`,
  `pair_free_triangle_inter_card_le_one`, `pair_free_triangle_omits_at_least_two`,
  `triangles_disjoint_coprime6`, `pair_free_triangle_family_bound`,
  plus overlap-barrier theorems `vd_triangle_t_not_disjoint`
  and `vd_triangle_s_not_disjoint`, and quantitative overlap lower bounds
  `vd_triangle_t_overlap_card_lb`, `vd_triangle_t_overlap_card_lb_strong`,
  `vd_triangle_t_overlap_card_ge_two`, `vd_triangle_t_overlap_card_ge_three`,
  `vd_triangle_t_overlap_subset_channels`,
  `vd_triangle_t_overlap_card_le_strong`,
  `vd_triangle_t_overlap_card_eq_strong`,
  `vd_triangle_t_net_bound`,
  `vd_triangle_s_overlap_card_lb`, `vd_triangle_s_overlap_card_pos`,
  `vd_triangle_s_overlap_card_ge_two`, `vd_triangle_s_overlap_card_ge_three`,
  `vd_triangle_s_overlap_subset_channel`,
  `vd_triangle_s_overlap_card_le_strong`,
  `vd_triangle_s_overlap_card_eq_strong`,
  `vd_triangle_s_full_overlap_subset_channel`,
  `vd_triangle_s_full_overlap_card_le_strong`,
  `vd_triangle_s_full_overlap_card_lb`,
  `vd_triangle_s_full_overlap_card_eq_strong`, and overlap-aware mixed inequalities
  `vd_triangle_t_overlap_penalty_bound`,
  `vd_triangle_s_full_overlap_penalty_bound`,
  `vd_triangle_s_overlap_penalty_bound`
  (`UnitFractionPairs/Density.lean`, `UnitFractionPairs/VanDoorn.lean`).
  This now yields a first global packing inequality from triangles:
  `A.card + 2 * |{d ≤ N/180 : gcd(d,6)=1}| ≤ N`.
  It also proves overlap is not just nonempty: for
  `D△ = {d ≤ N/180 : gcd(d,6)=1}`, the overlap with the full T-union satisfies
  `|U△ ∩ U_T| ≥ |D△|` (one shared `60d` per parameter).
  A stronger bound is now formalized:
  `|U△ ∩ U_T| ≥ |{d ≤ N/180 : gcd(d,6)=1}| + |{d ≤ N/540 : gcd(d,6)=1}|`,
  using an additional overlap channel `180d = 4*(45d)` on the `N/540` band.
  This is now tight: overlap was classified exactly via two channels and we proved
  the exact formula
  `|U△ ∩ U_T| = |{d ≤ N/180 : gcd(d,6)=1}| + |{d ≤ N/540 : gcd(d,6)=1}|`.
  In particular, for all `N ≥ 540`, this forces at least two overlaps:
  `|U△ ∩ U_T| ≥ 2`, and for `N ≥ 900`, `|U△ ∩ U_T| ≥ 3`.
  Dually, on the low band `D_low = {d ≤ N/240 : gcd(d,6)=1}`, overlap with
  the full S-union satisfies `|U_low ∩ U_S| ≥ |D_low|` (one shared `120d` per parameter),
  hence `|U_low ∩ U_S| ≥ 1` for `N ≥ 240`, `|U_low ∩ U_S| ≥ 2` for `N ≥ 1200`,
  and `|U_low ∩ U_S| ≥ 3` for `N ≥ 1680`.
  This is now tight on the low band as well:
  `|U_low ∩ U_S| = |{d ≤ N/240 : gcd(d,6)=1}|`.
  We now pushed this to the full triangle range too:
  if `U△ = ⋃_{d≤N/180, gcd(d,6)=1} {60d,120d,180d}`, then
  `|U△ ∩ U_S| = |{d ≤ N/240 : gcd(d,6)=1}|`.
  We also now have overlap-aware combined counting inequalities:
  `A.card + 2|D△| + |D_T| ≤ N + |U△ ∩ U_T|`,
  `A.card + 2|D△| + |D_S| ≤ N + |U△ ∩ U_S|`,
  `A.card + 2|D_low| + |D_S| ≤ N + |U_low ∩ U_S|`,
  which makes the overlap penalty explicit when trying to merge triangle and
  van Doorn families without disjointness assumptions.
  Substituting the exact T-overlap formula yields a cleaned net theorem:
  `A.card + |D_T| + (|D△| - |D540|) ≤ N` (`vd_triangle_t_net_bound`).
  Substituting the exact S-overlap formula yields:
  `A.card + |D_S| + |D_low| ≤ N` (`vd_triangle_s_net_bound`).
  Substituting the full-range S-overlap formula yields:
  `A.card + |D_S| + (2|D△| - |D_low|) ≤ N`
  (`vd_triangle_s_full_net_bound`).
  Quantitative finite-`N` corollaries are now formalized:
  `A.card + |D_S| + 1 ≤ N` for `N ≥ 240`,
  `A.card + |D_S| + 2 ≤ N` for `N ≥ 1200`,
  `A.card + |D_S| + 3 ≤ N` for `N ≥ 1680`
  (`vd_triangle_s_net_bound_ge_one`, `_ge_two`, `_ge_three`).
  **New large-scale barrier**: `vd_triangle_full_overlap_absorbs_deficit`
  shows that for `N ≥ 18720`, the exact overlaps of the full triangle union
  with the full S- and T-unions already satisfy
  `2|D△| ≤ |U△ ∩ U_S| + |U△ ∩ U_T|`.
  So, beyond that scale, the full triangle family cannot yield a positive net
  gain over van Doorn's two-family packing by simple overlap-aware union
  counting alone.
  **Status:** local-to-global step complete for one family, and we now have a
  structural barrier: the full triangle family is provably not cross-disjoint
  from full van Doorn S/T families, so a direct three-family disjoint packing
  upgrade is impossible. Remaining: overlap-aware counting or trimmed domains.

### Ideas To Try

- **Upper half is NOT pair-free**: ✓ **DONE** (UpperHalf.lean). The pair (10m, 15m)
  satisfies 1/(10m) + 1/(15m) = 1/(6m) and lies in (N/2, N] for N = 15m.
  Proved for all m ≥ 1, giving infinitely many N where the upper half fails.
  This structurally distinguishes #327 from #302 and #301, where the upper half
  is always triple-free/sum-free. **The magnitude obstruction fails for #327.**
- **Mixed construction**: Odd numbers in [1, N/3] ∪ (N/2, N]. Gives density ~2/3,
  but need to verify cross-term pair-freeness. **Worth investigating.**
- **Computational lower bound**: Use `pair_n_cn_iff` to enumerate ALL pair constraints
  in [1, N] and greedily build pair-free sets. Compare density to 0.705 (SAT data).
  Not a Lean formalization, but would clarify the conjectured density.
- **Pair gadget mining via `pair_n_cn_iff`**: The master characterization (n, cn) pair
  ⟺ (c+1)|n is a perfect interface for systematic gadget search. Search over multiplier
  sets G ⊆ {1,...,M}, put an edge between u,v whenever the pair condition always holds
  between u·a and v·a (for appropriate parameter restrictions on a), and compute the
  minimum vertex cover. Choose parameter conditions (valuation signatures) for disjoint
  packing. Could rediscover Van Doorn's construction as one point in the space and
  potentially find smaller-multiplier gadgets with better omission ratios.
  **Formalizable: YES. Pair identities via `pair_n_cn_iff` are very short proofs.**

---

## Problem #302: Unit Fraction Triples (1/a = 1/b + 1/c)

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Graham 1980 | Original problem statement |
| Cambie (erdosproblems.com) | Lower bound f(N) ≥ (5/8+o(1))N: odds in [1,N/4] ∪ (N/2,N] |
| van Doorn (erdosproblems.com) | Upper bound f(N) ≤ (9/10+o(1))N |
| Brown-Rödl 1991 ([Bull. Aust. Math. Soc.](https://doi.org/10.1017/S0004972700029221)) | Coloring version (#303): any finite coloring has monochromatic 1/a = 1/b + 1/c. Statement formalized in [Google DeepMind formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/303.lean). |

**Cambie's 5/8 construction**: Take odd integers ≤ N/4 (about N/8 elements) plus all
integers in (N/2, N] (about N/2 elements). Total: ~5N/8.
- Upper half is triple-free (our `upper_half_triple_free`)
- Odds ≤ N/4 are triple-free (parity: odd+odd = even, odd·odd = odd)
- Cross-terms: if a odd ≤ N/4 and b,c ∈ (N/2,N], then a = bc/(b+c) > (N/2)²/N = N/4,
  contradicting a ≤ N/4.
**Formalizable: YES, using our existing infrastructure.**

### Ideas Tried

- **Factor identity (b-a)(c-a) = a²**: Elegant, powers the upper-half result.
  Key insight: expand in ℤ, use `zify` + `nlinarith`.
- **`triple_forces_small`**: Any triple member a satisfies 2a ≤ N. From a² ≤ (N-a)².
- **Upper half (N/2, N] is triple-free**: Proved, gives f(N) ≥ ⌊N/2⌋.
- **Odd numbers are triple-free**: Parity argument via `Nat.not_even_iff_odd` +
  `Odd.mul`/`Even.mul_left` to construct witnesses, then `omega`. ✓
- **Cambie's 5/8 construction**: Three-case proof (upper half, parity, cross-term
  magnitude via (a+1)² > a²). `cambie_triple_free`. ✓
- **Factor identity → triple classification**: Full bijection between divisors d ≤ a
  of a² and triples (a, a+d, a+a²/d). `triple_count_eq_divisor_count`. ✓

### Ideas Tried (continued)

- **Van Doorn's 9/10 upper bound**: ✓ **DONE** (VanDoorn.lean, 581 lines).
  Two disjoint families: S-family (2a,3a,6a) with v₂,v₃ even, T-family (4e,5e,20e)
  with 4|v₂, v₃,v₅ even. Disjointness via p-adic valuation signatures.
- **Star neighborhoods**: ✓ **DONE** (StarNeighborhood.lean). 11N/12 and 17N/18 bounds
  via two-missing-element technique.

### Ideas To Try

- **Tighten the 9/10 bound**: ✓ **RESOLVED — STRUCTURAL BARRIER** (VanDoorn.lean,
  Classification.lean). A systematic search for a third "U-family" to extend the S+T
  approach found that **no simple third family can improve the 9/10 bound**. Three
  interlocking obstructions prevent this:

  1. **Coprime-to-6 impossibility** (`triple_has_even_element`): Every triple
     1/c = 1/d + 1/e has at least one even element. If c is odd, then from
     (d-c)(e-c) = c², both d-c and e-c are odd, making d and e even
     (`triple_odd_smallest_forces_even`). So every triple family {c·k,d·k,e·k}
     must have at least one even multiplier — no family can avoid interaction
     with prime 2.

  2. **S-disjointness forces (even v₂, even v₃)**: S-elements have (odd v₂ OR
     odd v₃). Any U-element disjoint from S must therefore have even v₂ AND
     even v₃ — the same p-adic quadrant occupied by the T-family.

  3. **T-shadow covers the remaining quadrant**: All 8 S-compatible triples
     with max multiplier ≤ 100 were tested. For every one, the UParam
     configuration needed for S-disjointness creates fatal T-collisions:

  | Triple | Max mult | UParam constraint | Fatal T-collisions |
  |--------|----------|------------------|--------------------|
  | (4,5,20) | 20 | — | **This IS the T-family** |
  | (8,10,40) | 40 | v₂≡1(4), Odd v₅ | 8f=5e\_t, 10f=4e\_t |
  | (20,36,45) | 45 | v₂≡2(4), Odd v₅ | 36f=5e\_t, 45f=4e\_t |
  | (12,15,60) | 60 | v₂≡2(4), Odd v₅ | 12f=5e\_t, 15f=4e\_t |
  | (28,44,77) | 77 | v₂≡0(4), Odd v₅ | 28f=20e\_t, 44f=20e\_t, 77f=5e\_t |
  | (16,20,80) | 80 | v₂≡0(4), Odd v₅ | 20f=4e\_t (unblockable) |
  | (40,72,90) | 90 | — | Similar pattern |
  | (20,25,100) | 100 | — | Similar pattern |

  New triple identities formalized: `triple_20k_36k_45k`, `triple_28k_44k_77k`,
  `triple_12k_15k_60k`. These extend the library of known families but cannot
  serve as a third family due to the barrier above. **The 9/10 bound is tight
  for the S+T family approach; improving it requires a fundamentally different
  technique (e.g., non-parametric or Fourier-analytic methods).**

- **Lower bound beyond 5/8**: Cambie's construction combines odds ≤ N/4 with (N/2, N].
  Could we push further? Adding even numbers with special structure (e.g., powers of 2)
  to the set might preserve triple-freeness. Need to check: is there a triple (2^k, b, c)
  with b, c odd? From (b-2^k)(c-2^k) = 2^{2k}, both factors must be powers of 2,
  so b and c would be even — contradiction. **So powers of 2 can extend the Cambie set.**
  Adds ~log₂(N/4) elements: negligible asymptotically, but structurally interesting.
- **Graph coloring connection**: Brown-Rödl (1991) proved the Ramsey version (#303).
  Formalizing the connection between Ramsey and density versions would clarify the
  structural landscape. **Moderate effort.**
- **Systematic gadget mining**: The star neighborhood {2d,3d,4d,6d,12d} was found by hand.
  A systematic search over multiplier sets G ⊆ {1,...,M} would find all triple identities
  among elements of G, compute the hitting number τ(G) (minimum elements to remove to
  destroy all triples), and identify configurations with better omission-per-parameter than
  the star. The S+T barrier only blocks *parametric family* extensions; multi-element
  *gadgets* that force ≥3 omissions from a 6+ element set could bypass it entirely.
  Use z3 to enumerate candidate gadgets, then verify triple identities by `ring`.
  Disjointness via valuation signatures (see Infrastructure: ValSignature library).
  **This is the most credible path past 9/10 without deep number theory.**
  **Formalizable: YES, high priority. Depends on signature abstraction infrastructure.**
- **Supersaturation via divisor classification**: ✓ **d=1 PIPELINE COMPLETE**
  (Supersaturation.lean). The full d=1 program is done end-to-end:
  - Per-element exclusion (`triple_free_forces_exclusion`)
  - Endpoint separation (`exclusion_endpoints_pairwise_disjoint`)
  - Consecutive exclusion d=1 (`triple_free_consecutive_exclusion`)
  - Multiplicity characterization (`endpoint_dvd_sq_iff`)
  - Injectivity of exclusion map (`sq_add_strict_mono`)
  - Consecutive forcing (`triple_free_consecutive_forces_complement`)
  - **End-to-end counting bound** (`triple_free_consecutive_pair_bound`): |P| + |A| ≤ N
  The d=1 bound gives |A| ≤ N − O(√N), weaker than VanDoorn 9/10 but a complete
  proof-of-concept for the paradigm. The **full** program (all d | a² + average τ(n²))
  requires analytic number theory beyond current Mathlib (Dirichlet series, mean-value
  estimates of multiplicative functions). **Remaining work: VERY HARD (research-level).**
- **Non-uniform (variable-size) gadgets**: Instead of fixed-size gadgets like {2d,3d,6d}
  (always 3 elements), use structures whose size grows with the parameter. The full
  "divisor star" of d — all multiples c·d where c·d appears in some triple with d — has
  variable size depending on τ(d²). If the hitting number scales favorably with gadget
  size, this could give better exclusion ratios than fixed-size families. The challenge is
  proving disjointness when gadget sizes vary (the ValSignature approach assumes fixed
  multiplier sets). A hybrid approach: group parameters by τ(a²) value and use different
  gadgets per group. The PackingBound framework would need generalization to handle
  variable-size gadgets (each gadget d has its own size s_d and bound r_d).
  **Formalizable: MEDIUM. Requires generalizing PackingBound to variable sizes.**
- **Fourier-analytic methods**: The standard technique for density problems in additive
  combinatorics. The equation 1/a = 1/b + 1/c is multiplicative (a(b+c) = bc), making
  direct Fourier analysis on (ℤ/Nℤ, +) less natural. Two approaches:
  (1) Multiplicative Fourier analysis on (ℤ/Nℤ)×, viewing the constraint as a
  multiplicative convolution condition.
  (2) Divisor parametrization: b = a+d, c = a+a²/d reduces to an additive constraint
  on d, amenable to circle-method techniques.
  The Bloom-Mehta formalization demonstrates that circle-method proofs CAN be formalized
  in Lean ([b-mehta.github.io/unit-fractions](https://b-mehta.github.io/unit-fractions/)),
  though at substantial engineering cost. For #302 specifically, the per-element exclusion
  count τ(a²) connects to the Dirichlet divisor problem, where sharp bounds on
  ∑_{n≤N} τ(n²) are known (asymptotic to c·N·log²N). This average-case divisor density
  is the key input for a Fourier-flavored supersaturation bound.
  **Formalizable: HARD. Research-level mathematics + heavy Lean engineering.**

---

## Problem #313: Primary Pseudoperfect Numbers

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Graham 1980 | Original problem statement |
| Butske-Jaje-Mayernik 2000 | Studies `∑_{p|N} 1/p + 1/N = 1`, primary pseudoperfect numbers, and related graph-theoretic formulations |

Primary pseudoperfect numbers are a natural bridge problem for this repository:
their defining equation uses reciprocals of distinct primes, but after adjoining
`1/m` it becomes an Egyptian-fraction representation of `1`, so the
`pseudoperfect_iff_unit_sum` bridge from the weird-number side becomes directly
relevant.

### Ideas Tried

- **Statement formalization**: ✓ **DONE** (`PrimaryPseudoperfect/Statement.lean`).
  We formalized the prime-reciprocal witness predicate and the infinite
  conjecture.
- **Bridge to pseudoperfect numbers**: ✓ **DONE** (`PrimaryPseudoperfect/Connections.lean`).
  For every witness with `m > 2`, adjoining `m` itself turns the defining
  equation into a divisor-set Egyptian-fraction representation of `1`, so
  `m` is pseudoperfect. Consequently primary pseudoperfect numbers are never
  weird.
- **Successor-prime extension**: ✓ **DONE** (`PrimaryPseudoperfect/Examples.lean`).
  If `m` is primary pseudoperfect and `m + 1` is prime, then `m * (m + 1)` is
  primary pseudoperfect. This recovers the classical chain `2 → 6 → 42 → 1806`.
- **Concrete examples**: ✓ **DONE** (`PrimaryPseudoperfect/Examples.lean`).
  Formalized examples `2`, `6`, `42`, and `1806`.

### Ideas To Try

- **Import more known examples**: `47058`, `2214502422`, and beyond from the
  current known list. This is straightforward and gives a larger verified testbed.
- **Squarefree reformulation**: show our witness-based definition is equivalent
  to the standard squarefree divisor equation
  `∑_{p|m} 1/p + 1/m = 1`.
- **Graph-theoretic bridge**: connect the prime-reciprocal equation to the
  "perfectly weighted graph" viewpoint from Butske-Jaje-Mayernik.
- **Successor-prime chain diagnostics**: characterize when the elementary
  extension step can continue and where it must fail.

---

## Problem #364: Consecutive Powerful Triples

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős 1976 / Erdős-Graham 1980 | Original problem statement: are there any triples of consecutive positive integers all of which are powerful? |
| Mollin-Walsh 1986 | Records the problem in the context of consecutive powerful numbers; consecutive pairs exist infinitely often via Pell-type constructions |
| Chan 2025 | Excludes certain cube-centered triples where the two neighbors have shape `p^3 x^2` |
| She 2025 | Excludes cube-centered triples where the two neighbors have shape `p^2 x^3` |

As of **2026-04-16**, the Erdős Problems site still lists #364 as **open** and
marks it **verifiable**: finite certificates can rule out initial ranges, but
no general proof is known.

### Ideas Tried

- **Statement formalization**: ✓ **DONE** (`ConsecutivePowerful/Statement.lean`).
  We formalized the predicate `Powerful`, the triple-start predicate
  `ConsecutivePowerfulTriple`, and the existential conjecture.
- **First modular obstruction**: ✓ **DONE** (`ConsecutivePowerful/Modular.lean`).
  A number congruent to `2 mod 4` cannot be powerful, so there are no four
  consecutive powerful numbers and any triple start satisfies `n ≡ 3 (mod 4)`.
- **Second modular obstruction**: ✓ **DONE** (`ConsecutivePowerful/Modular.lean`).
  In a hypothetical triple, the unique multiple of `3` is automatically a
  multiple of `9`, forcing `n ≡ 0, 7, 8 (mod 9)`.
- **Combined CRT barrier**: ✓ **DONE** (`ConsecutivePowerful/Modular.lean`).
  Combining the mod-`4` and mod-`9` constraints yields the clean necessary
  condition `n ≡ 7, 27, 35 (mod 36)`.
- **Residue-class certified search**: ✓ **DONE** (`ConsecutivePowerful/Search.lean`).
  We characterized `Powerful` via finite factorization support, made it
  decidable, and then machine-checked that there is no triple start below
  `1000000`. The search only needs to inspect the three admissible residue
  classes modulo `36`, so the computation reflects the modular theorem rather
  than brute-forcing every start.

### Ideas To Try

- **Push local obstructions beyond `2` and `3`**: derive stronger admissible
  residue classes modulo `2^a 3^b` or mixed moduli that interact with the
  squarefull condition more sharply than the current `mod 36` barrier.
- **Import the cube-centered literature**: formalize Chan's and She's 2025
  exclusions as the first genuinely nonlinear partial results.
- **Square/cube decomposition route**: every powerful number is of the form
  `a^2 b^3`. A formal decomposition theorem could turn the triple question into
  a Diophantine system on neighboring square-cube products.
- **Finite certified search**: package a `native_decide` or verified external
  certificate for small ranges as infrastructure toward the site's
  finite-verification framing.

---

## Problem #301: Unit Fraction Sum-Free Sets (1/a = Σ 1/bᵢ)

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Graham 1980 | Original problem statement |
| van Doorn (erdosproblems.com) | Upper bound f(N) ≤ (25/28+o(1))N (same as #327!) |
| Bloom 2021 ([arXiv:2112.03726](https://arxiv.org/abs/2112.03726)) | Any set of positive upper density contains finite subset with reciprocals summing to 1 |
| Bloom-Mehta (Lean formalization) | [b-mehta.github.io/unit-fractions](https://b-mehta.github.io/unit-fractions/) — formalized Hardy-Littlewood circle method |
| Liu-Sawhney 2024/2026 ([arXiv:2404.07113](https://arxiv.org/abs/2404.07113)) | Quantitative threshold: \|A\| ≥ (1-1/e+ε)N forces a reciprocal-sum-1 subset; constant 1-1/e is sharp |
| Conlon-Fox-Pham-Sudakov-Tran 2025 ([arXiv:2311.01416](https://arxiv.org/abs/2311.01416)) | Asymptotic for #300 (largest Egyptian-1-avoiding subset of [1,N] is (1-1/e+o(1))N), giving a structural template for reciprocal-sum forcing |

**Bloom's theorem** (any set of positive upper density contains a finite subset
with Σ 1/n = 1) is the *dual* of Problem #301. Problem #301 asks how dense a set
can be while avoiding 1/a = Σ 1/bᵢ (target must be in the set). The gap between
these — where the target must be in the set — is the content of #301.

**Van Doorn's 25/28 bound works for both #301 and #327.** The disjoint witness
sets produce forbidden configurations for both problems.

### Ideas Tried

- **SumFree ⟹ TripleFree**: Proved as structural connection (`sumFree_implies_tripleFree`).
  Witnesses that Problem 301 ⊇ Problem 302.
- **Upper half is sum-free**: `upper_half_sum_free`. Proof splits by |S|: k=1 forces
  a=b (contradiction), k≥2 gives Σ1/b ≥ 2/N > 1/a (since a > N/2). Clean
  `Finset.sum_le_sum` proof without needing upper-half-triple-free. ✓
- **9/10 upper bound via inheritance**: ✓ **DONE** (UpperBound.lean). Since SumFree→TripleFree,
  van Doorn's 9/10 bound for triple-free sets transfers directly to sum-free sets.
  One-line proof: `van_doorn_upper_bound N A (sumFree_implies_tripleFree hA) hAN`.
  **First formalized upper bound for Problem 301.**

- **Extended star gadget analysis**: ✓ **DONE** (ExtendedStar.lean). The extended star
  E_d = {2d, 3d, 4d, 6d, 10d, 12d, 15d} has 7 elements with 4 triple violations
  and 4 additional k=3 sum-free violations. Triple-free sets keep ≤ 5 elements
  (e.g., {2d,3d,10d,12d,15d}), but sum-free sets keep ≤ 4. The 5-element
  triple-free subset is NOT sum-free (1/(2d) = 1/(3d)+1/(10d)+1/(15d)), providing
  a systematic gadget-level explanation for why #301 has tighter bounds than #302.
  **Novel: first formal demonstration of the sum-free/triple-free gap at gadget level.**
  `sum_identity_2_3_10_15`, `sum_identity_2_4_6_12`, `sum_identity_3_6_10_15`,
  `sum_identity_4_10_12_15`, `extended_star_card_eq_seven`,
  `sum_free_inter_extended_star_le_four`, `triple_free_extended_star_five`,
  `sum_free_strictly_more_restrictive`.

### Ideas To Try

- **Odd numbers are NOT sum-free**: ✓ **DONE** (Parity.lean). Counterexample:
  1/3 = 1/5 + 1/9 + 1/45 (all odd, k=3). The parity obstruction only blocks
  even-length representations: clearing denominators gives ∏ b = a · Σ ∏_{j≠i} bⱼ;
  for k even, RHS = sum of even-many odds = even ≠ odd = LHS. For k odd, both
  sides are odd and no contradiction arises. **Corrects the earlier conjecture.**
- **Even-length parity obstruction (odd sets)**: ✓ **DONE** (Parity.lean).
  Formalized the general obstruction: if all elements are odd and
  `1/a = ∑_{b∈S} 1/b`, then `S.card` must be odd. Equivalently, even-cardinality
  witnesses are impossible (`odd_even_card_no_unit_sum`,
  `odd_set_even_card_obstruction`), with the direct parity-forcing corollary
  `odd_set_witness_card_odd`.
- **Cambie's 5/8 construction for #301**: ✓ **RESOLVED — DOES NOT LIFT** (Cambie.lean).
  The k=2 cross-terms are blocked by magnitude (each 1/b < 2/N, sum < 4/N ≤ 1/a).
  But k=3 allows violations: 1/15 = 1/36 + 1/45 + 1/60 sits in cambieSet(60).
  General family: 1/(15m) = 1/(36m) + 1/(45m) + 1/(60m) for all odd m.
  Both parity and magnitude barriers break for k=3: sum of 3 odd products is odd
  (no parity contradiction), and 3 reciprocals from (N/2,N] can sum to ≥ 4/N.
  **The 5/8 lower bound is specific to #302; #301 needs a different approach.**
  `cambie_not_sum_free`, `cambie_not_sum_free_family`, `cambie_triple_free_but_not_sum_free`.
- **Van Doorn's 25/28 bound for #301**: A dedicated construction (not via TripleFree
  inheritance) would require showing star neighborhoods {2a,3a,4a,6a,12a} produce
  forbidden sum-free configurations. Would improve the bound from 9/10 to 25/28.
  Note: SumFree does NOT imply PairFree, so the #327 bound cannot be inherited.
  **Would need to show {3a, 6a} or {4a, 12a} pairs produce sum-free violations.**
- **Multiplier-fiber reduction**: ✓ **DONE** (`MultiplierFiber.lean`).
  The core reduction is now formalized via `sum_free_fiber_egyptian_free`:
  for each `a ∈ A`, the fiber `K_a = {k ≥ 2 : a*k ∈ A}` is `EgyptianOneFree`.
  The bridge is now packaged in both directions: if a fiber contains all
  nontrivial divisors of `n`, then sum-freeness forces `DivisorEgyptianFree n`
  (`sum_free_fiber_divisor_egyptian_free`); contrapositively, every
  pseudoperfect divisor set obstructs sum-freeness of the ambient fiber
  (`not_sum_free_of_pseudoperfect_fiber_cover`).
  This isolates the remaining bottleneck to *quantitative forcing on fibers*.
- **Fiber diagnostics pipeline (bounded witness optimization)**: ✓ **DONE (experimental)**.
  `scripts/gadget_mine.py --sumfree-fibers` now builds bounded witness hypergraphs
  (`1/a = Σ 1/b`, RHS size ≤ `k`), solves max-set instances (z3 when available),
  and reports per-fiber reciprocal-mass diagnostics (`|K_a|`, best subset sum ≤ 1,
  exact witness detection, and optional stronger audit with larger RHS bound).
  It now also supports an automatic **cut-loop** (`--cut-loop`): optimize, audit,
  add violating witness, and re-optimize.
  Empirically (N up to 36), unrestricted runs are often dominated by long `a=1`
  witnesses, while `1 ∉ A` runs still produce near-threshold fibers (especially
  around `a=2`) with no exact Σ1/k = 1 witness under stronger audit (`rhs ≤ 12`).
  A quick sweep (`N = 30,32,34,36,38,40`, `rhs ≤ 8`, audit `rhs ≤ 12`) yields
  bounded-model densities around `0.75 ± 0.03` and repeatedly identifies the
  tightest audited fibers at small multipliers (`a = 2,4,5`) with tiny positive
  gaps to 1 (e.g. `1/3740`, `1/6840`, `1/120`, `1/20`).
  **Use:** hypothesis generation for fiber-density forcing lemmas, not proof.
- **Fiber-density forcing via Bloom/Liu-Sawhney thresholds**: Use quantitative
  reciprocal-sum-1 forcing to show that sufficiently dense fibers `K_a` cannot
  occur in a SumFree set. This is the clearest currently-known route from the
  fiber reduction to stronger #301 upper bounds.
  **Triage: HIGH impact, HARD (research-level).**
- **Import #300 asymptotic technology (Conlon-Fox-Pham-Sudakov-Tran)**:
  adapt the `(1-1/e+o(1))N` Egyptian-1-avoiding machinery as a template for
  structural decompositions of fibers. The transfer to #301 is nontrivial because
  #301 includes an in-set target condition (`a ∈ A`).
  **Triage: MEDIUM impact, VERY HARD.**
- **Weird number connection**: The bridge `pseudoperfect_iff_unit_sum` shows that
  the divisors of any weird number form a set where ∑_{d>1} 1/d > 1 but no
  subset sums to 1. This is a "local" instance of the #301 phenomenon. Could we
  extract structural properties of sum-free subsets of divisor sets?
  **Novel direction, unclear feasibility.**

---

## Problem #470: Weird Numbers

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Sierpiński 1965 | Original definition of pseudoperfect numbers |
| Zachariou-Zachariou 1972 | Classification and structural results for semiperfect numbers |
| Benkoski-Erdős 1974 | Positive density; pn construction; primitive weird defined |
| Kravitz 1976 | Large PWN construction via Mersenne primes |
| Friedman 1993 ([JNT 44(3)](https://doi.org/10.1006/jnth.1993.1057)) | Pseudoperfect ↔ unit-fraction sum of divisors (Egyptian fraction bridge) |
| Butske-Jaje-Mayernik 2000 | Equations ∑_{p|N} 1/p + 1/N = 1; pseudoperfect/perfectly weighted graphs |
| Melfi 2015 ([ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0022314X14002637)) | Infinite PWNs conditional on Cramér's conjecture |
| Liddy-Riedl 2018 | Odd weird ⟹ ≥6 distinct prime factors |
| Amato-Hasler-Melfi-Parton 2019 ([arXiv:1802.07178](https://arxiv.org/abs/1802.07178)) | PWNs with up to 16 prime factors; largest has 14712 digits |
| Fang 2022 ([arXiv:2207.12906](https://arxiv.org/abs/2207.12906)) | No odd weird number below 10^21 (reverse search) |
| McNew-Setty 2025 ([arXiv:2507.23041](https://arxiv.org/abs/2507.23041)) | Refined density bounds for abundant numbers |

**The pn construction (Benkoski-Erdős)**: If n is weird and p > σ(n) is prime with
p ∤ n, then pn is weird. Proof: divisors of pn decompose as {d} ∪ {pd} for d | n.
The p-multiples are all > n, so any subset summing to pn from divisors of pn would
require using the divisors of n to reach n — impossible since n is weird.
**Highly formalizable. This is the core structural theorem about weird numbers.**

**Every multiple of a pseudoperfect number is pseudoperfect**: If Σ_{s∈S} s = n
for S ⊆ properDivisors(n), then {ms : s ∈ S} ⊆ properDivisors(mn) and sums to mn.
Contrapositive: if mn is weird, then n is not pseudoperfect.
**Highly formalizable.**

**Weird ⟹ ≥ 3 distinct prime factors**: Any abundant number with ≤ 2 distinct
prime factors is pseudoperfect. The divisor lattice of p^a · q^b allows greedy
subset-sum construction. **Moderately formalizable.**

**Why odd weird numbers are elusive**: Odd abundant numbers need many small prime
factors (3,5,7,11,...) to achieve σ(n)/n > 2. But many small factors create a
rich divisor set making subset sums easy to find → pseudoperfection likely.

### Ideas Tried

- **Computational verification**: 70 is smallest weird, primitive weird via `native_decide`.
- **Perfect ⟹ pseudoperfect**: Proved. Perfect numbers are not weird.

### Ideas Tried (continued)

- **"pn is weird" theorem**: ✓ **DONE** (`weird_mul_prime` in Structure.lean). Full
  Benkoski-Erdős construction with σ multiplicativity and subset-sum decomposition.
- **"Multiples of pseudoperfect are pseudoperfect"**: ✓ **DONE** (`pseudoperfect_mul`).
- **Pseudoperfect ↔ Egyptian fraction of 1**: ✓ **DONE** (`pseudoperfect_iff_unit_sum`
  + full abundancy chain in EgyptianBridge.lean).
- **Odd weird ≥ 3 prime factors**: ✓ **DONE** (`odd_weird_three_prime_factors`).
- **Primitive weird 2pq**: ✓ **DONE** (`two_pq_primitive_when_weird`).
- **Infinitely many weird numbers**: ✓ **DONE** (`infinitely_many_weird`).
- **DivisorEgyptianFree characterization**: ✓ **DONE** (DivisorEgyptianFree.lean).
  Defined `DivisorEgyptianFree(n)` := no nonempty T ⊆ divisors(n)\{1} with Σ 1/t = 1.
  Master theorem: `weird_iff_abundant_egyptian_free` — weird ⟺ abundant ∧ DivisorEgyptianFree.
  Also proved `prime_divisor_egyptian_free` (primes are trivially DEF) and
  `perfect_not_divisor_egyptian_free` (perfect numbers are NOT DEF).
  **Unifies #470 with the unit-fraction avoidance framework of #301/#302.**

### Ideas To Try

- **Deficient/prime not weird**: ✓ **DONE** (Statement.lean). Deficient numbers are
  not abundant hence not weird. Primes have properDivisors = {1}, sum = 1 < p.
  Uses Mathlib's `Nat.sum_properDivisors_eq_one_iff_prime`.
- **836 is weird / primitive weird**: ✓ **DONE** (Statement.lean). Second-smallest
  weird number, verified via `native_decide`.
- **4030, 5830 (next weird numbers)**: Extend computational verification.
  **Easy, ~5 lines each.**
- **Odd weird ≥ 6 prime factors (Liddy-Riedl full result)**: We proved ≥ 3. The gap
  to 6 requires showing that odd abundant numbers with 3, 4, or 5 distinct prime
  factors are always pseudoperfect. This is a serious case analysis:
  - 3 primes: σ(p^a q^b r^c)/p^a q^b r^c grows with exponents, but greedy subset-sum
    on the divisor lattice should succeed.
  - 4–5 primes: similar but harder, need to track all 2^k-1 proper subsets.
  **Moderate-hard. Would be a significant strengthening of our result.**
- **Odd weird ≥ 4 prime factors** (incremental push): Extend the σ-bounding approach
  from `odd_weird_three_prime_factors` to three-prime forms p^a·q^b·r^c. Show that
  odd abundant numbers with exactly 3 distinct primes are always pseudoperfect via
  σ multiplicativity + greedy subset-sum on the divisor lattice. Same proof flavor
  as ≥3 (cascading σ inequalities, coprimality decomposition), scales linearly with
  cases. Pushing from 3 to 4 (and potentially 5) toward the known ≥6 (Liddy-Riedl)
  would be meaningful formalized progress.
  **Formalizable: YES, medium effort. Mechanically similar to existing proof.**
- **DivisorEgyptianFree families**: ✓ **DEFINITION DONE** (DivisorEgyptianFree.lean).
  `DivisorEgyptianFree` defined and `weird_iff_abundant_egyptian_free` proved.
  Next step: if DivisorEgyptianFree holds for structured infinite families
  (e.g., certain 2^k·p·q patterns with constraints), this produces new families of weird
  numbers. Reuses the unit-fraction machinery rather than doing subset-sum directly.
  For small divisor sets, `native_decide` on the finite check may suffice.
  **Formalizable: YES. Bridges #470 and #301 infrastructure.**
- **Kravitz-style large primitive weird numbers**: Construct explicit primitive weird
  numbers using Mersenne primes. If 2^p - 1 is prime, then 2^{p-1}(2^p - 1)q for
  suitable q could be primitive weird. **Interesting but needs careful analysis.**
- **Abundancy gap theorem**: For weird n, we know σ(n)/n > 2 (strictly).
  Can we prove a lower bound on the gap? E.g., σ(n)/n ≥ 2 + 1/n or similar?
  For 70: σ(70)/70 = 144/70 ≈ 2.057. **Research-level, unclear.**
- **Weird number density**: Benkoski-Erdős proved positive density. Formalizing this
  requires showing the set {n : Weird n} has positive lower density. The proof uses
  pn construction + prime number theorem. **Hard (PNT dependency), but impactful.**

---

## Cross-Cutting Observations

### The 1/2 Barrier

Problems #327, #302, #301 all conjecture f(N) = (1/2+o(1))N. Two independent
constructions achieve density 1/2:

1. **Parity (odd numbers)**: Works for all three. The obstruction is algebraic:
   odd+odd = even can't divide odd·odd = odd.
2. **Magnitude (upper half)**: Works for #302 and #301 (not #327). The obstruction
   is analytic: elements > N/2 have reciprocals < 2/N, too small to reconstruct.

Both achieve 1/2 by completely different mechanisms. For #302, Cambie's 5/8
*combines* both — odds up to N/4 (parity) ∪ (N/2, N] (magnitude). This suggests
the true extremal sets exploit both mechanisms simultaneously.

**Potential theorem**: For any pair-free (or triple-free, or sum-free) set A ⊆ [1,N]
with |A| > N/2, A must contain elements of both parities. This would show pure-parity
constructions are optimal. **Potentially provable and clean.**

### All Four Unit Fraction Problems Share Algebraic Core

| Problem | Equation | Divisibility form |
|---------|----------|-------------------|
| #242 | 4/n = 1/x + 1/y + 1/z | 4xyz = n(xy+xz+yz) |
| #327 | 1/a + 1/b = 1/k | (a+b) \| ab |
| #302 | 1/a = 1/b + 1/c | a(b+c) = bc |
| #301 | 1/a = Σ 1/bᵢ | Σ a·∏_{j≠i} bⱼ = ∏ bⱼ |

Our `triple_iff_div` and `unit_fraction_pair_iff` capture the first three. A
common abstraction might be worth building.

### Erdős-Straus Generates Unit Fraction Triples

Every Erdős-Straus solution 4/n = 1/x + 1/y + 1/z can be rearranged:
1/y + 1/z = 4/n - 1/x = (4x-n)/(nx). When this equals 1/a for some a,
we get the unit fraction triple 1/a = 1/y + 1/z. **Formalizable connection
between #242 and #302.**

### Pseudoperfect Numbers = Egyptian Fractions of 1 ✓ FORMALIZED

n pseudoperfect ⟺ ∃ S ⊆ properDivisors(n) with Σ s = n
⟺ ∃ S ⊆ {n/d : d | n, d < n} with Σ 1/s = 1.

So weird numbers are *exactly* the abundant n for which 1 has no Egyptian
fraction representation using reciprocals of complementary divisors of n.
This bridges #470 with the Egyptian fraction universe of #301.

**Formalized as**: `pseudoperfect_iff_unit_sum`, `weird_no_unit_sum`,
`pseudoperfect_divisors_not_sumFree`, plus the full abundancy chain.

### Abundancy Index as a Unifying Lens ✓ FORMALIZED

The identity ∑_{d|n} 1/d = σ(n)/n converts between the discrete world
(divisor sums, abundancy) and the continuous world (unit-fraction sums).
This gives bidirectional characterizations:
- Abundant ↔ ∑ 1/d ≥ 2
- Perfect ↔ ∑ 1/d = 2
- Deficient ↔ ∑ 1/d < 2
- Weird ⟹ ∑_{d>1} 1/d > 1 but no subset sums to 1

**Potential new theorem**: "Intermediate value" — for any abundant n, there
exists T ⊂ {divisors > 1} with ∑_{t∈T} 1/t ∈ (0, 1). This is trivially
true (take any singleton {d} with d > 1), but the interesting question is
whether we can get ∑ 1/t arbitrarily close to 1 from below. For weird numbers,
we can't HIT 1, but can we get within ε? **Unclear, research-level.**

### Graph/Hypergraph Perspective

Each avoidance problem defines a (hyper)graph on [N]:
- #327: graph, edges = pairs (a,b) with (a+b)|ab. PairFree = independent set.
- #302: 3-uniform hypergraph, edges = triples {a,b,c} with 1/a = 1/b + 1/c.
- #301: hypergraph with variable-size edges.

Van Doorn's bounds use Turán-type arguments: find disjoint edge-neighborhoods
forcing omissions. Our `pair_n_cn_iff` is essentially computing the neighborhood
structure.

### The Bloom-Mehta Formalization Precedent

[b-mehta.github.io/unit-fractions](https://b-mehta.github.io/unit-fractions/) formalized
the Erdős-Graham density conjecture proof in Lean, including the Hardy-Littlewood
circle method. While their analytic techniques are far heavier than what we need,
their blueprint approach (dependency graphs, modular proof structure) is a good model.

---

## Priority Queue for Next Formalizations

### Completed

| # | Theorem | Problem | Status |
|---|---------|---------|--------|
| 1 | Cambie's 5/8 construction | #302 | **DONE** ✓ |
| 2 | "pn is weird" (Benkoski-Erdős) | #470 | **DONE** ✓ |
| 3 | Odd numbers are triple-free | #302 | **DONE** ✓ |
| 4 | Multiples of pseudoperfect are pseudoperfect | #470 | **DONE** ✓ |
| 5 | Upper half is sum-free | #301 | **DONE** ✓ |
| 7 | Pseudoperfect ↔ Egyptian fraction of 1 | #470↔#301 | **DONE** ✓ |
| 8 | Factor identity → triple classification | #302 | **DONE** ✓ |
| — | Van Doorn's 9/10 upper bound | #302 | **DONE** ✓ |
| — | Star neighborhood bounds (11/12, 17/18) | #302 | **DONE** ✓ |
| — | Odd weird ≥ 3 prime factors | #470 | **DONE** ✓ |
| — | Primitive weird 2pq | #470 | **DONE** ✓ |
| — | Infinitely many weird numbers | #470 | **DONE** ✓ |
| — | Abundancy chain (5 theorems) | #470 | **DONE** ✓ |
| — | Upper half NOT pair-free | #327 | **DONE** ✓ |
| — | Deficient/prime not weird | #470 | **DONE** ✓ |
| — | 836 is primitive weird | #470 | **DONE** ✓ |
| — | Odd numbers NOT sum-free (counterexample) | #301 | **DONE** ✓ |
| — | Even-length parity obstruction on odd sets | #301 | **DONE** ✓ |
| — | Van Doorn's 25/28 upper bound (pair-free) | #327 | **DONE** ✓ |
| — | 9/10 upper bound (sum-free via inheritance) | #301 | **DONE** ✓ |
| — | Cambie set NOT sum-free (structural gap #301 vs #302) | #301 | **DONE** ✓ |
| — | Erdős-Straus → triples connection | #242 → #302 | **DONE** ✓ |
| — | ValSignature abstraction library | Infra | **DONE** ✓ |
| — | Packing/omission framework (PackingBound) | Infra | **DONE** ✓ |
| — | Gadget mining script (z3) | #302, #327 | **DONE** ✓ |
| — | Supersaturation d=1 pipeline (full end-to-end) | #302 | **DONE** ✓ |
| — | Extended star gadget analysis (#301 ≠ #302) | #301 | **DONE** ✓ |
| — | Third-family barrier (S+T approach is tight) | #302 | **DONE** ✓ |
| — | DivisorEgyptianFree bridge (#470 ↔ #301) | #470 | **DONE** ✓ |
| — | Multiplier-fiber reduction (#301 fiber reformulation + #470 bridge) | #301 | **DONE** ✓ |
| — | Parity optimality (odd uniquely optimal for #302/#327; neither for #301) | #327, #302, #301 | **DONE** ✓ |

### Active Queue (ranked by impact × feasibility)

| Priority | Theorem / Task | Problem | Effort | Notes |
|----------|---------------|---------|--------|-------|
| **A** | **Odd weird ≥ 4 prime factors** | #470 | Medium | Incremental push toward Liddy-Riedl (≥6). Same proof flavor as ≥3 (σ multiplicativity + coprimality decomposition), scales linearly with cases. |
| **B** | **Non-uniform gadgets** | #302 | Medium | Variable-size gadgets whose size scales with τ(a²). Requires generalizing PackingBound to variable sizes. Could bypass S+T barrier. |
| **C** | **Fiber-density forcing for #301** | #301 | Hard | Build on `sum_free_fiber_egyptian_free` and apply quantitative reciprocal-sum-1 thresholds (Bloom/Liu-Sawhney) to force contradictions from dense fibers. Most direct route to improve the 9/10 inherited bound. |
| **D** | **Pair gadget mining for #327** | #327 | Medium | **PARTIAL:** triangle gadget now has global packing bound (`pair_free_triangle_family_bound`), and new barrier theorems (`vd_triangle_t_not_disjoint`, `vd_triangle_s_not_disjoint`, `vd_triangle_t_overlap_card_lb`, `vd_triangle_t_overlap_card_lb_strong`, `vd_triangle_t_overlap_card_ge_two`, `vd_triangle_t_overlap_card_ge_three`, `vd_triangle_t_overlap_subset_channels`, `vd_triangle_t_overlap_card_le_strong`, `vd_triangle_t_overlap_card_eq_strong`, `vd_triangle_t_net_bound`, `vd_triangle_s_overlap_card_lb`, `vd_triangle_s_overlap_card_pos`, `vd_triangle_s_overlap_card_ge_two`) show full-family disjoint merge with van Doorn S/T is impossible and quantify unavoidable overlap with both T and S (including exact T-overlap formula). We now also have overlap-aware merge inequalities (`vd_triangle_t_overlap_penalty_bound`, `vd_triangle_s_overlap_penalty_bound`). Triage update: no known published upper bound better than 25/28; likely wins are finite-`N` improvements, refined lower bounds, or overlap-aware constants. |
| **E** | **DivisorEgyptianFree families** | #470 | Medium | New weird number construction technique via unit-fraction avoidance on divisor sets. Bridges #470 and #301 machinery. |
| **F** | **Odd weird ≥ 6 prime factors** | #470 | Hard | Liddy-Riedl full result; case analysis on 3–5 prime factors. Item A is a stepping stone. |
| **G** | **Full supersaturation (all divisors)** | #302 | Very Hard | Extend d=1 pipeline to all d | a² using average order of τ(n²) ∼ c·log²n. Requires Mathlib extensions for Dirichlet series / mean-value estimates. Research-level analytic NT. |
| **H** | **Fourier-analytic methods** | #302 | Very Hard | Multiplicative Fourier analysis or circle method via divisor parametrization. Research-level + heavy Lean engineering. |
| **I** | **Weird number density** | #470 | Very Hard | Benkoski-Erdős positive density; requires PNT. |

**Recommended next steps**: A (odd weird ≥4 primes) and C (fiber-density forcing for #301) are the highest-impact options now. B and D remain practical medium-effort explorations.

### Abundancy Chain (completed)

Building on the Egyptian fraction bridge (`pseudoperfect_iff_unit_sum`), we proved:
- `sum_reciprocal_divisors_eq`: ∑_{d|n} 1/d = σ(n)/n (the classical abundancy identity)
- `perfect_canonical_unit_sum`: perfect ⟹ ∑_{d>1} 1/d = 1
- `weird_reciprocal_overshoot`: weird ⟹ ∑_{d>1} 1/d > 1 (but no subset hits 1)
- `abundant_iff_reciprocal_sum_ge_two`: abundant ↔ ∑ 1/d ≥ 2
- `perfect_iff_reciprocal_sum_two`: perfect ↔ ∑ 1/d = 2

These characterizations complete the unit-fraction perspective on weird/abundant/perfect.

### Bradford 2026 Investigation
Bradford's arXiv:2602.11774 claims full proof of Erdős-Straus. **Verdict: CRITICAL GAP.**
The algebraic identities are correct (3 formalized in Lean), but the covering system
claim is unproven and likely false due to Schinzel's 1956 barrier: polynomial identity
congruences cannot cover quadratic residue classes. The Erdős-Straus conjecture remains OPEN.

---

## Novelty Assessment

Results are classified as **Novel** (not known to appear in the literature),
**Possibly novel** (elementary but we have not found a prior statement),
or **Known** (formalization of a published result or folklore).

### Novel

| Result | Problem | File | Why novel |
|--------|---------|------|-----------|
| Cambie set is NOT sum-free | #301 | `UnitFractionSets/Cambie.lean` | Cambie proposed the 5/8 construction for #302; no prior work checks whether it works for #301. The counterexample 1/15 = 1/36 + 1/45 + 1/60 and the analysis of why both parity and magnitude barriers break for k=3 appear to be original. |
| Cambie set fails for infinitely many N | #301 | `UnitFractionSets/Cambie.lean` | The scaled family 1/(15m) = 1/(36m) + 1/(45m) + 1/(60m) for all odd m extends the base counterexample to an infinite family. |
| Structural gap: triple-free but not sum-free | #301 vs #302 | `UnitFractionSets/Cambie.lean` | The combination `cambie_triple_free_but_not_sum_free` is a clean witness that #301 ≠ #302 structurally. This is a concrete negative result separating two Erdős problems. |
| Star neighborhood bounds (17/18, 11/12) | #302 | `UnitFractionTriples/StarNeighborhood.lean` | The 5-element star {2d,3d,4d,6d,12d} hitting-set argument is a different proof technique from van Doorn's S+T family approach. These intermediate bounds may not appear in the literature. |

### Novel (continued)

| Result | Problem | File | Why novel |
|--------|---------|------|-----------|
| Coprime-to-6 impossibility for triples | #302 | `UnitFractionTriples/Classification.lean` | `triple_has_even_element` and the stronger `triple_odd_smallest_forces_even` (odd smallest → both larger even). The fact that every triple family must have an even multiplier, and the complete barrier analysis explaining why no third family can improve the 9/10 bound, appear to be original. |
| Third-family barrier analysis | #302 | `UnitFractionTriples/VanDoorn.lean`, `LITERATURE.md` | Systematic enumeration of all S-disjoint triples up to max multiplier 100, showing fatal T-collisions for all candidates. Proves the S+T approach cannot be extended by simple parametric families. |

### Possibly Novel

| Result | Problem | File | Notes |
|--------|---------|------|-------|
| Value-truncation stability for lower isolated sums | #152 | `SidonSumsets/Stability.lean` | Elementary observation: below a value cutoff, sumset membership is already determined by the truncated set. We have not found this exact infinite-strategy packaging in the literature. |
| Strong-gap sequences have infinitely many isolated sums | #152 | `SidonSumsets/FastGrowth.lean` | The criterion `2u_n + 1 < u_{n+1}` is elementary, but we have not found this exact theorem or its formulation as a stable lower-isolated witness class in the literature. |
| Finite Sidon obstruction family with empty lower-isolated region | #152 | `SidonSumsets/Obstructions.lean` | The construction is elementary, but we have not found this explicit infinite family showing the naive finite value-truncation strengthening fails. |
| Odd numbers are NOT sum-free | #301 | `UnitFractionSets/Parity.lean` | The identity 1/3 = 1/5 + 1/9 + 1/45 is trivially checkable, but the explicit observation that the parity obstruction is length-dependent (blocks even k, fails for odd k) may not have been stated. |
| Upper half NOT pair-free | #327 | `UnitFractionPairs/UpperHalf.lean` | The (10m, 15m) family is an immediate consequence of known pair families, but the explicit conclusion that the upper-half strategy fails for #327 (distinguishing it from #302/#301) may not have been noted. |
| 9/10 upper bound for sum-free sets | #301 | `UnitFractionSets/UpperBound.lean` | The inheritance SumFree→TripleFree→9/10 is trivial, but this specific bound for #301 may not appear in the literature (van Doorn's 25/28 is stated for #301, not 9/10). |

### Known (Formalizations)

| Result | Attribution | File |
|--------|------------|------|
| E-S even case, mod 3, mod 4 | Mordell (1967) | `ErdosStraus/EvenCase.lean` etc. |
| Reduction to primes ≡ 1 (mod 24) | Mordell/Schinzel | `ErdosStraus/Main.lean` |
| Cambie 5/8 construction (triple-free) | Cambie, erdosproblems.com | `UnitFractionTriples/Cambie.lean` |
| Van Doorn 9/10 bound (triples) | van Doorn, erdosproblems.com | `UnitFractionTriples/VanDoorn.lean` |
| Van Doorn 25/28 bound (pairs) | van Doorn, erdosproblems.com | `UnitFractionPairs/VanDoorn.lean` |
| Benkoski-Erdős (pn weird) | Benkoski & Erdős (1974) | `WeirdNumbers/Structure.lean` |
| Pseudoperfect ↔ unit fraction sum | Friedman (1993) | `WeirdNumbers/EgyptianBridge.lean` |
| Factor identity (b−a)(c−a) = a² | Classical | `UnitFractionTriples/UpperHalf.lean` |
| Odd weird ≥ 3 prime factors | Elementary (toward Liddy-Riedl) | `WeirdNumbers/OddWeirdFactors.lean` |
| Infinitely many weird numbers | Benkoski & Erdős (1974) | `WeirdNumbers/Structure.lean` |
| #242 → #302 bridge | Elementary algebra | `ErdosStraus/TripleBridge.lean` |
| SumFree → TripleFree | Trivial | `UnitFractionSets/Connections.lean` |

**Maintaining this table**: When a new theorem is proved, add it here and
classify it. When a result previously marked "Novel" or "Possibly novel"
is found in the literature, move it to "Known" and add the reference to
REFERENCES.md.

---

## Areas for Improvement

### Strengthening Existing Bounds

**Gap analysis** (best formalized bound vs. best known vs. conjectured):

| Problem | Best Lower | Best Upper | Conjectured | Formalized Lower | Formalized Upper |
|---------|-----------|-----------|-------------|-----------------|-----------------|
| #327 | ≥ N/2 (odd) | ≤ 25N/28 (vD) | N/2 + o(N) | ✓ N/2 | ✓ 25N/28 |
| #302 | ≥ 5N/8 (Cambie) | ≤ 9N/10 (vD) | N/2 + o(N) | ✓ 5N/8 | ✓ 9N/10 |
| #301 | ≥ N/2 (upper half) | ≤ 25N/28 (vD) | N/2 + o(N) | ✓ N/2 | ✓ 9N/10 |

**Status**: All three problems now have formalized upper bounds.
- #327 matches the best known bound (25/28) via two-family VDParam construction.
- As of **2026-03-05**, we have no vetted literature improvement beyond #327's 25/28 upper bound.
- #301 inherits 9/10 via SumFree→TripleFree; a dedicated 25/28 construction
  would require showing star neighborhoods produce forbidden sum-free configurations.
- #302 has the tightest analysis (5/8 to 9/10 gap).
- **NEW**: The Cambie 5/8 construction does NOT lift from #302 to #301
  (`cambie_not_sum_free`). This proves the lower bound gap between #301 and #302
  is genuine — improving #301 beyond N/2 requires a different construction.

### Deepening the Weird Numbers Theory

The weird numbers module is the most mature (#470), but several directions remain:

1. **Algebraic characterization of primitivity**: When is a weird number primitive?
   We have `two_pq_primitive_when_weird` for the 2pq case. Can we characterize
   primitive weird numbers in terms of their factorization structure?

2. **The abundancy gap**: For weird n, σ(n)/n > 2 strictly (`weird_reciprocal_overshoot`).
   What's the infimum of σ(n)/n over weird numbers? Known: 70 has σ(70)/70 ≈ 2.057.
   Is there a weird number with abundancy arbitrarily close to 2?

3. **Weird numbers and Egyptian fractions**: The bridge shows weird numbers are "Egyptian
   fraction avoiding." Can we use the divisor-classification machinery (`triple_count_eq_divisor_count`)
   to count how many near-miss subsets exist? This would quantify "how close" weird
   numbers come to being pseudoperfect.

### Connecting More Problems

Several cross-problem connections are identified but not formalized:

1. **#242 → #302**: ✓ FORMALIZED in `ErdosStraus/TripleBridge.lean`. Consecutive triple family, residual identity, conditional bridge, even-case specialization.
2. **Pure-parity theorem**: ✓ FORMALIZED in `Common/ParityOptimality.lean`. Odd uniquely optimal for #302/#327; neither parity works for #301. Even scaling lemma + filter bridge.
3. **Common abstraction**: All four problems have the form "avoid solutions to
   unit-fraction equations." A unified framework (Egyptian fraction avoidance sets)
   might yield shared lemmas.
4. **Divisor-based avoidance**: The weird number bridge shows divisor sets of abundant
   numbers are NOT sum-free. Can we characterize WHICH divisor sets are pair-free,
   triple-free, or sum-free?

### Infrastructure Improvements

1. **Valuation-signature abstraction library** (`Common/ValSignature.lean`): Both VanDoorn
   files repeat the same proof skeleton: define parameter predicates via padicValNat
   congruences → prove valuation shifts under multiplication → prove signature injectivity
   → disjointness. Abstract this into a reusable mini-library:
   - A general `Signature : ℕ → (Fin t → ZMod k)` built from padicValNat p n mod k.
   - Lemma: `Signature (c * n) = Signature n + Signature c` (componentwise).
   - Generic "if signatures differ then sets are disjoint" lemma.
   This turns trying a new family into: choose multipliers, choose a signature basis
   (primes + moduli), prove a short separation lemma, get disjointness for free.
   **HIGH PRIORITY — this is the enabler for gadget mining (#302, #327, #301).**

2. **Packing/omission framework** (`Common/PackingBound.lean`): The same combinatorial
   skeleton appears in StarNeighborhood.lean, both VanDoorn.lean files, and UpperBound.lean:
   disjoint structures × forced omissions → global size upper bound. Factor into:
   ```
   theorem packing_upper_bound (F : ℕ → Finset ℕ) (D : Finset ℕ) (s r : ℕ)
     (hsize : ∀ d ∈ D, (F d).card = s)
     (hpwd : (↑D : Set ℕ).PairwiseDisjoint F)
     (hfree : ∀ d ∈ D, (F d ∩ A).card ≤ s - r)
     (hrange : ∀ d ∈ D, F d ⊆ Icc 1 N) :
     A.card ≤ N - r * D.card
   ```
   Works for graphs (#327), 3-uniform hypergraphs (#302), and sum-free configs (#301).
   Makes new bounds literally plug-and-play.
   **HIGH PRIORITY — combined with (1), creates a "bound factory" loop.**

3. **Shared library**: Factor out common patterns (complement involution, reciprocal sum
   identity, parity obstruction) into `Erdos/Common/` for reuse across problems.
4. **P-adic signature bundles**: Subsumed by (1) above. The bundled `PadicSignature` type
   is the core of the ValSignature library.
5. **Divisor sum library**: `sum_reciprocal_divisors_eq` and the complement map are
   general enough to live in a shared module. Other problems might need them.
6. **Minor linter fixes**: Unused variables in Classification.lean, flexible `simp`
   in VanDoorn.lean + Structure.lean. Cosmetic but improves Mathlib compatibility.
7. **Extremal functions as first-class objects**: Define `f302(N) := max |A| over
   A ⊆ Icc 1 N, TripleFree A` (similarly f327, f301). Every new forcing gadget proof
   then yields a theorem about fXXX, making results easier to compare and reuse.
   Note: `Finset.sup` over all subsets requires decidability of the constraint, which
   may be awkward; the current ∀-quantified style (`∀ A, TripleFree A → ...`) is
   equivalent and more practical. **LOW PRIORITY — mostly cosmetic.**
