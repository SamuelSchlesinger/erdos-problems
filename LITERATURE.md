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
| Verified to 10^18 ([arXiv:2509.00128](https://arxiv.org/abs/2509.00128)) | Computational push + empirical f(p) data |
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
  Each identity is `ring`-verifiable. **Formalizable: YES.**
- **Bradford's one-dimensional reduction**: if the 2026 proof holds up, its core step
  reduces to: for every prime p, some x in [p/4, p/2] has a divisor of x² satisfying
  a modular equation. This is concrete and finitistic. **Worth monitoring.**
- **Elsholtz-Tao Type A/B classification**: restructures the solution space; might reveal
  new identities within p ≡ 1 (mod 24). **Moderate formalization effort.**

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

### Ideas Tried

- **Odd numbers are pair-free**: Proved, gives f(N) ≥ ⌈N/2⌉. Parity obstruction:
  odd+odd = even, odd·odd = odd, so even cannot divide odd.
- **GCD classification**: Full parametric characterization via `sum_dvd_gcd_of_pair`.
- **Master constraint `pair_n_cn_iff`**: (n, cn) pair ⟺ (c+1) | n. Very powerful.
- **Forbidden pair families**: (3m,6m), (4m,12m), (10m,15m) all proved.

### Ideas To Try

- **Van Doorn's 25/28 upper bound**: Use `pair_n_cn_iff` to verify all pairs within
  S_a = {2a,3a,4a,6a,12a}. Count disjoint copies. **High priority, formalizable.**
- **Upper half for pair-free**: Check if (N/2, N] is pair-free. Unlike #302, this is
  NOT automatic — need to check (a+b)|ab for a,b > N/2. Hypothesis: probably NOT
  pair-free since (N/2+1, N) could have (a+b)|ab.
- **Mixed construction**: Odd numbers in [1, N/3] ∪ (N/2, N]. Gives density ~2/3,
  but need to verify cross-term pair-freeness. **Worth investigating.**

---

## Problem #302: Unit Fraction Triples (1/a = 1/b + 1/c)

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Graham 1980 | Original problem statement |
| Cambie (erdosproblems.com) | Lower bound f(N) ≥ (5/8+o(1))N: odds in [1,N/4] ∪ (N/2,N] |
| van Doorn (erdosproblems.com) | Upper bound f(N) ≤ (9/10+o(1))N |
| Brown-Rödl 1991 | Coloring version (#303): any finite coloring has monochromatic 1/a = 1/b + 1/c. **Formalized in Lean.** |

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

### Ideas To Try

- **Van Doorn's 9/10 upper bound**: Similar witness-set technique to the 25/28 bound.
  **Moderate effort.**

---

## Problem #301: Unit Fraction Sum-Free Sets (1/a = Σ 1/bᵢ)

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Erdős-Graham 1980 | Original problem statement |
| van Doorn (erdosproblems.com) | Upper bound f(N) ≤ (25/28+o(1))N (same as #327!) |
| Bloom 2021 ([arXiv:2112.03726](https://arxiv.org/abs/2112.03726)) | Any set of positive upper density contains finite subset with reciprocals summing to 1 |
| Bloom-Mehta (Lean formalization) | [b-mehta.github.io/unit-fractions](https://b-mehta.github.io/unit-fractions/) — formalized Hardy-Littlewood circle method |
| Liu-Sawhney 2024 ([arXiv:2404.07113](https://arxiv.org/abs/2404.07113)) | |A| ≥ (1-1/e+ε)N suffices for subset with reciprocals summing to 1; 1-1/e is sharp |

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

### Ideas To Try

- **Odd numbers are sum-free**: Generalize parity to arbitrary-length sums.
  **Formalizable.**
- **Cambie's 5/8 construction for #301**: Need to check if it's sum-free, not just triple-free.
  The k≥3 case needs careful bounding. **Worth investigating.**

---

## Problem #470: Weird Numbers

### Papers & Techniques

| Paper | Key Contribution |
|-------|-----------------|
| Benkoski-Erdős 1974 | Positive density; pn construction; primitive weird defined |
| Kravitz 1976 | Large PWN construction via Mersenne primes |
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

### Ideas To Try

- **"pn is weird" theorem**: Formalize the Benkoski-Erdős construction. Requires
  divisor decomposition for products with large primes and a subset-sum argument.
  **High priority, the core structural result.**
- **"Multiples of pseudoperfect are pseudoperfect"**: Clean, structural, directly
  useful. Gives contrapositive: weird numbers have no pseudoperfect proper divisors.
  **High priority, quick win.**
- **Pseudoperfect ↔ Egyptian fraction of 1**: n is pseudoperfect iff 1 can be written
  as sum of reciprocals from {n/d : d ∈ properDivisors(n)}. This bridges the WeirdNumbers
  and UnitFractionSets modules. **Novel connection, formalizable.**
- **Deficient/prime/prime-power are not weird**: Trivial (not abundant). Quick wins.
- **836 is weird / primitive weird**: Extend computational verification via `native_decide`.

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

### Pseudoperfect Numbers = Egyptian Fractions of 1

n pseudoperfect ⟺ ∃ S ⊆ properDivisors(n) with Σ s = n
⟺ ∃ S ⊆ {n/d : d | n, d < n} with Σ 1/s = 1.

So weird numbers are *exactly* the abundant n for which 1 has no Egyptian
fraction representation using reciprocals of complementary divisors of n.
This bridges #470 with the Egyptian fraction universe of #301.

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

Based on impact, novelty, and feasibility:

| Priority | Theorem | Problem | Effort | Status |
|----------|---------|---------|--------|--------|
| 1 | Cambie's 5/8 construction | #302 | Medium | **DONE** ✓ |
| 2 | "pn is weird" (Benkoski-Erdős) | #470 | Medium | **STUB** (sorry) |
| 3 | Odd numbers are triple-free | #302 | Easy | **DONE** ✓ |
| 4 | Multiples of pseudoperfect are pseudoperfect | #470 | Easy-Medium | **DONE** ✓ |
| 5 | Upper half is sum-free | #301 | Medium | **DONE** ✓ |
| 6 | Van Doorn's 25/28 upper bound | #327, #301 | Hard | TODO |
| 7 | Pseudoperfect ↔ Egyptian fraction of 1 | #470↔#301 | Medium | TODO |
| 8 | Factor identity → triple classification | #302 | Medium | **DONE** ✓ |

### Bradford 2026 Investigation
Bradford's arXiv:2602.11774 claims full proof of Erdős-Straus. **Verdict: CRITICAL GAP.**
The algebraic identities are correct (3 formalized in Lean), but the covering system
claim is unproven and likely false due to Schinzel's 1956 barrier: polynomial identity
congruences cannot cover quadratic residue classes. The Erdős-Straus conjecture remains OPEN.
