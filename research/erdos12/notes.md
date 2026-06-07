# Erdős #12 (reciprocal-sum) — research log toward closing the open core

**Status: genuinely open** (known open Erdős problem). This log drives an autonomous
research loop: each iteration takes one concrete idea below, works it rigorously,
formalizes any TRUE partial result, and updates the obstruction map. Be Lean-honest;
no fabricated closes.

## The exact crux (proved equivalence)

For avoiding `A`, the dyadic shell mass satisfies `shell_k ≤ 2·(3/4)^{t(k)}` where
`t(k) = ` max pairwise-coprime subset of `A∩[4,2^k)` with product `≤ 2^k`
(= max coprime-LCM rank at scale `k`; `AvoidingSet.dyadicShell_mass_le_two_mul_geometric_of_coprime`).
Hence:

> **A is reciprocal-summable  ⟸  ∑_k (3/4)^{t(k)} < ∞  ⟸  t(k) ≳ c·log k.**

Bounded-rank (`t(k) ≤ R`) is closed by descent (irreducible ⇒ contradiction).
So `t(k) → ∞`. **The entire open problem = force the RATE `t(k) ≳ log k`** for an
avoiding, quotient-irreducible, non-summable `A`. Slow growth (e.g. `t(k)=log log k`)
gives `∑(3/4)^{t(k)} = ∑(log k)^{-c} = ∞`, consistent with non-summability — so rate
is essential, not just `t→∞`.

## Obstruction map (why elementary attacks fail — verified)

- **Fresh-prime escape.** Maximal coprime family `M_k` ⇒ `A∩[4,2^k)` covered by
  `support(M_k)` ≈ first ~`t(k)` primes. To force rank growth one needs a covered
  heavy room to yield a descent; but the support proliferates and each individual
  prime layer `primeLayerBudget A p` is finite (irreducibility), so no FIXED prime
  carries divergent mass. `∑_p primeLayerBudget A p = ∑_a ω(a)/a = ∞` spread over
  infinitely many primes, each finite. Descent needs a per-element (non-uniform)
  divisor — outside the quotient framework.
- **K-unbounded budget.** `exists_manyFresh_largeBudget…` constraints are jointly
  satisfiable for unbounded `K`; the budget → ∞ with `K`, all other constraints are
  lower bounds on `K`. No self-contained contradiction.
- **Scale-uniform room bound (proved, CollectiveDescent.lean):** covered room mass
  `≤ ∑_{p∈support} primeLayerBudget A p` (no `K`). Bounded ⇒ unbounded rank but NOT
  fast rank (witness scale `K(m) ≫ m`). Doesn't close.
- **Long plateaus carry bounded mass.** If `t=R` on `[k₁,k₂]`, that range's mass
  `≤ ∑_{p∈support(R)} budget < ∞`. So plateaus are short on mass; divergence forces
  infinitely many rank increments. But the cover bound `∑_R Φ'(R)` recharges each
  prime every level (loose by an `ω` factor) — no contradiction.

## Idea queue (ranked; one per loop iteration)

1. **Cross-modulus correlation (energy method).** The multi-modulus bound treats
   moduli independently via CRT (`∏(1/2+1/aᵢ)`). Avoidance may forbid residue
   COMBINATIONS across moduli (a `b+c≡0` constraint that couples `mod a₁` and
   `mod a₂`). If the joint density beats the product even slightly per-pair, it could
   compound. Target: a 2-modulus bound `< (1/2+1/a₁)(1/2+1/a₂)`. Likely Fourier/energy
   on `A`'s indicator restricted to residue classes. HIGH payoff, HARD.
2. **Force rank growth from heavy prefix directly.** Heavy prefix + minimality: the
   maximal family at scale `k` must be "large" because otherwise its support primes'
   layers (finite, fixed) can't carry the heavy prefix mass. Make quantitative:
   prefix mass `P(m) ≤ Φ'(t(2^{m+1}))`; if `Φ'` grows slower than `P`, contradiction.
   Need a good upper bound on `Φ'(R)=∑_{p∈support(R)}budget` — the `ω`-overcounting is
   the enemy. MEDIUM.
3. **Uniform quotient-mass bound.** Is `primeQuotientBudget A p` (mass of `quotientSet
   p A`, an avoiding set) uniformly bounded in `p`? If `≤ C`, then `room ≤ ∑_{p∈supp}
   (1/p)·C ≤ C·∑_{p≤p_r}1/p ≈ C·log log r`; compare to heavy prefix. Probably NOT
   uniform, but worth a concrete attempt/counterexample. MEDIUM.
4. **Sub-case A ⊆ primes (or bounded ω).** Pairwise-coprime ⇒ rank = count; the
   self-referential `count ≤ 2^k(3/4)^{count-with-product-≤2^k}`. Check whether
   avoiding forces enough sparsity. Same crux but maybe tractable in this case.
   LOWER, but a clean sub-case close would be real.
5. **Second-moment / additive-energy density bound** (cf. DistinctSubsetSums/Fourier).
   Bound `countUpTo A N` below `N/log N` via the additive structure of `a|b+c`.
   Research-level.

## Attempt log

- **Idea 1 (cross-modulus correlation) — likely DEAD.** The forbidden-triple
  constraints `aᵢ | b+c` are SEPARATE per modulus. For a single `b∈A` above `a₁,a₂`,
  there is no constraint coupling `(b mod a₁, b mod a₂)` from the `aᵢ`-divisibility
  conditions (they involve PAIRS `b,c`, and each `aᵢ` independently). CRT density
  `∏(1/2+1/aᵢ)` is not improved per-pair by the avoiding condition restricted to the
  fixed moduli. The REAL extra constraints come from using LARGER elements as moduli
  (every `a∈A` makes `A∩(a,∞)` sum-free mod `a`) — that's the global avoiding
  condition itself, i.e. idea 2/5, not a 2-modulus correction.
- **Idea 2 (heavy prefix forces rank) — CIRCULAR.** Decompositions all reduce to:
  the maximal coprime family `M`'s own reciprocal sum `∑_{a∈M}1/a` is bounded iff
  `M`'s coprime rank grows (shell bound `2(3/4)^{|M∩[4,2^j)|}`) — same rate question.
  Even "core mass bounded" is the crux. Note primes show coprime ⇏ summable, so the
  bound genuinely needs avoidance + rank-rate. No non-circular reduction found.

**Net:** the open core is self-referential around rank-rate. The one place not fully
exhausted: the GLOBAL all-elements-as-moduli condition (every `a` ⇒ `A∩(a,∞)`
sum-free mod `a`) compounding to force density `o(x/log x)`. This is where any real
progress must come from (ideas 3,4,5). Likely needs analytic input (Fourier/energy),
not elementary residue packing.

## Deep attempt 2 (analytic + density increment) — convergence finding

- **Energy bound, elementary.** Sum-free mod `a` ⟹ occupied residues `≤ a/2+1` ⟹
  (Cauchy-Schwarz) `∑_r n_r² ≥ |A_k|²/(a/2+1)`. No Fourier needed.
- **Density increment.** ⟹ a residue class mod `a` with `A_k`-density `≥ 2δ_k`.
  Iterate over coprime small moduli `a₁..a_t` ⟹ `δ_k ≤ ∏(1/2+1/aᵢ)`. This EQUALS
  the existing multi-modulus count bound (density-increment ≡ direct count; the
  "2^{-t}" and "(3/4)^t" are both `∏(1/2+1/aᵢ)`). No improvement.
- **Single-shell is unconstrained beyond residue packing.** A shell can be a full
  AP `{r+mD : r≢0 mod D}`: `x_b+x_c=2x_a` is impossible for `b,c>a`, and `=3x_a`
  forces `r≡0`. So no INTERNAL triples. ⟹ the summability force is purely
  CROSS-SCALE (a low-shell divisor `a` constraining a high shell `A_k`), which
  single-scale energy cannot capture.
- **Construction evidence the conjecture is TRUE.** Greedy avoiding sets are forced
  lacunary (summable); slow growth ⟹ residue constraints unsatisfiable.

### NEW concrete target (cross-scale coupling)
The open crux `t(k)≳log k` must come from coupling low-shell elements (as moduli)
to high shells SIMULTANEOUSLY across many scales. Concretely:
- (T1) If `δ_j ≳ c` for many low `j` (non-summable lower part), those shells supply
  many candidate moduli; the obstruction is they may share prime factors. Need:
  a dense lower part forces a coprime sub-family growing with the number of dense
  shells. = "coprime rank ≳ #dense-shells". UNRESOLVED — attack next.
- (T2) Telescoping: combine the per-scale increments across a RANGE of shells into a
  single multi-scale density increment, so the modulus budget is `2^{(range)}` not
  `2^k`. If the increment compounds across shells, the effective `t` could grow with
  the range ⟹ rank growth. Needs the increment to not "reset" between shells.
- (T3) Energy across scales: count triples `(a,b,c)` with `a` in a low shell, `b,c`
  in a high shell — this is 0 (avoiding). The cross-scale energy `∑_{a low} (#sum-free
  deficit)` might force aggregate structure. Genuinely analytic, unexplored.

## Deep attempt 3 (descent-FORCED density increment) — genuinely new argument

Iterate the density increment on `A∩[N,2N]` (positive upper density δ), but use
DESCENT at each step:
- **Each increment is FORCED to a nonzero class.** Densest class mod `a` (a∈A) has
  rel. density `≥2δ`. If that class is `≡0 mod a`, then `A∩aℕ` has upper density
  `≥2δ`, i.e. `quotientSet a A` has density `≥2δ`; but it is summable (irreducible)
  ⟹ density 0 ⟹ δ≤0. So **the densest class is always `r≢0 mod a`.** (New: descent
  rules out the 0-class branch.)
- Iterate with moduli `a₁,…,a_t` (small A-elts): rel. density `≥2^t δ`, in AP
  `{≡r mod D}`, `D=lcm(aᵢ)`, with `r≢0 mod each aᵢ`.
- **Termination ⟹ near-full AP, killed by any coprime small elt.** When `2^tδ→1`
  we get a near-full AP `{r+iD}∩[N,2N]` (~N/D elts) ⊆ A. It has NO internal triples
  (`b+c=2a` impossible for `b,c>a`; `b+c=3a` needs `D|r`, false). BUT if ∃ `a'∈A`,
  `a'<N`, `gcd(a',D)=1`, then `{r+iD} mod a'` hits ALL residues ⟹ two elts sum `≡0
  mod a'` ⟹ forbidden triple. So termination forces: every small A-elt shares a
  prime with `D` ⟹ coprime rank = t ⟹ **δ ≤ 2^{-t(N)}** (same bound, now via
  descent+AP-rigidity — a real mechanism, still rank-limited).
- **New structural fact (descent):** `A` is "almost-primitive": `|{x∈A∩[N,2N]: a|x}|
  = o(N/a)` for each `a∈A` (quotient summable). So `∑_{x∈A∩[N,2N]} #{a∈A,a≤Y:a|x} =
  o(N·H_A(Y))` — A-elements are rarely divisible by smaller A-elements.

T3 (cross-scale triple energy) is CIRCULAR: the energy sum `∑_a ∑_r n_r(a)²` equals
`∑_{b,c}#{a|b-c}`, achievable `=|A_{≤Y}|` when A⊆AP (self-similar). Trivial bound.

### NEW angle T4 (cross-scale AP rigidity) — fresh, unexplored
At each scale `N`, non-summable A contains a near-full AP `{r_N + i·D_N}∩[N,2N]`,
`D_N=lcm(rank-moduli)`, all small A-elts sharing primes with `D_N`. Compare the APs
at scales `N, 2N, 4N,…`: do `(r_N,D_N)` and `(r_{2N},D_{2N})` conflict? The small
A-elts (`< N`) must share primes with EVERY `D_M` (M≥N) ⟹ they share primes with
`gcd`-structure across scales. If the `D_M` are "coprime-ish" across scales, the
small elts can't share with all ⟹ contradiction. Concretely: a fixed small `a∈A`
shares a prime with `D_M` for all M ⟹ `a`'s primes recur in every scale's modulus
lcm ⟹ those primes' multiples carry mass at every scale ⟹ candidate for a FIXED
prime descent. ATTACK NEXT.

### T4 resolved (AP coprime-extraction) — converges to rank-rate again
The near-full AP `{r_N+iD_N}` (gcd(r_N,D_N)=1) has CONSECUTIVE elements coprime
(gcd | (i-(i+1))=1), so it contains ~(N/D_N)/log pairwise-coprime A-elements ≈ N.
NEW coprime elements! But each is ≈N, so a product-≤N^c budget fits only ~c of
them ⟹ they boost rank by O(1) per scale-doubling. Same rank-rate. The barrier is
structural: coprime elements with SMALL product (small elements) are what's needed,
and large coprime elements eat the product budget.

## T5 (large sieve) — genuinely DIFFERENT tool; sub-case lever
If `a∈A` is PRIME, then `A` sum-free mod `a` ⟹ `A` avoids ~`(a-1)/2` residues mod
the prime `a`. The arithmetic large sieve over prime moduli `a∈A∩[1,√N]` gives
`|A∩[N,2N]| ≤ (N+N)/L`, `L ≈ ∑_{prime a∈A,≤√N} 1`, i.e.
**δ_N ≲ 1/π_A(√N)** where `π_A` counts PRIME elements of A. This is in terms of the
COUNT of small prime elements, NOT coprime rank — a different quantity. 
- Closes the sub-case "A has ≳ N^ε prime elements below N" (then δ_N→0 fast).
- Caveat: needs PRIME (or squarefree, via a more careful sieve) A-elements; sum-free
  mod composite `a` does NOT give mod-prime avoidance. So the lever is the
  distribution of A's prime/squarefree elements.
- ATTACK: (i) make the squarefree large-sieve version rigorous (sum-free mod
  squarefree `a` ⟹ residue avoidance mod `a`, feed Montgomery's sieve);
  (ii) handle A with FEW prime/squarefree elements — then A is mostly powerful
  numbers / high-prime-power, a sparse set itself (powerful numbers are summable!).
  Sub-case split: A's squarefree part (large sieve) vs powerful part (sparse).
  THIS split might actually close it — powerful numbers ∑1/n converges, and the
  large sieve handles the squarefree-rich case. NEXT.

### T5 also CONVERGES (honest correction)
Pushed it: the large sieve gives `δ_N ≤ 2^{-π_A(√N)}` (π_A = PRIME element count).
But prime elements are coprime, so `π_A(√N) ≤ t(√N) ≤ t(N)` — large sieve ⊆
multi-modulus (prime moduli ⊆ coprime moduli). No improvement. And the squarefree/
powerful split is NOT exhaustive (most integers are neither; non-squarefree has
positive density, only POWERFUL numbers ~√X are sparse), and "few prime elements"
does NOT bound rank (composite coprime elements — prime powers, distinct-prime
products — still give rank). So T5 closes only the sub-case "A has ≳log N prime
elements below √N", which is again a rank-rate condition. CONVERGES.

## FINAL CONVERGENCE ASSESSMENT (after genuine maximal-effort multi-technique attack)
Techniques deployed to conclusion: residue packing; multi-modulus packing; Fourier/
energy (elementary Cauchy-Schwarz form); density increment; DESCENT-FORCED density
increment (forced-nonzero-class via quotient summability); near-full-AP rigidity;
AP coprime-extraction; cross-scale triple energy; arithmetic large sieve; almost-
primitivity (quotient-summable ⟹ o(N/a) multiples). **ALL converge to the same
irreducible core: force coprime-rank-rate `t(k) ≳ log k`.** Single-scale and
cross-scale, combinatorial and analytic — they give `δ_k ≤ ∏(1/2+1/aᵢ) ≈ 2^{-t(k)}`
and cannot force the rate. This convergence is strong evidence the rate is the TRUE
open core, requiring an idea outside the standard density/sieve/energy toolkit
(candidates not attempted: Bohr-set / Bourgain density increment; Furstenberg
correspondence — both heavy, speculative, no clear modulus-budget escape).
GENUINE partial results banked (RankGrowthKernel + CollectiveDescent). Honest call:
autonomous looping now re-derives this wall; further real progress needs either a
new idea (interactive) or accept the open core. Not a failure of ambition — the
maximal standard attack genuinely converges here.

## Frontier: Bohr-set / Bourgain density increment (T6) — the one tool that COULD escape

The AP increment is a rank-1 Bohr-set increment; its modulus budget `∏aᵢ ≤ N` caps
steps at the coprime rank `t(N)`. Bourgain's insight (Roth 3-AP): use a Bohr set
`B(θ₁,…,θ_d; ρ)` of dimension `d`, where each large Fourier coefficient adds a
frequency; the dimension can grow to `~log N` (vs rank) before the Bohr set goes
trivial (`ρ^d N ≥ 1`).

For us: sum-free mod `a` ⟹ `∑_{j≠0}|f̂(j/a)|² ≥ |A|²` (FULL-strength coefficient,
not `δ²`) ⟹ a Bohr-step density increment of a CONSTANT factor (×2-ish), not the
weak `×(1+cδ)` of Roth. If the Bohr dimension reaches `~log N` with ×const
increments, then `δ_N ≤ const^{-log N} = N^{-c}` ⟹ **SUMMABLE**. This is the
genuine candidate close.

**The crux of T6 (= why the problem is plausibly open):**
- If the large coefficient is at `j/a` with `gcd(j,a)=1`, concentration is mod `a`
  (full → rank-1 AP, modulus `a`); combining `d` of these → modulus `∏aᵢ`, rank-
  capped AGAIN. The Bohr advantage needs PARTIAL concentration (radius `ρ` not `1/a`)
  so the Bohr set stays thick across many frequencies.
- Sum-free gives concentration in `≤a/2+1` residues — but that's an ARBITRARY
  residue set, not a Bohr interval `{‖x/a‖<ρ}`. To run the Bohr increment one needs
  the occupied residues to have additive structure (a Bohr/GAP), which sum-free does
  NOT directly provide. Bridging "≤a/2 occupied residues" → "thick Bohr structure"
  is the open analytic gap.
- So T6's success hinges on: does the sum-free Fourier concentration live in a
  bounded-dimension Bohr set (escape) or spread to rank-1 pieces (cap)? Unresolved —
  this is the genuine research frontier and almost certainly where the open
  difficulty sits.

**Honest status of T6:** the right modern tool; plausibly the close; but executing it
rigorously (radius bookkeeping, dimension growth vs Bohr-set triviality, the
sum-free→Bohr-structure bridge) is open-research-level and HIGH-RISK for autonomous
unverified work. Best pursued interactively/carefully, not in a commit-loop.

## CAMPAIGN: autonomous formal-verification attack (user-authorized, reviewed before publish)

Mathlib leverage found:
- `Mathlib/Analysis/Fourier/ZMod.lean` — discrete Fourier transform on ZMod N (energy/Parseval).
- `Mathlib/Combinatorics/Additive/{Energy,PluenneckeRuzsa,Dissociation,ApproximateSubgroup,Convolution,Corner,AP}` — additive combinatorics (Bohr/Bourgain world).
- `Mathlib/NumberTheory/SelbergSieve.lean` — sieve (siftedSum ≤ mainSum + errSum).

**Critical new finding (verification earned its keep): the LARGE-SIEVE route does NOT
close it, and the answer may not even be "summable".** The sieve gives
`δ_N ≲ 1/|A∩[1,√N]|`. Tried to PROVE this ⟹ `∑δ_k<∞`: FALSE. Counterexample to the
implication: set `δ_j = 1/2` on even dyadic blocks `j∈⋃_{m even}[2^m,2^{m+1})`, tiny on
odd blocks. Then the dyadic constraint `δ_k·δ_{⌊k/2⌋} ≤ C·2^{-k/2}` (the sieve coupling)
holds yet `∑δ_j = ∑_{m even}2^{m-1} = ∞`. So a **BURSTY** set evades the sieve. This is
exactly what a non-summable avoiding CONSTRUCTION would exploit ⟹ MUST also seriously
attempt construction (#12 reciprocal-sum direction is genuinely undecided here).

### Campaign phases (Lean-verified; sorry = explicit gap, kept out of the library)
- **P1 (construction probe).** Can a bursty avoiding set be non-summable? Try to build
  dense dyadic blocks `(3·2^{m-1},2^{m+1})` (each internally avoiding, density ~1/4) on a
  sparse scale sequence `m∈M`, with cross-block triples avoided. If YES ⟹ #12 reciprocal
  is FALSE (huge). If the cross-block constraints force `M` lacunary ⟹ summable evidence.
  FORMALIZE the cross-block obstruction precisely.
- **P2 (Selberg-sieve density bound).** Formalize `δ_N ≲ 1/Σ_{prime a∈A,≤√N}(...)` via
  Mathlib SelbergSieve. Real density bound for avoiding sets (also #12 part-1). Verified.
- **P3 (Fourier energy, Mathlib DFT).** Formalize sum-free ⟹ `∑n_r² ≥ |A_k|²/(a/2+1)` and
  the density increment, via `Analytic/Fourier/ZMod`. Substrate for Bohr.
- **P4 (Bohr/Bourgain increment).** Use `Combinatorics/Additive/{Dissociation,Approximate
  Subgroup}` to attempt the dimension-`log N` increment. The make-or-break analytic step.

## Formalized partial results so far (axiom-clean, committed)
RankGrowthKernel.lean (kernel naming) + CollectiveDescent.lean (scale-uniform room
bound, sharp prefix bound, bounded-mass⇒unbounded-rank, smooth-part summability,
divergence-concentration). See memory `erdos12-rank-growth-frontier.md`.
