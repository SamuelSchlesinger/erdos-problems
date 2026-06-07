# Erdős #12 — Literature Review (state of the art, June 2026)

Compiled 2026-06-07 from primary sources (erdosproblems.com/12 + its forum thread,
google-deepmind/formal-conjectures, arXiv, and Tao's "AI contributions" wiki). Every
claim below is sourced in §8. **Bottom line up front:** parts (i) and (ii) of #12 were
*solved* in April 2026 (DeepMind + Tao/Sothanaphan, formalized in Lean). **Part (iii),
the reciprocal-summability question this project targets, is the sole remaining open part,
and the recognized experts (Tao, Bloom) lean toward it being TRUE (the sum converges).**
The proof they expect it to need is an *inverse theorem* — and that is exactly the object
our coprime-rank kernel is a fragment of.

---

## 1. The problem

**Erdős #12** (Erdős–Sárközy, 1970). Call an infinite set `A ⊆ ℕ` an *avoiding set*
(Erdős–Sárközy's "property P") if there are **no** distinct `a,b,c ∈ A` with `a ∣ (b+c)`
and `b,c > a`. Three questions:

- **(i)** Is there such an `A` with `liminf |A∩[1,N]| / N^{1/2} > 0`?  *(√N density)*
- **(ii)** Is there `c>0` such that *every* such `A` has `|A∩[1,N]| < N^{1-c}` infinitely
  often?  *(power-saving upper bound)*
- **(iii)** Is `∑_{n∈A} 1/n < ∞` for every such `A`?  *(reciprocal summability — **our target**)*

This matches our `Erdos12SummabilityQuestion` and DeepMind's `Erdos12.IsGood` exactly
(`IsGood A := A.Infinite ∧ ∀ a b c ∈ A, a ∣ b+c → a<b → a<c → b=c`).

**Finite version = Erdős #13** (different problem): for `A ⊆ [n]` with property P, how large
can `|A|` be? Erdős offered **\$100** for whether `|A| ≤ n/3 + C`. **Solved by Benjamin Bedert
(2023):** `|A| ≤ ⌊n/3⌋ + 1` for large `n` (arXiv 2301.07065). The `n/3` extremal sets live in
a single top band `(n/3, n]`, a trick unavailable to an infinite set — so #13 does **not**
settle #12.

---

## 2. Status table

| Part | Question | Status (June 2026) | By whom |
|------|----------|--------------------|---------|
| (i)  | √N density achievable | **SOLVED — YES** | DeepMind prover agent, 7 Apr 2026 (Lean, formalized) |
| (ii) | power-saving forced | **SOLVED — NO** | DeepMind prover agent, 7 Apr 2026 (Lean, formalized) |
| (iii)| `∑1/n < ∞` always | **OPEN** | — (experts lean: TRUE/converges) |
| #13  | finite `n/3` bound | **SOLVED** `⌊n/3⌋+1` | Bedert, 2023 |

Tao's AI-contributions wiki logs #12 as DeepMind "🟡 Partial result (Lean) (solutions to
first part and second part)" + Tao/Sothanaphan/GPT-5.4 "🟡 Partial result" — "partial"
precisely *because (iii) is untouched*. **No solution, partial or complete, to (iii) exists.**

---

## 3. Constructions (the lower-bound / "set is dense" side)

All known dense avoiding sets share one architecture:

> **`A = ⋃_k B_k`, where (cross-block) each block `B_k` is pinned to a FRESH modulus
> `q_k` via `n ≡ 0 (mod q_k)` and `n ≡ 1 (mod q_i)` for `i<k`; and (within-block) `B_k`
> is a 3-AP-free set squeezed into a short interval `[P_k, 1.1 P_k]`.**

Why this is property-P:
- *Cross-block.* If `a ∈ B_k` and a larger `b ∈ B_j` (`j>k`), then `a ≡ 0 (mod q_k)` but
  `b+c ≡ 1` or `2 (mod q_k)` (both larger elements are `≡ 1 (mod q_k)`, or one is `≡ 0`),
  never `0`. So `a ∤ b+c`. **This needs the `q_k` distinct (no repeats).**
- *Within-block.* The block sits in `[P_k, 1.1P_k]`, so for `a,b,c ∈ B_k`, `b+c ∈ [2P_k, 2.2P_k]`
  and `a ∈ [P_k,1.1P_k]` force the only possible quotient to be `2`: `2a = b+c`. A
  **3-AP-free** (Behrend/Salem–Spencer) interior has no such triple.

The lineage:

1. **Erdős–Sárközy (1970)** — first dense example: integers in `(y_i, 3/2·y_i)` that are
   `≡ 1 (mod (2 y_{i-1})!)`, `y_i` growing fast. Gives `|A∩[1,N]| ≫ √N/log N` along a
   subsequence, and a near-counterexample to (i): for *any* `f(x)→∞`, an avoiding `A` with
   `|A∩[1,N]| > N/f(N)` infinitely often (this is the "density 0 is essentially sharp" result).
2. **`{p² : p ≡ 3 (mod 4) prime}`** — clean textbook example with `liminf |A∩[1,N]|·log N/√N > 0`
   (i.e. `~ √N/log N`). Works because `p ≡ 3 (mod 4) ⇒ −1` is a non-residue, so `p² ∣ q²+r² ⇒
   p∣q, p∣r`. Formalized by AlphaProof.
3. **Elsholtz–Planitzer (2017, arXiv 1609.07935)** — improved the √N-scale constant to
   `|A∩[1,N]| ≫ √N / ((log N)^{1/2}(log log N)²(log log log N)²)`.
4. **DeepMind/AlphaProof Nexus (Apr 2026)** — the breakthrough on (i)/(ii). Two formalized
   constructions, both CRT-blocks + 3-AP-free interiors:
   - **(i):** interior = image of the base-2 → base-3 digit map `f` (`f(n)` read binary, output
     ternary; `f(a)+f(b)=2f(c) ⇒ a=b=c`, so 3-AP-free); blocks pinned mod the i-th odd prime.
     Gives `liminf |A∩[1,N]|/√N ≥ 1/√2`.
   - **(ii):** interior = **Behrend (1946)** sphere set `{v ∈ {1..m}^{V−1} : ‖v‖² = K}` read in
     base `2m+1` (no carrying ⇒ 3-AP-free); blocks pinned mod fresh primes. Gives
     `|A∩[1,N]| ≥ N^{1−ε}` for every `ε>0` and all large `N`, refuting (ii). (The Lean proof
     vaguely credits a construction of **Javier Cilleruelo**.)
5. **Tao / Sothanaphan / Bloom comment-thread refinement (7–8 Apr 2026)** — simplified and
   pushed the density up by encoding the block's congruence conditions in **binary** (≈ `log k`
   primes per block instead of `k`): blocks `B_k = {2^k ≤ n < 3/2·2^k : n ≡ u_i (mod p_i)}` where
   `u_1…u_{O(log k)}` are the **binary digits of `k`**. This reaches
   ```
   |A∩[1,N]| ≥ N / (log N)^{O(log log log N)}   for all large N,
   ```
   and along a sparse subsequence of `N` (those `2^k` with `k` having `O(1)` binary digits)
   even `≥ N / ((log N)(log log N)^{O(1)})`.

---

## 4. Upper bounds (the "set is forced sparse" side — thin!)

- **Erdős–Sárközy (1970):** every avoiding set has **density 0** (`|A∩[1,N]| = o(N)`). This is
  the *only* upper bound known for general avoiding sets, and it is essentially sharp at the
  `o(N)` scale (item 1 above). **There is no known `N/(log N)^c`-type upper bound.**
- **Schoen (2001):** if `A` is **pairwise coprime**, `|A∩[1,N]| ≪ N^{2/3}` infinitely often.
- **Baier (2004):** improved the coprime case to `≪ N^{2/3}/log N` i.o.
- The coprime restriction is essential to Schoen/Baier; the general case is wide open beyond `o(N)`.

---

## 5. The crux of part (iii) — and why it's a knife-edge

**Divergence threshold.** For a set with density profile `A(N) ≈ N/(log N)^α`, partial summation
gives `∑_{n∈A} 1/n ≈ ∫ du/u^α` (`u = log t`), which **diverges iff `α ≤ 1`**. So:

> `∑_{n∈A} 1/n = ∞` requires density essentially `≥ N/(log N)^{1-c}` (Bloom's own remark).

The best construction (§3.5) has `α = O(log log log N) → ∞` — deep in the **convergent** regime,
though it touches `α = 1+o(1)` along a *sparse* subsequence of `N` (not enough to diverge, since
the sum is dominated by the typical `N`). So every known construction **converges**, and they sit
a single `(log log log N)`-in-an-exponent away from the threshold.

**Tao's barrier (9 Apr 2026) — the key expert statement.** Congruence-on-blocks constructions
*cannot* be pushed to divergence:

> "Every block needs a divisibility condition `n ≡ 0 (mod q_k)` … we cannot afford any
> repetitions in the `q_k`: if `q_k = q_{k'}` (`k<k'`) we have no mechanism for preventing an
> element of `B_k` dividing the sum of two elements of `B_{k'}`. So `q_k` has to grow at least as
> fast as `k`, so `∑_k 1/q_k` can only barely diverge. This is already the density limit … but
> then one also has the additional side conditions, and now one can only afford to sparsify the set
> further by about `log k` before we make `∑ 1/n` converge. This doesn't look feasible. So if the
> third question is to have a negative answer, one has to go beyond congruence conditions on
> blocks — but it's really hard to envisage what more efficient construction there could be.
> Perhaps these constructions are already close to optimal and the answer to the third question is
> positive, but this may require some sort of **inverse theorem** that formalizes the intuition that
> congruence constructions are nearly optimal."

**Expert sentiment:** Bloom — "I'd be surprised if one could get `A` dense enough for `∑1/n=∞`";
Sothanaphan — "there could be some fundamental barrier preventing `∑1/n` from diverging." So the
*weak consensus is that (iii) is TRUE (the sum always converges)*, blocked on a missing inverse/
structure theorem.

**This is precisely our project's obstruction, independently rediscovered.** Tao's "`q_k` distinct,
`∑1/q_k` barely diverges, side conditions cost another `log k`" **is** the "small-prime-convergence
/ fresh-prime escape" wall in `research/erdos12/notes.md`, and **is** the content of
`EventuallyFastCoprimeRank` (force coprime rank `t(k) ≳ log k`). The cross-block fresh modulus `q_k`
= the coprime-rank coordinate; the within-block 3-AP-free interior = the residue-packing/sum-free
factor. We reached the genuine research frontier and named the same gap the experts name.

---

## 6. What this means for the Lean project (honest synthesis)

1. **We target the right (only) open part.** `Erdos12SummabilityQuestion` = part (iii), the live
   frontier. Parts (i)/(ii) are solved *and already formalized* by DeepMind — our construction-side
   infrastructure (`BertrandConstruction`, `BlockCoverage`, `GoodCore`, …) is at best re-deriving
   known/formalized results; it is not progress on the open question and should not be mistaken for
   it. The CRT-block + 3-AP-free architecture in §3 is exactly what those files reconstruct.

2. **The positive direction is the right bet** — experts agree the sum likely converges, and the
   negative direction (a divergent example) is, per Tao, "really hard to envisage" and needs a
   genuinely non-congruence idea that no one has. Our `ThresholdStrategy`/`EventuallyFastCoprimeRank`
   positive route is aligned with the expert-favored answer.

3. **The genuine missing object is an inverse theorem** ("avoiding sets are essentially congruence
   constructions, hence subject to the `∑1/q_k` barrier"). Our coprime-rank kernel is a *fragment* of
   this; the "slow unbounded rank" wall (case 4 in `RankGrowthKernel.lean`) is — confirmed by Tao's
   independent analysis — **the open problem itself**, not a gap in our scaffolding. This corroborates
   the earlier honest exhaustion verdict: grinding the kernel further is a moonshot, not engineering.

4. **The bankable, reviewer-grade contributions available now are formalizations of the known
   results**, none of which are in Mathlib and all of which are currently `sorry` in DeepMind's repo:
   - Erdős–Sárközy **density-0** theorem (the foundational upper bound) — cleanest high-value target.
   - **Schoen** `N^{2/3}` and **Baier** `N^{2/3}/log N` (pairwise-coprime upper bounds).
   - **Bedert** `⌊n/3⌋+1` finite bound (#13).
   - The **Elsholtz–Planitzer** and **DeepMind** density constructions (parts i/ii) if we want
     self-contained Lean proofs rather than importing DeepMind's.
   These are *real mathematics made formal*, not scaffolding — the right use of the verification
   safety net while the open core waits on a new idea.

**Recommendation.** Keep the part-(iii) positive kernel as a long-shot track (it is correctly aimed),
but invest the reliable effort in formalizing the density-0 theorem and the Schoen/Baier coprime
bounds — genuine, finishable, Mathlib-worthy results that also build the exact machinery (residue
counting mod `a`, coprime-family/√N packing) any eventual inverse theorem will reuse.

---

## 7. References

- **[ErSa70]** P. Erdős, A. Sárközy, *On the divisibility properties of sequences of integers*,
  Proc. London Math. Soc. (3) 21 (1970), 97–101. — origin; density 0; sharpness; `√N/log N` example.
- **[Sc01]** T. Schoen (2001) — pairwise-coprime avoiding sets: `≪ N^{2/3}` i.o.
- **[Ba04]** S. Baier (2004) — improvement: `≪ N^{2/3}/log N` i.o.
- **[ElPl17]** C. Elsholtz, S. Planitzer, *On Erdős and Sárközy's sequences with Property P*,
  arXiv:1609.07935 (2017) — `√N/((log N)^{1/2}(log log N)²(log log log N)²)` construction.
- **[Be23]** B. Bedert, *On a problem of Erdős and Sárközy about sequences with no term dividing the
  sum of two larger terms*, arXiv:2301.07065 (2023) — finite version (#13): `|A| ≤ ⌊n/3⌋+1`, settling
  Erdős's \$100 conjecture.
- **DeepMind/AlphaProof Nexus (Gemini-based) + Tao/Sothanaphan**, erdosproblems.com/12 forum thread &
  google-deepmind/formal-conjectures, Apr 2026 — formal solutions to (i),(ii); construction refinement
  to `N/(log N)^{O(log log log N)}`; Tao's inverse-theorem barrier for (iii).
- Also cited on the problem page: [Er73], [Er75b], [Er77c], [Er80 p.113], [Er92c], [Er95c], [Er97],
  [Er97b], [Er97e], [Er98] (Erdős's own problem-survey restatements).

## 8. Sources accessed (2026-06-07)

- https://www.erdosproblems.com/12 — statement, status, remarks, reference keys.
- https://www.erdosproblems.com/forum/discuss/12 — the 13-comment thread: April 2026 construction
  refinements (Bloom, Tao, Sothanaphan) and Tao's barrier/inverse-theorem analysis of part (iii);
  DeepMind's informal write-ups of the (i)/(ii) proofs.
- https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/12.lean
  — `Erdos12.IsGood`; (i) `research solved` True, (ii) `research solved` False, (iii) `research open`
  `answer(sorry)`; formalized variants: Erdős–Sárközy density-0, the `f(x)` near-counterexample, the
  `p²` example, Schoen, Baier.
- https://arxiv.org/abs/2301.07065 — Bedert abstract (finite version).
- https://arxiv.org/pdf/1609.07935 — Elsholtz–Planitzer (Property P constructions).
- https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems — confirms #12 (i)/(ii)
  solved 7 Apr 2026, (iii) untouched.
- https://officechai.com/ai/google-deepminds-alphaproof-nexus-agent-has-solved-9-open-erdos-problems-...
  — popular-press context on the AlphaProof Nexus agent (secondary).
