# Game-Theoretic / Adversarial Attack on SAS Bipartite Rigidity

**Research note, 2026-05-22.** Eighteenth attack in the `below-√2` program
for strong almost-Sidon (SAS) sets. After 17 prior aggregate / Fourier /
L^p / structural attempts (all negative for closing the gap to `2/√3`),
this note explores a fundamentally different paradigm: a **two-player
extremal game** whose value is exactly the SAS extremizer size `f(N)`.

## 1. Setup: the SAS-Builder-Saboteur game

We define a perfect-information online game `G(N)`:

- **State:** a finite set `A ⊆ [1, N]`, and a "current exception"
  `n* ∈ [2, 2N] ∪ {⊥}` recording the unique value (if any) with at
  least two unordered representations as a sum from `A`.
- **Initial state:** `A₀ := ∅`, `n*₀ := ⊥`.
- **Builder's move at step `t`:** choose `a_t ∈ [1, N] \ A_{t-1}` (the
  builder may choose to **pass**, ending the game).
- **Validity check (Saboteur):** let `A_t := A_{t-1} ∪ {a_t}`. Saboteur
  declares `A_t` *invalid* if there exists a sum value `s ∈ [2, 2N]`
  with `s ≠ n*_{t-1}` and `r_{A_t}(s) ≥ 2`. Otherwise update:
  `n*_t := n*_{t-1}` if `n*_{t-1} ≠ ⊥`; else `n*_t := s` if a new
  doubled value `s` appeared; else `n*_t := ⊥`.
- **Terminal condition:** game ends when (a) Builder passes, or
  (b) Builder is *stuck*: every remaining element of `[1, N] \ A_{t-1}`
  would make `A_t` invalid.
- **Payoff:** `|A_T|` (the final SAS set size).

**Claim (well-defined value):** the optimal Builder strategy achieves
exactly `f(N)`, the SAS extremizer size.

**Proof sketch.** Any SAS set `A` with `|A| = f(N)` can be reached by
the Builder by inserting elements one at a time (the intermediate
prefixes are SAS because SAS is monotone under removal: removing an
element never creates a new doubled value). Conversely any terminal
Builder configuration is SAS. So the game value equals `max{|A| : A
SAS, A ⊆ [1, N]} = f(N)`.

This is a *single-player* game in disguise (Saboteur is deterministic
given Builder's choices). The game-theoretic framing only becomes
non-trivial under one of:

  (G1) **randomized Saboteur** (Yao's principle),
  (G2) **online / no-recourse Builder** (competitive ratio),
  (G3) **strategy-stealing / symmetry exploitation**.

We investigate each below.

## 2. Strategy-stealing and symmetry

**Symmetry of the game.** The game has a `ℤ/2` reflection symmetry:
`a ↦ N + 1 − a`. If Builder strategy `σ` achieves a SAS set `A`, then
`(N + 1) − A := {N + 1 − a : a ∈ A}` is also SAS (sum-reflection
preserves multiplicities), and Builder strategy `σ` reflected
achieves it. So the *set* of achievable SAS configurations is closed
under reflection.

**Strategy stealing.** Classical strategy stealing (Hales-Jewett /
Hex-style) requires:
- The game has no benefit from passing (extra moves never hurt).
- A symmetry that lets the second player "steal" the first player's
  winning strategy.

Here the game is solitary; there's no "second player" to steal from.
The reflection symmetry instead gives only:

  *Lemma (reflection-closure):* if Builder achieves `A` against
  optimal play, Builder also achieves the reflected set
  `(N + 1) − A`.

**Consequence (mild):** WLOG we may assume the optimal `A` is
reflection-symmetric *as a set* (i.e., `A = (N + 1) − A`). This forces
`n* = N + 1` whenever `|A|` is achieved by a symmetric extremizer.
But this is already the **Erdős–Freud structure**, so we have not
gained over the existing rigidity story.

**Verdict on (G3): symmetry / strategy stealing recovers only what
the explicit EF construction already gives. No new bound.**

## 3. Yao's principle: randomized Saboteur

Yao's principle: `min_σ max_x payoff(σ, x) = max_p min_σ E_{x ∼ p}
[payoff(σ, x)]`. For our game, the natural translation is:

- *Pure version:* `f(N) = max_{Builder strategy σ}` (payoff against
  the empty Saboteur).
- *Randomized lower bound (useless direction):* `f(N) ≥ E[|A|]` for
  any random SAS construction. The EF construction gives
  `E[|A|] = (2/√3 + o(1)) · √N` deterministically, already known.
- *Randomized upper bound (the interesting direction):* requires a
  random "input distribution" against which any Builder strategy is
  bad.

What would a randomized Saboteur look like? The Saboteur has no
choices (its responses are determined by Builder's moves). The
randomization must enter at the **rule level**: a random *modification*
of the SAS validity check.

**Candidate randomization:** Saboteur picks a uniformly random offset
`τ ∈ [1, N]` at the start, and declares `A_t` invalid if it fails SAS
**after the cyclic shift `a ↦ a + τ (mod N)`**. By cyclic
translation-invariance of SAS validity in `ℤ/N`, this is no constraint
on Builder if we work in `ℤ/N`. In `[1, N]` (non-cyclic), the boundary
breaks translation invariance, and a random `τ` gives an *averaged*
constraint.

**Computation (sketch):** in `ℤ/N` with random `τ`, the cyclic SAS
problem has extremizer size at most `√N + O(N^{1/4})` (every cyclic
SAS set is Sidon-up-to-one, and cyclic Sidon sets have size
`√N + O(1)` by Lindström-type cyclic bounds).

This gives `E_τ[f_{cyclic shift}(N)] ≤ √N + 1`, but **`f(N)` in `[1, N]`
is NOT directly bounded by this**: the boundary lets Builder use the
asymmetry `a + b ≤ 2N` differently than `a + b ≡ 0 (mod N)`. So
Yao's principle, in this form, does not transfer.

**Verdict on (G2/Yao):** the natural randomization either coincides
with the cyclic problem (which has a strictly tighter bound `√N` —
not informative about `[1, N]`) or doesn't randomize anything (since
Saboteur is deterministic). **No new bound.**

## 4. Online / competitive ratio analysis

Reframe Builder as an *online* algorithm that must commit to
elements without foresight. The optimal *offline* configuration has
`f(N)` elements; the *online* (greedy) configuration has some smaller
size `g(N) ≤ f(N)`.

**Empirical greedy benchmarks.** Numerical experiments (cf.
`random-restart-report.md`) confirm:
- Pure greedy (Builder inserts smallest valid element) at `N = 1000`
  achieves `|A| = 32` against offline optimum `≥ 42`. Competitive
  ratio `≈ 0.76`.
- Randomized greedy (Builder inserts uniformly random valid element)
  at `N = 1000` achieves median `|A| ≈ 30`.

The competitive ratio `g(N)/f(N) ∈ [0.7, 0.8]` is **stable** across
the empirical range. This tells us:

> Even with no foresight, Builder reaches a constant fraction of
> the optimal SAS size.

This is interesting but tells us nothing new about `f(N)` itself — it
only relates `g(N)` to `f(N)`.

**Could an upper bound on `g(N)` give an upper bound on `f(N)`?**
**No.** The online competitive ratio bounds `g(N)/f(N)`, not `f(N)`
absolutely. To improve `f(N)`'s upper bound, we'd need a *direct*
argument that *no* offline configuration exceeds `(c) · √N` for some
`c < √2`.

**Verdict on online analysis:** competitive-ratio statements about
the game are intrinsically *relative* (`g/f`), not absolute. They
**cannot** bound `f(N)` from above. **No new bound.**

## 5. Random potential function / Khintchine-style attempt

The most concrete game-theoretic idea: define a real-valued potential
`Φ : 2^{[1,N]} → ℝ` such that:

- (P1) `Φ(∅) = 0`.
- (P2) For any valid SAS `A`, `Φ(A) ≥ |A|`.
- (P3) For any almost-Sidon `A`, `Φ(A) ≤ c · √N` for the desired `c`.

If such `Φ` exists, then `|A| ≤ Φ(A) ≤ c · √N`, closing the bound.

**Candidate Φ.** The natural choice from Fourier analysis:
```
Φ(A) := (1/N) · ∫_{ℤ/N} |1_A^(t)|² · w(t) dt
```
for some weight `w(t)`. By Parseval, `(1/N) · ∫ |1_A^(t)|² dt = |A|`,
which gives (P2) when `w ≡ 1`. (P3) requires bounding the weighted
Plancherel integral by `c · √N` using the SAS structure.

But this is **exactly the Pikhurko-style Fourier attack**, which is
attempt A in our prior work (`pikhurko-adaptation.md`), and which
*failed* with the constant `K = 0.93` instead of the required
`K < 1/2`. The "game" framing of `Φ` adds no leverage: the bound
`Φ(A) ≤ c · √N` is the same Fourier inequality regardless of whether
we view `Φ` as a potential in a game or as a Plancherel integral
directly.

**Lovász Local Lemma analogy.** A genuine LLL-style potential would
argue: a *random* SAS configuration has expected size `< c · √N`, so
some deterministic configuration must also be `< c · √N`. But this
argument runs *in the wrong direction*: we want an *upper* bound on
the maximum, but LLL gives existence of large objects (lower bound),
not impossibility (upper bound).

**Verdict on potential functions:** the natural potentials all
reduce to prior Fourier attacks. The "game" framing does not add
new analytic content. **No new bound.**

## 6. Honest verdict

The game-theoretic framing of SAS provides:

1. **A clean restatement** of `f(N)` as the value of a two-player
   game. Aesthetic, not technically useful.
2. **Symmetry-closure** (Sec. 2): recovers the EF structure but no
   new constraint.
3. **Online competitive ratios** (Sec. 4): only relate `g(N)` to
   `f(N)`, do not bound `f(N)` absolutely.
4. **Yao / randomized adversary** (Sec. 3): cyclic relaxation gives
   a tighter bound but doesn't transfer to the original problem.
5. **Random potential functions** (Sec. 5): collapse to prior
   Fourier attacks; no new bound.

The game perspective fails for the same meta-reason identified in
the 17 prior attacks: the SAS constraint is **simultaneously L^∞
single-atom-strong AND positionally sensitive**. A game-theoretic
invariant (game value, competitive ratio, potential function) is
either:
- a *global aggregate* (game value = `f(N)`, trivially tautological),
- a *competitive ratio* (relative to `f(N)`, not absolute),
- or a *Fourier-equivalent potential* (collapses to known L²/L^p
  attacks).

**There is no genuine "game-theoretic invariant" between these three
that captures the SAS bipartite rigidity.** The hope that "game
structure" would expose a new combinatorial handle is, on inspection,
the same hope that motivated the eleven prior attacks — and runs into
the same obstruction.

## 7. One residual idea worth noting

The game perspective does illuminate one *empirical* fact:

> **Observation.** In the SAS game, after the first ~⌊√N/√3⌋ Builder
> moves selected as in the EF construction, *every* remaining valid
> move lies in the EF support `B ∪ (N − B)`. The game becomes
> "trapped" near the EF configuration.

This is a *trapping* / *contraction* phenomenon: the game's reachable
set after a small prefix is dramatically constrained. If one could
prove this rigorously — that *any* near-extremal prefix forces the
remainder of the game into EF-like positions — that would be a
**dynamical version of the rigidity conjecture** (cf.
`below-sqrt2.md` Sec. "Refined rigidity conjecture").

This is essentially the rigidity conjecture restated as an online
algorithm: "any near-optimal Builder strategy is *forced* into the
EF construction." Proving it is no easier than proving the static
rigidity directly, but it's a possibly suggestive reformulation
worth recording.

## 8. Tracking

| Date | Event |
|------|-------|
| 2026-05-22 | Game formulation drafted; symmetry / Yao / online / potential / strategy-stealing all checked. |
| 2026-05-22 | Verdict: **negative**. Game-theoretic invariants either tautological, relative, or collapse to prior Fourier attacks. |
| 2026-05-22 | Residual observation: empirical "trapping" of near-EF prefixes restates the rigidity conjecture in dynamical form — no easier to prove, but suggestive. |

## 9. Recommendation

**Do not pursue game-theoretic reformulations for the `2/√3` gap.**
The three handles a game perspective offers (Yao, competitive ratio,
strategy stealing) provably do not give absolute bounds on `f(N)`.
A random-potential argument collapses to prior Fourier attacks.

The honest path forward remains the Freiman-style structural rigidity
conjecture identified at the end of `below-sqrt2.md` — a multi-month
research project, not amenable to elementary methods.
