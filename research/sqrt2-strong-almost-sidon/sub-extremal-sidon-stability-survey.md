# Sub-extremal Sidon Stability Survey

**Date:** 2026-05-22. Companion to `op-on-B-attack.md` (Stream 3) and
`rigidity-survey.md`. Targets the open intermediate identified by Stream 3:
a Sidon stability theorem at density `c·√M` with `c < 1` (specifically
`c ≈ 0.82` for the EF-decomposed half `B`).

**The exact question.** Is there a theorem of the form: *"If `B ⊆ [1, M]`
is Sidon with `|B| ≥ c·√M` for `c ∈ (c₀, 1)`, then `B` has [structural
property X]"* — and can X force `e(A) ≤ 1` for near-extremal SAS?

---

## A. Known sub-extremal Sidon stability results

### A.1 Ortega–Prendiville 2023 (arXiv:2110.13447) — extremal-only
Theorem 1.2 (verbatim): `‖1̂_S − (|S|/N)1̂_[N]‖_∞ ≪ N^{1/2}·(||S|/N^{1/2}−1| + N^{−1/6})^{1/2}`.
Corollaries 1.5–1.11 (equidistribution in short intervals, residue classes,
Bohr sets) explicitly require `|S| ≥ N^{1/2}/100` (footnote 4: "any positive
absolute constant"). **However**, all corollaries carry the *same* error
`(|S|/N^{1/2}−1)^{1/2} + N^{−1/6}`, so when `|S|/√N = c < 1` the error is
`(1−c)^{1/2} = Θ(1)` — saturating at the *trivial* bound. The corollaries
are useful only when `c = 1 + o(1)`.
**Density threshold for non-trivial conclusion: `c = 1`.**

### A.2 Conlon–Fox–Sudakov–Zhao 2020 + Prendiville 2020 (arXiv:2005.03484)
**Sub-extremal at every positive constant density `δ > 0`.**
Prendiville Thm 1.1: For `s ≥ 5`, `a₁+···+aₛ=0`, if `S ⊂ [N]` satisfies
`|S| ≥ δ·N^{1/2}` and `E(S) ≤ (2+η)|S|²` (almost-Sidon), then either
`N ≤ exp exp(O(1/δ))`, `η ≥ exp(−exp(O(1/δ)))`, or
`Σ_{a·x=0} ∏ 1_S(xᵢ) ≥ exp(−O(1/δ))·N^{s/2−1}`.
**Structural conclusion**: dense (sub-extremal) Sidon sets contain many
solutions to *every* translation-invariant `s ≥ 5`-variable equation.
**Density threshold: arbitrary positive constant `δ > 0`.**
The bound has *doubly exponential dependence* on `1/δ`.

### A.3 Eberhard–Manners 2023 (arXiv:2107.05744) — conjectural
For density `(1−o(1))·n^{1/2}` in finite abelian groups; conjectures all
such Sidon sets come from projective planes. Proved only for desarguesian
case (cyclic groups). Not effective at `c < 1`, not for integers `[N]`.

### A.4 Schoen–Sisask 2016 (arXiv:1408.2568) — Roth-type, not Sidon
Roth for 4 variables: dense set in `[N]` (constant density) contains many
solutions to `x+y+z=3w`. *Not* a Sidon stability statement; used as a
black box by Prendiville (A.2) to improve the doubly-exponential bound.

### A.5 Bloom–Sisask logarithmic Roth (arXiv:2007.03528) — not Sidon
Three-term AP-free sets have density `O(1/(log N)^{1+c})`. Combined with
the Helfgott–de Roton transference principle for Sidon, this gives the
improved iterated-log bound in A.2 corollary 1.3 (4-variable case).
Still *no positional/Fourier* rigidity for sub-extremal Sidon.

### A.6 Roth-type in K_{s,t}-free sets 2026 (arXiv:2601.18738) — extension
For K_{s,t}-free `A ⊂ [N]` with `|A| = Ω(n^{1−1/s})`, every translation-
invariant linear equation in `≥ 5` variables has nontrivial solutions in
`A`. Generalises CFSZ; same structural-only conclusion as A.2; gives no
positional rigidity, no 4-variable result.

### A.7 White 2022 (arXiv:2210.16437) — wrong asymptotic
L² autoconvolution `g → ∞` limit; uniqueness of continuous extremizer.
Not applicable at SAS regime `g = 1` with one heavy atom.

### A.8 Sayan Dutta 2024 (arXiv:2409.01986) — m-th element
For `|A| = N^{1/2}−L`, `aₘ = m·N^{1/2}+O(N^{7/8}+L^{1/2}N^{3/4})`. *Positional*
but only near-extremal regime (`L ≪ N^{1/2}`, i.e. `c = 1−o(1)`). At our
`c = 0.82` this gives `aₘ = m·N^{1/2}+O(N)` — vacuous.

### A.9 Forey–Fresán–Kowalski 2024 (algebraic geometry) — not integers
Sidon sets in `F_q^n` from algebraic varieties; finite-field-only, not
applicable to integer interval setting.

---

## B. Applicability to SAS rigidity

| Result | Density `c` | Conclusion | Closes our gap? |
|--------|-------------|-----------|-----------------|
| OP (A.1) | only `c=1+o(1)` | Fourier uniformity | No: trivial at `c=0.82` |
| CFSZ/Prendiville (A.2) | any `c>0` | 5-var equations solvable | **Possibly** (see below) |
| EM (A.3) | `c=1−o(1)` | from projective plane | No: conjectural |
| Dutta (A.8) | `c=1−o(1)` | positional spacing | No: error too large |

### Can A.2 (Prendiville's 5-variable theorem) close the SAS gap?

The EF-decomposed `B ⊆ [1, M]` with `c_B ≈ 0.82` is a *genuine* Sidon set
(no almost-Sidon slack). Prendiville's Thm 1.1 with `η = 0` and `δ = 0.82`
gives: `B` contains many solutions to every translation-invariant
`s ≥ 5`-variable equation `a·x = 0` (`a₁+···+aₛ=0`).

**The needed bridge to `e(A) ≤ 1`.** Recall SAS = "at most one bad
value with multiplicity > 2". For the EF construction (`A = B ∪ (n*−B)`),
`e(A)` is governed by 4-tuples `(b₁,b₂,b₃,b₄) ∈ B⁴` with
`b₁+b₂ = b₃+b₄`. By Sidon, all such solutions are trivial — but the
*cross* sums `b + (n*−b') = b" + (n*−b''')` (i.e. `b−b' = b"−b'''`) inside
the reflection structure are governed by `B−B` collisions, again trivial
by Sidon.

So `e(A) ≤ 1` does *not* directly follow from a 5-variable theorem.
The genuine constraint we need is **4-variable** Sidon rigidity, but
Prendiville's method *fails* at 4 variables (Sidon is *defined* as
`a+b=c+d` having only trivial solutions, so the 4-variable equation is
the wrong target).

**The relevant 5-variable equations.** `x₁+x₂+x₃+x₄ = 4x₅` (Roth on
average) or `x₁+x₂+x₃ = x₄+x₅+x₆` (additive triples). Prendiville says
`B` contains solutions to each. But SAS rigidity asks: does `B`'s
*shape* (interval, vs spread out) match the EF template? Not directly
implied.

**Conclusion.** Prendiville's 5-var theorem gives `B` *some* additive
structure (many additive 5-tuples) but **not the positional EF structure**
required for SAS rigidity. The implication "5-var solutions ⇒ B is
near-interval inside `[1, M]`" is itself a strong open inverse problem
(analogue of Freiman 3k-4 for Sidon sets, which is famously hard
because Sidon sets *cannot* have small doubling).

---

## C. Recommendation

**Verdict: nothing in the existing literature directly closes the gap.**
The closest sub-extremal Sidon stability result is
**Prendiville/CFSZ A.2**, which works at our density `c = 0.82` but
delivers *additive* (not *positional*) rigidity, in the wrong number of
variables (`s ≥ 5`, while we need `s = 4`).

**Three plausible paths forward, ranked by feasibility:**

1. **Adapt Prendiville's method to 4-variable approximations.** Sidon
   forbids exact 4-var solutions, but a *quantitative* deficit
   ("4-var solution count compared to a random set of size `|B|`") may
   be controllable. The Helfgott–de Roton transference Prendiville uses
   could in principle bound deviations from the Sidon mean. **Novel
   mathematics but in the same toolkit.** Estimated effort: 1–2 months
   for a quantitative reformulation, longer to push through.

2. **Prove a sub-extremal OP analogue.** Re-derive OP Theorem 1.2 with
   the goal of getting a *nontrivial* Fourier sup-norm bound at
   `c = 0.82`. The OP proof loses at the step `|S|²−N | ≤ |S|·N^{−1/2}`
   (Lemma 2.2), which is tight for `c = 1` and vacuous for `c < 1`. A
   sub-extremal refinement would need to use the *gap* `1 − c²` to gain
   a power of `M`. **Genuinely new Fourier-analytic input needed.**
   Estimated effort: a research paper in its own right.

3. **Bypass Sidon stability entirely via direct multiplicity bookkeeping.**
   Use the EF decomposition (R4) together with the *exact* Sidon
   property of `B` to count `r_A(n*)` directly, avoiding any Fourier
   detour. This is essentially the strategy already underway in
   `r4_ef_decomposition` and its consequences. **Already in progress in
   Lean; no new external results required.**

**Primary recommendation: Path 3.** The Lean formalisation is already
exploiting the exact-Sidon property of `B` (no slack); pushing harder on
the combinatorial multiplicity bookkeeping is more tractable than the
two genuinely-open Fourier problems (Paths 1 and 2).

**Secondary recommendation: Path 1.** If Path 3 stalls, Prendiville's
transference machinery is the closest existing toolkit. A clean
quantitative 4-variable formulation is a *publishable note* in its own
right, independently of the SAS application.

**Honest summary of the literature gap.** No paper in 2020–2026 proves a
"sub-extremal Sidon stability" theorem in the form we need (density
`c < 1` ⇒ positional structure on `B`). The community appears to view
this as genuinely hard, consistent with Eberhard–Manners explicitly
conjecturing (but not proving) such structure even at `c = 1−o(1)`.

---

## References

1. M. Ortega, S. Prendiville, *Extremal Sidon Sets are Fourier Uniform*,
   J. Théor. Nombres Bordeaux **35** (2023). arXiv:2110.13447.
2. S. Prendiville, *Solving equations in dense Sidon sets*, Math. Proc.
   Cambridge Philos. Soc. **173** (2022). arXiv:2005.03484.
3. D. Conlon, J. Fox, B. Sudakov, Y. Zhao, *The regularity method for
   graphs with few 4-cycles*, J. London Math. Soc. **104** (2021).
4. S. Eberhard, F. Manners, *The apparent structure of dense Sidon sets*,
   Electron. J. Combin. **30** (2023). arXiv:2107.05744.
5. T. Schoen, O. Sisask, *Roth's theorem for four variables*, Forum
   Math. Sigma **4** (2016). arXiv:1408.2568.
6. T. F. Bloom, O. Sisask, *Breaking the logarithmic barrier in Roth's
   theorem*, arXiv:2007.03528 (2020).
7. S. Dutta, *The m-th element of a Sidon set*, arXiv:2409.01986 (2024).
8. *Roth-type theorems in K_{s,t}-free sets*, arXiv:2601.18738 (2026).
9. H. Helfgott, A. de Roton, *Improving Roth's theorem in the primes*,
   IMRN (2011). arXiv:0912.1842.
