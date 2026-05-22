# Rigidity Survey for Strong Almost-Sidon Sets

**Date:** 2026-05-22. Companion to `paper.md` and `below-sqrt2.md`.

**Question:** Is there prior work on Freiman-style rigidity / structural extremal
characterizations for Sidon, B_2[g], or quasi-Sidon sets that bears on the
hypothesised SAS rigidity statement

> If `A ⊆ {1,...,N}` is strong almost-Sidon with `|A| ≥ (2/√3 + ε)·√N`, then
> `A` is approximately of Erdős–Freud reflection form `B ∪ (N − B)` for some
> Sidon `B ⊂ [1, N/3]`?

This survey collects the relevant literature and assesses adaptation feasibility.

---

## A. Known rigidity results

### A.1 Ortega–Prendiville 2023: "Extremal Sidon sets are Fourier uniform"

**Reference:** Miquel Ortega, Sean Prendiville,
*Extremal Sidon Sets are Fourier Uniform, with Applications to Partition
Regularity*, J. Théor. Nombres Bordeaux **35** (2023), arXiv:2110.13447.

**Setting.** Genuine Sidon sets `S ⊂ [N]`.

**Statement (Theorem 1.2 / Corollary 1.4).** For any Sidon `S ⊂ [N]`,

  `‖1̂_S − (|S|/N)·1̂_{[N]}‖_∞ ≪ |S| · max(|S|/N^{1/2} − 1, N^{-1/12})`.

When `|S| = N^{1/2}(1 + o(1))`, this says `1̂_S` differs from a renormalised
indicator of `[N]` by `O(|S|·N^{-1/12})` in sup norm — i.e., the extremal
Sidon set is Fourier-pseudorandom.

**Corollaries 1.5–1.11.** Extremal Sidon sets `S` (any Sidon set with
`|S| ≥ N^{1/2}/100`) are equidistributed in:

- short intervals (generalising Erdős–Freud 1991);
- arithmetic progressions (generalising Lindström 1998);
- regular Bohr neighbourhoods.

**Proximity to SAS setting.** Their hypothesis `|S| ≥ N^{1/2}/100` is *very*
mild — it permits sets a positive constant smaller than the extremal density.
In particular, any SAS set of size `≥ (2/√3 + ε)·√N` whose Sidon parts `A_±`
have size `≥ √N/100` would inherit Fourier uniformity on each half.

**Would it close our gap?** Not directly. Ortega–Prendiville give a
*distributional* rigidity (the set looks uniform), not a *positional*
rigidity (the set is `B ∪ (N − B)` for some specific `B`). For the SAS
problem, we need to argue from "Sidon halves are Fourier-uniform" to
"the only way two Sidon halves can have many cross-pairs summing to `n*`
is if they are reflections of each other in a small ambient interval."
This is a non-trivial second step.

### A.2 Eberhard–Manners 2023: "The apparent structure of dense Sidon sets"

**Reference:** Sean Eberhard, Freddie Manners, *The Apparent Structure of
Dense Sidon Sets*, Electron. J. Combin. **30** (2023), arXiv:2107.05744.

**Setting.** Sidon sets in finite abelian groups `G` of order `n`.

**Statement.** *Conjectural*. The five "best known" constructions (Erdős–Turán
parabola, Singer, Bose, Spence, Hughes) all arise as point-line stabilizers
in `PGL_3(K)` for some finite field `K`. Eberhard–Manners *conjecture* that
every dense Sidon set (size `≥ (1 − o(1))·n^{1/2}`) arises in this way from
some finite projective plane. They classify the desarguesian-plane case fully
and prove the conjecture for that case.

**Proximity to SAS setting.** The closest formal analogue of an SAS rigidity
theorem: "near-extremal Sidon sets must come from a specific algebraic
construction." But this is for cyclic-group Sidon sets, not `[1,N]` Sidon
sets. The integer/interval setting is mentioned only as motivation; the
paper notes (with Gowers) that the same heuristic question — what do
"really really dense" Sidon sets in `[N]` look like — appears equally
mysterious.

**Would it close our gap?** Conjecturally yes, by extrapolation: if dense
Sidon sets in `[N]` must come from projective planes, then the only way to
build an SAS set of size near `√2·√N` is to glue two projective-plane Sidon
sets at a common sum. The Erdős–Freud reflection construction is essentially
the unique such glueing up to symmetry. *But the conjecture is unproved
even in the integer setting*, and the proven desarguesian case does not
suffice (one can construct nondesarguesian counterexamples).

### A.3 Cilleruelo 2010 ("Gaps in dense Sidon sets"); Cilleruelo–Ruzsa–Vinuesa 2010

**Reference:** J. Cilleruelo, *Gaps in dense Sidon sets*, Integers (2010);
J. Cilleruelo, I. Z. Ruzsa, C. Vinuesa, *Generalized Sidon sets*,
arXiv:0909.5024.

**Setting.** Sidon sets and `B_2[g]` sets in `[N]`.

**Statement.** Cilleruelo strengthens the Erdős–Freud equidistribution-in-short-intervals
result. For a Sidon `A ⊂ [N]` with `|A| ≥ c·√N`, the count in any subinterval
`I ⊂ [N]` of length `≥ N^{1/2 + α}` is `|A|·|I|/N · (1 + o(1))`. The
CRV paper gives asymptotically sharp estimates for the cardinality of
`B_2[g]` sets, with constants `σ_2(g) → π/(π+2) · √(2g)` as `g → ∞`,
matching the L¹-autoconvolution lower bound.

**Proximity to SAS setting.** Same flavour as Ortega–Prendiville:
distributional, not positional, rigidity. The CRV asymptotics are sharp in
the *large-g* limit and give no useful information at `g → 1⁺` (where
`g = 1` is the SAS limit).

**Would it close our gap?** No. The CRV bounds applied at `g = 2` give the
Pikhurko/Yu-style constant `≈ 1.74`, far above `√2`.

### A.4 White 2022: "An almost-tight L² autoconvolution inequality"

**Reference:** Ethan Patrick White, arXiv:2210.16437.

**Setting.** Continuous L² autoconvolution: `μ_2² = inf_{f ∈ F} ‖f * f‖_2²`
where `F = {f : [-1/2, 1/2] → ℝ : ∫f = 1}`.

**Statement.** `0.574635728 ≤ μ_2² ≤ 0.574643711`, and the infimum is
*attained at a unique minimizer* `f^♦ ∈ F` (Proposition 4).

**Proximity to SAS setting.** The uniqueness result IS a rigidity theorem
for the autoconvolution problem, and the autoconvolution problem is the
continuous limit of the `B_2[g]` upper-bound problem as `g → ∞`. The
uniqueness extremizer `f^♦` is therefore the conjectural "shape" of an
extremal `B_2[g]` set rescaled to `[-1/2, 1/2]`.

**Would it close our gap?** Not directly. (i) White's setting is `g → ∞`,
not `g → 1⁺`; the SAS notion is `g = 1` with a single bad atom of unbounded
multiplicity, which is the opposite asymptotic. (ii) The uniqueness is for
the continuous extremizer; a stability statement ("if `‖f*f‖_2²` is close
to `μ_2²` then `f` is close to `f^♦`") is not proved.

### A.5 Cilleruelo (1996), Lindström (1998), and the classical
equidistribution-in-AP results

These are the precursors to Ortega–Prendiville. Erdős–Freud (1991) proved
equidistribution in short intervals; Lindström (1998) proved equidistribution
in arithmetic progressions; Cilleruelo (2000) improved both. All require
only `|A| ≥ c·√N` for a small constant `c`. None says anything about the
positional structure of `A` — only that the count in any "nice" subset is
`|A|·(subset size)/N · (1 + o(1))`.

### A.6 Riblet 2022: "Sidon sets in a union of intervals"

**Reference:** R. Riblet, arXiv:2202.01296.

**Setting.** Sets `A = I_1 ∪ I_2 ⊂ ℕ` that are unions of two integer intervals.

**Statement.** If `|A| = n` then `A` contains a Sidon subset of size
`≥ 0.876·√n`. (A lower bound on the Sidon-extraction problem.)

**Proximity to SAS setting.** The Erdős–Freud lower bound is exactly a Sidon
subset of a union of two intervals `[1, N/3] ∪ [2N/3, N]`. Riblet says any
such union of two intervals has a Sidon subset of size `0.876·√n` — but
this is in the *other* direction (lower bound on Sidon-extraction, not
upper bound on the SAS containment).

**Would it close our gap?** No. The result goes the wrong direction.

### A.7 Cilleruelo 2014: "An upper bound on the size of Sidon sets"
(Balogh–Füredi–Roy 2021)

**Reference:** Balogh, Füredi, Roy, arXiv:2103.15850.

**Setting.** Genuine Sidon sets `A ⊂ [N]`.

**Statement.** `|A| ≤ √N + 0.998·N^{1/4}` for large `N`.

**Proximity to SAS setting.** This is the current record for the
Erdős–Turán Sidon upper bound problem. It is a pure size bound with no
structural content. Plugging it into our midpoint-split gives a slightly
sharper version of `√2·√N + O(N^{1/4})`, but the leading constant `√2`
is unchanged.

### A.8 Forbidden Sidon subsets of perfect difference sets (Nov 2025)

**Reference:** arXiv:2510.19804 (human-assisted proof, 2025).

**Setting.** Sidon subsets of perfect difference sets (Singer-style).

**Statement.** Establishes "forbidden subset" patterns inside perfect
difference sets, supporting Eberhard–Manners-style rigidity.

**Proximity to SAS setting.** Adjacent in spirit but the technical
machinery is finite-projective-plane combinatorics, not integer interval
analysis.

---

## B. Most promising near-miss

**The closest result in spirit is Ortega–Prendiville 2023 (Theorem 1.2 +
Corollaries 1.5–1.11).** Reasoning:

1. It is *quantitative* (explicit `N^{-1/12}` error), not just asymptotic.
2. It applies under a *very mild* density assumption (`|S| ≥ √N/100`),
   covering the entire range `|A| ≥ c·√N` for any positive `c`.
3. The conclusion ("`A` is Fourier-pseudorandom") is precisely the
   ingredient one needs to combine with the midpoint-split: each Sidon
   half `A_±` is Fourier-uniform, so the cross-pair convolution
   `1_{A_-} * 1_{A_+}` should also be Fourier-controllable.
4. The dependence on `Cilleruelo's sharper Sidon estimate` makes the error
   term improvable to `N^{-1/4}`, more than enough headroom.

The runner-up is **Eberhard–Manners 2023**, but it is (a) conjectural in
the regime we need, (b) for finite abelian groups rather than `[1,N]`.

A distant third is **White 2022's uniqueness Theorem (Proposition 4)** —
it tells us the *continuous* extremizer is unique, but does not give a
quantitative stability statement, and the L²-autoconvolution problem is
the `g → ∞` limit of `B_2[g]`, not `g → 1⁺`.

---

## C. Adaptation feasibility

**Target:** prove SAS rigidity by combining Ortega–Prendiville Fourier
uniformity (per Sidon half) with the midpoint-split structure (Lemma 2.1
in `paper.md`).

**Sketch of the adapted argument.**

1. *Setup.* Let `A ⊆ [N]` be SAS with `|A| ≥ (2/√3 + ε)·√N`, exceptional
   value `n*`. The midpoint split gives Sidon `A_- ⊆ [1, n*/2]` and
   `A_+ ⊆ (n*/2, N]` with `|A_-| + |A_+| = |A|`.

2. *Apply OP per half.* If `|A_-|, |A_+| ≥ √N/100`, then by Ortega–Prendiville
   Theorem 1.2, both `1̂_{A_-}` and `1̂_{A_+}` are
   `O(|A_±| · N^{-1/12})`-close to renormalised indicators in `‖·‖_∞`.

3. *Bipartite Fourier analysis.* The number of cross-pairs `(a, b) ∈ A_- × A_+`
   summing to `n*` is

      `k = |{(a,b) : a + b = n*}| = (1_{A_-} * 1_{A_+})(n*)`.

   By Plancherel, `(1_{A_-} * 1_{A_+})(n*) = ∫ 1̂_{A_-}(α)·1̂_{A_+}(α)·e(-α·n*)dα`.

4. *Rigidity step.* For `k` to be large (i.e., for many cross-pairs to
   sum to the SAS exceptional value), the Fourier integrand must
   concentrate at `α = 0`, forcing both Fourier transforms to be
   essentially supported at zero frequency. By Ortega–Prendiville this
   forces both `A_-` and `A_+` to *be* essentially intervals
   (the indicator function is Fourier-concentrated only if the set is
   structurally an interval). But Sidon sets cannot fill an interval —
   they have density `√(L)/L = L^{-1/2}` at best. So either
   `|A_-|, |A_+|` are small (giving a sharper bound) or they fill a
   small interval (giving the EF reflection structure).

5. *Extract rigidity.* If `|A_-| ≈ |A_+| ≈ √(N/2)·(1 − o(1))` and both
   are Fourier-uniform, then the cross-pair count `k` cannot exceed
   `O(|A_-|·|A_+|/N) = O(1)`. With `k = O(1)` the SAS hypothesis is
   *vacuously* preserved — the bound `√2·√N` becomes the bound for
   *pure* Sidon (Case 1 in paper.md), not the bound for SAS.
   To exploit SAS optimally, `k` must be `Θ(√N)`. This forces
   *concentration* of the Fourier mass, contradicting Fourier
   uniformity — hence `A_-` and `A_+` cannot simultaneously be
   near-extremal Sidon and EF-concentrated.

**Where this gets hard.**

- *Step 3 → 4 is the genuine new mathematics.* The standard "Fourier
  concentration ⇒ structure" implication is in the direction of
  *additive structure* (Freiman 3k-4 type), but Sidon sets cannot have
  additive structure in the usual sense — they are anti-structural. So
  the implication "Fourier-concentrated Sidon ⇒ contained in a short
  interval" requires a *different* argument from the standard Freiman
  toolkit. This might invoke Bohr-set machinery from Sanders 2012 or
  Schoen–Sisask 2018, but these tools are usually for sets with
  *small doubling*, not Sidon.

- *Quantitative loss.* OP's error `N^{-1/12}` (or improved `N^{-1/4}`)
  is fine for asymptotic rigidity, but to extract a quantitative
  `c < √2` constant from the rigidity, we need the error to be smaller
  than the gap between `√2` and the target. The gap to `2/√3` is about
  `0.26`, so an error of `N^{-1/12}` is more than enough as long as the
  rigidity conversion doesn't lose powers of `N`.

- *The single-atom corner.* The SAS hypothesis "one bad value" is
  qualitatively different from "Sidon" (no bad values) and from
  "B_2[g] with g ≥ 2" (many bad values). The OP method is designed for
  pure Sidon and might not adapt cleanly to the single-bad-atom regime
  without losing the sharp constants.

**Estimated effort.** Months, not weeks. The combination of
Ortega–Prendiville's Fourier analysis with the bipartite structure of
the midpoint split is conceptually clean but technically demanding.
A serious attempt would require:

1. (1–2 weeks) Verify the OP argument adapts cleanly to give Fourier
   uniformity *per midpoint half*.
2. (2–4 weeks) Develop the bipartite-Plancherel step (3 above) to extract
   the cross-pair count `k` in terms of Fourier data.
3. (1–2 months) Prove the "Fourier-concentrated Sidon ⇒ structured" step
   (Step 4). This is the genuine open problem.
4. (Weeks) Assemble the rigidity into an explicit upper-bound constant
   `c < √2`.

If Step 3 reaches `c = 2/√3` cleanly, the problem is solved. More likely
outcome: `c ∈ [1.30, 1.40]` (consistent with the heuristic in `below-sqrt2.md`),
because the Fourier-rigidity step will lose some quantitative power.

---

## D. Recommendations

**Verdict: This is "new rigidity theorem inspired by an existing one"
(medium-case scenario from the four-option spectrum), not direct adaptation.**

Ortega–Prendiville gives a *distributional* rigidity (Fourier uniformity)
for genuine Sidon sets. The SAS rigidity we conjecture is *positional*
(forces the EF reflection shape). Bridging these is genuine new
mathematics. Eberhard–Manners' positional conjecture is in spirit closest
but remains conjectural even for the cyclic-group case it directly
addresses. White's uniqueness is in the wrong asymptotic regime (`g → ∞`).

**Recommended next step.** Pursue the **Ortega–Prendiville + midpoint
hybrid (Section C above)**. Specifically:

1. *First week.* Re-derive Ortega–Prendiville Theorem 1.2 with the
   single-atom modification: instead of pure Sidon, allow one value with
   multiplicity `k` and track how the Fourier-uniformity error degrades.
   This will tell us whether the OP method survives the SAS hypothesis at
   all.

2. *Following weeks.* If (1) succeeds, attempt the bipartite-Plancherel
   computation for the cross-pair count `k`. Most likely outcome: a
   quantitative inequality of the form

      `k ≤ |A_-| · |A_+| · N^{-1} + (error)`,

   which combined with `|A| = |A_-| + |A_+|` gives a sub-`√2` constant
   *provided* the error is `o(√N)`. This is the explicit calculation
   that will tell us whether `c = 2/√3` is reachable or whether we land
   in the heuristic `[1.30, 1.40]` range.

3. *Backup.* In parallel, ask Sean Prendiville (paper author) or Freddie
   Manners by email whether they have any unpublished thoughts on SAS;
   both have explicitly cited the OP problem in lecture series and may
   have informal notes. The Erdős Problems forum thread #864 has been
   followed by `DesmondWeisenberg`, who may also have informal ideas.

**Realistic best case:** publishable note proving `c ≤ (2/√3 + δ)` for some
explicit `δ > 0` (or `c ≤ √2 − δ` if Step 3 of Section C is incomplete).
A full resolution to `c = 2/√3` is a substantial research project on the
order of a strong paper, and would close Erdős Problem #864 unconditionally.

**Realistic worst case:** The adaptation gets stuck at Step 3 in Section
C (Fourier-concentrated Sidon ⇒ structured), and the survey conclusion
is that this is the hard step. That is still useful: it identifies a
clean obstacle and a concrete intermediate conjecture.

---

## References

1. M. Ortega, S. Prendiville, *Extremal Sidon Sets are Fourier Uniform,
   with Applications to Partition Regularity*, J. Théor. Nombres Bordeaux
   **35** (2023). arXiv:2110.13447.
2. S. Eberhard, F. Manners, *The Apparent Structure of Dense Sidon Sets*,
   Electron. J. Combin. **30** (2023). arXiv:2107.05744.
3. J. Cilleruelo, *Gaps in dense Sidon sets*, Integers, 2010.
   https://math.colgate.edu/~integers/a11/a11.pdf
4. J. Cilleruelo, I. Z. Ruzsa, C. Vinuesa, *Generalized Sidon sets*,
   arXiv:0909.5024.
5. E. P. White, *An almost-tight L² autoconvolution inequality*,
   arXiv:2210.16437.
6. R. Riblet, *Sidon sets in a union of intervals*, arXiv:2202.01296.
7. J. Balogh, Z. Füredi, S. Roy, *An upper bound on the size of Sidon
   sets*, arXiv:2103.15850.
8. C. Vinuesa, *Generalized Sidon Sets* (Ph.D. thesis under J. Cilleruelo,
   Univ. Autónoma de Madrid). https://www.icmat.es/Thesis/CVinuesa.pdf
9. P. Erdős, R. Freud, *On sums of a Sidon-sequence*, J. Number Theory
   **38** (1991), 196–205.
10. B. Lindström, *Determination of two vectors from the sum*, J. Combin.
    Theory **6** (1969); *On B_2-sequences of vectors*, J. Number Theory
    (1998).
11. O. Pikhurko, *Dense edge-magic graphs and thin additive bases*,
    arXiv:math/0309029.
