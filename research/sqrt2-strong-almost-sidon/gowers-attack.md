# Gowers U² Inverse Theorem Attack on SAS Bipartite Rigidity

**Worked analysis, 2026-05-22.** Companion to `below-sqrt2.md`,
`op-application.md`, and `density-profile-attack.md`. Investigates whether
Gowers U² inverse theorems (Gowers 2001, Green–Tao–Ziegler, Sanders 2008/2012,
Manners 2018) can supply the bipartite rigidity needed to push the SAS
upper bound below `√2 · √N`.

## 0. Executive verdict

**Verdict: NO.** The Gowers / Sanders / Manners U² inverse-theorem programme is
structurally inapplicable to SAS. The Gowers U² norm of `1_A` for SAS sets
is **at the trivial Sidon minimum**, not large. Inverse theorems require
*large* U² to extract structure; SAS sits at the wrong end of the dichotomy.

$$
\boxed{\;c \;\le\; \sqrt 2 + o(1)\;\text{ (Gowers U² inverse theorems give no improvement).}\;}
$$

This is the *seventh* attack-line converging on the same meta-obstruction:
the relevant technique is either translation-invariant, `L^p`-averaged, or
requires a regime SAS does not occupy.

## 1. U² norm computation for SAS

For `f : ℤ_N → ℂ`,
`‖f‖_{U²}⁴ = E_{x,h₁,h₂} f(x)\overline{f(x+h₁)}\overline{f(x+h₂)}f(x+h₁+h₂)`.
Equivalently `‖f‖_{U²}⁴ = E(f)/N³` with additive energy
`E(A) = #{(a,b,c,d) ∈ A⁴ : a + b = c + d}` for `f = 1_A`.

**Sidon case.** Sidon means `E(A) = 2|A|² - |A|` (only trivial quadruples).
With `|A| ≍ √N` and `α := |A|/N ≍ N^{-1/2}`:
$$
\|1_A\|_{U^2}^4 \;=\; \frac{2|A|^2 - |A|}{N^3} \;\asymp\; \frac{2}{N^2} \;=\; 2 α^4 N^0.
$$
The trivial lower bound is `α⁴ = N^{-2}` — matched up to a factor of 2.
Sidon sets are **extremally U²-uniform**.

**SAS case.** A bad atom at `n*` with multiplicity `k` adds at most `k²`
quadruples to `E(A)`. So
$$
\|1_A\|_{U^2}^4 \;\le\; \frac{2|A|^2 + k^2}{N^3}.
$$
For `k ≤ |A|/2 ≍ √N`, this is `≍ 9α⁴/4` — **a constant-factor bump above
the Sidon floor**, still in the U²-uniform regime.

## 2. Why inverse theorems need *large* U²

### 2.1 Gowers U² inverse (qualitative)

> If `f : ℤ_N → ℂ`, `‖f‖_∞ ≤ 1`, and `‖f‖_{U²} ≥ δ`, then there exists
> `ξ ∈ ℤ_N` with `|f̂(ξ)| ≥ δ² N`.

The hypothesis is `large U²`. For SAS, `‖1_A‖_{U²} ≍ α \cdot 2^{1/4}
\cdot N^0/N^{1/2}`, i.e., U² **decays as `α/√{anything}`**. Calling the U²
bound `δ`, we have `δ ≍ N^{-1/2}`, well below any threshold that gives
meaningful Fourier concentration: the inverse statement yields `ξ` with
`|f̂(ξ)| ≥ N^{-1} \cdot N = O(1)`, **vacuous**.

### 2.2 Sanders (arXiv:1011.0107) — quantitative Bogolyubov–Ruzsa

> If `A ⊆ ℤ_N` has additive energy `E(A) ≥ K^{-1} α³ N³`, then `A − A`
> contains a Bohr set of rank `O(\log^c K)` and bandwidth `\exp(-\log^c K)`.

For SAS, `K := α³ N³ / E(A) = α³ N / (2α² + …) ≍ α N = |A| ≍ √N`. The
"doubling constant" diverges as `√N`. Sanders requires `K ≤ \text{polylog}(N)`
to give a nontrivial Bohr-set conclusion. **Bound is vacuous in SAS regime.**

### 2.3 Manners 2018 (arXiv:1811.00718)

Manners' polynomial-quantitative inverse for `U^s` (`s ≥ 2`) likewise needs
`‖f‖_{U^s} ≥ δ` with `δ` polylog in `1/N`. SAS sits at `δ = N^{-1/2}`, far
below threshold. **Vacuous.**

## 3. Structural diagnosis: SAS is the *wrong* regime

Gowers / Sanders / Manners answer:
> *Given that `f` has substantial additive structure (large U²), what does
> `f` look like?*

The conclusion is a positive structure (linear phase, polynomial phase,
nilsequence) that *explains* the U² mass. For SAS:

- `‖1_A‖_{U²}⁴ ≍ α²/N` is the Sidon **floor**.
- The bad atom adds at most `O(1)` factor — does not push U² past any
  "structure threshold".
- Even hypothetically applying the inverse statement would yield "`A`
  correlates with a linear phase `e(ξx/N)`", but Sidon sets *cannot* be
  approximate APs (an AP of length `√N` has `Ω(N)` collisions), so the
  output structure is either vacuous or self-contradictory.

The hoped-for use case — "the bad atom contributes a specific phase
`e(ξ n*/N)`, extract it" — does **not** trigger an inverse theorem because
the Sidon background washes the phase out: `k² ≤ |A_-| \cdot |A_+|` by
Cauchy–Schwarz (= the trivial pair-size bound), giving no new structural
input beyond elementary counting.

## 4. Comparison with OP-distributional

`op-application.md` analysed Ortega–Prendiville `|1̂_{A_±}(ξ)| ≤ N^{11/12}`
(`ξ ≠ 0`). It closes Gaps (G1) and (G2) of `density-profile-attack.md` but
does **not** close (G3): the slack `1/4` at `α = β = 1/2` is *geometric*
(linear function `d_- + d_× = v/N` saturating only at `n*`), not statistical.

Gowers U² is *strictly weaker* than OP-distributional as a hypothesis on
`1_A`. The strict inclusion of structural information yielded:

| Hypothesis | Strength | SAS regime | Effect |
|---|---|---|---|
| Sidon (`E = 2|A|² - |A|`) | gives `‖1_A‖_{U²} ≍ N^{-1/2}` | tight | `√2` baseline |
| OP-distributional | strictly stronger than Sidon | true at extremality | no improvement (`1/4` geometric slack) |
| Sanders large-energy structure | needs `K ≤ \text{polylog} N` | violated (`K = √N`) | vacuous |
| Manners `U^s` inverse, `s ≥ 2` | needs `‖f‖_{U^s} ≥ \text{polylog}^{-1}` | violated | vacuous |

**Anything Gowers tools say about SAS is already weaker than OP, and OP
does not break `√2`.**

## 5. The actionable Plancherel inequality (and its trivial content)

The one quantitative statement reachable via U² / Plancherel for SAS is:
$$
k \;=\; \frac{1}{N}\sum_\xi 1̂_{A_-}(\xi)\,\overline{1̂_{A_+}(\xi)}\, e(-ξ n^*/N).
$$
Cauchy–Schwarz:
$$
\boxed{\;k^2 \;\le\; \frac{1}{N^2}\sum_\xi |1̂_{A_-}|^2 \sum_\xi |1̂_{A_+}|^2 \;=\; |A_-|\cdot|A_+| \;\le\; \tfrac{1}{2}N.\;}
$$
This is the **same** bound (`k ≤ √{LU}`) already noted in
`below-sqrt2.md` §"Elementary counting attempts" as vacuous. Gowers/Plancherel
recovers it without improvement.

A naive Plancherel attempt to exploit OP `|1̂(ξ)| ≤ N^{11/12}` to bound
constructive alignment at `n*` (Appendix A.2 of `op-application.md`) shows
that `k = Ω(√N)` requires `≍ N^{2/3}` non-zero frequencies contributing
constructively — possible but not in itself contradictory.

## 6. Conclusion and recommendation

The Gowers U² inverse-theorem framework cannot help with SAS bipartite
rigidity because:

1. **Wrong regime.** Inverse theorems require *large* U²; SAS sets have
   minimal U² (`≍ Sidon floor`), so no inverse statement triggers.
2. **Wrong output.** Even hypothetically, the structural conclusion is a
   linear phase / Bohr correlate, both *translation-invariant*. Bipartite
   SAS rigidity is *positional* (the EF support interval `[1, N/3]`
   matters).
3. **Wrong granularity.** The bad-atom strength `k² ≍ N` adds a constant
   factor to U²; no asymptotic threshold is crossed.

This makes Gowers attacks the **seventh independent attack-line** to
converge on the meta-obstruction documented in
`below-sqrt2.md`: every standard additive-combinatorics tool is either
translation-invariant, `L^p`-averaged, or requires a regime (large U²,
small doubling) that SAS does not occupy.

**Recommendation:** de-emphasize Gowers-style tools for the
$(2/\sqrt 3, \sqrt 2)$ gap. The genuine route remains the Freiman-style
positional rigidity conjecture stated in `below-sqrt2.md`, which lacks
any known elementary proof.

## References

1. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA **11** (2001), 465–588.
2. T. Sanders, *On the Bogolyubov–Ruzsa lemma*, Anal. PDE **5** (2012),
   627–655. arXiv:1011.0107.
3. T. Sanders, *A quantitative version of the idempotent theorem*, Ann. Math.
   **174** (2011), 531–599.
4. F. Manners, *Quantitative bounds in the inverse theorem for U^{s+1}*,
   arXiv:1811.00718.
5. M. Ortega, S. Prendiville, *Extremal Sidon Sets are Fourier Uniform*,
   arXiv:2110.13447.
6. `op-application.md`, `density-profile-attack.md`, `below-sqrt2.md`,
   this directory.
