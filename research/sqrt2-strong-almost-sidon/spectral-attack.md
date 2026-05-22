# Spectral / Cayley Graph Attack on Strong Almost-Sidon Bipartite Rigidity

**Scouting note, 2026-05-22.** Companion to `below-sqrt2.md`,
`density-profile-attack.md`, and `op-application.md`. Investigates whether
Cayley graph spectra and the expander mixing lemma (EML) can prove the
joint constraint `α + β < 1` on the midpoint halves of an SAS set
(equivalently: break the `√2` barrier toward `2/√3`).

## 0. Executive summary

The Cayley / spectral framework can be set up cleanly for SAS sets, but
**the expander mixing lemma yields only per-half information** —
exactly the obstruction (G3) flagged in `op-application.md`. The
spectral angle reduces to the same Plancherel identity that drives the
Pikhurko adaptation; it does **not** introduce new joint information
about the pair `(A_-, A_+)`.

| Angle | Joint constraint? | Verdict |
|---|---|---|
| Cayley sum graph EML on `A_-, A_+` | Reproduces Pikhurko cross bound | Vacuous (see Attack A) |
| Alon–Boppana / Alon–Roichman | Needs random connection sets | Inapplicable |
| Bipartite Cayley spectral gap | Same Fourier sup-norm input | No new content |
| Grothendieck-style cut-norm | Could in principle | Open; speculative |

**Verdict:** spectral graph theory in its standard forms is *equivalent*
to the Fourier analysis already attempted (Attacks A, C, D1, D2). It
does not provide a new lever on the bipartite rigidity problem.

---

## 1. The Cayley sum graph for a Sidon set

For `A ⊆ ℤ_N`, define the **Cayley sum graph** `G_A = Cay_+(ℤ_N, A)` on
vertex set `ℤ_N`, with `x ~ y` iff `x + y ∈ A`. The adjacency operator
`M_{x,y} = 1_A(x+y)` is circulant; its eigenvectors are the characters
`χ_ξ(x) = e(ξx/N)`, with eigenvalues

  `λ_ξ = |f̂_A(ξ)|`,  where `f̂_A(ξ) = ∑_{a ∈ A} e(−ξa/N)`. (S-1)

Trivial eigenvalue `λ_0 = |A|`. For a Sidon set, Parseval gives

  `∑_ξ |f̂_A(ξ)|⁴ = N · ∑_n r_A(n)²`,

where `r_A(n) = #{(a,b) ∈ A² : a − b = n}`. Sidon means `r_A(n) ≤ 1`
for `n ≠ 0`, so `∑_n r_A(n)² ≤ |A|² + (|A|² − |A|) = 2|A|² − |A|`. Combined
with `|f̂_A(0)|⁴ = |A|⁴`, this gives `max_{ξ ≠ 0} |f̂_A(ξ)|² ≤
√(N(2|A|² − |A|))` in the worst case — equivalently `λ_* ≪ N^{1/4} |A|^{1/2}`.
Ortega–Prendiville sharpens this to `λ_* ≤ N^{11/12}` for `(1+o(1))`-extremal
Sidon sets.

So **the Cayley sum graph of a near-extremal Sidon set is an excellent
spectral expander**, with degree `d = |A| ≈ √N` and second eigenvalue
`λ_* ≪ N^{11/12} = d^{11/6} \cdot N^{-1/12}` under OP rigidity.

## 2. Bipartite expander mixing applied to `(A_-, A_+)`

The expander mixing lemma for Cayley sum graphs states: for `X, Y ⊆ ℤ_N`,

  `e_+(X, Y) := #{(x, y) ∈ X × Y : x + y ∈ A}
    = |X||Y||A|/N + θ`,    `|θ| ≤ λ_* √(|X||Y|).` (S-2)

Take `X = A_-`, `Y = A_+`, with `A` itself as connection set. Each pair
`(x, y) ∈ A_- × A_+` has cross-sum `x + y ∈ (n*/2, n* + N/2]`, which lies
*entirely outside* the range of `A ⊆ [1, N]` for the typical regime
`n* = N`. So `e_+(A_-, A_+) = 0` trivially, and (S-2) gives

  `0 = LU · L_+/N + θ`,  `|θ| ≤ λ_* √(LU)`

which forces `LU · L_+/N ≤ λ_*√(LU)`, i.e., `√(LU) ≤ λ_* · N/L_+`. With
`L_+ = |A| ≈ √(2N)` and `λ_* ≤ N^{11/12}` (OP), this gives
`√(LU) ≤ N^{11/12 + 1/2} = N^{17/12}`, vacuously larger than `√N`. **No
content.**

The issue: the connection set `A` is at the wrong "scale" relative to
the cross-sum support.

### 2.1 Corrected: take connection set = cross-sumset support

Let `S_× := A_- + A_+` (a subset of `(n*/2, 3n*/2]`). Define
`Cay_+(ℤ_{2N+1}, S_×)`. The expander mixing lemma now says

  `e_+(A_-, A_+; S_×) = LU = LU · |S_×|/(2N+1) + θ`,
   `|θ| ≤ λ_*^{S_×} · √(LU)`. (S-3)

Rearranging: `LU (1 − |S_×|/(2N+1)) ≤ λ_*^{S_×} √(LU)`, i.e.,

  `√(LU) ≤ λ_*^{S_×} / (1 − |S_×|/(2N+1))`. (S-4)

Now `|S_×| ≤ LU` (with equality iff all cross-sums distinct, i.e., the
SAS case with `k = 1`). So `1 − |S_×|/(2N+1) ≥ 1 − LU/(2N) ≥ 1/2` at
`LU ≤ N`. Then (S-4) becomes

  `√(LU) ≤ 2 · λ_*^{S_×}`. (S-5)

What is `λ_*^{S_×}`? Its eigenvalues are `|1̂_{S_×}(ξ)|`. Crucial fact:
the SAS hypothesis gives `1_{S_×} = (1_{A_-} * 1_{A_+}) \cdot 1_{≠ n*}/1`
plus a `k · δ_{n*}` term — i.e., `1_{S_×}` is essentially the *support*
indicator of the convolution `1_{A_-} * 1_{A_+}`.

This is precisely the input to **Pikhurko's gap-deficit Fourier
inequality** applied to the cross convolution
(`pikhurko-adaptation.md`, Attack A). The output:
`L · U ≤ ((π+2)²/((π+2)² + 2)) · N ≈ 0.93 N`. Vacuous (we already have
`LU ≤ √(αβ)·N ≤ N/2`).

**Conclusion of §2:** EML on the cross sumset reproduces the Pikhurko
cross bound. The reduction goes: spectral gap of `Cay_+(S_×)` ↔ Fourier
sup-norm of `1_{S_×}` ↔ Pikhurko gap-deficit. No new information.

## 3. Per-half spectral data is per-half

The fundamental obstruction is that the Cayley graph spectrum of
`A_-` (resp. `A_+`) — controlling `|f̂_-(ξ)|`, `|f̂_+(ξ)|` separately —
is exactly the OP-distributional rigidity input. The integrated
SAS-overlap constraint (`op-application.md` §4) is

  `τ/(4α) + τ/(2√(αβ)) ≤ 1 + O(N^{-1/12})`, (D-9-OP)

with slack `1/4` at `α = β = 1/2`. This slack is **geometric** (linear
profile saturating only at `n*`). Per-half Cayley spectra cannot bend
the linear profile.

## 4. Joint spectral lever attempts (all speculative)

- **Matching graph `(A_-, A_+)` of `n*`-pairs.** Bipartite, `k`-regular
  on one side. Leading eigenvalue `≈ √k`. Too sparse/rigid for a
  spectral gap argument.
- **Cross-correlation matrix** `M_{a,b} = 1_{a+b ≠ n*}`. Nearly
  all-ones; operator norm `≈ √(LU)`. No new content.
- **Grothendieck cut-norm of `r_× − 1`.** SAS gives `r_× − 1 ∈ {−1, 0}`
  off `n*`. Cut-norm is `O(N^{1/2})`; we'd need a *lower* cut-norm
  bound to force `α + β < 1`. None known.
- **Alon–Roichman.** Requires random connection sets; our connection
  set is structured. Inapplicable.

## 5. Why spectral methods don't help: structural reason

The bipartite rigidity question — "must `α + β < 1`?" — is a
*positional* (real-space) question about where `A_-, A_+` sit on the
integer line. Spectral methods on `ℤ_N` are translation-invariant; they
cannot distinguish `A_- ⊆ [1, N/3]` from `A_- ⊆ [1, N/2]` at the
Fourier level, because both have the same distribution of `|f̂_-(ξ)|`
up to phase. This mirrors the OP-distributional vs OP-positional gap
in `op-application.md` §7.

## 6. Remaining spectral hopes (speculative)

Genuine joint spectral objects encoding `(A_-, A_+)` together:
- 3-uniform hypergraph with hyperedges `(a, b, a+b)`. No off-the-shelf
  bipartite EML at the needed strength; hypergraph spectral theory
  underdeveloped here.
- Signed Cayley graph (weights `±1` separating SAS-valid sums from
  collisions). The spectral gap might separate `n*`-pair structure
  from generic structure. **Not investigated; speculative.**

## 7. Honest verdict

**Spectral graph theory / Cayley graph methods do not appear to give
new leverage on the SAS bipartite rigidity problem.**

Reasons:
1. The Cayley spectrum of `A_-` resp. `A_+` is equivalent to the
   Fourier data already in Attack A (Pikhurko cross) and D1 (OP). It
   reproduces those negative outcomes via EML.
2. The expander mixing lemma applied to cross-pairs reduces to the
   Pikhurko gap-deficit on the cross sumset — vacuous, by the same
   `LU ≈ N/2` obstacle.
3. Cayley spectra are translation-invariant; SAS rigidity is a
   positional (non-translation-invariant) question. Mismatch is
   structural, not technical.
4. Joint spectral objects on `(A_-, A_+)` (matching graph, bipartite
   Cayley) are either too rigid (no spectral gap) or reduce to known
   Fourier inputs.

The genuinely open joint constraint must come from a *non-translation-
invariant* structural theorem (Freiman-style rigidity for SAS), or from
exotic tools (hypergraph spectra, signed Cayley graphs) that do not
have off-the-shelf strength sufficient for the problem.

This adds one more line to the convergent meta-finding in
`below-sqrt2.md` (Attempts A, B, C, D1, D2): spectral graph theory
joins Pikhurko-Fourier, autoconvolution, density-profile, and
Fourier-uniformity as elementary/semi-elementary approaches that
cannot break `√2`.

**Recommendation:** do not invest in a spectral attack as a primary
line. The Cayley/EML framework is a useful conceptual reframing of the
Fourier picture but does not introduce new content. The honest path
forward remains the Freiman-style SAS-rigidity programme outlined in
`below-sqrt2.md` §"Verdict on the open question".

| Date | Event |
|---|---|
| 2026-05-22 | Spectral/Cayley scouting note drafted. Adds a sixth elementary approach to the convergent negative meta-finding. |
