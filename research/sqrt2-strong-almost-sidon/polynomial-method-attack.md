# Polynomial-Method Attack on SAS Bipartite Rigidity

**Research scouting note, 2026-05-22.** Can Croot–Lev–Pach (CLP) /
Ellenberg–Gijswijt / slice-rank / partition-rank / Tao-PFR techniques
prove `α + β < 1` for the midpoint-split halves of near-extremal
strong almost-Sidon (SAS) sets in `[1, N]`?

## TL;DR

**No — not in any direct, presently available form.** Every published
slice-rank / CLP / polynomial-method success exploits a structural
feature (multilinearity + small group exponent + tensor diagonal) that
the SAS-in-`[1, N]` problem fundamentally lacks. The closest analogues
have been considered and dismissed by the additive-combinatorics
community. The recent PFR breakthrough (Gowers–Green–Manners–Tao 2023)
is in `𝔽₂ⁿ`; the integer analogue is open and would not directly
yield SAS rigidity even if proved.

## What the polynomial method has done (post-2016)

The CLP/slice-rank revolution gave exponential-savings bounds in
`𝔽_pⁿ` for:

- **Cap-sets** (Ellenberg–Gijswijt 2017): `|A| ≤ (2.756)ⁿ` in `𝔽₃ⁿ`.
- **Erdős–Ginzburg–Ziv** in `𝔽_pⁿ` (Naslund 2018+; partition rank).
- **Sunflower-free sets** (Naslund–Sawin 2017).
- **Tri-coloured sum-free sets** (multiple authors, 2017).
- **2-caps = Sidon sets in `𝔽₃ⁿ`** (Tait et al., arXiv:1809.05117) —
  the only direct CLP-style attack on a Sidon problem the survey
  located; bound `|S| ≤ 3ⁿ/(n+1)·O(1)`, far from interesting in the
  integer regime.

The Sauermann 2024 survey ("The Slice Rank Polynomial Method – A
Survey a Few Years Later", *Surveys in Combinatorics*) explicitly
documents limitations: for APs of length `≥ 8`, slice rank cannot
beat trivial bounds; the method is structurally tied to **short
multilinear patterns over small-exponent groups**.

## Why each angle fails for SAS-in-`[1, N]`

### Angle 1: CLP via CRT-style embedding `[1, N] ↪ 𝔽_pⁿ`

**Idea:** lift SAS to `𝔽_pⁿ` via a digit/CRT encoding and apply CLP.

**Why it fails.** (i) Sidon-ness in `[1, N]` is *not* preserved by
any natural embedding into `𝔽_pⁿ`: integer sums carry, integer
collisions are not character collisions. (ii) CLP gives exponential
savings in `n` (the dimension); we need polynomial-in-`√N`
sharpness, not exponential. (iii) The "single exception at `n*`"
hypothesis is an `L∞` statement — CLP works on multiplicity-pattern
*polynomials* and is blind to single atoms in the same way the
autoconvolution attempt B was (see `autoconvolution-attack.md`). The
folklore observation that "polynomial method gives only logarithmic
savings in `ℤ`" (cf. arXiv:1701.07196 commentary) reflects exactly
this gap.

### Angle 2: Bipartite / slice-rank analogue on `A_- × A_+`

**Idea:** the SAS midpoint split *is* bipartite — set up a tensor
`T[a, b] = δ_{a + b = n*}` on `A_- × A_+` and bound its slice rank.

**Why it fails.** The CLP/slice-rank pipeline produces useful bounds
only when the tensor's diagonal pattern is *combinatorially rigid*
(diagonal = the "good" pattern; off-diagonal = forbidden). For
SAS-cross we want the *opposite*: the cross-pair sumset `A_- + A_+`
covers an *interval* in `ℤ`, with multiplicity profile to be
controlled. Slice rank cannot extract such profile information; it
counts diagonal solutions, not value-disjointness. This is the same
"per-half vs joint" obstruction identified in `op-application.md`
(attempt D2): per-half rigidity is what slice rank could potentially
yield (if integer-adapted), and per-half rigidity does *not* close the
`√2 → 2/√3` gap.

### Angle 3: Polynomial method adapted to cyclic groups `ℤ_N`

Croot–Lev–Pach's original paper was `ℤ_4ⁿ`; subsequent work covered
`ℤ_pⁿ` (cap-sets). Direct adaptation to a *single* `ℤ_N` (not a
power) gives only `O(N / log log N)`-type savings, which is
catastrophically weak compared to the `√N` regime SAS lives in.
Petrov-style polynomial-method results for restricted sumsets in
`ℤ_n` (arXiv:1810.05346, 2210.12044) yield *lower* bounds for sumset
size, the wrong direction for SAS.

### Angle 4: Tao-style polynomial Freiman–Ruzsa rigidity

The Gowers–Green–Manners–Tao PFR resolution (2023; published Ann.
Math. 2025) is for `𝔽₂ⁿ`. The integer analogue (Plünnecke–Ruzsa
with polynomial parameters in `ℤ`) is still open. Even granting the
integer PFR conjecture, it would give "`A` covered by polynomially
many translates of a generalised arithmetic progression of bounded
dimension" — a *structure* statement on sets of small doubling.
SAS sets have `|A + A| ≈ |A|²/2`, i.e. *maximum* doubling, the
opposite regime. PFR-style rigidity is irrelevant here.

## Specific arXiv pointers (2016–2026, polynomial method × Sidon-adjacent)

- arXiv:1605.01506 (Croot–Lev–Pach) — origin paper.
- arXiv:1605.09223 (Ellenberg–Gijswijt) — cap-set.
- arXiv:1612.01929 (Petrov, "Sumsets as unions of sumsets") — uses
  CLP + Meshulam; integer sumset structure, *not* Sidon.
- arXiv:1701.07196 (Bary-Soroker / Castryck commentary) — explicit
  remark that polynomial method gives only `log` savings in `ℤ`.
- arXiv:1712.00228 (Naslund) — EGZ in finite abelian groups.
- arXiv:1809.05117 (Tait et al.) — 2-caps = Sidon in `𝔽₃ⁿ`; the
  bound is far from the integer Lindström regime.
- arXiv:1909.10509 (Sauermann, "Avoiding a shape") — slice rank for
  systems of equations; SAS is not a system of equations.
- arXiv:2208.06932 (Karam, partition rank) — generalises slice rank;
  applies to multilinear-form rigidity, not to interval-Sidon.
- Sauermann 2024 survey (Cambridge, *Surveys in Combinatorics 2024*)
  — explicitly notes limitations on longer patterns / integer regimes.

The systematic literature scan found **zero** papers attempting CLP
or slice-rank attacks on `B₂[g]` sets in integer intervals. This is a
strong negative signal: in the post-CLP boom (2016–2026), every
combinatorialist with a tensor-rank idea would have tried integer
Sidon if it were tractable.

## Verdict on the four angles posed

| Angle | Specific obstruction | Probability of success |
|---|---|---|
| 1. CRT embedding `[1, N] ↪ 𝔽_pⁿ` | Sidonness not preserved; CLP gives exponential-in-`n` savings, wrong granularity | ~0 |
| 2. Bipartite slice rank on `A_- × A_+` | Slice rank counts diagonals, blind to value-disjointness profile | ~0 |
| 3. CLP adapted to `ℤ_N` | Single cyclic group gives only log savings | ~0 |
| 4. Polynomial PFR / Tao rigidity | Wrong regime (SAS has maximum doubling, not small) | ~0 |

## Where polynomial methods *could* still help — caveat

If one could prove an integer analogue of PFR with parameters
sharp enough to characterise sets *of moderate doubling* `K ∈ [2,
log N]` (rather than `K = O(1)`), and combine it with a separate
bound forcing extremal SAS sets to have moderate doubling on
*some scale*, there might be a route. This is highly speculative
and would itself constitute a major additive-combinatorics
breakthrough independent of SAS.

## Recommendation

**Do not invest further effort in polynomial-method angles for the
SAS `√2 → 2/√3` problem.** The structural mismatch (interval vs.
`𝔽_pⁿ`; single-atom vs. multilinear-diagonal; maximum-doubling vs.
small-doubling) is fundamental. Continue with the bipartite-rigidity
direction (`below-sqrt2.md` line 1' + density-profile attempt C) or
move to the Freiman-style structural rigidity conjecture.

## Tracking

| Date | Event |
|------|-------|
| 2026-05-22 | Scouting note drafted; four polynomial-method angles each individually disqualified by structural mismatch. No prior art for CLP-style attacks on integer Sidon found in 2016–2026 arXiv scan. |
