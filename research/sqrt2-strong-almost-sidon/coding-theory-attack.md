# Coding-Theory Attack on SAS Bipartite Rigidity

**Research note, 2026-05-22.** Scouting whether linear / MDS / LP /
locally-recoverable code techniques can prove the bipartite-rigidity
inequality `α + β < 1` for near-extremal strong-almost-Sidon (SAS)
sets in `[1, N]`.

## Prior art on Sidon ↔ codes

1. **Czerwinski–Pott 2023 (arXiv:2304.07906, AMC 2024).** The cleanest
   modern reference. They establish a *bijection* between sum-free
   Sidon sets `A ⊆ 𝔽₂ᵗ` and binary linear codes with `t` check bits
   and minimum distance `≥ 5`. Sharpened-Johnson + Plotkin-type
   non-existence theorems for `d = 5` codes translate directly into
   improved upper bounds on `|A|` in 𝔽₂ᵗ.
2. **Czerwinski–Pott 2024 (arXiv:2411.12911).** Constructive: each
   large Sidon set in 𝔽₂ᵗ yields a `[n, n−t, 5]` binary code. Used
   to build a Sidon set of size 192 in 𝔽₂¹⁵.
3. **Cilleruelo et al. (arXiv:math/0311385, "Error correcting codes
   and Bₕ-sequences").** Bₕ-sequences in `(𝔽_q[X]/P)*` correspond to
   constant-weight codes (Graham–Sloane).
4. **Bose–Chowla construction (arXiv:2104.12711, expository).**
   A `θ ∈ 𝔽_{q²}*` of order `q²−1` gives a Sidon set of size `q` in
   `ℤ/(q²−1)`. The Sidon condition is equivalent to a minimum-distance
   property of an `[q+1, ·, ·]_q` Reed-Solomon-like evaluation code.
5. **Cilleruelo–Ruzsa–Trujillo 2002 / Lev 2004** (cited via 2103.15850
   §3.1). "An inequality from coding theory" — uses a `q`-ary code of
   length `|A|` whose minimum distance is forced by the Sidon
   property. Yields the same `|A| ≤ √N + O(N^{1/4})` as Lindström,
   not better.

## Mapping SAS → code parameters

A Sidon set `A ⊂ [1, N]` of size `s` viewed as a code via
`a ↦ (a mod p₁, …, a mod p_t)` with `p₁, …, p_t` prime gives a code
of length `t`, alphabet `max(p_i)`, dimension `log_q s`. The Sidon
condition imposes minimum-distance `≥ t − 1` in a Hamming-style sense
(any two codewords disagree in all but ≤ 1 coordinate, otherwise a
non-trivial collision occurs).

This is essentially **Singleton-saturating**: `d = t − 1` with
`k = log_q s` gives `s ≤ q^{n−d+1} = q²`, matching `s ≤ √N` up to
constants if `q ≈ √N`.

**Conclusion:** the Sidon ↔ code dictionary recovers Lindström but does
not beat it. The Singleton/Plotkin/Hamming bounds applied directly
encode "pairwise sums distinct" which is exactly the Sidon hypothesis;
no extra slack is extracted.

## The bipartite question

The SAS bipartite rigidity question asks: given a midpoint split
`A = A_- ∪ A_+` with `|A_-| = √(αN)`, `|A_+| = √(βN)`, and the SAS
condition (one bad atom at `n*`), can we force `α + β < 1`?

Translating to codes: `A_-` is a length-`|A_-|` code with Sidon
distance property in `[1, N/2]`; `A_+` similarly in `[N/2, N]`. The
cross-pair `A_- × A_+` is a *bipartite product code* whose codewords
have sums `a + b ∈ ((1−β)N, (1+α)N]`. The SAS condition forces:

- (within) `A_-` is Sidon, `A_+` is Sidon — per-half Singleton-style
  bounds give the Lindström constraints `α ≤ 1/2`, `β ≤ 1/2`.
- (cross) the cross-sums are distinct *except at `n*`*, i.e., the
  bipartite "product code" has minimum distance `2` except for one
  pair of "siblings."

**The relevant joint constraint** would be a "**bipartite Singleton**"
of the form: `|A_-| · |A_+| ≤ (cross-sum range) + (slack at n*)`.
Plugging in: `|A_-| · |A_+| ≤ N + (k − 1)`, where `k` is the
multiplicity at `n*`. With `|A_-| = √(αN)`, `|A_+| = √(βN)`:

  `√(αβ) · N ≤ N + O(√N)`  ⟹  `√(αβ) ≤ 1 + o(1)`.

This is **vacuous** since `αβ ≤ 1/4` automatically.

## Why coding bounds are too weak for bipartite rigidity

All of Singleton, Plotkin, Hamming, and Delsarte LP for minimum-
distance-`d` codes are *cardinality-of-codewords* statements. They
control `|A|` but not the *location* of the elements of `A` inside
`[1, N]`. The bipartite rigidity question `α + β < 1` is precisely a
location statement: it forces `A` to vacate either the bottom or top
half-interval.

Coding theory bounds are translation-invariant; the integer-Sidon
problem is *not* translation-invariant for the rigidity question.
This is the fundamental mismatch.

### Quantitative check

Even the strongest code bound — Delsarte LP for `d ≥ 5` binary codes
applied via Czerwinski–Pott (the *only* coding-theoretic improvement
over Lindström known) — gives a ~1–2% improvement on the leading
constant in the 𝔽₂ᵗ setting. For integer Sidon sets in `[1, N]` the
constant `√N` is already known up to lower-order terms; coding bounds
do not improve the asymptotic constant `1`.

There is no possible factor-of-(√2 − 2/√3 ≈ 0.26) improvement extractable
from the Czerwinski–Pott style argument: it operates on the wrong
ambient group.

## Locally-recoverable codes (LRC)

The "Hayes–Khare" reference in the prompt does not appear in the
literature (no such bipartite-rigidity LRC result is published as of
2026-05-22). LRC theory provides distance/locality tradeoffs that are
inherently about *small repair sets*, not bipartite halves. Applying
LRC bounds to Sidon sets gives nothing new beyond Singleton-type
restrictions already covered above.

## Reed-Muller / Reed-Solomon / Bose-Chowla constructions

These are *lower-bound* tools — they construct Sidon sets, not bound
them. Asking "when does a Bose-Chowla Sidon set split as a reflected
pair `B ∪ (N − B)`?" gives the algebraic-number-theoretic angle
explored in `algebraic-nt-attack.md`, not a coding-theoretic upper
bound.

## MacWilliams / dual code / LP angle

For *binary* linear codes, MacWilliams identity relates a code's
weight enumerator to its dual's, and Delsarte LP exploits this to get
upper bounds. The Sidon ↔ code-of-min-distance-5 correspondence
(Czerwinski-Pott) opens the door to LP bounds on Sidon sets in 𝔽₂ᵗ.
But the LP bound is **also cardinality-only** — it bounds the number
of codewords, not their distribution in any ambient interval. For
integer Sidon sets in `[1, N]`, there is no analogous MacWilliams
duality because `[1, N]` is not a group.

One could *try* to embed `[1, N] ↪ ℤ/(2N+1)` and apply Delsarte for
codes in cyclic groups, but:
- The resulting code is a constant-weight `(2N+1, |A|, ...)` code with
  no special distance property beyond Sidon.
- LP bounds on such codes are no sharper than Lindström.

## Honest verdict

**Coding theory does NOT give bipartite rigidity for SAS.**

1. The known Sidon ↔ code correspondences (Czerwinski–Pott;
   Cilleruelo–Lev "inequality from coding theory") are
   *cardinality-only* statements. They recover Lindström, not beat it.
2. The "bipartite Singleton" constraint `|A_-| · |A_+| ≤ N + O(√N)` is
   vacuous (slack of factor 4 at the worst case).
3. Code bounds are translation-invariant; SAS bipartite rigidity is
   inherently location-dependent. There is a structural mismatch.
4. No prior work attempts a coding-theoretic proof of integer Sidon
   *location* constraints; the only Sidon-via-code results are in
   `𝔽₂ᵗ` and yield ≤ 2% constant improvements, far short of the
   needed `(√2 − 2/√3)/√2 ≈ 18%` gap.
5. **LRC, MDS, Reed-Muller, Reed-Solomon angles all reduce to the
   same Singleton-type cardinality bound**, vacuous here.

The coding-theoretic toolkit is *one more sophisticated method that
extracts per-half cardinality info but no joint location info* — the
same diagnosis as the Fourier / autoconvolution / density-profile
attacks already documented (see `below-sqrt2.md` §"Three negative
attacks").

**Recommendation:** **stand down on coding-theory attack.** The
correspondence is real and useful for `𝔽₂ᵗ` Sidon problems, but the
ambient group mismatch makes it structurally inapplicable to integer
SAS bipartite rigidity. Effort better spent on Freiman-style
rigidity (the only known route to `2/√3`).

## References

- Czerwinski–Pott, *Sidon sets, sum-free sets and linear codes*,
  arXiv:2304.07906 / AMC 18 (2024) 549–566.
- Czerwinski–Pott, *On large Sidon sets*, arXiv:2411.12911 (2024).
- Cilleruelo et al., *Error correcting codes and Bₕ-sequences*,
  arXiv:math/0311385.
- Balogh–Füredi–Roy, *An upper bound on the size of Sidon sets*,
  arXiv:2103.15850, §3.1 "an inequality from coding theory."
- Riblet, *Sidon sets in a union of intervals*, arXiv:2202.01296
  (lower bound `0.876√n` for Sidon subsets of two-interval unions —
  wrong direction for our purposes).
- Bose–Chowla expository: Cilleruelo–Lev arXiv:2104.12711.
