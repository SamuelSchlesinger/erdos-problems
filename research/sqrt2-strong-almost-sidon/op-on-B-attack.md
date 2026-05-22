# OP Rigidity Applied to the EF-Decomposed Half `B`

**Worked analysis, 2026-05-22.** Companion to `rigidity-survey.md`,
`op-application.md`, `op-adaptation.md`, and the formal R4 in
`Erdos/AlmostSidonSets/Rigidity.lean` (line 1263, `r4_ef_decomposition`).

**Distinct from prior notes.** `op-application.md` applies OP to the
*midpoint split* halves of an SAS set whose EF shape is *not assumed*.
The present note *assumes* the EF decomposition `A = B ∪ (n* - B)`
(the conclusion of R4 under exact-half multiplicity) and applies OP
to the Sidon set `B`. Goal: see what extra rigidity falls out, and
whether the pipeline is anything more than circular.

---

## 1. The set `B` and its parameters

**Hypothesis (EF-decomp).** `A ⊆ [1, N]` SAS with exceptional `n*`
and saturating multiplicity. By R4 (`r4_ef_decomposition`),
`A = B ∪ (n* - B)` with `B := A ∩ [1, ⌊n*/2⌋]` Sidon.

**Hypothesis (near-extremal).** `|A| ≥ (2/√3 + ε)·√N` for ε > 0 fixed.

**Derived parameters.**

- `|B| = |A|/2` (no-self-pair case) or `(|A|+1)/2` (self-pair case);
  in either case `|B| = (1 + o(1))·|A|/2 ≥ (1/√3 + ε/2)·√N`.
- `B ⊆ [1, M]` with `M := ⌊n*/2⌋`. The EF construction
  (`B ⊆ [1, N/3]`, `n* = 4N/3`) gives `M ≈ 2N/3`, while the
  midpoint-split absurdity case (`n* = N`) gives `M ≈ N/2`. In all
  cases `M ≤ N`, so `B` lives in an interval of length `≤ N`.
- Sidon-extremal density in `[1, M]` is `√M`. Since
  `|B| ≈ (1/√3)·√N` and `√M ∈ [√(N/2), √N]`, the *relative density*
  `|B|/√M` ranges in `[1/√3·√(2), 1/√3] ≈ [0.816, 0.577]`.

So `B` sits at **58 %–82 % of Sidon-extremal density in its ambient
interval**.

## 2. Translating OP to `B`

Apply OP Theorem 1.2 (or its Corollary 1.4) with `[N] ↦ [1, M]`,
`S ↦ B`:

$$
\Big\| \widehat{1_B} - \tfrac{|B|}{M}\, \widehat{1_{[1,M]}} \Big\|_\infty
\;\ll\; M^{1/2}\!\left( \Big|\tfrac{|B|}{M^{1/2}} - 1\Big|
+ M^{-1/6}\right)^{1/2}.
$$

With `|B| = c_B · √M` for some `c_B ∈ [0.577, 0.82]` (depending on
the value of `M`), this gives

$$
\Big\| \widehat{1_B} - \tfrac{|B|}{M}\, \widehat{1_{[1,M]}} \Big\|_\infty
\;\ll\; M^{1/2}\!\left( |c_B - 1| + M^{-1/6}\right)^{1/2}
\;=\; O(M^{1/2}) \;=\; O(N^{1/2}).
$$

For the **explicit corollary form** suited to "extremal" `B` (OP Cor.
1.4) we would need `c_B = 1 + o(1)`, but `c_B ≤ 0.82 < 1`, so the
*sharp* `M^{-1/12}` corollary form does *not* apply — only the
**main theorem** does, with `|c_B - 1| ≍ 1` as the dominant term.

**Effective bound.** The Fourier sup-norm bound on `1̂_B` is
`O(√M) = O(√N)`, the *trivial* `‖1̂_B‖_∞ ≤ |B|` rephrased. **OP gives
no nontrivial gain on `B` in the regime `c_B ≤ 0.82`.**

This is the first warning sign. Re-reading OP: the `N^{-1/12}` error
in the OP corollary comes from solving the quadratic
`|S|² / N − 1 ≤ N^{-1/6}` for `|S|/√N = 1 + O(N^{-1/12})`. Below the
*Sidon-extremal* density, the bound saturates at the trivial
`O(√M)`. So OP-on-B is non-vacuous only if `c_B → 1`, i.e. only if
`|B|/√M → 1`. In our regime `c_B ≤ 1/√3 · √2 ≈ 0.82`, so the bound
is trivial.

## 3. Structural consequence: A's Fourier transform under EF reflection

Suppose for a moment we *did* have nontrivial OP-control on `B`, say
`|1̂_B(ξ)| ≤ N^{11/12}` for ξ ≠ 0. The reflection structure
`A = B ∪ (n* - B)` gives the exact Fourier identity (over `[1, N]`):

$$
\widehat{1_A}(\xi) \;=\; \widehat{1_B}(\xi) \;+\; e(-\xi n^*)\cdot \overline{\widehat{1_B}(\xi)}.
$$

(Self-pair element, if any, contributes a single fixed-point correction
`O(1)`.) Writing `1̂_B(ξ) = R + iI`, we get

$$
|\widehat{1_A}(\xi)|^2 \;=\; |1̂_B(ξ)|^2 \cdot |1 + e(-\xi n^*)\cdot \mathrm{rot}|^2 \;\le\; 4 |1̂_B(ξ)|^2.
$$

So `‖1̂_A‖_∞ ≤ 2·‖1̂_B‖_∞ + O(1)`. Conversely, at the **atom frequency**
`ξ* := 1/n*`, the two summands rotate into alignment, giving
`|1̂_A(ξ*)| = 2|Re(e(ξ*·middle) 1̂_B(ξ*))| ≈ 2|1̂_B(ξ*)|` (constructive
interference). Plancherel locates the "atom at `n*`" in `A * A`:

$$
\#\{(a_1,a_2) \in A^2 : a_1 + a_2 = n^*\} \;=\; \int_0^1 |\widehat{1_A}(\alpha)|^2 e(-\alpha n^*)\, d\alpha
\;=\; \tfrac{|A|^2}{N} \;+\; \sum_{\xi \neq 0} |1̂_A(\xi)|^2 e(-\xi n^*)/N.
$$

The SAS hypothesis forces the off-zero sum to concentrate on the atom
frequency `ξ*`. So under OP-on-B, the size of the SAS exception is
*bounded* by the (assumed small) off-zero Fourier mass of `B`. But
**OP gives no off-zero control of `B` at the density `c_B < 1`**
(§2), so the constructive-interference argument vacates.

## 4. Bound on `|A|` from OP-on-B (counterfactual)

*If* one had `‖1̂_B − (|B|/M)·1̂_{[M]}‖_∞ ≤ |B|·M^{-1/12}`,
the Plancherel identity for `r_A(n*)` would read
`r_A(n*) = |A|²/N + O(|B|²·N^{-1/12})`. SAS extremality gives
`r_A(n*) ≈ |A|/2`, so `|A| ≈ N/2 ± O(N^{11/12})` — wildly weaker
than `√(2N)`. The OP error *dwarfs* the size we want to bound.
Even with the counterfactual corollary, the pipeline is too lossy
for `√N`-scale rigidity.

## 5. Exact-half-multiplicity bridge: does OP help?

The point of the EF-decomposition hypothesis is the multiplicity
saturation `2·r_A(n*) = |A|`. The Plancherel side of OP-on-B gives

$$
r_A(n^*) \;=\; \int_0^1 |1̂_B(\alpha)|^2 \,d\alpha \;+\; \text{atom-cross terms},
$$

via the reflection identity in §3 evaluated at `n*`. If `B` were
OP-uniform off zero, the integral simplifies to `|B|² / M + O(\text{err})`
— a single density-square term. The SAS saturation `2r = |A| ≈ 2|B|`
would then read `|B|²/M ≈ |B|`, i.e. `|B| ≈ M`, i.e. `B` is the **whole
interval**. That contradicts Sidon (which forces `|B| ≤ √M`). So the
"OP gives exact saturation" implication is *vacuous in the wrong
direction*: OP-uniform `B` cannot saturate multiplicity. The
exact-half-multiplicity hypothesis is **incompatible** with OP-Fourier-uniformity
of `B`, except in a trivial sense.

**Reinterpretation.** OP says: extremal Sidon sets are *random-like*
(uniform in APs). An EF-decomposed `A` has `r_A(n*) ≈ |A|/2 = Θ(√N)`
representations of `n*` — a *highly concentrated* sumset behaviour at
one value. These two facts are in direct tension. OP-on-B and
exact-half-multiplicity *both* holding is the EF construction's own
internal balance; neither implies the other.

## 6. Pitfall: is this circular?

**Yes, structurally.** To apply R4 we *assumed* the EF decomposition.
R4's hypothesis is "exact half multiplicity," which is itself a *very
strong* arithmetic constraint that already forces near-EF shape (R3
plus R4). So:

> "Near-extremal SAS ⇒ EF decomposition ⇒ B Sidon ⇒ apply OP to B ⇒ structure
> of A."

The first implication is the SAS rigidity conjecture (the goal). The
chain only delivers genuine new content if OP-on-B produces a constraint
that *would fail* for a hypothetical non-EF near-extremal SAS, i.e. if
OP-on-B is a *necessary* condition that some alternative extremizer
fails to satisfy. From §§2–4, OP-on-B is *not* a constraint at all
(it's vacuous at our density); so this chain is not a proof.

## 7. Possible salvage: perturbation around EF

If `A` is **near-EF** in symmetric difference (`A △ A_EF = o(√N)`),
then `B := A ∩ [1, n*/2]` is **near-extremal Sidon** in `[1, M]`. An OP
*stability* statement ("near-extremal Sidon ⇒ near-Fourier-uniform")
would then constrain the deviation of `A` from EF. **OP itself does
not prove this stability** — OP is sharp only at `|S| = √N(1+o(1))`.
At density `0.577·√N`, OP is silent.

## 8. Honest verdict

1. **OP-on-B is trivial at our density.** `|B| ≈ 0.577·√M` is too
   low for the OP corollary's `N^{-1/12}` bound; only the trivial
   `O(√M)` bound holds.
2. **The chain "near-extremal SAS ⇒ EF ⇒ apply OP to B" is circular.**
   The EF step is the conjecture; OP-on-B adds no new constraint.
3. **The exact-half-multiplicity hypothesis is in *tension* with
   OP-uniformity**, not implied by it. They co-exist in the EF
   construction by a balanced-design accident, not by Fourier
   compulsion.
4. **The only genuinely new direction is OP-stability** from
   extremal-density down to `(1/√3)·√M ≈ 0.577·√M`. This is open and
   would itself be a significant Fourier-analysis paper.
5. **No new size bound on `|A|`** is delivered by this conditional
   pipeline beyond what `op-application.md` already derives via the
   midpoint split (which is `√2·√N`, not `2/√3·√N`).

**Net contribution.** This attack identifies a clean conjectural
intermediate — an "OP stability at sub-extremal Sidon density" — whose
proof would, combined with R4, deliver SAS rigidity. But the intermediate
is genuinely open and OP itself does not prove it.

## 9. Recommended next investigation

Survey Fourier stability for Sidon sets at *sub-extremal* density:
Schoen–Sisask 2018 (Bohr-set machinery), Sanders 2012
(Bogolyubov–Ruzsa), Bloom–Sisask 2020 (logarithmic Roth) — adapt any
to give nontrivial `o(√N)`-control on `1̂_B(ξ)` at ξ ≠ 0 for
`c_B ≈ 0.58`. Until then, **the OP-on-B conditional approach is
circular and yields no new bound**.
