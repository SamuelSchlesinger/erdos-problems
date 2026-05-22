# Ergodic / Furstenberg-Correspondence Attack on SAS Bipartite Rigidity

**Date:** 2026-05-22. Research scout note. Companion to `below-sqrt2.md`
and the 11 prior attack documents.

## TL;DR (verdict)

**NO.** Furstenberg correspondence + Host–Kra–Ziegler structure theorems
cannot, even in principle, deliver bipartite rigidity for strong
almost-Sidon (SAS) sets, for **three independent and converging reasons**:

1. **Density-zero kills the correspondence.** SAS sets have
   `|A_N|/N = Θ(N^{−1/2}) → 0`. Furstenberg correspondence requires
   positive upper density to produce a non-trivial invariant measure.
2. **Wrong problem class.** Furstenberg-style theorems extract
   recurrence/multilinear-average information (Szemerédi: existence of
   APs; Bergelson–Leibman: polynomial recurrence). They do not produce
   **avoidance** or **multiplicity = 1** statements. SAS is an
   avoidance/multiplicity hypothesis.
3. **L^p averaging blindness, again.** Host–Kra characteristic factors
   are L²-projections onto nilfactors. Like every other L^p method we
   tried (entropy, autoconvolution, restriction), the single-atom
   strength of SAS is washed out by L² averaging in the ergodic limit.

This is the same meta-obstruction the 11-attack convergent diagnosis
identified, in ergodic disguise. Details below.

## 1. Setting up SAS as a correspondence problem

### 1.1 Naive Furstenberg correspondence

Standard Furstenberg correspondence (1977): given `A_N ⊆ [1, N]` with
`|A_N|/N → δ > 0`, there exist a probability space `(X, μ, T)` and a
measurable set `E ⊆ X` with `μ(E) = δ` such that for any finite
`F ⊆ ℤ`,
```
limsup_N |A_N ∩ ⋂_{f ∈ F} (A_N − f)| / N ≥ μ(⋂_{f ∈ F} T^{−f} E).
```
This bridges "density-of-shifts" on the finite side to "measure of
intersection of orbits" on the ergodic side.

### 1.2 Failure mode 1: density-zero

For SAS, `|A_N| ≤ √(2N)`, hence `δ_N := |A_N|/N = O(N^{−1/2}) → 0`. The
Furstenberg correspondence gives `μ(E) = 0`, which makes every
intersection statement trivially `0 = 0`. The correspondence in its
standard form yields **no information** on density-zero sets.

This is well-known: Szemerédi's theorem is a positive-density statement.
Density-zero analogues (Green–Tao on primes; Frantzikinakis–Host on
multiplicative functions) require a separate **transference** step
(W-trick, pseudorandom majorant) before any ergodic machinery applies.
No transference principle is known for Sidon-type / B₂[g] sets in the
single-atom regime; the natural "majorant" would have to be a finite
set of size `√N`, which has zero density.

### 1.3 Rescaling attempt — pretransference at scale √N

The natural fix: rescale. Define `f_N := √N · 1_{A_N} / |A_N|` (so
`‖f_N‖_∞ = √N / |A_N| = Θ(1)` at extremality and `∫ f_N = Θ(N^{−1/2})·N
= Θ(√N)`). This is the "Sidon density" normalization — it's the right
scaling for L⁴ identity (`‖f̂_N‖_4^4 = Θ(N²)` at extremality).

But this rescaled `f_N` does not embed in a Furstenberg correspondence,
because the limit measure is not a probability measure — total mass
`∫ f_N → ∞`. One can normalize to a probability and recover an ergodic
system, but then SAS-specific info (single atom of mass `k ≈ √N` in
`f_N * f_N`) becomes an atom of mass `Θ(1/√N)` in the limit, which
**vanishes**.

This is the density-zero × single-atom double bind: any normalization
that makes the limit a probability measure crushes the SAS signal to
measure zero in the limit; any normalization that preserves the SAS
signal has infinite total mass and no ergodic theory applies.

## 2. Host–Kra–Ziegler structure: even if correspondence worked

Suppose, counterfactually, that we had a valid correspondence with a
positive limit measure carrying the SAS signal. What would HKZ buy?

### 2.1 Characteristic factors

Host–Kra (2005): for `f_0, …, f_k ∈ L^∞(μ)`, the multilinear average
`(1/N) Σ f_0(x) f_1(T^n x) ⋯ f_k(T^{kn} x)` converges in L² to a
projection onto the `k`-step nilfactor `Z_k`. The k=1 case reduces to
the Kronecker factor (eigenfunctions of `T`). This is the **only HKZ
piece relevant to SAS**, since SAS is a two-variable (`a+b = a'+b'`)
condition.

### 2.2 Kronecker factor = Plancherel, translation-invariant

For Sidon, `‖f̂‖_4 = (2+o(1))^{1/4} ‖f̂‖_2`. The Kronecker factor
encodes only `|f̂(n)|²` magnitudes — translation-invariant in the
spectrum — exactly the defect that killed the Cayley/spectral attack
(`spectral-attack.md`). HKZ at level 1 recovers Plancherel/Sidon-via-L⁴,
i.e. `√N`-per-half. No bipartite info.

### 2.3 No higher-step structure to exploit

Higher nilfactors `Z_k, k ≥ 2` characterize length-`≥3` AP averages
and `U^{k+1}`-defects. SAS is genuinely length-2; the relevant
nilfactor is `Z_1`. There is no higher-step lever.

### 2.4 Product-system bipartite encoding fails the same way

A joint system on `(X × X, μ × μ, T × T)` could encode `(A_-, A_+)`
bipartite-ly. But the cross-sum condition is still length-2; the
joint characteristic factor is a product of Kroneckers and reduces
to two Plancherel identities. This is the Pikhurko-cross calculation
(`pikhurko-adaptation.md`) in ergodic disguise — no new content.

## 3. The single-atom blindness, repeated

Even ignoring (1) and (2), point (3) is decisive. Every HKZ-type
statement is an L² (or L^∞ → L²) **projection**. The SAS hypothesis
is "multiplicity ≤ 1 except at one atom of mass `k ≈ √N`." In the
rescaled / normalized limit:

- The "regular" part (multiplicity 1 on `Θ(N)` values) contributes
  L²-mass `Θ(N) · 1 = Θ(N)`.
- The single atom contributes L²-mass `k² ≈ N`.

These are **comparable**, but ergodic averages return only the L²
*norm*, not its decomposition. To recover the single-atom information
from the L²-norm one needs an L^∞ inverse theorem — and that is
exactly the inverse-Gowers / Ortega–Prendiville machinery already
analyzed in `op-adaptation.md` and `op-application.md`, both negative.

In particular: Host–Kra's structure theorem and Tao's inverse-Gowers
theorem are **dual** statements; converting one to the other is
formally an equivalence up to the polynomial-loss inverse Gowers
inequality (Manners 2018, Sanders 2012). So ergodic-side HKZ cannot
do anything that finite-side inverse-Gowers cannot — and the latter
has been ruled vacuous in the SAS regime by `op-adaptation.md`
(Δ ≪ N^{5/12} + k·N^{1/6} survives only for `k ≪ N^{1/3}`, vacuous
for `k ≈ √N/√2`).

## 4. What about Frantzikinakis-style density-zero ergodic theorems?

Frantzikinakis (2010s) developed ergodic theorems for sequences of
density zero (primes, multiplicative functions, smooth sequences) via
**uniform extensions**: embed the sparse set into a positive-density
"pretransferred" sequence, run HKZ, transfer back. This requires:

- A **pseudorandom majorant** with explicit Gowers-norm bounds (Green–
  Tao's `ν` for primes).
- A **correlation estimate** of the majorant against nilsequences.

For SAS, neither object exists. A pseudorandom majorant for "single-
atom multiplicity" would need to be a Sidon-like set itself, which
brings us back to the original problem. Frantzikinakis machinery
cannot bootstrap from nothing.

## 5. Bottom line / honest verdict

**Ergodic methods cannot break the `√2` barrier for SAS.** The three
obstructions stack:

| Obstruction | Severity | Could be circumvented by ... |
|---|---|---|
| Density-zero in correspondence | Fatal | A pretransference theorem (does not exist for SAS). |
| Length-2 nature of SAS limits to Kronecker | Major | Inventing a length-≥3 reformulation (not visible). |
| L² averaging is single-atom-blind | Fatal (shared with entropy/autoconv/restriction) | An L^∞ extraction step = inverse-Gowers, already vacuous. |

This makes the **ergodic attack the 12th in a converging family**.
All twelve attacks (5 Fourier-direct, 6 cross-domain scouts, this
ergodic scout) confirm: **SAS bipartite rigidity is location-sensitive
and single-atom-sharp; every L^p-averaged or translation-invariant
toolkit is structurally inadequate.** Ergodic theory falls under
L²-averaging.

The honest research direction remains: a **structural rigidity
theorem** for SAS extremizers (Freiman-style), to be approached via
direct combinatorial / additive-structural arguments, not via any
limit-theoretic machinery currently in the toolkit.

## 6. Caveats and what would change this verdict

A genuinely new ergodic input would be:

- **A non-conventional ergodic theorem** that survives density-zero
  and extracts L^∞ (not L²) information. None is known.
- **A nilsequence inverse theorem with sharper-than-polynomial
  bounds** in the regime `k = Θ(√N)`. Manners' bounds are
  polynomial; the SAS regime needs `k/√N`-scale precision, which
  current inverse theorems do not provide.
- **A bipartite Host–Kra theorem** for two-set joint actions. None
  exists in the literature; constructing one is a serious research
  project distinct from the SAS application.

None of these are on the horizon. Verdict: **ergodic attack closed
negative**.
