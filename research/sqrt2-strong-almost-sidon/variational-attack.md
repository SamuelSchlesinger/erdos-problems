# Variational / Euler–Lagrange Characterization of SAS Extremizers

**Status: negative for unconditional `2/√3`, but identifies the *exact*
missing ingredient.** Draft, 2026-05-22. Companion to `below-sqrt2.md`.

## 1. Continuous model

Rescale `[1, N]` to `[0, 1]` via `x ↦ x/N`. A near-extremal SAS set
becomes a finite measure `μ` on `[0, 1]`. Density `‖μ‖ = c · N^{-1/2}`
(so `c` corresponds to the asymptotic constant). The exception axis
`n*/N =: t* ∈ [0, 2]` carries a Dirac mass in the convolution.

**SAS constraint (continuous form).** With `h(x) := dx/N` the natural
"granularity" measure on `[0, 2]`,

  `(μ * μ)(y) ≤ h(y)` for all `y ∈ [0, 2] \ {t*}`,

i.e. the convolution density is `≤ 1` per unit-length in normalized
coordinates. (After full rescaling by `N^{1/2}`, this is the right
threshold; the lone atom at `t*` is allowed an arbitrary mass `k/N`.)

**Bipartite split.** `μ = μ_- + μ_+` with `μ_-` supported on `[0, 1/2]`,
`μ_+` on `(1/2, 1]`. The three convolutions `μ_-*μ_-`, `μ_+*μ_+`,
`μ_-*μ_+ = μ_+*μ_-` all obey the same `≤ 1`-density constraint off `t*`.

## 2. Lagrangian

Maximize `J(μ) := ‖μ_-‖ + ‖μ_+‖ = ∫_0^{1/2} dμ_- + ∫_{1/2}^1 dμ_+`
subject to

  `g_{--}(y) := 1 − (μ_- * μ_-)(y) ≥ 0` on `[0, 1] \ {t*}`,
  `g_{++}(y) := 1 − (μ_+ * μ_+)(y) ≥ 0` on `[1, 2] \ {t*}`,
  `g_{-+}(y) := 1 − (μ_- * μ_+)(y) ≥ 0` on `[1/2, 3/2] \ {t*}`,
  `μ_-, μ_+ ≥ 0`.

Introduce non-negative Lagrange multipliers `λ_{--}, λ_{++}, λ_{-+}`
(measures on the respective intervals; KKT slackness will pin them down)
and non-negative "non-negativity" multipliers `ν_-, ν_+` on `[0, 1/2]`
and `(1/2, 1]`. The Lagrangian is

  `L = ‖μ_-‖ + ‖μ_+‖`
     `− ⟨λ_{--}, μ_- * μ_- − 1⟩`
     `− ⟨λ_{++}, μ_+ * μ_+ − 1⟩`
     `− ⟨λ_{-+}, μ_- * μ_+ − 1⟩`
     `+ ⟨ν_-, μ_-⟩ + ⟨ν_+, μ_+⟩`.

## 3. Euler–Lagrange equations

Take `δL/δμ_-(x)` at `x ∈ [0, 1/2]`. Using `δ/δμ_-(x) [μ_-*μ_-](y)
= 2 μ_-(y − x)` and `δ/δμ_-(x) [μ_-*μ_+](y) = μ_+(y − x)`:

  **(EL−)**: `1 − 2(λ_{--} * μ_-)(x) − (λ_{-+} * μ_+)(x) + ν_-(x) = 0`,
            for `x ∈ [0, 1/2]`.

Symmetrically,

  **(EL+)**: `1 − 2(λ_{++} * μ_+)(x) − (λ_{-+} * μ_-)(x) + ν_+(x) = 0`,
            for `x ∈ (1/2, 1]`.

KKT complementary slackness:

  `λ_{--}(y) · g_{--}(y) = 0`, `λ_{++}(y) · g_{++}(y) = 0`,
  `λ_{-+}(y) · g_{-+}(y) = 0`, `ν_±(x) · μ_±(x) = 0`.

The convolutions in (EL±) here are "backwards" convolutions: e.g.
`(λ_{--} * μ_-)(x) = ∫ λ_{--}(x + z) dμ_-(z)`, viewed as an integral
over the support of the active constraint.

## 4. Reading the Euler–Lagrange system

**Saturation interpretation.** `λ_{--}` is supported on the
*saturation set* `S_{--} := { y : (μ_-*μ_-)(y) = 1 }`. (EL−) at a
point `x ∈ supp(μ_-)` (where `ν_-(x) = 0`) becomes a *balance*:

  `2 ∫_{S_{--}} λ_{--}(x + z) dμ_-(z) + ∫_{S_{-+}} λ_{-+}(x + z) dμ_+(z) = 1`.

So at every point of `μ_-`'s support, the "shadow cost" of moving mass
locally is exactly 1. This is the optimality condition: no local
perturbation of `μ_-` near `x` can increase `‖μ_-‖`.

**Consequence 1 (saturation must be heavy).** Integrating (EL−)
against `dμ_-(x)`:

  `‖μ_-‖ = 2 ∫_{S_{--}} λ_{--}(y) (μ_-*μ_-)(y) dy + ∫_{S_{-+}} λ_{-+}(y) (μ_-*μ_+)(y) dy`
        `= 2 λ_{--}(S_{--}) + λ_{-+}(S_{-+})`

(using complementary slackness so the convolutions equal 1 on the
respective saturation sets). Symmetrically `‖μ_+‖ = 2 λ_{++}(S_{++})
+ λ_{-+}(S_{-+})`. So:

  `J = ‖μ_-‖ + ‖μ_+‖ = 2 λ_{--}(S_{--}) + 2 λ_{++}(S_{++}) + 2 λ_{-+}(S_{-+})`.

The objective equals twice the total Lagrange-multiplier mass.

**Consequence 2 (sumset cover).** `S_{--}, S_{++}, S_{-+}` are the
*essential supports* of the three convolutions. Their union lies in
`[0, 2]`. If each were full Lebesgue, the multiplier masses would total
≤ `2`, giving `J ≤ 4`, i.e. `c ≤ 4` — far too weak. The real
restriction comes from the *granularity* `≤ 1`-density (the constraint
is *per-point*, not integrated).

## 5. Does the system force EF support `[0, 1/3]`?

Plug in the EF ansatz `μ_- = ρ · 1_{[0, 1/3]}` for the Lebesgue density
`ρ` ("uniform Sidon limit"). Then:

- `μ_- * μ_-` is a tent on `[0, 2/3]` with peak `ρ²/3`. Saturation at
  the peak demands `ρ²/3 = 1`, so `ρ = √3`, giving `‖μ_-‖ = √3/3 =
  1/√3`. Likewise `‖μ_+‖ = 1/√3`, so `c = 2/√3`. **Matches the
  conjecture.**

- `λ_{--}` supported where the tent is at its peak — a single point
  (the apex). KKT places a Dirac at that apex; (EL−) then becomes
  `1 = 2 ρ λ_{--}^{apex}`, fixing `λ_{--}^{apex} = 1/(2√3)`. Consistent.

- The cross convolution `μ_- * μ_+` is supported on `[1/2, 4/3]`. Its
  peak (under EF reflection symmetry around `1/2`) is at `t* = 1`,
  with mass `k/N` (the exception). On `(1/2, 1) ∪ (1, 4/3)` it is
  *strictly below* the bound — so `λ_{-+} ≡ 0` on the interior. The
  cross constraint is *inactive* off `t*`.

**So far so good.** But: does this *uniquely* solve the EL system?
The pitfall:

**Negative observation.** Take the *√2-corner* ansatz: `μ_-` Lebesgue-
uniform on `[0, 1/2]` with density `√2`, so `‖μ_-‖ = √2/2 = 1/√2`,
likewise for `μ_+`. Then `c = √2`. The tent of `μ_-*μ_-` has peak
`(√2)²·(1/2) = 1` exactly — saturated *on a set of measure zero* (just
the apex at `y = 1/2`). The EL conditions can be satisfied with a
Dirac `λ_{--}` at `y = 1/2` and `λ_{-+}` Dirac at `t*`. **The
continuous Lagrangian admits BOTH the EF solution `c = 2/√3` AND the
`√2`-uniform solution.**

Why both? Because the *only* constraint forcing saturation on a
positive-measure set is the requirement that the convolution density
hit the bound `≤ 1` on a fat set. The continuous relaxation does not
distinguish a single-point apex from a fat saturation region — the
constraint `(μ*μ)(y) ≤ 1` is pointwise but the *density* of saturation
is invisible to first-order optimality.

## 6. The missing ingredient: a second-order / quantization constraint

The discrete SAS condition `r_A(n) ≤ 1` for `n ≠ n*` is an *integer*
constraint: there is no `r_A(n) = 1/2`. The continuous relaxation
loses this. To recover the asymmetry between EF and √2-uniform:

**Quantization heuristic.** In the discrete problem, the contribution
of each `(a, b)` pair to `r_A(a + b)` is `1`, not infinitesimal. So
the natural constraint is not `(μ*μ)(y) ≤ 1` pointwise but rather

  `∫_I (μ*μ)(y) dy ≤ |I|` for *every* sub-interval `I` of length ≥ ε,

with `ε ≈ 1/N` setting the discrete resolution. This is the BV
("bounded variation") / fat-support refinement. The √2-uniform
solution violates this: `μ*μ ≡ √2 · √2 · y = 2y` on `[0, 1/2]`, which
near `y = 1/2` exceeds 1 on a set of positive density when discretized.

**Adding the BV constraint to the Lagrangian** introduces a multiplier
on *intervals*, not just points. The new EL equation gains a term
`(λ_{BV} * 1_{[0,ε]})(x)` which acts as a smoothing penalty. Solving
the smoothed EL system forces the support of `μ_-` to *shrink* —
heuristically, away from the midpoint `1/2`, because pushing mass
toward `1/2` increases `μ_- * μ_-` near `1` and violates the BV bound
asymmetrically.

This is plausible but not rigorous. The honest verdict: the BV
constraint is *equivalent* to the discrete rigidity conjecture; we
have re-derived rigidity, not proved it.

## 7. Verdict

**Result.** The naive variational principle (Lagrangian on measures
with pointwise convolution bound) **does not force EF support**. Both
the EF extremizer (`c = 2/√3`) and the √2-uniform "ghost" extremizer
(`c = √2`) satisfy the same Euler–Lagrange system.

**Diagnosis.** The continuous relaxation drops the integer constraint
`r_A ∈ ℤ_{≥0}`. The lost information is exactly the *bipartite
rigidity* meta-obstruction identified by the 11 attacks.

**What would close the gap.** A *fat-saturation* / BV refinement:
require `(μ*μ)` to satisfy a uniform sub-interval bound, not just a
pointwise bound. This is plausibly equivalent to the discrete
quantization and re-encodes the rigidity conjecture; it does not
constitute an independent proof.

**Recommendation.** Variational methods give the right answer at the
EF critical point but cannot rule out the √2 ghost without the BV /
quantization input. Combine with the computer-search evidence
(`computer-search-report.md`, `random-restart-report.md`,
`asymmetric-report.md`): no √2-uniform witness exists at `N ≤ 10^4`,
so the ghost is a continuous artifact. Proving its non-existence in
the discrete problem is *equivalent to* the SAS bipartite rigidity
conjecture.

**Status: same meta-obstruction as the 11 prior attacks** — the
variational method is *not* L^p-averaged (good) and *not* translation-
invariant (good), but it *is* dimensionally blind to the discrete
quantization, which is the precise content of the rigidity conjecture.
