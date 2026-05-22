# Applying Ortega–Prendiville-style Rigidity to the SAS Midpoint Split

**Worked calculation, 2026-05-22.** Companion to `density-profile-attack.md`,
`rigidity-survey.md`, and `below-sqrt2.md`. Investigates whether adding the
Ortega–Prendiville (OP) Fourier-uniformity rigidity hypothesis to the
midpoint-split density-profile attack closes the `1/4` slack at
$\alpha=\beta=1/2$ identified in (D-9-corr).

**Reference:** M. Ortega, S. Prendiville, *Extremal Sidon Sets are Fourier
Uniform*, J. Théor. Nombres Bordeaux 35 (2023). arXiv:2110.13447.

## 0. Executive summary

Three layers of rigidity are considered. Their consequences for the SAS
upper bound constant $c$:

| Rigidity hypothesis | New constraint | Final $c$ |
|---|---|---|
| OP-(a) distributional only ($A_\pm$ Fourier-uniform) | reverts (D-9-corr) to (D-9), but same slack | $\sqrt 2$ (no improvement) |
| OP-(a) + cross convolution = trapezoid | (D-9-OP) below | $\sqrt 2$ (still slack $1/4$ at $\alpha=\beta=1/2$) |
| OP-(b) positional ($A_\pm$ close to EF $B \cup (N-B)$, $B \subset [N/3]$) | forces $\alpha, \beta \le 1/3 + o(1)$ | $2/\sqrt 3 + o(1)$ |

**Headline boxed constant under the strongest natural OP hypothesis:**

$$
\boxed{\;c \;=\; \sqrt 2 + o(1)\;\text{ (OP distributional)};\qquad c \;=\; \tfrac{2}{\sqrt 3} + o(1)\;\text{ (OP positional, but circular).}\;}
$$

The strong distributional OP hypothesis (Fourier sup-norm bound $|\hat A_\pm(\xi)| \le N^{11/12}$
for $\xi\neq 0$) is **not enough** to close the $1/4$ slack. The slack is
*intrinsic to the integration* and not a deficiency of the cross-density
profile that OP corrects.

The positional version (assuming $A_\pm$ is close to the Erdős–Freud
construction) immediately gives $c=2/\sqrt 3$, but it is essentially
equivalent to assuming the conclusion.

**No "intermediate" constant $c \in (2/\sqrt 3, \sqrt 2)$ is obtained by
distributional OP alone.** The structural obstruction (G3 in
`density-profile-attack.md`) is unaffected by Fourier-uniformity per half.
Genuine progress requires a *joint* rigidity statement on the pair $(A_-, A_+)$
that constrains support intervals (where positional information lives), not
just internal distribution.

---

## 1. The OP hypothesis as a real-space density statement

### 1.1 Statement

**Hypothesis (OP, distributional).** For SAS $A \subseteq [N]$ with
$|A| \ge (1-\varepsilon)\sqrt{2N}$, the halves $A_\pm := A \cap [1, N/2]$ resp.
$A \cap (N/2, N]$ each satisfy

$$
\big|\widehat{1_{A_\pm}}(\xi)\big| \;\le\; N^{1 - 1/12} \;=\; N^{11/12}, \qquad \forall\, \xi \in \tfrac{1}{N}\mathbb{Z}\setminus\{0\}. \tag{OP-F}
$$

Here $\widehat f(\xi) := \sum_{n \in [N]} f(n) e(-\xi n)$ with $e(x) := e^{2\pi i x}$,
following OP's normalisation.

### 1.2 Plancherel translation to discrepancy in APs

By the standard discrepancy-Fourier dictionary: for any AP
$P = \{a, a+q, a+2q, \ldots\} \subseteq [N]$ of length $L$ and common difference $q$,
$$
\Big|\,|A_- \cap P| - \tfrac{L}{N}\cdot|A_-|\,\Big|
\;\le\; \frac{1}{N}\sum_{\xi \neq 0} |\widehat{1_{A_-}}(\xi)|\cdot|\widehat{1_P}(\xi)|.
$$
Combining (OP-F) with the elementary $\sum_\xi |\widehat{1_P}(\xi)| \ll qL\log N$:
$$
\big|\,|A_- \cap P| - \tfrac{L}{N}|A_-|\,\big| \;\ll\; N^{-1/12}\cdot qL\log N. \tag{OP-D}
$$
For *macroscopic* APs with $qL \le N$ and $L \ge N^{1/2 + 1/12}$, the error
$N^{-1/12}qL \log N \le N^{11/12}\log N$ is dwarfed by the main term
$L|A_-|/N \asymp L/\sqrt{N}$ whenever $L \gg N^{1/2 + 1/12}\log N$.

**Net statement:** $A_-$ is equidistributed in every macroscopic interval/AP
of length $\gtrsim N^{7/12 + o(1)}$, with relative error $N^{-1/12+o(1)}$.
This *quantitatively* upgrades [EF, Lemma 1].

## 2. Re-deriving the within-half density profile under OP

Under (OP-D), the count of $A_-$ in any window $[v, v + hN] \subseteq [1, \alpha N]$
with $h \ge N^{-5/12+o(1)}$ equals
$$
|A_- \cap [v, v+hN]| \;=\; (1 + O(N^{-1/12}))\cdot \tfrac{hN}{\alpha N}\cdot|A_-|
\;=\; \tfrac{h\, |A_-|}{\alpha} \cdot (1 + O(N^{-1/12})).
$$

Erdős–Freud Lemma 3 then upgrades (with explicit error) from
$$
d_-(v) \;=\; \frac{\min(v, 2\alpha N - v)}{2\alpha N}
$$
(the symmetric triangular profile, max $1/2$ at $v=\alpha N$, vanishing at the
endpoints) to the *quantitative* version
$$
d_-(v) \;=\; \frac{\min(v, 2\alpha N - v)}{2\alpha N}\cdot (1 + O(N^{-1/12})) \tag{D-2-OP}
$$
valid in any macroscopic window. **No qualitative change** from (D-2); OP just
makes the EF profile rigorous beyond the strict $(1+o(1))$-extremality regime
identified in gap G1 of `density-profile-attack.md`.

**Gain over the bare (D-2):** the profile is robust to having $|A_-|$ a few
$o(\sqrt{\alpha N})$ off extremal — this closes Gap (G1).

## 3. Re-deriving the cross-density profile under OP

This is where the G2 correction in `density-profile-attack.md` lived.
**Critical recap:** the naive convolution profile (D-4) is the *multiplicity*
$r_\times(v) = (1_{A_-} * 1_{A_+})(v)$. SAS at the value level forces
$r_\times(v) \le 1$ for $v \neq n^*$, so the *value-density* (the indicator
$\mathbf 1\{v \in S_\times\}$ averaged over a window) is
$\sqrt{\alpha\beta}/(\alpha+\beta)$ — the *constant indicator*, not the trapezoid.

### 3.1 OP says the multiplicity profile IS the trapezoid

Under (OP-F), the joint statistics of $A_-$ and $A_+$ are
quasi-independent: for any window of length $h N$ centered at $v$,
$$
\sum_{n \in [v, v+hN]} r_\times(n) \;=\; \rho_-\rho_+ \cdot \int_{[v, v+hN]} \ell(u)\,du \cdot (1 + O(N^{-1/12})), \tag{C-OP}
$$
where $\ell(v) = |J(v)|$ from §4 of `density-profile-attack.md`, and
$\rho_\pm = 1/\sqrt{\alpha N}$, $1/\sqrt{\beta N}$.

In other words: OP rigidity says the convolution is *exactly* the trapezoid up
to $N^{-1/12}$ error, in a quantitative sense.

### 3.2 The forced tension with SAS

Two formulae for the same multiplicity:

- **OP/Fourier**: $r_\times(v) \approx \ell(v)/(N\sqrt{\alpha\beta})$, peak height
  $\sqrt{\min(\alpha,\beta)/\max(\alpha,\beta)} \le 1$.
- **SAS value-level**: $r_\times(v) \le 1$ for $v \neq n^*$, equality at $n^*$.

These coexist iff the trapezoid peak $\le 1$, which is automatic. **OP does
not introduce a new constraint at $\alpha=\beta$**, because the trapezoid peak
is exactly $1$ when $\alpha = \beta$ — saturating SAS but not violating it.

### 3.3 *Where* on the trapezoid the peak sits

At $\alpha = \beta = 1/2$: the cross-sumset support is $(N/2, 3N/2]$ of length
$N$; the trapezoid ramps up on $(N/2, N]$, peaks at $v = N$, ramps down on
$[N, 3N/2]$. **The trapezoid plateau degenerates to a single point at $v = N$.**

But $v = N = n^*$ is *exactly* the SAS exceptional value where multiplicity is
unrestricted. So the cross-multiplicity is allowed to be large precisely at the
one point where OP says it's largest. **No contradiction.**

This is the structural reason why distributional OP rigidity cannot break the
$\sqrt 2$ barrier at $\alpha = \beta = 1/2$: the only point where the
multiplicity profile saturates the trapezoid is the SAS-exempt point $n^*$.

## 4. Re-doing the integrated constraint under OP

### 4.1 Pointwise version

Under OP, both within-half and cross are quantitatively governed by their
EF/trapezoid profiles. The SAS pointwise constraint for $v \neq n^*$,
$$
d_-(v) + d_+(v) + r_\times(v) \;\le\; 1,
$$
becomes, in the $S_-$-vs-$S_\times$ overlap $((1-\beta)N, 2\alpha N]$ (away
from $n^*$):
$$
\underbrace{\big(1 - \tfrac{v}{2\alpha N}\big)}_{d_-(v)}
\;+\; \underbrace{\tfrac{v - (1-\beta)N}{N\sqrt{\alpha\beta}}}_{r_\times(v)\, \text{[OP trapezoid]}}
\;\le\; 1 + O(N^{-1/12}). \tag{D-5-OP}
$$

(Compare (D-6) of `density-profile-attack.md`, which is the same inequality.
Under OP rigidity this becomes a quantitative *equality up to* $N^{-1/12}$,
not just a soft bound.)

### 4.2 Integration

Identical to the calculation in §6.5 of `density-profile-attack.md`. Setting
$\tau := 2\alpha+\beta-1$ (overlap width fraction):
$$
\frac{\tau}{4\alpha} \;+\; \frac{\tau}{2\sqrt{\alpha\beta}} \;\le\; 1 + O(N^{-1/12}). \tag{D-9-OP}
$$

At the critical corner $\alpha = \beta = 1/2$, $\tau = 1/2$:
$$
\frac{1/2}{2} \;+\; \frac{1/2}{2\cdot 1/2} \;=\; \tfrac14 + \tfrac12 \;=\; \tfrac34 \;\le\; 1.
$$
**Slack $1/4$, same as before.** OP rigidity does **not** improve the
constraint at the symmetric corner.

### 4.3 Why doesn't OP help?

The slack at $\alpha=\beta=1/2$ comes from the fact that $d_-(v) + r_\times(v) = v/N$
on the overlap, ranging from $1/2$ to $1$. The constraint $\le 1$ is
attained **only at $v=N=n^*$** — the one point OP and SAS both exempt.

The function is linear in $v$, so its integral over the overlap of length
$N/2$ is $\int_{N/2}^N (v/N)\, dv = N \cdot 3/8 = 3N/8$, against the available
$\tau N = N/2$. Slack $N/8$, or $1/4$ relative to overlap length. **This slack
is geometric (linear function with maximum at $n^*$), not statistical.** No
finer Fourier control over $A_-$, $A_+$ can change the linear shape of
$d_- + r_\times$ as a function of $v$.

## 5. The pointwise check at the corner: detailed

At $\alpha = \beta = 1/2$, overlap is $[N/2, N]$. In this interval:

- $d_-(v) = 1 - v/N$ — drops from $1/2$ at $v=N/2$ to $0$ at $v=N$.
- $r_\times^{\rm OP}(v) = (v - N/2)/(N \cdot 1/2) = 2v/N - 1$ — rises from $0$
  at $v=N/2$ to $1$ at $v=N$.

Sum: $d_- + r_\times = v/N$. **Linear interpolation between $1/2$ and $1$.**

For $v \in [N/2, N - 1]$, $d_- + r_\times = v/N \le (N-1)/N < 1$, so SAS
satisfied with room to spare.

At $v=N$: $d_- + r_\times = 1$, but this is $n^*$, SAS-exempt.

**Verdict: pointwise SAS gives no obstruction in the overlap at $\alpha=\beta=1/2$.**
This is consistent with the EF construction: the EF set
$B \cup (N-B)$ for $B \subset [1, N/3]$ Sidon has *all* cross-sums equal to
$N$, so the cross-multiplicity profile is a $\delta$-function at $v=N$ —
exactly the SAS-exempt point.

## 6. Where the positional ((b)) part of the hypothesis would help

If we strengthen the hypothesis to **positional rigidity**, i.e., $A_-$ is
$o(1)$-close in symmetric difference to a Sidon $T_- \subset [1, \alpha N]$
*of EF form*, where $T_- = B \subset [1, N/3]$, then:

- $\max A_- \le N/3 + o(N)$, hence $\alpha \le 1/3 + o(1)$.
- By symmetry, $\beta \le 1/3 + o(1)$ (with $A_+$ close to $N - B$).
- $|A| \le \sqrt{\alpha N} + \sqrt{\beta N} \le 2\sqrt{(1/3)N}\cdot (1 + o(1)) = \frac{2}{\sqrt 3}\sqrt N \cdot (1 + o(1))$.

**This is the boxed conditional from `density-profile-attack.md` (Section 0).**
But it *assumes* the positional shape, which is precisely the SAS rigidity
conjecture.

## 7. Quantifying the minimum rigidity needed

To close the slack and reach $c < \sqrt 2$, the integration in §4 needs
$d_- + r_\times \le 1 - \delta$ pointwise for some $\delta > 0$ on a positive
fraction of the overlap. Under distributional OP this cannot happen because
the sum is the linear function $v/N$ — its only solution involves *bending*
either $d_-$ or $r_\times$ away from the EF/trapezoid prediction.

**The minimum rigidity needed** is therefore something *beyond* what
distributional OP provides — a constraint that says: "the cross-multiplicity
cannot put mass close to $n^*$ except via the EF reflection structure."

Concretely, one would want a statement like:

> **(Conjectured rigidity, strictly stronger than OP-(a)):** if $A_\pm$ are
> SAS halves with $|A_-|, |A_+| \ge (1-\varepsilon)\sqrt{N/2}$, then either
> $\alpha + \beta \le 2/3 + O(\varepsilon)$, or there exist
> $\Omega(N^{1/2 - \delta})$ pairs $(a, b) \in A_- \times A_+$ with $a + b \neq n^*$
> *clustering on a single secondary value*, violating SAS.

This is precisely what `pikhurko-adaptation.md` calls the "bipartite Fourier
gap-deficit" target, and what `rigidity-survey.md` §C identifies as Step
3 → 4 of the OP-adaptation programme. It is *not* a corollary of
distributional Fourier uniformity per half; it requires *correlated* Fourier
information across the pair $(A_-, A_+)$.

## 8. An honest intermediate constant via a quantitative OP variant

Suppose we have a *partial* positional rigidity:

> **Hypothesis (OP-medium):** at least one of $\alpha, \beta$ satisfies
> $\alpha \le 1/2 - \delta$ for some explicit $\delta > 0$.

By concavity of $\sqrt\cdot$ and the constraint $\alpha, \beta \le 1/2$,
$$
|A| / \sqrt N \;\le\; \sqrt{1/2-\delta} + \sqrt{1/2} \;=\; \sqrt{1/2}\left(\sqrt{1 - 2\delta} + 1\right).
$$
For $\delta = 1/6$ (which corresponds to one half being at most $1/3$),
$$
c \;\le\; \sqrt{1/2}\cdot\left(\sqrt{2/3} + 1\right) \;=\; \tfrac{1}{\sqrt 2}\big(\sqrt{2/3} + 1\big) \;\approx\; 0.7071 \cdot 1.8165 \;\approx\; 1.284.
$$

For $\delta = 1/12$ (the natural OP error scale):
$$
c \;\le\; \sqrt{1/2}\cdot\left(\sqrt{5/6} + 1\right) \;=\; \tfrac{1}{\sqrt 2}(0.9129 + 1) \;\approx\; 0.7071 \cdot 1.9129 \;\approx\; 1.353.
$$

This *is* in the target range $c \in (2/\sqrt 3, \sqrt 2) \approx (1.155, 1.414)$.

**The catch:** OP-medium has no proof. The distributional OP hypothesis
**does not imply** OP-medium: a set can be Fourier-uniform on $[1, \alpha N]$
with $\alpha = 1/2$ without being concentrated to a smaller interval.

The simplest scenario where OP-medium might be forced is: if the cross-pair
count to $n^*$ is forced (by Plancherel + SAS at value level) to be
$\le k_0 < |A_-|$, then $A_-$ cannot "use up" its full support density to
match elements of $A_+$, so the effective interval shrinks. But this requires
the bipartite Plancherel calculation hinted at in
`rigidity-survey.md` §C, step 4.

## 9. Final assessment

### 9.1 What OP-distributional achieves

- **Closes Gap (G1)** of `density-profile-attack.md`: the EF density profile
  now holds quantitatively, robust to sub-extremal halves up to $N^{-1/12}$.
- **Closes Gap (G2)**: the cross-multiplicity profile IS the trapezoid (with
  quantitative error), and SAS imposes $r_\times \le 1$ pointwise compatibly.
- **Does NOT close Gap (G3)**: the integrated constraint at $\alpha=\beta=1/2$
  has slack $1/4$, which is *geometric* (linear sum saturating only at
  $n^*$), not statistical.

### 9.2 Final constant under OP-distributional

$$
\boxed{\;c \;\le\; \sqrt 2 + o(1)\;\text{ (no improvement).}\;}
$$

### 9.3 Final constant under OP-positional

$$
\boxed{\;c \;\le\; \tfrac{2}{\sqrt 3} + o(1) \;\approx\; 1.1547 \;\text{ (but circular).}\;}
$$

### 9.4 Conjectural intermediate

If OP-medium (forced asymmetry, one half supported on $\le (1/2-\delta)N$)
can be derived from a *bipartite* OP-style argument (not done here):

$$
c \;\le\; \tfrac{1}{\sqrt 2}\big(\sqrt{1 - 2\delta} + 1\big),
$$

quantitatively $c \approx 1.35$ for $\delta = 1/12$, $c \approx 1.28$ for
$\delta = 1/6$. **This is the most plausible target for a real
sub-$\sqrt 2$ result.**

---

## Appendix A: Plancherel sanity checks

**A.1** Energy identity: $\sum_v r_\times(v)^2 = \|1_{A_-} * 1_{A_+}\|_2^2
= \frac{1}{N}\sum_\xi |\widehat{1_{A_-}}(\xi)|^2 |\widehat{1_{A_+}}(\xi)|^2$.

Main term ($\xi = 0$): $\frac{1}{N}|A_-|^2 |A_+|^2 = \frac{1}{N}(\alpha N)(\beta N) = \alpha\beta N$.

OP error: $\frac{1}{N}\sum_{\xi\neq 0} |\widehat{1_{A_-}}|^2 |\widehat{1_{A_+}}|^2
\le \frac{1}{N}\|\widehat{1_{A_-}}\|_\infty^2 \cdot \sum_\xi |\widehat{1_{A_+}}|^2
= \frac{1}{N} N^{11/6} \cdot N |A_+| = N^{11/6}|A_+| \approx N^{11/6 + 1/4}\sqrt\beta$.

For $|A_+| = \sqrt{\beta N} \approx N^{1/2}$, error is $N^{11/6} \cdot N^{1/2} = N^{14/6} = N^{7/3}$, dominating the main term $\alpha\beta N \sim N$.

**This naive Plancherel bound is too weak.** A sharper variant of OP (perhaps
the improved Cilleruelo-version error $N^{-1/4}$ mentioned in
`rigidity-survey.md`) is needed for the Plancherel route to give nontrivial
info. We do not pursue this here.

**A.2** Cross-pair count at $n^*$:
$$
k = r_\times(n^*) = (1_{A_-} * 1_{A_+})(n^*) = \frac{1}{N}\sum_\xi \widehat{1_{A_-}}(\xi)\overline{\widehat{1_{A_+}}(\xi)} e(-\xi n^*).
$$
Main term: $\frac{1}{N}|A_-||A_+| = \sqrt{\alpha\beta}\cdot N^{1/2}$. Hmm —
this says the *average* cross-multiplicity is $O(N^{-1/2})$, vanishing. So
$k$ being large ($\Omega(\sqrt N)$, as needed for the EF construction)
requires the off-zero Fourier coefficients to *concentrate* at frequencies
aligned with $n^*$.

**Under OP-(a) with $|\widehat{1_{A_\pm}}(\xi)| \le N^{11/12}$**, the maximum
contribution from a single non-zero frequency is
$|\widehat{1_{A_-}}\widehat{1_{A_+}}|/N \le N^{22/12 - 1} = N^{10/12} = N^{5/6}$.
For $k = \Omega(\sqrt N) = \Omega(N^{1/2})$ to be achieved, we'd need
$\sim N^{1/2 - 5/6 + 1} = N^{2/3}$ frequencies all contributing constructively —
which is most non-zero frequencies. This is consistent with OP allowing a
generic distribution of Fourier mass, but does not by itself force EF
structure.

**Conclusion of A.2.** The Plancherel/Fourier control under OP-(a) is
*compatible* with $k = \Omega(\sqrt N)$ at $n^* = N$ for $\alpha=\beta=1/2$
— it does not rule out the $\sqrt 2$-extremal configuration.

---

## References

1. M. Ortega, S. Prendiville, *Extremal Sidon Sets are Fourier Uniform, with
   Applications to Partition Regularity*, J. Théor. Nombres Bordeaux 35 (2023).
   arXiv:2110.13447.
2. P. Erdős and R. Freud, *On sums of a Sidon-sequence*, J. Number Theory **38**
   (1991), 196–205.
3. `density-profile-attack.md`, this directory: source of (D-9), (D-9-corr),
   and gaps (G1), (G2), (G3).
4. `rigidity-survey.md`, this directory: identifies OP as nearest-miss and
   sketches the adaptation programme in §C.
5. `below-sqrt2.md`, this directory: roadmap of attempted sub-$\sqrt 2$
   strategies; identifies Freiman-style structural rigidity as the right
   conditional.
6. `pikhurko-adaptation.md`, this directory: prior Fourier attempt (Attempt A,
   bipartite gap-deficit).
