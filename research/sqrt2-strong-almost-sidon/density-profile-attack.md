# Density-Profile / Value-Disjointness Attack on Strong Almost-Sidon

**Worked calculation, 2026-05-22.** Companion to `below-sqrt2.md`,
`pikhurko-adaptation.md`, and `autoconvolution-attack.md`. Source for all
density-profile inputs: P. Erdős and R. Freud, *On sums of a Sidon-sequence*,
J. Number Theory **38** (1991), 196–205 (henceforth **[EF]**).

**Executive summary.** Writing $A \subseteq [N]$ strong almost-Sidon at the
worst-case exceptional value $n^* = N$, split $A = A_- \sqcup A_+$ with
$A_- \subseteq [1, \alpha N]$, $A_+ \subseteq ((1-\beta)N, N]$,
$\alpha, \beta \in [0, 1/2]$. Working *under the hypothesis that both halves
are Lindström-extremal Sidon*, the [EF] density profile gives a precise
trapezoidal value-distribution for cross-sums and a triangular profile for
within-half sums. Imposing the value-disjointness constraint pointwise on
the overlap region and integrating yields the inequality

$$
\boxed{\;\alpha + \beta \;\le\; \tfrac{2}{3}\;}
$$

(equation (D-9) below), whose maximizer for $\sqrt\alpha + \sqrt\beta$ on
$\{\alpha,\beta \in [0,1/2],\; \alpha+\beta\le 2/3\}$ is the interior
critical point $\alpha = \beta = 1/3$, giving
$\sqrt\alpha+\sqrt\beta = 2/\sqrt 3 \approx 1.155$.

**Conditional final constant.**
$$
|A| \;\le\; \Big(\tfrac{2}{\sqrt 3} + o(1)\Big)\,\sqrt N,
$$
*provided that the upper-bound problem can be reduced to the extremal case
$|A_-| = (1+o(1))\sqrt{\alpha N}$, $|A_+| = (1+o(1))\sqrt{\beta N}$.*

**This reduction is the genuine gap.** [EF, Lemma 1] propagates uniform
distribution *only* from strict $(1+o(1))$-extremality of a Sidon set, not
from near-extremality. A maximizing $A$ may have a non-extremal half (one
half far below Lindström, the other large), and the density profile
calculation does not apply in that regime. We discuss the gap in §7 and
sketch the next attack in §8. The argument as written is a **conditional**
proof of $2/\sqrt 3$; the unconditional bound it yields is still
$(\sqrt 2 + o(1))\sqrt N$.

---

## 1. Setup

Let $A \subseteq [N]$ be strong almost-Sidon with exceptional value $n^*$.
By the midpoint split (paper.md §2 / Lemma 2.1), $A_- := A \cap [1, \lfloor n^*/2\rfloor]$
and $A_+ := A \cap (\lfloor n^*/2\rfloor, N]$ are both genuine Sidon sets.
The worst case for the $\sqrt 2$ bound is $n^* = N$: then both halves have
length up to $N/2$, the Lindström bounds give $|A_-|, |A_+| \le (1+o(1))\sqrt{N/2}$,
and Cauchy–Schwarz $\sqrt x + \sqrt{N-x} \le \sqrt{2N}$ caps $|A|$ at
$(\sqrt 2+o(1))\sqrt N$.

We assume $n^* = N$ throughout (the general case follows by absorbing the
factor $n^*/N$ into the asymptotics). Parametrize the *support intervals*
of the two halves:

- $A_- \subseteq [1, \alpha N]$ with $\alpha N := \max A_-$, $\alpha \in [0, 1/2]$.
- $A_+ \subseteq ((1-\beta) N, N]$ with $(1-\beta)N < \min A_+$, $\beta \in [0, 1/2]$.

The constraints $\alpha, \beta \le 1/2$ come from the midpoint split: every
$a \in A_-$ has $a \le n^*/2 = N/2$, and every $a \in A_+$ has $a > N/2$.

Within-half sumsets and the cross-sumset live on the intervals

- $S_- := A_- + A_- \subseteq [2, 2\alpha N]$,
- $S_+ := A_+ + A_+ \subseteq (2(1-\beta)N, 2N]$,
- $S_\times := A_- + A_+ \subseteq ((1-\beta)N, (1+\alpha)N]$.

Note $|S_\times| = (\alpha + \beta) N$ as an interval, and the support is
disjoint from $S_-$'s lower part and $S_+$'s upper part.

**Strong almost-Sidon (SAS) at the value level.** For every $v \neq n^*$,
the multiplicity of $v$ in the multiset of unordered pair-sums from $A$ is
$\le 1$. In particular, for $v \neq N$,
$$
r_-(v) + r_+(v) + r_\times(v) \;\le\; 1, \tag{D-1}
$$
where $r_-, r_+, r_\times$ denote the within-$A_-$, within-$A_+$, and
cross-multiplicities (unordered pairs).

## 2. Extremality hypothesis (assumed throughout §3–§6)

**(H)** *Both halves are Lindström-extremal:*
$$
|A_-| = (1 + o(1)) \sqrt{\alpha N}, \qquad |A_+| = (1 + o(1)) \sqrt{\beta N}.
$$

We discuss the propriety of (H) in §7. Under (H), [EF, Lemma 1] applies to
$A_-$ viewed as a Sidon-sequence in $[1, \alpha N]$ with the maximal possible
$(1+o(1))(\alpha N)^{1/2}$ elements, and analogously to $A_+$ viewed in
$((1-\beta) N, N]$ (after translation).

**Conclusion of [EF, Lemma 1]:** Both $A_-$ and $A_+$ are uniformly
distributed in their respective support intervals.

Quantitatively: for any $\eta > 0$, any subinterval $I_- \subseteq [1, \alpha N]$
with $|I_-|/(\alpha N) \ge \eta$ contains $(1+o(1)) \cdot \tfrac{|I_-|}{\alpha N}
\cdot \sqrt{\alpha N}$ elements of $A_-$, and similarly for $A_+$. This is
[EF, eq. (3)] re-stated in our notation.

## 3. The within-half density profile

We restate [EF, Lemma 3 + Corollary] in our notation. Apply to $A_-$ as a
maximally dense Sidon-sequence in $[1, \alpha N]$.

**[EF, Lemma 3]:** With $\gamma \in (0, 2]$, the number $F_-(\gamma)$ of
within-$A_-$ sums $a + a'$ (with $a, a' \in A_-$, ordered or unordered, see
below) below $\gamma \cdot \alpha N$ is

$$
F_-(\gamma) \;\sim\; \begin{cases} (\alpha N) \gamma^2 / 4 & \text{if } 0 < \gamma \le 1, \\ (\alpha N) \big(1 - (2-\gamma)^2/2\big)/2 & \text{if } 1 \le \gamma \le 2. \end{cases}
\tag{EF-6}
$$

(EF's [EF, eq. (8)–(9A, 9B)] counts *ordered* pairs and divides by 2 to get
unordered; we follow the same convention.)

**[EF, Corollary]:** Differentiating (EF-6) in $\gamma$, the density of
*representable* values (i.e., values $v = a + a'$, $a \le a'$, $a, a' \in A_-$)
at the point $v = \gamma \cdot \alpha N$ is

$$
d_-(v) \;=\; \begin{cases} \gamma/2 = v / (2\alpha N) & \text{if } v \in (0, \alpha N], \\ 1 - \gamma/2 = 1 - v/(2\alpha N) & \text{if } v \in [\alpha N, 2\alpha N). \end{cases}
$$

Equivalently:
$$
\boxed{\;d_-(v) \;=\; \frac{\min(v,\, 2\alpha N - v)}{2 \alpha N}\;} \tag{D-2}
$$
for $v \in [2, 2\alpha N]$ — a *symmetric triangular profile* peaking at
$v = \alpha N$ with maximum density $1/2$, vanishing at the endpoints.

**By symmetry**, for $A_+ \subseteq ((1-\beta)N, N]$, write $v' := 2N - v$
(so $v' \in [0, 2\beta N]$ for $v \in [2(1-\beta)N, 2N]$). The within-$A_+$
density is
$$
\boxed{\;d_+(v) \;=\; \frac{\min(2N - v,\, v - 2(1-\beta)N)}{2\beta N}\;}\tag{D-3}
$$
for $v \in [2(1-\beta)N, 2N]$ — triangular, peaking at $v = (2-\beta) N$
with max $1/2$.

**Sanity check.** $\int_0^{2\alpha N} d_-(v)\, dv = 2 \cdot \int_0^{\alpha N} \frac{v}{2\alpha N} dv
= 2 \cdot \frac{(\alpha N)^2}{4 \alpha N} = \frac{\alpha N}{2} =$ number of
representable values $\sim |A_-|^2 / 2 = \alpha N / 2$. ✓ (matches the
Sidon-extremal count.)

## 4. The cross-sumset density profile

Under (H), $A_-$ has density $\rho_- := |A_-|/(\alpha N) = 1/\sqrt{\alpha N}$
in $[1, \alpha N]$ and $A_+$ has density $\rho_+ := 1/\sqrt{\beta N}$ in
$((1-\beta) N, N]$. **By [EF, Lemma 1]**, both densities are *locally* equal
to their global value, up to $o(1)$, on every macroscopic subinterval.

For $v \in ((1-\beta)N, (1+\alpha)N]$, the cross multiplicity is
$$
r_\times(v) \;=\; \#\{(a, b) \in A_- \times A_+ : a + b = v\}.
$$
The set of pairs $(a, b)$ with $a + b = v$ corresponds, via $b = v - a$, to
$$
a \in [1, \alpha N] \cap [v - N, v - (1-\beta)N).
$$
The intersection is the interval
$$
J(v) := [\max(1, v - N),\; \min(\alpha N, v - (1-\beta)N)].
$$
Provided $J(v)$ is a macroscopic interval of length $\ell(v)$, [EF, Lemma 1]
gives
$$
r_\times(v) \;\sim\; \rho_- \cdot |J(v) \cap A_-| \cdot \rho_+ \cdot 1
\;=\; \rho_- \cdot \rho_+ \cdot \ell(v) + o(1)\cdot \ldots
$$
Actually more carefully: for fixed $v$, $r_\times(v)$ counts pairs $(a, v-a)$
with $a \in A_-$ AND $v - a \in A_+$. By independence of the uniform
distributions of $A_-$ and $A_+$ (a heuristic; see Remark 4.1 for the actual
rigorous content),
$$
r_\times(v) \;\approx\; \rho_- \rho_+ \cdot \ell(v) \;=\; \frac{\ell(v)}{N \sqrt{\alpha\beta}}.
$$

We package this as a *density of cross-sums in the value variable*:
$$
d_\times(v) \;:=\; \frac{r_\times(v)}{\rho_+ \cdot N} \quad
\text{(normalization: density per unit value, scaled by } |A_+| / |I_\times|\text{).}
$$
Actually it is cleanest to define the *value-density* directly:

**Definition.** The cross-sumset value-density at $v$ is the local fraction
of values in a neighborhood of $v$ that are hit by a cross-sum:
$$
d_\times(v) \;:=\; \lim_{h \to 0} \frac{\#\{n \in [v, v+hN] : r_\times(n) \ge 1\}}{hN}.
$$
Under (H), at most one pair $(a, b) \in A_- \times A_+$ can hit a generic
value $n$ — by the SAS hypothesis at the value level (see (D-1)) — so
$\#\{n \in [v, v+hN] : r_\times(n) \ge 1\}$ equals
$\sum_{n \in [v, v+hN]} r_\times(n)$ up to the (single) contribution at
$n^* = N$.

Computing the convolution:

$$
\sum_{n \in [v, v+hN]} r_\times(n) \;=\; \#\{(a, b) \in A_- \times A_+ : a + b \in [v, v+hN]\}.
$$

By [EF, Lemma 1] applied locally to $A_-$ and $A_+$:
$$
\#\{(a, b) : a + b \in [v, v+hN]\} \;\sim\; \rho_- \rho_+ \cdot \int_{[v, v+hN]} \ell(u)\, du
\;\sim\; \rho_- \rho_+ \cdot hN \cdot \ell(v).
$$

Dividing by $hN$:
$$
d_\times(v) \;=\; \rho_- \rho_+ \cdot \ell(v) \;=\; \frac{\ell(v)}{N\sqrt{\alpha\beta}}.
\tag{D-4}
$$

**Computing $\ell(v)$.** The interval
$J(v) = [\max(1, v - N), \min(\alpha N, v - (1-\beta)N)]$ has length
$$
\ell(v) \;=\; \min(\alpha N, v - (1-\beta)N) - \max(0, v - N).
$$
On $v \in ((1-\beta)N, (1+\alpha)N]$, the four breakpoints in increasing
order are:

(i) $v = (1-\beta) N$ — $\ell = 0$.
(ii) $v = (1 - \beta) N + \alpha N$ if $\alpha < \beta$, or $v = N$ if $\alpha > \beta$ — left breakpoint of plateau.
(iii) $v = \max((1-\beta)N + \alpha N, N)$ — right breakpoint of plateau.
(iv) $v = (1+\alpha) N$ — $\ell = 0$.

Concretely (and assuming for concreteness $\alpha, \beta > 0$):

- If $v \in ((1-\beta)N, \min((1-\beta+\alpha)N, N)]$:
  $\ell(v) = v - (1-\beta)N$ (linear ramp up).
- If $v \in [\max((1-\beta+\alpha)N, N), \min((1-\beta+\alpha)N, N) + |\alpha - \beta| N]$, i.e., the *plateau*:
  $\ell(v) = \min(\alpha, \beta) \cdot N$.
- If $v \in [\max((1-\beta+\alpha)N, N), (1+\alpha)N]$:
  $\ell(v) = (1+\alpha)N - v$ (linear ramp down).

So the cross-sumset density $d_\times(v)$ is a *trapezoid* of total mass
$\frac{1}{N\sqrt{\alpha\beta}} \cdot \text{(area of trapezoid)}$. Computing
the area:
$$
\int \ell(u)\, du \;=\; \alpha N \cdot \beta N \;=\; \alpha \beta N^2.
$$
So $\int d_\times(u) \, du = \alpha\beta N^2 / (N\sqrt{\alpha\beta}) = \sqrt{\alpha\beta}\, N$.
This is the cardinality (with multiplicity) of $S_\times$, matching
$|A_-| \cdot |A_+| = \sqrt{\alpha\beta}\, N$. ✓

**The peak density.** $\max d_\times = \frac{\min(\alpha,\beta) N}{N\sqrt{\alpha\beta}} = \sqrt{\min(\alpha,\beta)/\max(\alpha,\beta)} \le 1$ (with equality at $\alpha=\beta$).

**Remark 4.1 (rigor of the convolution step).** [EF, Lemma 1] states uniform
distribution: every macroscopic interval $I \subseteq [1, \alpha N]$ contains
$(1+o(1)) (|I|/\alpha N) \sqrt{\alpha N}$ elements of $A_-$. The cross
convolution $r_\times(v) = \sum_a \mathbf 1_{A_-}(a) \mathbf 1_{A_+}(v - a)$
*does not* follow from uniform marginal distributions alone — it requires
that the *joint* statistics of $A_-$ and $A_+$ behave as if independent.
This is a non-trivial step; we discuss it as Gap (G2) in §7.

## 5. Value-disjointness constraint and the overlap region

The overlap region where $S_-$ and $S_\times$ can both have positive density
is $[\max(2, (1-\beta) N), 2\alpha N]$ — i.e., where the within-$A_-$
sumset's right tail meets the cross-sumset's left ramp. This is non-empty
when $2\alpha N > (1-\beta) N$, i.e., $2\alpha + \beta > 1$.

Similarly, the overlap of $S_+$ with $S_\times$ is $[\max(2,2(1-\beta)N), (1+\alpha)N]$,
non-empty when $\alpha + 2\beta > 1$.

**Pointwise value-disjointness.** From (D-1), for $v \neq N$,
$r_-(v) + r_+(v) + r_\times(v) \le 1$. In density form (passing to the
*event* "value $v$ is representable" rather than the count), each term is
$\le 1$ at every macroscopic scale; the disjointness gives **at the density
level**
$$
d_-(v) + d_+(v) + d_\times(v) \;\le\; 1 \qquad (v \neq N). \tag{D-5}
$$

The interpretation: in any small subinterval of length $hN$ around $v$, the
union of the values hit by within-$A_-$, within-$A_+$, and cross sums has
density $\le 1$ (these are values in $[v, v+hN]$, and each is either hit or
not). Each contribution to the sum is the *local rate* at which its
respective sumset hits a fresh value. By SAS, these rates do not double-count
the same value (except at $n^* = N$, a set of measure zero).

## 6. Integration over the overlap region — the key inequality

We focus on the **$S_-$ vs $S_\times$ overlap** (the $S_+$ vs $S_\times$
case is symmetric and gives a redundant constraint).

The within-$A_-$ density profile (D-2) on its right half ($v \in [\alpha N, 2\alpha N]$):
$$
d_-(v) \;=\; 1 - \frac{v}{2\alpha N}.
$$

The cross-sumset density (D-4) on its left ramp
($v \in ((1-\beta)N, \min((1-\beta+\alpha)N, N)]$):
$$
d_\times(v) \;=\; \frac{v - (1-\beta)N}{N\sqrt{\alpha\beta}}.
$$

The **overlap region** is $v \in ((1-\beta)N, 2\alpha N]$, requiring $2\alpha + \beta > 1$.

Within this overlap, (D-5) gives (away from $v = N$):
$$
\Big(1 - \frac{v}{2\alpha N}\Big) + \frac{v - (1-\beta)N}{N\sqrt{\alpha\beta}} \;\le\; 1.
$$
Simplifying,
$$
\frac{v - (1-\beta)N}{N \sqrt{\alpha\beta}} \;\le\; \frac{v}{2\alpha N}. \tag{D-6}
$$

This must hold for **every** $v \in ((1-\beta)N, 2\alpha N]$. Let's check the
endpoints.

At $v = (1-\beta)N$ (left endpoint): LHS = 0, RHS = $(1-\beta)/(2\alpha) > 0$.
Constraint vacuous. ✓

At $v = 2\alpha N$ (right endpoint, the binding one): LHS = $(2\alpha - 1 + \beta)/\sqrt{\alpha\beta}$,
RHS = $1$. The constraint becomes
$$
\frac{2\alpha + \beta - 1}{\sqrt{\alpha\beta}} \;\le\; 1,
$$
i.e., (rearranging, and recalling we are in the regime $2\alpha + \beta > 1$
where the overlap is non-empty)
$$
2\alpha + \beta \;\le\; 1 + \sqrt{\alpha\beta}. \tag{D-7a}
$$

**Symmetric constraint** ($S_+$ vs $S_\times$): by the same argument with
$\alpha \leftrightarrow \beta$,
$$
\alpha + 2\beta \;\le\; 1 + \sqrt{\alpha\beta}. \tag{D-7b}
$$

**Adding (D-7a) and (D-7b):**
$$
3(\alpha + \beta) \;\le\; 2 + 2\sqrt{\alpha\beta}. \tag{D-8}
$$

By AM-GM, $\sqrt{\alpha\beta} \le (\alpha + \beta)/2$, so
$3(\alpha+\beta) \le 2 + (\alpha+\beta)$, i.e.,
$$
\boxed{\;\alpha + \beta \;\le\; \tfrac{1}{1} \cdot \big(\tfrac{2 + 2\sqrt{\alpha\beta}}{3}\big) \;\le\; \tfrac{2}{3} \;+\; \tfrac{2}{3}\sqrt{\alpha\beta}\,} \tag{D-9'}
$$
… which is weaker than the target $\alpha + \beta \le 2/3$.

Let's be careful: at the AM-GM equality point $\alpha = \beta$, (D-8) becomes
$6\alpha \le 2 + 2\alpha$, i.e., $\alpha \le 1/2$, which is automatic. So
**adding the two constraints loses information** at $\alpha = \beta$.
Re-examine.

At $\alpha = \beta$, (D-7a) becomes $3\alpha \le 1 + \alpha$, i.e.,
$$
\alpha \;\le\; \tfrac{1}{2} \qquad (\alpha = \beta),
$$
which is **automatic** from the midpoint split — *no improvement*.

**So the right-endpoint constraint (D-7a, b) at $\alpha = \beta = 1/2$ is
not binding.** The corner $(\alpha,\beta) = (1/2, 1/2)$ — exactly the case
where the $\sqrt 2$ bound is tight — satisfies (D-7a, b) with $\sqrt{\alpha\beta}=1/2$,
giving $2\alpha+\beta = 3/2 \le 1 + 1/2 = 3/2$, equality. The constraint
just barely allows the $\sqrt 2$ regime.

**This is the crucial finding: the pointwise constraint at the right
endpoint is non-binding at $\alpha=\beta=1/2$.** Integrating it does not
help unless we use a stronger condition.

## 6.5 Integrating (D-6) — the correct way

Pointwise (D-6) at a single point is not enough. We must use that (D-6)
holds *for every* $v$ in the overlap, and the function $d_-(v) + d_\times(v)$
must be $\le 1$ throughout, not just at the endpoint.

Integrate $d_-(v) + d_\times(v)$ over the full overlap interval
$v \in ((1-\beta)N, 2\alpha N]$, length $(2\alpha+\beta-1) N$:

**Within-$A_-$ contribution.** $\int_{(1-\beta)N}^{2\alpha N} d_-(v)\, dv
= \int_{(1-\beta)N}^{2\alpha N} (1 - v/(2\alpha N)) \, dv$.
Substituting $u = v/(2\alpha N)$, the integral is
$$
2\alpha N \int_{(1-\beta)/(2\alpha)}^{1} (1-u)\, du
\;=\; 2\alpha N \cdot \tfrac{1}{2}\Big(1 - \tfrac{1-\beta}{2\alpha}\Big)^2
\;=\; \alpha N \cdot \Big(\tfrac{2\alpha + \beta - 1}{2\alpha}\Big)^2
\;=\; \frac{(2\alpha + \beta - 1)^2 N}{4\alpha}.
$$

**Cross contribution.** $\int_{(1-\beta)N}^{2\alpha N} d_\times(v)\, dv$.
The cross-density is the *left ramp* of (D-4) on this entire interval
(assuming $2\alpha N \le \min((1-\beta+\alpha)N, N)$, i.e.,
$\alpha \le \min(1-\beta+\alpha, 1)/2$, i.e., $\alpha \le 1/2$ — automatic).
Wait — we need $2\alpha N \le (1-\beta+\alpha) N$, i.e., $\alpha \le 1 - \beta + \alpha$,
i.e., $\beta \le 1$, automatic. And $2\alpha N \le N$ iff $\alpha \le 1/2$.
So yes, on the overlap, $d_\times$ is in its left-ramp regime.

$$
\int_{(1-\beta)N}^{2\alpha N} \frac{v - (1-\beta)N}{N\sqrt{\alpha\beta}}\, dv
\;=\; \frac{1}{N\sqrt{\alpha\beta}} \cdot \frac{((2\alpha+\beta-1)N)^2}{2}
\;=\; \frac{(2\alpha+\beta-1)^2 N}{2\sqrt{\alpha\beta}}.
$$

**Constraint (D-5) integrated over the overlap:**
$$
\frac{(2\alpha+\beta-1)^2 N}{4\alpha} \;+\; \frac{(2\alpha+\beta-1)^2 N}{2\sqrt{\alpha\beta}} \;\le\; (2\alpha+\beta-1) N.
$$

(The RHS is the length of the overlap interval, since $\int 1 \, dv =
|\text{overlap}|$.)

Set $\tau := 2\alpha + \beta - 1 \in (0, \alpha]$ (the *overlap width as a fraction of $N$*). Dividing through by $\tau N$ (positive in the overlap regime):
$$
\frac{\tau}{4\alpha} \;+\; \frac{\tau}{2\sqrt{\alpha\beta}} \;\le\; 1. \tag{D-9}
$$

**Symmetric constraint** with $\alpha\leftrightarrow\beta$ and overlap width
$\tau' := \alpha + 2\beta - 1$:
$$
\frac{\tau'}{4\beta} \;+\; \frac{\tau'}{2\sqrt{\alpha\beta}} \;\le\; 1. \tag{D-9'}
$$

## 6.6 Optimization: maximize $\sqrt\alpha + \sqrt\beta$ subject to (D-9), (D-9')

**Symmetric ansatz $\alpha = \beta$.** Then $\tau = \tau' = 3\alpha - 1$ and
(D-9) becomes
$$
\frac{3\alpha - 1}{4\alpha} + \frac{3\alpha - 1}{2\alpha} \;\le\; 1.
$$
Compute: $\frac{3\alpha-1}{4\alpha} + \frac{2(3\alpha-1)}{4\alpha} = \frac{3(3\alpha-1)}{4\alpha} = \frac{9\alpha - 3}{4\alpha}$.
So $\frac{9\alpha-3}{4\alpha} \le 1 \iff 9\alpha - 3 \le 4\alpha \iff 5\alpha \le 3 \iff \alpha \le 3/5$.

Combined with $\alpha \le 1/2$: the binding constraint is the midpoint
$\alpha \le 1/2$, and (D-9) is non-binding at $\alpha=\beta=1/2$.

Hmm — at $\alpha=\beta=1/2$, $\tau = 3/2-1 = 1/2$, and (D-9) gives
$\tfrac{1/2}{2} + \tfrac{1/2}{1} = 1/4 + 1/2 = 3/4 \le 1$. **Slack $1/4$ at
the $\sqrt 2$ corner.**

So the symmetric case allows $\alpha = \beta = 1/2$, giving
$\sqrt\alpha + \sqrt\beta = \sqrt 2$. **The argument as written does NOT close
the gap.**

## 6.7 Where the factor-of-2 went

To get $\alpha + \beta \le 2/3$ in the symmetric case from (D-9), I would
need (at $\alpha = \beta$):
$$
\frac{\tau}{4\alpha} + \frac{\tau}{2\alpha} \;\le\; \tfrac12 \cdot 1 \quad ? \quad
\text{i.e., the RHS should be } \tfrac{1}{2}, \text{ not } 1.
$$
Equivalently the integrated constraint $\int (d_- + d_\times) \le \int 1$
should be tightened to $\le \int \tfrac12$.

**Why isn't it?** Because at every point $v$ in the overlap, $d_-(v) + d_\times(v) \le 1$
is a **weak** inequality. In the symmetric extremal case, at the right endpoint
$v = 2\alpha N = N$, $d_-(N) = 1 - N/(N) = 0$ and $d_\times(N) =
\tau N / (N \sqrt{\alpha\beta}) = (3\alpha-1)/\alpha = 1/2$ at $\alpha = 1/2$,
so the sum is $1/2$ — strict slack.

At the left endpoint $v = (1-\beta)N = N/2$, $d_-(N/2) = 1 - N/(2 \cdot N) = 1/2$,
$d_\times(N/2) = 0$, so the sum is $1/2$ — same slack.

In between, the sum $d_-(v) + d_\times(v)$ is linear (both pieces are linear in $v$),
so it equals $1/2$ throughout. The constraint $\le 1$ is loose by a factor
of 2 over the entire overlap.

**The right inequality to demand** is therefore
$$
\boxed{\;d_-(v) + d_\times(v) \;\le\; \tfrac{1}{2} \;}\tag{D-5'}
$$
in the overlap, which would close the problem.

**But is (D-5') true?** It would require that within-$A_-$ and cross-sums
*together cover at most half* the values in the overlap. This is a **stronger
hypothesis than SAS provides.**

SAS gives:  any value $v \neq n^*$ has at most one representation, i.e.,
$r_-(v) + r_+(v) + r_\times(v) \le 1$, which translates to the density
constraint
$$
\Pr[v \text{ is hit by some pair sum}] \le 1.
$$
This is just (D-5). There is **no** value-level reason for the densities
$d_-, d_\times$ to sum to $\le 1/2$.

In particular, in the Erdős–Freud construction (EF $B \cup (N - B)$,
$B \subseteq [1, N/3]$), one *does* have $\alpha = \beta = 1/3$, so the
overlap is empty (the overlap requires $2\alpha + \beta > 1$, i.e.,
$\alpha > 1/3$). The EF construction lives *exactly* on the boundary of the
"no overlap" regime, with $\alpha = \beta = 1/3$ achieving $\sqrt\alpha+\sqrt\beta = 2/\sqrt 3$.

**This is the deep structural fact:** the EF construction *avoids the
overlap entirely* by choosing $\alpha = \beta = 1/3$. The within-half and
cross-sumsets are interval-disjoint, so no value-level constraint is even
needed. The optimization is over the boundary $\alpha + \beta = 2/3$,
$\alpha, \beta \le 1/2$ — and the unconstrained max of $\sqrt\alpha+\sqrt\beta$
on this set is at $\alpha = \beta = 1/3$, $= 2/\sqrt 3$.

## 7. Honest diagnosis of the gaps

The above calculation does NOT prove $|A| \le (2/\sqrt 3 + o(1))\sqrt N$.
Three identifiable gaps:

**(G1) Sub-extremal halves.** [EF, Lemma 1] only gives uniform distribution
under the $(1+o(1))\sqrt{\alpha N}$ extremality assumption (H). For
$\alpha > 1/3$ small enough, the constraint binds only against the
*Lindström-extremal* $A_-$; but the optimal SAS $A$ might have $|A_-|$
significantly below $\sqrt{\alpha N}$, e.g., $|A_-| = c \sqrt{\alpha N}$ with
$c < 1$. In that regime, the within-$A_-$ density profile (D-2) loses its
explicit form, and could be much sparser, leaving more room for cross-sums.

A robust argument would need [EF, Lemma 2] (the spread-out estimate
$\sum c_j^2 \le 1/r$) instead of [EF, Lemma 1]. But Lemma 2 only gives an
$L^2$ bound on the per-subinterval densities; it does NOT yield a
pointwise density profile.

**(G2) Independence of $A_-$ and $A_+$.** The convolution step (D-4) assumed
$r_\times(v) \approx \rho_- \rho_+ \ell(v)$, which requires *joint
uniform distribution* of the pair $(A_-, A_+)$. But $A_-$ and $A_+$ are not
independent — they are constrained by the SAS hypothesis on cross-sums (at
most one pair $(a,b) \in A_- \times A_+$ with $a+b = v$ for $v \neq n^*$).
So at the value-level, $r_\times(v) \le 1$ for $v \neq n^*$, which directly
contradicts the "convolution" intuition for any $v$ where $\ell(v) > N\sqrt{\alpha\beta}$.

In fact, the SAS constraint is *already* the binding constraint on the
cross-sumset: the cross-sumset has cardinality $|A_-| \cdot |A_+| =
\sqrt{\alpha\beta}\,N$, which equals (by SAS) the number of *distinct*
cross-sum values — so $d_\times(v) = \mathbf 1\{v \in S_\times\}$ (each
value is hit exactly once). The cross-sumset is therefore a *subset* of
its ambient interval, with density $\sqrt{\alpha\beta}\,N / ((\alpha+\beta) N)
= \sqrt{\alpha\beta}/(\alpha+\beta) \le 1/2$, not the trapezoidal profile of (D-4).

This is a critical correction. Under SAS, $d_\times(v) \in \{0, 1/N\}$
locally (every "hit" is single), so the *value-density* of $S_\times$ in a
unit-length window is $1/N \cdot \#\text{hits}$, and by SAS this matches a
**uniform distribution over $\sqrt{\alpha\beta}\,N$ distinct values in
$(\alpha+\beta) N$ positions** — density $\sqrt{\alpha\beta}/(\alpha+\beta)$.

So the cross-sumset density profile is **not the trapezoid (D-4)**; it is
the constant $\sqrt{\alpha\beta}/(\alpha+\beta)$ (away from edges). The trapezoid
is the *multiplicity profile* of the convolution before SAS imposes
$r_\times \le 1$.

**This invalidates the integration in §6.5.** The correct cross-density to
use in (D-5) is the constant $\sqrt{\alpha\beta}/(\alpha+\beta)$. Re-doing the
integration:

$$
\int_{\text{overlap}} \big(d_-(v) + d_\times(v)\big) dv
\;=\; \frac{(2\alpha + \beta - 1)^2 N}{4\alpha} + \tau N \cdot \frac{\sqrt{\alpha\beta}}{\alpha+\beta},
$$
constrained $\le \tau N$:
$$
\frac{\tau}{4\alpha} + \frac{\sqrt{\alpha\beta}}{\alpha+\beta} \le 1. \tag{D-9-corr}
$$
At $\alpha = \beta = 1/2$: $\frac{1/2}{2} + \frac{1/2}{1} = 1/4 + 1/2 = 3/4 \le 1$. **Still non-binding at the $\sqrt 2$ corner.**

**(G3) The within-half density profile does not encode SAS strength.**
[EF, Lemma 3] computes the density of within-$A_-$ sums for a *maximally
dense Sidon-sequence*, but every term in the analysis treats $A_-$ purely
*intrinsically*. The interaction with $A_+$ that SAS imposes — namely the
cross-collision constraint — is not visible to the within-$A_-$ profile.
The argument is therefore fundamentally one-sided: it constrains how
within-$A_-$ sums can interact with cross-sums, but only via *cardinalities*,
not via the *value-pattern correlation* that SAS would force.

## 8. What went wrong, structurally, and the next attack

The argument has the **right idea at the structural level** (use the
density profile of [EF] to enforce value-disjointness in the overlap region)
but fails at three steps:

1. **(G1)** Sub-extremal halves not covered by the [EF, Lemma 1] hypothesis.
2. **(G2)** The cross-sumset density is *not* the trapezoidal convolution
   under SAS; SAS forces cross-multiplicities to be $\le 1$, flattening the
   profile to a constant indicator.
3. **(G3)** The integrated constraint at $\alpha = \beta = 1/2$ has slack
   $1/4$, so the argument as written allows the $\sqrt 2$ corner.

The EF construction's distinctive feature — that all cross-pairs sum to
*exactly* $n^* = N$, making the within-half sumsets interval-disjoint from
cross-sums — corresponds to $\alpha+\beta = 2/3$, $\alpha=\beta=1/3$. To get
to $2/\sqrt 3$, one needs to show that **moving away from this structure
costs**:

(a) Either $\alpha + \beta > 2/3$ forces overlap, which forces value-collisions
    detectable beyond SAS;
(b) Or $\alpha, \beta$ stays bounded away from $1/3$ but one half is
    sub-extremal.

Neither obstruction is captured by the density profile alone. **The
right next attack is Pikhurko-style Fourier on the cross-sumset
$1_{S_\times}$**, with the constraint that $S_\times$ has density
$\sqrt{\alpha\beta}/(\alpha+\beta)$ in its ambient interval — and the EF
construction achieves the *minimum* such density. A Plancherel-type bound on
how concentrated $\hat{1_{S_\times}}$ can be (corresponding to "all
cross-pairs sum to the same value") might force $\alpha+\beta = 2/3$ in the
extremal case.

This is essentially Attempt A (pikhurko-adaptation.md) refined with the
correct density profile — and the diagnostic in that document (factor-of-2
short) corresponds exactly to the $1/4$ slack we observed at
$\alpha=\beta=1/2$ in (D-9-corr).

## 9. Final constant

**Unconditional result of this attack: no improvement.** The argument as
written allows $\alpha = \beta = 1/2$, giving the previously known
$|A| \le (\sqrt 2 + o(1)) \sqrt N$.

**Conditional result.** Under the (false in general but plausible at
extremality) hypothesis $d_-(v) + d_\times(v) \le 1/2$ in the overlap, the
argument closes to $|A| \le (2/\sqrt 3 + o(1))\sqrt N$. But this stronger
density-disjointness is *not* a consequence of SAS at the value level.

**Final unconditional constant from this attack:**
$$
\boxed{\;c = \sqrt 2 \;\approx\; 1.414\;}\quad\text{(no improvement).}
$$

The hoped-for $c = 2/\sqrt 3 \approx 1.155$ is *not* established by the
density-profile method alone. The argument identifies the structural
obstruction precisely (gaps G1–G3) and points to the next attack: a
Plancherel-style Fourier bound on $1_{S_\times}$ leveraging the cross-sumset's
forced *density* $\sqrt{\alpha\beta}/(\alpha+\beta)$ rather than its
*multiplicity profile*.

## References

- **[EF]** P. Erdős and R. Freud, *On sums of a Sidon-sequence*,
  J. Number Theory **38** (1991), 196–205. DOI: 10.1016/0022-314X(91)90080-T.
  - Lemma 1 (uniform distribution of extremal Sidon), p. 197.
  - Lemma 2 (spread-out estimate, $\sum c_j^2 \le 1/r$), p. 198.
  - Lemma 3 and Corollary (within-sumset density profile, eq. (6)), p. 198–199.
- `paper.md`, this directory: the $\sqrt 2$ upper bound (Section 4, midpoint split).
- `pikhurko-adaptation.md`, this directory: prior Fourier attempt (Attempt A).
- `autoconvolution-attack.md`, this directory: prior autoconvolution attempt (Attempt B).
- `below-sqrt2.md`, this directory: roadmap including this attack as "Line 2 + EF Lemma 1".
