# Autoconvolution attack on strong almost-Sidon below $\sqrt{2}$

**Draft research note, 2026-05-22.** Companion to `paper.md` and
`below-sqrt2.md`. This note works through the $B_2[g]$ autoconvolution
adaptation in the limit $g \to 1^+$ with the single "bad atom" isolated at
the midpoint. The final outcome: **the argument as currently constituted
gets stuck**, and we identify exactly where. The stopping point is
quantitative; the obstruction is structural.

---

## 1. Setup and notation

Let $A \subseteq \{1, \dots, N\}$ be strong almost-Sidon (SAS) with
exceptional value $n^*$, and let
$k := r_A(n^*)/2 = \#\{(a, b) \in A^2 : a < b, a + b = n^*\}$ be the number
of unordered representations of $n^*$. (If $n^*$ is itself $2a$ for some
$a \in A$, count that pair once as well.) Apply the midpoint split of
[paper.md, §2]:
$$A_- := A \cap [1, \lfloor n^*/2 \rfloor], \qquad A_+ := A \cap (\lfloor n^*/2\rfloor, N].$$
Lemma 2.1 of paper.md gives that $A_-$ and $A_+$ are each genuine Sidon
sets. Set $L := |A_-|$, $U := |A_+|$, $\alpha := \lfloor n^*/2 \rfloor / N$,
so $A_- \subseteq [1, \alpha N]$ and $A_+ \subseteq (\alpha N, N]$.

Write $f_- := \mathbf{1}_{A_-}$, $f_+ := \mathbf{1}_{A_+}$, $f := f_- + f_+
= \mathbf{1}_A$, viewed as functions on $\mathbb{Z}$. Discrete
autoconvolution:
$$(f * f)(n) := \sum_{a \in \mathbb{Z}} f(a) f(n-a) = r_A(n),$$
where $r_A(n)$ counts ordered representations $n = a_1 + a_2$ with
$a_i \in A$. Decompose:
$$f * f = f_- * f_- + 2 f_- * f_+ + f_+ * f_+.$$

* $f_- * f_-$: supported on $[2, 2\alpha N]$, pure Sidon (every value
  appears with multiplicity 1 if it's not in $2 \cdot A_-$, multiplicity
  $\le 2$ if it is, since for $r$ we count ordered pairs and $a + a$
  appears once).
* $f_+ * f_+$: supported on $(2\alpha N, 2N]$, pure Sidon analogously.
* $f_- * f_+$: supported on $(\alpha N, (1 + \alpha) N]$. This is the
  **cross-convolution** carrying the bad atom: $(f_- * f_+)(n^*) = k$
  (counted as ordered, so $2k$ if we include $a < b$ versus $b < a$; we
  fix the unordered count $k$ throughout to avoid factor-of-2 confusion
  and adjust where necessary).

The within-half autoconvolutions $f_\pm * f_\pm$ behave like genuine Sidon
autoconvolutions. The cross-convolution $f_- * f_+$ is a **bipartite
convolution** with a single concentrated atom at $n^*$.

---

## 2. State of the art: White (2022)

**White's main theorem** [White 2022, Theorem 1, p.~3]. Let
$\mathcal{F}$ denote the family of $f \in L^1([-1/2, 1/2])$ with
$\int f = 1$. Define
$$\mu_2^2 := \inf_{f \in \mathcal{F}} \|f * f\|_2^2.$$
Then
$$0.57463\,5728 \le \mu_2^2 \le 0.57464\,3711.$$

**White's Corollary 2** [White 2022, p.~3]. For the $B_h[g]$ constant
$$\sigma_h(g) := \lim_{N \to \infty} \frac{R_h[g](N)}{(gN)^{1/h}},$$
one has, for $h = 2$,
$$\boxed{\sigma_2(g) \le \sqrt{\frac{2 - 1/g}{\mu_2^2}}.}$$

Numerical consequences:

| $g$ | $\sigma_2(g)$ upper bound | $|A|/\sqrt{N}$ upper bound |
|---|---|---|
| $1$ | $\sqrt{1/0.5746} \approx 1.3193$ | $\sigma_2(1) \cdot 1 \approx 1.319$ |
| $2$ | $\sqrt{1.5/0.5746} \approx 1.6155$ | $\sigma_2(2) \cdot \sqrt{2} \approx 2.285$ |
| $\to\infty$ | $\to \sqrt{2/\mu_2^2} \approx 1.866$ | $\sigma_2(g) \sqrt{g} \approx 1.866 \sqrt{g}$ |

The bound at $g = 1$ is $1.319 \sqrt{N}$, which is **already worse than
the trivial Lindström bound $|A| \le \sqrt{N} + N^{1/4} + 1$ (which gives
$\sigma_2(1) = 1$).** White's argument is asymptotic in $g$; it is *not*
designed to be tight at $g = 1$, and indeed the $g = 1$ case is the unique
case for which $\sigma_h(g)$ is known exactly (equals 1; see White §1).

**Sharpness regime.** White comments [p.~2]: "*the key to improving upper
bounds on $\sigma_2(g)$ is to better estimate the 2-norm of an
autoconvolution for small $g$ and infinity norm of an autoconvolution for
large $g$.*" The $L^2$ method is genuinely sharper for *small* $g$; the
$L^\infty$ method is sharper for large $g$. We are interested in $g \to
1^+$, so the $L^2$ method (White) is the right starting point.

**The $g \to 1^+$ limit.** Taking $g = 1 + \varepsilon$ in White's
Corollary 2:
$$\sigma_2(1 + \varepsilon) \le \sqrt{\frac{2 - 1/(1 + \varepsilon)}{\mu_2^2}} = \sqrt{\frac{1 + \varepsilon + O(\varepsilon^2)}{\mu_2^2}}.$$
As $\varepsilon \to 0^+$ this tends to $1/\mu_2 \approx 1.319$. But the
known truth at $g = 1$ is $\sigma_2(1) = 1$, so the bound has slack of
$\approx 0.319$ at $g = 1$. We cannot recover Lindström from White's
inequality in the limit.

**Implication for the SAS problem.** The SAS hypothesis is *not* a
$B_2[g]$ hypothesis for any fixed $g$. Plugging $g = k$ (where $k$ is the
multiplicity at $n^*$) into White gives $|A| \le 1.319 \sqrt{kN}$, which
is much *worse* than the desired $1.155\sqrt{N}$ when $k \ge 1$ — and
trivially worse than the known $\sqrt{2}\sqrt{N}$ when $k$ is large. So
**direct application of White is hopeless**.

---

## 3. CRV 2010: stratified representation bounds

A more flexible inequality comes from
**Cilleruelo–Ruzsa–Vinuesa 2010 Theorem 2.1** [CRV, p.~5]:

> Let $G$ be a finite commutative group with $|G| = q$. Let $k \ge 2$,
> $l \ge 0$, and $A \subseteq G$ with representation function
> $r(x) = \#\{(a_1, a_2) : a_1, a_2 \in A, a_1 + a_2 = x\}$ satisfying
> $$r(x) \le k \text{ if } x \notin 2 \cdot A, \quad r(x) \le k + l \text{ if } x \in 2 \cdot A.$$
> Then
> $$|A| < \sqrt{(k - 1)q} + 1 + \frac{l}{2} + \frac{l(l + 1)}{2(k - 1)}.$$

For *integer* Sidon-type sets $A \subseteq \{1, \dots, N\}$, this transfers
via $q = 2N - 1$ (or $q = 2N$ for convenience). For SAS, one has $r(x)
\le 2$ everywhere except possibly at $x = n^*$ where $r(n^*) = 2k$
(unordered count $k$). Naively applying CRV with $k_{\text{CRV}} = 2$
(everywhere bound) and "stratifying at $n^*$":

* Pretend the stratification is on $2 \cdot A$ — but it's on the
  *single* value $n^*$, which may or may not lie in $2 \cdot A$.
* Even if we generalize CRV's $l$ from "extra slack on $2 \cdot A$" to
  "extra slack at one element," the bound becomes:
  $$|A| < \sqrt{q} + 1 + \frac{l}{2} + \frac{l(l + 1)}{2}$$
  with $q = 2N$, $k_{\text{CRV}} = 2$, $l = 2k - 2$ (excess at $n^*$).
  Substituting:
  $$|A| < \sqrt{2N} + 1 + (k - 1) + (k - 1)(2k - 1) = \sqrt{2N} + (k - 1)(2k) + 1.$$
* For $k = O(\sqrt{N})$ (which is the SAS-allowed range, since
  $k \le \min(L, U) \lesssim \sqrt{N}$), the second term is $O(N)$ and
  **dominates** the main term, making the bound vacuous.

**Verdict on CRV:** the stratification-at-one-point form of CRV is too
weak to handle the SAS "single bad atom of size $\sqrt{N}$" scenario,
for exactly the same Pikhurko-style reason already noted in
`below-sqrt2.md` Line 1: the slack $\sum (r(n) - 2)_+^2$ is dominated by
the single $k^2$ contribution, making any Cauchy–Schwarz-style argument
vacuous unless $k$ is bounded by a constant.

---

## 4. Cross-convolution bipartite analysis

The strategic insight of the proposed attack is that the bad atom is
*entirely localized* on the cross-convolution $f_- * f_+$, while the
within-half autoconvolutions $f_\pm * f_\pm$ are pure Sidon (no excess).
This suggests:

1. Use White's tight bound only on $f_\pm * f_\pm$.
2. Handle the cross-convolution $f_- * f_+$ separately by an L^p-style
   argument that exploits its bipartite structure and the explicit
   atom at $n^*$.

### 4.1 Within-half terms (pure Sidon)

For Sidon $A_- \subseteq [1, \alpha N]$, the discrete autoconvolution
$f_- * f_-$ has the following profile:
* $L^1$ mass: $\|f_- * f_-\|_1 = L^2$.
* $L^\infty$: $\|f_- * f_-\|_\infty \le 2$ (Sidon: every value has at
  most one unordered representation; in ordered counts, multiplicity at
  most 2 except at the diagonal $2a$).
* $L^2$ mass: $\|f_- * f_-\|_2^2 = \sum_n r_-(n)^2 = 2L^2 - L + \text{(diagonal)}$
  $= 2L^2 + O(L)$ (each ordered Sidon pair contributes 1; the diagonal
  $a = a'$ contributes $L$, and the off-diagonal pairs contribute $2 \cdot
  \binom{L}{2} \cdot 1$).

So $\|f_- * f_-\|_2^2 = 2L^2 - L$. By Plancherel
$\int |\hat{f}_-(\xi)|^4\,d\xi = \|f_- * f_-\|_2^2 / N$ in the discrete
setting (with the right normalization), this is the standard "Sidon =
$L^4$-flat Fourier" identity.

For the $\sqrt{2} \cdot \sqrt{N}$ argument we only used Lindström's
elementary bound $L \le \sqrt{\alpha N} + O(N^{1/4})$, $U \le \sqrt{(1 -
\alpha) N} + O(N^{1/4})$. **There is no slack to extract from the
within-half terms** in the Sidon-extremal regime — Lindström is sharp
up to lower-order terms.

The autoconvolution viewpoint can recover Lindström as an upper bound via
discretization (CRV §6: the Schinzel–Schmidt discretization gives
$\beta_2(N) \le \sigma\sqrt{N}(1 + o(1))$ where $\sigma \le 1.2525$
[CRV p.~4]). This *worse* than Lindström's $\sqrt{N} + O(N^{1/4})$;
the discretization step is lossy at $g = 1$.

### 4.2 Cross term: the L¹–L^∞ inequality is vacuous

Let's compute the norms of $f_- * f_+$:

* **L¹ norm:** $\|f_- * f_+\|_1 = L \cdot U$ (every cross pair contributes
  1 to one value in $(\alpha N, (1 + \alpha) N]$).

* **L^∞ norm:** $\|f_- * f_+\|_\infty = k$ (the multiplicity at $n^*$).

* **L² norm:** $\|f_- * f_+\|_2^2 = \sum_n (f_- * f_+)(n)^2$. Every cross
  pair $(a, b) \in A_- \times A_+$ contributes 1 to one value; cross pairs
  $(a_1, b_1)$ and $(a_2, b_2)$ collide at the same sum iff $a_1 + b_1 =
  a_2 + b_2$. By SAS, the only value with multiplicity $> 1$ is $n^*$, so
  $\sum_n (f_- * f_+)(n)^2 = k^2 + (\text{number of cross pairs not at } n^*)$
  $= k^2 + (LU - k)$. Hence
  $$\|f_- * f_+\|_2^2 = LU + k^2 - k = LU + k(k - 1).$$

* **Support size:** $LU - k + 1$ (since $k$ cross pairs hit $n^*$, the
  rest hit distinct values).

### 4.3 The Plancherel constraint

By Plancherel on $\mathbb{Z}/(2N + 1)\mathbb{Z}$ (or directly on
$\mathbb{Z}$ when convolution is finitely supported):
$$\|f * f\|_2^2 = \|f_- * f_-\|_2^2 + 4 \|f_- * f_+\|_2^2 + \|f_+ * f_+\|_2^2 + 2\langle f_- * f_-, f_+ * f_+\rangle + 4 \langle f_- * f_-, f_- * f_+\rangle + 4 \langle f_+ * f_+, f_- * f_+ \rangle.$$
(Here we use $f * f = f_- * f_- + 2 f_- * f_+ + f_+ * f_+$, and we
square.)

The inner products $\langle f_- * f_-, f_+ * f_+\rangle$ etc.~are zero
unless the supports overlap:
* $\operatorname{supp}(f_- * f_-) \subseteq [2, 2\alpha N]$
* $\operatorname{supp}(f_+ * f_+) \subseteq [2\alpha N + 2, 2N]$
* $\operatorname{supp}(f_- * f_+) \subseteq [\alpha N + 1, (1 + \alpha) N]$

So $\langle f_- * f_-, f_+ * f_+\rangle = 0$. The cross-within inner
products are typically nonzero (overlap regions are
$[\alpha N + 1, 2\alpha N]$ and $[2\alpha N + 2, (1 + \alpha) N]$). For
SAS, every collision in these overlap regions (other than at $n^*$) is
*forbidden* — so the cross-within inner products are forced to be exactly
the number of collisions, which equals $0$ or $1$ at $n^*$ only. Let's
make this precise.

For $x \in [\alpha N + 1, 2 \alpha N]$ (overlap of within-$A_-$ and cross
ranges), let $r_-(x) = (f_- * f_-)(x)$ (count of ordered pairs in $A_-$
summing to $x$, so $\le 2$), and $r_\times(x) = (f_- * f_+)(x)$. SAS says
the *unordered* sum representation count is $\le 1$ except at $n^*$.
The unordered count combining within-$A_-$ and cross is:
$$r_-^*(x) + r_\times(x) \le 1 \text{ for } x \ne n^*, \quad r_-^*(n^*) + r_\times(n^*) \le k.$$
(Here $r_-^*(x) := \lceil r_-(x)/2 \rceil$ is the unordered within-count.)

This gives the **collision constraint:** for $x \ne n^*$, at least one of
$r_-^*(x), r_\times(x)$ is zero. Equivalently $r_-^*(x) \cdot r_\times(x)
= 0$ for $x \ne n^*$.

So $\langle f_- * f_-, f_- * f_+\rangle = \sum_x r_-(x) \cdot r_\times(x)$.
For $x = n^*$ this is $\le 2 k_-$ where $k_- := r_-^*(n^*)$ if $n^* \in 2A_-$,
else $0$. For $x \ne n^*$, $r_-(x) > 0 \Rightarrow r_\times(x) = 0$. So
the inner product is at most $2 k_- \cdot k \le 2 L \cdot k$.

But notice: in the *worst case*, the collision constraint at $x \ne n^*$
*is binding* on the cross sumset. Each value the cross sumset hits is
*forbidden* to be a within-$A_-$ sum. So:
$$\operatorname{supp}(f_- * f_+) \cap \operatorname{supp}(f_- * f_-) \subseteq \{n^*\}.$$

This means the cross sumset and within-$A_-$ sumset are essentially
*disjoint subsets of* $[\alpha N + 1, 2 \alpha N]$ in the overlap region.
Their cardinalities sum to at most the available room:
$$|\operatorname{supp}(f_- * f_+) \cap [\alpha N + 1, 2\alpha N]| + |\operatorname{supp}(f_- * f_-) \cap [\alpha N + 1, 2\alpha N]| \le \alpha N + O(1).$$

This is essentially the constraint already explored unsuccessfully in
`below-sqrt2.md` ("naive energy counting"). Let's formalize and check
whether it bites.

### 4.4 The disjointness constraint quantified

Let $S_- := \operatorname{supp}(f_- * f_-) \subseteq [2, 2\alpha N]$,
$S_\times := \operatorname{supp}(f_- * f_+) \subseteq [\alpha N + 1, (1 + \alpha) N]$,
$S_+ := \operatorname{supp}(f_+ * f_+) \subseteq [2\alpha N + 2, 2N]$.
By Sidon-ness of $A_-, A_+$:
$$|S_-| \ge L(L - 1)/2 + 1, \qquad |S_+| \ge U(U - 1)/2 + 1$$
(actually $|S_-| = L(L+1)/2$ counting the doubled elements $2a$; for
asymptotics let's use $|S_-| \ge L^2/2 (1 - o(1))$ and similarly $|S_+|$.)

By SAS-collision avoidance:
$$S_- \cap S_\times \subseteq \{n^*\}, \quad S_+ \cap S_\times \subseteq \{n^*\}, \quad S_- \cap S_+ = \emptyset.$$

Now sum cardinalities and use that all live in $[2, 2N]$:
$$|S_-| + |S_+| + |S_\times| - 2 \le 2N - 1$$
(subtracting 2 for the possible double-counting at $n^*$ in both
$S_-, S_\times$ and $S_+, S_\times$).

We have $|S_\times| = LU - k + 1$. Substituting:
$$L^2/2 + U^2/2 + LU - k + 1 - 2 \le 2N - 1 + O(1).$$
$$\boxed{(L + U)^2 / 2 \le 2N + k + O(1).} \qquad (\star)$$

So $|A| = L + U \le \sqrt{4N + 2k}$. With $k \le \min(L, U) \le |A|/2$:
$$|A|^2 \le 4N + |A|, \quad |A| \le 2\sqrt{N} + O(1).$$

That's $2\sqrt{N}$ — **strictly worse than the $\sqrt{2}\sqrt{N}$ bound
from paper.md.** Why? Because we *didn't use Sidon-ness of the halves
within their own intervals* — we only used the cardinalities of the
sumsets. The Lindström-on-each-half bound is what gave us $L \le
\sqrt{\alpha N}$, and that's the bound dominating the answer, not the
collision constraint.

### 4.5 Combining all constraints

The full optimization problem is:
$$\text{maximize } L + U \text{ subject to:}$$
\begin{align*}
& L \le \sqrt{\alpha N}(1 + o(1)) \qquad \text{(Lindström on } A_-\text{)}\\
& U \le \sqrt{(1 - \alpha) N}(1 + o(1)) \qquad \text{(Lindström on } A_+\text{)}\\
& L^2/2 + U^2/2 + LU - k + 1 \le 2N + O(1) \qquad \text{(collision $(\star)$)}\\
& 0 \le k \le \min(L, U).
\end{align*}

* From Lindström alone: $L + U \le \sqrt{\alpha N} + \sqrt{(1 -\alpha) N}
  \le \sqrt{2 N}$ (by Cauchy–Schwarz), giving $\sqrt{2} \sqrt{N}$ at
  $\alpha = 1/2$.
* From collision $(\star)$ alone: $(L + U)^2 \le 4N + 2k$, so $L + U \le
  2\sqrt{N}$ — vacuous.
* **Joint:** at $\alpha = 1/2$, $L = U = \sqrt{N/2}$, $L + U = \sqrt{2N}$,
  $L^2 + U^2 + 2LU = 2N = 2N$. Collision constraint becomes $N + N - 2k \le
  2N - 2$, i.e., $k \ge 1$ — automatic.

**So at the Lindström-optimal point $\alpha = 1/2$, the collision
constraint $(\star)$ is vacuous (binding only when $k = 0$, in which case
it would force $LU \le N$).**

To make the collision constraint bite, we need to push *away* from
$\alpha = 1/2$. But Lindström is then strict on the shorter half, and
the resulting $L + U$ is smaller. So the optimum stays at $\alpha = 1/2$
with $L + U = \sqrt{2N}$. **No improvement.**

---

## 5. Where the argument gets stuck

We tried three things:

1. **Direct White Corollary 2 on $A$ as a $B_2[k]$ set.** Vacuous because
   $\sigma_2(k) \approx 1.3 \sqrt{k}$, and $k$ can be $\Theta(\sqrt{N})$.
2. **CRV Theorem 2.1 with stratified-at-$n^*$ representations.** Vacuous
   because the $l^2$ slack term dominates when $l = 2k - 2 = \Theta(\sqrt{N})$.
3. **Cross-convolution disjointness in the midpoint split.** Gives a
   constraint $(\star)$ that is *redundant* with the Lindström-on-halves
   bound at the Lindström-optimal point $\alpha = 1/2$.

The structural reason is the same in all three approaches:
**at the Lindström-optimal configuration, the within-half Sidon sumsets
are dense enough (filling $\sim L^2/2 + U^2/2$ values in a range of $\sim
2N$) that the cross-sumset has plenty of room ($\sim LU = N/2$ values
in a range of $N$) and the collision constraint is vacuous.**

The construction $A = B \cup (N - B)$ (Erdős–Freud), by contrast, is *not*
at this Lindström-optimal configuration: its halves only have size
$\sqrt{N/3}$, not $\sqrt{N/2}$. The construction "wastes" packing density
in order to force *all* cross-sums to land at $n^* = N$, which makes the
collision constraint binding for it but not for arbitrary near-extremal $A$.

### 5.1 The L^2 cross-norm: where Plancherel could help

The cross-convolution L² norm $\|f_- * f_+\|_2^2 = LU + k(k - 1)$ contains
the key information about the bad atom (via the $k^2$ term). The question
is whether one can combine this with a *lower* bound on $\|f_- * f_+\|_2^2$
coming from the $L^1$ mass and support disjointness.

By Cauchy–Schwarz $\|f_- * f_+\|_2^2 \ge \|f_- * f_+\|_1^2 / |S_\times|
= (LU)^2 / (LU - k + 1)$. So:
$$LU + k(k - 1) \ge \frac{L^2 U^2}{LU - k + 1}.$$
Rearranging:
$$(LU + k^2 - k)(LU - k + 1) \ge L^2 U^2.$$
$$L^2 U^2 - LUk + LU + LU k^2 - k^3 + k^2 + LU - k(k-1)(-k+1) \ge L^2 U^2$$
After simplification (keeping leading terms):
$$LU \cdot (k^2 - k + 2) \ge k(k - 1)(2k - 1) + \dots,$$
which gives $LU \ge \Omega(k)$. With $k \le \sqrt{N}$ and $LU \le N/2$,
this is automatic. **Vacuous again.**

The Plancherel-Bessel approach (lower-bounding $L^2$ by $L^4$ via
$\|f * f\|_2^2 \ge \|f * f\|_4^4 / \|f * f\|_\infty^2$) doesn't help
either, because the $L^\infty$ norm of $f * f$ is exactly $2k$ at the bad
atom, and the bound becomes self-referential.

### 5.2 The genuine White-style application would require an *averaged* form

White's Corollary 2 is proven via the inequality
$$\frac{|A|^2}{\sqrt{gN}} \le \frac{|Q_A|_1}{\sqrt{N \cdot |Q_A^2|_\infty}} \le \sigma$$
[CRV Theorem 5.1, p.~12; this is the Schinzel-Schmidt-style discretization
of the continuous autoconvolution constant]. Here $|Q_A^2|_\infty
\le g$ for $B_2[g]$ sets.

For SAS, $|Q_A^2|_\infty = 2k$ at $n^*$ (or 1 elsewhere up to factor of
2). So $|Q_A^2|_\infty = 2k$, and we get $|A|^2 \le \sigma \sqrt{2k N}
\cdot \sqrt{N}$, i.e., $|A| \le \sqrt{\sigma} \cdot (2kN)^{1/4} \cdot
N^{1/4}$. **This is much weaker than $\sqrt{N}$** because the $L^\infty$
norm $2k$ is what one might call "concentrated" rather than "averaged."

The right notion is: a **modified autoconvolution constant where the
$L^\infty$ norm is replaced by an $L^p$ average that downweights the
single bad atom.** Concretely, one would want an inequality of the form:
$$|A|^2 \le C \cdot \sqrt{N \cdot \|f * f\|_p^{2/p}} \cdot \text{(correction)}$$
for some $p < \infty$ that does not let a single atom dominate.

The natural candidate is $L^2$: $\|f * f\|_2^2 = 2L^2 + 2U^2 + 4 \|f_- *
f_+\|_2^2 + \dots = 2|A|^2 + 4k(k - 1) + O(|A|)$. White's bound on the
*continuous* $\mu_2^2 \approx 0.5746$ does not directly transfer because
White's set-up has $\int f = 1$ and the relevant identity is
$\|f * f\|_2^2 \ge \mu_2^2 \cdot \|f\|_1^4 / N^?$, and the powers don't
work out: for an integer Sidon set $\|f * f\|_2^2 \sim 2|A|^2$ and
$\|f\|_1 = |A|$, so $\|f * f\|_2^2 / \|f\|_1^4 = 2/|A|^2 \to 0$, *not*
$\to \mu_2^2$. The continuous-to-discrete transfer requires a rescaling
that kills the constant.

**This is the precise stopping point.** The continuous White inequality
$\int (f * f)^2 \ge \mu_2^2 (\int f)^2$ scales with $\int f$ to the
fourth power (because $f * f$ has L^1 norm $(\int f)^2$). The discrete
analogue, $\sum r(n)^2 \ge \mu_2^2 \cdot |A|^4 / N$, is **the
Erdős-Turán energy inequality**. For Sidon sets, $\sum r(n)^2 = 2|A|^2 -
|A|$, so we get $|A|^4/N \le (2|A|^2 - |A|)/\mu_2^2$, i.e., $|A|^2 \le 2N
/ \mu_2^2 \approx 3.48 N$, $|A| \le 1.866 \sqrt{N}$. **This is exactly
the $\sqrt{2/\mu_2^2}$ in White Corollary 2, the $g \to \infty$ limit.**

For SAS, $\sum r(n)^2 = 2|A|^2 - |A| + 2k(k - 1)$ (the bad atom adds
$k^2 - k$ to the unordered count, doubled for ordered, but only if we
were counting from a baseline of $r = 2$ at $n^*$, so the actual addition
is $(2k)^2 - 4 = 4k^2 - 4$; let me redo: SAS Sidon-everywhere-else means
$r(n) \le 2$ for $n \ne n^*$, so $\sum_{n \ne n^*} r(n)^2 \le 2|A|^2 -
|A| + O(|A|)$; at $n^*$, $r(n^*) = 2k$ contributing $4k^2 - 4$ over the
Sidon baseline; total $\sum r(n)^2 \le 2|A|^2 + 4k^2 + O(|A|)$). So the
$L^2$ energy bound becomes:
$$|A|^4 / N \le \mu_2^{-2} (2 |A|^2 + 4 k^2).$$
Setting $|A| = c \sqrt{N}$ and $k = \kappa \sqrt{N}$ with $0 \le \kappa
\le c/2$:
$$c^4 \le \mu_2^{-2} (2 c^2 + 4 \kappa^2).$$

The midpoint split tells us $k \le \min(L, U)$, but doesn't a priori
bound $\kappa$ tightly. The worst case is $\kappa = c/2$:
$$c^4 \le \mu_2^{-2} (2 c^2 + c^2) = 3 c^2 / \mu_2^2,$$
$$c^2 \le 3 / \mu_2^2, \quad c \le \sqrt{3/\mu_2^2} \approx 2.285.$$

This is the *worst-case* analysis with no constraint relating $\kappa$
to $c$. It gives $|A| \le 2.285 \sqrt{N}$, **worse than $\sqrt{2}$.**

To improve, we need to relate $\kappa$ to $c$ more tightly via the
*midpoint-split disjointness*. From §4.3: at the configuration $\alpha
= 1/2$, $L = U = c\sqrt{N}/2$, and $k \le c\sqrt{N}/2$. But we'd want
$k \ll \sqrt{N}$. **There's no direct way to bound $k$ better than
$\min(L, U)$ from the autoconvolution side.** The bound $k \le \min(L,
U)$ is the only available constraint.

If somehow we could show $k = O(1)$ (a single value with multiplicity
that doesn't grow with $N$), then $\sum r(n)^2 \le 2|A|^2 + O(1)$ and
the L^2 bound reduces to the pure-Sidon case $|A| \le \sqrt{2/\mu_2^2}
\sqrt{N} \approx 1.866\sqrt{N}$, still worse than $\sqrt{2}$.

To beat $\sqrt{2}$, we'd need:
$$c^4 \le \mu_2^{-2}(2 c^2 + o(c^2)) \quad \text{with } \mu_2^{-2} < 2,$$
which would require **$\mu_2^2 > 1/2$**. White proves $\mu_2^2 \ge
0.57464$, which *is* greater than $1/2$! So in principle, the discrete
L² bound gives $c \le \sqrt{2/\mu_2^2} \approx 1.866$, weaker than
$\sqrt{2}$.

**Wait — this means even pure Sidon's autoconvolution bound is $1.866
\sqrt{N}$, much weaker than Lindström's $\sqrt{N}(1 + o(1))$.** That's
right; the discrete-to-continuous Schinzel-Schmidt loss kills the
constant. The *continuous* extremizer for $\mu_2$ is not the indicator
of a Sidon set; it's a smoother function. Sidon sets occupy a smaller
slice of $\mathcal{F}$, and Lindström's bound ($\sigma_2(1) = 1$) is
strictly better than what the autoconvolution L² method can deliver.

---

## 6. Diagnosis: why the autoconvolution approach is fundamentally weak here

**Summary of why each lever fails:**

| Lever | Failure mode |
|---|---|
| White Corollary 2 with $g = k$ | At $k \ge 1$, gives $\ge 1.319\sqrt{kN}$, weaker than $\sqrt{2}\sqrt{N}$ unless $k < 1.15$ — i.e., never for SAS with a real bad atom. |
| CRV Theorem 2.1 with stratified $l = 2k - 2$ | Quadratic-in-$l$ slack dominates when $l \sim \sqrt{N}$. |
| White's continuous inequality discretized to SAS | Already weaker than Lindström at $k = 0$; SAS bad atom can only worsen it. |
| Midpoint-split collision constraint (the new ingredient) | Vacuous at the Lindström-optimal split $\alpha = 1/2$. Only binds when the construction is forced into a smaller-than-Lindström configuration, which the SAS hypothesis alone does not force. |

**The structural reason:** Autoconvolution (energy) methods are
tailor-made for "constraints averaged over all values" — they extract
total energy and lose individual-value information. The SAS hypothesis,
in contrast, is an "$L^\infty$ minus one atom" condition: it constrains
the *maximum*, not the average. The autoconvolution methods cannot
distinguish "Sidon with one bad atom" from "Sidon with several small bad
atoms" — both have similar $L^2$ energy. But the *combinatorial*
strength of SAS is exactly that the bad atom is isolated to one point.
Isolating a single point requires an $L^\infty$ or a support-set
argument, which is what the midpoint-split + Lindström argument
(paper.md) is.

In conclusion: **the autoconvolution-style argument cannot push below
$\sqrt{2}\sqrt{N}$ for SAS** because:

1. The $L^2$ energy of SAS is essentially the same as Sidon plus an
   irrelevant $O(k^2)$ correction. The energy bound recovers only the
   pure-Sidon autoconvolution constant $\sqrt{2/\mu_2^2} \approx 1.866$,
   strictly worse than $\sqrt{2}$.
2. The cross-convolution disjointness constraint (the natural SAS-aware
   refinement) is *redundant* with Lindström at the worst-case midpoint
   split $\alpha = 1/2$ and does not bind.
3. The continuous autoconvolution constant $\mu_2^2 \approx 0.5746$
   does not transfer tightly to integer sets at $g = 1$ — even for
   pure Sidon, $\sigma_2(1) = 1 < 1/\mu_2 = 1.319$. The "$g \to 1^+$
   limit" of White's bound is *strictly worse* than Lindström.

**Final outcome of the autoconvolution attack:**

> **No improvement on $\sqrt{2}$ is obtained.** The autoconvolution
> machinery is structurally mismatched with the SAS hypothesis. The
> best constant we can produce by this route is $\sqrt{2/\mu_2^2}
> \approx 1.866$ via raw discrete energy, or $\sqrt{2} \approx 1.414$
> via midpoint-split + Lindström + a (vacuous) cross-disjointness check.
> Neither improves on the existing paper.md bound.

---

## 7. What would be needed to actually go below $\sqrt{2}$

The honest diagnosis is that beating $\sqrt{2}$ requires *not* an energy
argument but a **structural argument** that forces near-extremal SAS sets
to lie in a smaller-than-Lindström configuration. The empirical data
(OEIS A389182, see `below-sqrt2.md` §"Empirical evidence") shows the
extremal SAS sets are essentially Erdős-Freud sets $B \cup (N - B)$ with
$B \subseteq [1, N/3]$. These have $|A_-| = |A_+| = \sqrt{N/3}$, *not*
$\sqrt{N/2}$. A successful below-$\sqrt{2}$ proof must establish that
$A_-$ (say) cannot exceed $\sqrt{N/3} \cdot (1 + o(1))$ — i.e., it must
prove a Lindström-strengthening on the half that knows about the cross
constraints.

Two routes seem viable but are *not* the autoconvolution route:

**(A) Density-profile argument.** Use Erdős-Freud's Lemma 1 (the density
profile of Sidon sumsets in their range): a Sidon set $A_- \subseteq
[1, \alpha N]$ has its sumset *uniformly distributed* in
$[2, 2\alpha N]$ with density approaching $L^2 / (2 \alpha N)$. For
$L = \sqrt{\alpha N}$, this density is $1/2$. Combined with the
cross-sumset density in $(\alpha N, (1 + \alpha) N]$, which is
$LU / N$, the *value-level* disjointness becomes a hard density
constraint. The paper.md note §6 discusses this. Required tool:
Erdős-Freud Lemma 1 + 3.

**(B) Pikhurko Theorem 2 adaptation.** The Pikhurko-style Fourier
argument on the cross-pair contributions only. This is the parallel
agent's target (`pikhurko-adaptation.md`); see the cross-reference there.

The autoconvolution attack we just worked through is **disqualified**
from below-$\sqrt{2}$ progress, but the structural insight it produced
(namely, that the cross-convolution L² mass is $LU + k(k - 1)$ and that
the cross-within disjointness is vacuous at $\alpha = 1/2$) is a useful
ingredient that the density-profile argument can build on.

---

## 8. Summary box

> **Result.** The B_2[g] autoconvolution machinery (White 2022,
> CRV 2010) in the limit $g \to 1^+$ does **not** improve the
> $\sqrt{2} \sqrt{N}$ bound on strong almost-Sidon sets. The best
> constant achievable by this route is $\sqrt{2/\mu_2^2} \approx 1.866$
> (pure-Sidon energy bound, ignoring the bad atom). The midpoint-split
> cross-convolution disjointness constraint $(\star)$ — the natural
> SAS-aware refinement — is *redundant* with the existing
> Lindström-on-halves bound at the worst-case split $\alpha = 1/2$,
> so the combined bound remains $\sqrt{2} \sqrt{N}$.
>
> **Where the argument is stuck.** The autoconvolution method extracts
> averaged ($L^2$) information from the representation function; the
> SAS hypothesis is an $L^\infty$ minus one atom constraint. These are
> structurally mismatched: SAS's combinatorial strength (the single
> isolated bad atom) is washed out by $L^2$ averaging.
>
> **Recommendation.** Pivot to either (a) density-profile arguments
> (Erdős-Freud Lemma 1 + 3) or (b) Pikhurko Theorem 2 adaptation on
> cross terms only. Both target the actual extremal configuration
> (Erdős-Freud reflection sets) directly.

---

## References

- **CRV 2010**: J. Cilleruelo, I.Z. Ruzsa, C. Vinuesa, *Generalized
  Sidon sets*, Adv. Math. 225 (2010), 2786–2807. arXiv:0909.5024.
  Specifically: Theorem 1.5 (p.~4), Theorem 2.1 (p.~5), Theorem 5.1
  (p.~12, Schinzel-Schmidt discretization), §6 (continuous-discrete).
- **White 2022**: E.P. White, *An almost-tight $L^2$ autoconvolution
  inequality*, arXiv:2210.16437. Specifically: Theorem 1 (p.~3),
  Corollary 2 (p.~3, $B_h[g]$ bounds), Lemma 7 (p.~7, Fourier expansion).
- Pikhurko 2006: O. Pikhurko, *Dense edge-magic graphs and thin
  additive bases*, Discrete Math. 306 (2006), 2097–2107.
  arXiv:math/0309029.
- Vinuesa 2009 thesis: C. Vinuesa, *On the maximum size of a Sidon
  set*, Universidad Autónoma de Madrid PhD thesis, 2009.
  icmat.es/Thesis/CVinuesa.pdf — Chapter 3 contains
  $B_2[g]$-as-$g$-varies analysis; the limit $g \to 1^+$ does not
  appear because Theorem 1.5 only gives the existence of $\sigma$ in the
  $g \to \infty$ limit; the $g \to 1^+$ case is governed by the
  unrelated Lindström bound $\sigma_2(1) = 1$.
- paper.md and below-sqrt2.md (this directory): companion notes.
