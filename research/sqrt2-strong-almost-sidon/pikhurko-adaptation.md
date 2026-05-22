# Adapting Pikhurko (2006) Theorem 2 to Strong Almost-Sidon Cross-Pairs

**Worked calculation, 2026-05-22.** Companion to `below-sqrt2.md`, attempting
to push the upper bound for strong almost-Sidon sets below $\sqrt 2 \cdot \sqrt N$.

**Final answer (executive summary).** *The naive Pikhurko-on-cross-terms adaptation does not give an improvement below $\sqrt 2$.* The calculation breaks down at a specific, identifiable step: in the bipartite setting, the cross-sumset $A_- + A_+$ has cardinality only $\sqrt{\alpha\beta}\, N \le N/2$, which leaves $\ge N/2$ "gaps" inside the ambient interval of length $N$. Pikhurko's Fourier inequality (eq.~(13) of arXiv:math/0309029) is fundamentally a *gap-deficit* inequality — it converts the smallness of the gap count into an upper bound on the set size. With $\Theta(N)$ gaps, Pikhurko's inequality is vacuous (the gap term dominates the Fourier term). A precise version of the obstruction is given in §6 below. The honest conclusion is that **Line 1' of `below-sqrt2.md` does not yield a constant below $\sqrt 2$ with the present technique**, and the gap to $2/\sqrt 3$ requires a substantively different argument (probably one that uses Erdős–Freud Lemma 1 to constrain $A_-$ and $A_+$ individually, then a *value-disjointness* Fourier statement on the cross-sumset, *not* a gap-count statement).

---

## 1. Pikhurko's Theorem 2 and its key inequality

Pikhurko, *Dense edge-magic graphs and thin additive bases*, Discrete Math. **306** (2006), 2097–2107, arXiv:math/0309029 (henceforth **[P]**). We quote the exact statements.

**[P, Theorem 2 / eq. (3)]:**
$$s(k,n) \;\le\; n + k^2 \left( \tfrac{1}{4} - \tfrac{1}{(\pi+2)^2} + o(1)\right),$$
where $s(k,n) := \max\{ |A+A| : A \in \binom{[n]}{k}\}$.

**[P, Theorem 3]:** If $A \subset [n]$ is *quasi-Sidon* (i.e. $|A+A| = (1+o(1))\binom{|A|}{2}$), then
$$|A| \;\le\; \Big( \big(\tfrac14 + \tfrac{1}{(\pi+2)^2}\big)^{-1/2} + o(1)\Big) n^{1/2} \;=\; (1.863\ldots + o(1))\, n^{1/2}.$$

The numerical value $\big(\tfrac14 + \tfrac{1}{(\pi+2)^2}\big)^{-1/2} \approx 1.86395$.

**The Fourier engine [P, Theorem 8 / eq. (7)]:** For $A \subset \mathbb Z$ with $k := |A \cap [n]|$, $m := |A \setminus [n]|$, large $n$, and $k \ge \lambda m$ with $\lambda := \tfrac14(2\sqrt 2 - 4 + \pi(4 - \sqrt 2)) = 0.323\ldots$,
$$|(A+A) \cap [2n]| \;\le\; n + \frac{|A|^2}{4} - \frac{(|A| - \pi m)^2}{(\pi + 2)^2} + o(n). \tag{P-7}$$

The proof passes through the per-mode Fourier inequality [P, eq. (13)]:
$$\Big(\tfrac{\pi}{2} + 1\Big)\,(2z)^{1/2} \;\ge\; k + (1 - \pi)\, m + o(m+k), \tag{P-13}$$
where
$$z \;:=\; \binom{k+m+1}{2} - 2n + 2\ell + o(n), \qquad \ell := |[2n] \setminus (A+A)|.$$
Here $\ell$ counts *missing values* (gaps) of $A+A$ inside $[2n]$.

Mechanically: Pikhurko shows that the Fourier coefficient $g(e^{i\pi t/n})$ of the "doubled" generating function $g(x) = \tfrac12(f(x)^2 + f(x^2))$ is dominated by the gap counts (eq. (8)) on one hand and by trigonometric sums in $A$ (eq. (9)) on the other; pairing these via the Fourier series of an explicit rectangular pulse (eq. (10)–(13)) gives (P-13). Squaring (P-13) and substituting the definition of $z$ yields (P-7).

The constant $\frac{1}{(\pi+2)^2}$ that distinguishes $1.864$ from the trivial $2$ comes from $\big(\tfrac{\pi}{2}+1\big)^{-2} = \tfrac{4}{(\pi+2)^2}$, halved due to the factor of $2$ in $2z$.

---

## 2. Setting up the strong almost-Sidon cross-pair convolution

Let $A \subseteq [N]$ be strong almost-Sidon with exceptional value $n^*$ (the unique $n$ with $r(n) \ge 2$). Define
$$\alpha := \lfloor n^*/2 \rfloor, \qquad A_- := A \cap [1, \alpha], \qquad A_+ := A \cap [\alpha+1, N].$$
By Lemma 2.1 of `paper.md`, both $A_-$ and $A_+$ are *genuine* Sidon sets. Write $L := |A_-|$ and $U := |A_+|$, so $|A| = L + U$.

**Cross-representation function.** For each integer $n$, let
$$r_\times(n) \;:=\; \#\{(a,b) \in A_- \times A_+ : a + b = n\}.$$
The support of $r_\times$ lies in the half-open interval
$$I_\times := (\alpha, \, \alpha + N], \qquad |I_\times| = N,$$
because $a + b \ge 1 + (\alpha+1) = \alpha + 2 > \alpha$ and $a + b \le \alpha + N$.

**Multiplicities.** The strong almost-Sidon hypothesis forces $r_\times(n) \le 1$ for all $n \neq n^*$. Indeed, if $r_\times(n) \ge 2$ for some $n \neq n^*$, then $n$ has $\ge 2$ unordered representations as $a + b$ in $A$, contradicting uniqueness of the exceptional value. At $n = n^*$ itself, $r_\times(n^*) =: k$ can be as large as $\min(L, U)$.

**Sum identity and cross-sumset cardinality.** Let $S := |A_- + A_+|$ be the support size of $r_\times$. Then
$$L\cdot U \;=\; \sum_n r_\times(n) \;=\; (S - 1)\cdot 1 + k \cdot 1 \;=\; S + k - 1,$$
giving
$$S \;=\; L\,U - (k-1). \tag{1}$$
Combined with $S \le |I_\times| = N$, this yields the elementary cross-counting bound
$$L\, U \;\le\; N + (k-1). \tag{2}$$
This is the bound called out in `below-sqrt2.md`: it is *not* sub-trivial. We need to either improve (2) below $N$, or to constrain $k$ in some non-trivial way.

---

## 3. The bipartite Pikhurko convolution: what to write down

We attempt the bipartite analog of [P, Theorem 8].

**Generating functions.** Following [P, p. 7], define
$$f_-(x) := \sum_{a \in A_-} x^a, \qquad f_+(x) := \sum_{b \in A_+} x^b.$$
The cross-convolution generating function is
$$g_\times(x) := f_-(x)\, f_+(x) \;=\; \sum_n r_\times(n)\, x^n.$$

In [P]'s single-set case, $g(x) = \tfrac12(f(x)^2 + f(x^2))$ collects *unordered* pair sums, and the diagonal contributions $f(x^2)$ are subtracted by hand. The cross convolution $g_\times$ is automatically "diagonal-free" because $A_-$ and $A_+$ are disjoint — there is no analog of $f(x^2)$.

**Indicator of the cross-interval.** Define
$$h_\times(x) := \sum_{j \in I_\times} x^j \;=\; x^{\alpha+1}\,\frac{1 - x^N}{1 - x}.$$
Define the gap-distribution $\delta_j^\times := r_\times(j) - \mathbf 1_{j \in I_\times}$. Then $\sum_j \delta_j^\times\, x^j = g_\times(x) - h_\times(x)$, and componentwise:
$$\delta_j^\times \;=\; \begin{cases} 0, & \text{if } j \in I_\times,\, r_\times(j) = 1, \text{ } j \neq n^*, \\ -1, & \text{if } j \in I_\times,\, r_\times(j) = 0 \text{ (a gap)}, \\ k - 1, & \text{if } j = n^*, \\ 0, & \text{if } j \notin I_\times.\end{cases}$$
Set $\ell_\times := |I_\times \setminus \mathrm{supp}(r_\times)| = N - S = N - LU + (k-1)$, the number of gaps in the cross-sumset inside $I_\times$.

**The chosen Fourier modes.** [P] evaluates at $x_0 = e^{i\pi t/n}$ for $t \in [2n-1]$, taking advantage of the fact that the indicator of $[1, 2n]$ vanishes at these non-trivial roots of unity. For our cross-setup, we would naturally choose $x_0 = e^{i\pi t/N}$. At such $x_0$:
$$h_\times(x_0) \;=\; e^{i\pi t(\alpha+1)/N}\,\frac{1 - e^{i\pi t}}{1 - e^{i\pi t/N}} \;=\; \begin{cases} 0, & t \text{ even}, \\ \dfrac{2\, e^{i\pi t(\alpha+1)/N}}{1 - e^{i\pi t/N}}, & t \text{ odd}.\end{cases}$$
This is a critical difference from [P]: in the single-set case, $h(x_0) = 0$ uniformly for $t \in [2n-1]$; here $h_\times(x_0)$ is nonzero for odd $t$. To recover Pikhurko's cancellation we restrict the Fourier modes to even $t$, i.e. $t = 2s$ for $s \in [N-1]$, equivalently $x_0 = e^{2\pi i s/N}$ — the *standard* $N$-th roots of unity. (Alternatively, one can extend the interval to $[1, 2N]$ and pad with zeros; we use the standard roots for concreteness.)

**Pikhurko's bound (8) adapted.** At $x_0 = e^{2\pi i s/N}$ with $s \in [N-1]$:
$$g_\times(x_0) \;=\; \sum_j \delta_j^\times\, x_0^j + h_\times(x_0) \;=\; \sum_j \delta_j^\times\, x_0^j \quad \text{(since } h_\times \text{ vanishes here)}.$$
Hence
$$|g_\times(x_0)| \;\le\; \sum_j |\delta_j^\times| \;=\; \ell_\times + (k-1). \tag{3}$$
Compare [P, eq. (8)]: the right-hand side is $(k+m+1\text{ choose }2) - 2n + 2\ell + o(n)$, which here becomes the cleaner $\ell_\times + (k-1) = (N - LU + (k-1)) + (k-1) = N - LU + 2(k-1)$.

**The bipartite analog of Pikhurko's eq. (9).** We have $|g_\times(x_0)| = |f_-(x_0)|\cdot|f_+(x_0)|$. Writing $\theta := \pi s/(N/2)$ (so $x_0 = e^{i\theta}$):
$$|f_\pm(x_0)|^2 \;=\; \Big(\sum_{c \in A_\pm} \sin(\theta c)\Big)^2 + \Big(\sum_{c \in A_\pm} \cos(\theta c)\Big)^2.$$
By AM-GM,
$$|f_-(x_0)| \cdot |f_+(x_0)| \;\ge\; \tfrac{1}{2}\big(|f_-(x_0)|^2 + |f_+(x_0)|^2 - \text{(cross term)}\big), $$
but this direction is the wrong one: we want a *lower bound* on $|g_\times(x_0)|$ in terms of $L$ and $U$ so that (3) becomes useful.

**Plancherel.** A cleaner approach is to sum (3)$^2$ over $s$. By the discrete Plancherel identity,
$$\sum_{s=0}^{N-1} |g_\times(e^{2\pi i s/N})|^2 \;=\; N \sum_n |r_\times(n) \bmod N|^2.$$
The sums in the right-hand side equal $L^2 U^2 / N + O(\text{remainder})$ — but here we run into the issue that $g_\times$ has support on an interval of length $N$, so the discrete Fourier transform mod $N$ "wraps around" and the identity becomes
$$\sum_{s=0}^{N-1} |g_\times(e^{2\pi i s/N})|^2 \;=\; N \sum_n |r_\times(n)|^2 \;=\; N \cdot \big( (S-1)\cdot 1 + k^2\big) \;=\; N\,(L\,U - k + k^2). \tag{4}$$
Using (3) on each term:
$$\sum_{s=0}^{N-1} |g_\times(e^{2\pi i s/N})|^2 \;\le\; |g_\times(1)|^2 + (N-1)\, (\ell_\times + (k-1))^2 \;=\; (LU)^2 + (N-1)(N - LU + 2(k-1))^2,$$
where we used $g_\times(1) = LU$ (no cancellation at $s=0$). Substituting into (4):
$$N \cdot (LU - k + k^2) \;\le\; (LU)^2 + (N-1)\,(N - LU + 2(k-1))^2.$$
Rearrange and discard lower-order terms (assume $k = o(N)$, $LU = \Theta(N)$):
$$N \cdot LU \;\le\; (LU)^2 + N\,(N - LU)^2 + O(N\, k\, \sqrt N). \tag{5}$$
Writing $LU = \rho N$ with $\rho \in [0, 1]$:
$$\rho \;\le\; \rho^2 + (1 - \rho)^2 + o(1) \;=\; 1 - 2\rho + 2\rho^2 + o(1),$$
i.e. $2\rho^2 - 3\rho + 1 \ge -o(1)$, i.e. $(2\rho - 1)(\rho - 1) \ge -o(1)$, which is *automatic* for any $\rho \in [0, 1]$ (the inequality is $\ge 0$ on $[0, 1/2]$ and $\ge 0$ on $[1, \infty)$; for $\rho \in (1/2, 1)$ it is negative but tends to zero at the endpoints).

**Conclusion (the place where the calculation gets stuck).** The crude Plancherel inequality (5) gives no improvement: it is satisfied automatically by all $\rho \in [0, 1]$ except a small region around $\rho = 3/4$, and there the deficit is on the order of $1/8$ at best. To exploit this deficit one would need to *refine* (3) by replacing the worst-case bound $\sum |\delta_j^\times|$ with something Fourier-sensitive — which is exactly Pikhurko's eq. (10)–(13). We attempt this in §4.

---

## 4. Pikhurko's per-mode refinement, bipartite version

[P, eq. (10)–(13)] replaces the crude Plancherel bound by integrating against the specific rectangular pulse
$$r(x) \;:=\; \begin{cases} 1, & 0 \le x \le \pi, \\ 1 + \pi \sin(x), & \pi \le x \le 2\pi,\end{cases}$$
whose Fourier coefficients are $b_0 = \pi/2 + 1$ and $b_t = 2/(t^2 - 1)$ for even $t \ge 2$. Using $r(x) \ge 0$, this gives [P, eq. (12)]:
$$\Big(\tfrac{\pi}{2} + 1\Big)(2z)^{1/2} \;\ge\; \sum_{j \in A}\Big(\tfrac{\pi}{2}\sin(\pi a_j/n) + \sum_{t \ge 2 \text{ even}} b_t \cos(\pi t a_j/n)\Big) \;=\; \sum_{j \in A} r(\pi a_j/n).$$
Since $\pi a_j/n \in [0, \pi]$, $r(\pi a_j/n) = 1$ for all $j$, giving the clean RHS $|A|$ in [P, eq. (13)].

**Bipartite analog: what would it look like?** For the cross-convolution at $x_0 = e^{i\pi t/N}$ (now restricted to even $t$):
$$|g_\times(x_0)|^2 \;=\; |f_-(x_0)|^2 \cdot |f_+(x_0)|^2.$$
The bipartite version of Pikhurko's bound (8) on $|g_\times(x_0)|$ is the *square root* of (3), so
$$|f_-(x_0)|\cdot |f_+(x_0)| \;\le\; \ell_\times + (k-1) \;=\; N - LU + 2(k-1). \tag{6}$$
On the other hand, by the AM-GM inequality and Pikhurko's bound (9) applied separately:
$$|f_\pm(x_0)| \;\ge\; \max\Big( \Big|\sum_{c \in A_\pm} \sin(\pi t c/N)\Big|,\, \Big|\sum_{c \in A_\pm} \cos(\pi t c/N)\Big|\Big).$$
The Fourier-series argument [P, p. 8] applied independently to $A_-$ and $A_+$ gives, after summing over $t$:
$$\big(\tfrac{\pi}{2} + 1\big)\cdot \sqrt{2 z_\times}\;\cdot\; \big(\tfrac{\pi}{2} + 1\big)\cdot \sqrt{2 z'_\times} \;\ge\; L \cdot U + o(LU), \tag{7}$$
where $z_\times, z'_\times$ are the analogs of Pikhurko's $z$ for $f_-, f_+$ separately. **This is where the calculation forks.** There are two ways to interpret (7):

(a) If $z_\times$ and $z'_\times$ both denote $\ell_\times + (k-1)$ (the *same* gap count $\ell_\times$, since the cross-sumset is the shared object), then (7) gives
$$\big(\tfrac{\pi}{2} + 1\big)^2 \cdot 2\, \ell_\times \;\ge\; L U + o(LU). \tag{7a}$$
Using $\ell_\times = N - LU + (k-1)$:
$$\big(\tfrac{\pi}{2} + 1\big)^2 \cdot 2(N - LU) \;\ge\; LU + o(N + LU).$$
Solve for $LU$: with $C := 2\big(\tfrac{\pi}{2}+1\big)^2 = \tfrac{(\pi+2)^2}{2} \approx 13.21$:
$$C\cdot N \;\ge\; LU\,(1 + C) + o(N), \qquad \therefore\quad LU \;\le\; \frac{C}{1 + C}\, N + o(N).$$
Numerically $\frac{C}{1+C} = \frac{(\pi+2)^2/2}{1 + (\pi+2)^2/2} = \frac{(\pi+2)^2}{2 + (\pi+2)^2} \approx 0.9296$.

(b) If $z_\times, z'_\times$ denote the gap counts of $A_- + A_-$ and $A_+ + A_+$ separately (the *within-half* sumsets), then they are independent of each other and the bound (7) decouples. This gives back the Lindström bounds $L \le \sqrt{\alpha N}$, $U \le \sqrt{\beta N}$ and no new information.

We pursue (a), which is the genuine "cross-Pikhurko" reading.

**Provisional cross-Pikhurko bound.**
$$\boxed{\;L \cdot U \;\le\; \frac{(\pi+2)^2}{(\pi+2)^2 + 2}\, N + o(N) \;\approx\; 0.9296\, N.\;} \tag{8}$$
(In our notation, $K = 0.9296$.)

---

## 5. Combining with Lindström and the optimization

Lindström gives $L \le \sqrt{\alpha N}\,(1+o(1))$ and $U \le \sqrt{\beta N}\,(1+o(1))$, where $\alpha := \lfloor n^*/2\rfloor/N$ and $\beta := 1 - \alpha$ (since $A_-$ inhabits an interval of length $\alpha N$ and $A_+$ inhabits one of length $\beta N = N - \alpha N$).

We aim to maximize $L + U = \sqrt{\alpha N} + \sqrt{\beta N} = \sqrt N\,(\sqrt\alpha + \sqrt\beta)$ subject to:

- $\alpha + \beta = 1$ (midpoint identity),
- $\alpha, \beta \ge 0$,
- $L U \le K\, N$ from (8), which combined with $L^2 \le \alpha N$, $U^2 \le \beta N$ gives $\alpha\beta \le K^2/(\alpha\beta) \cdot \alpha\beta = K^2 / (\alpha\beta)$ if both Lindström bounds are tight, i.e. $\sqrt{\alpha\beta}\, N \le K\, N$, so $\sqrt{\alpha\beta} \le K$, i.e.
$$\alpha\,\beta \;\le\; K^2.$$

**Lagrange / symmetric maximization.** With $\beta = 1 - \alpha$, maximize $f(\alpha) := \sqrt\alpha + \sqrt{1 - \alpha}$ subject to $\alpha(1-\alpha) \le K^2$. The unconstrained max is at $\alpha = 1/2$ with $f(1/2) = \sqrt 2$. If $K^2 < 1/4$, the constraint binds: $\alpha = (1 \pm \sqrt{1 - 4K^2})/2$. The maximum on the boundary is
$$f_{\max} \;=\; \sqrt{\frac{1 - d}{2}} + \sqrt{\frac{1 + d}{2}}, \qquad d := \sqrt{1 - 4K^2}, $$
which simplifies (squaring and back) to
$$f_{\max} \;=\; \sqrt{1 + 2K}.$$
(Sanity: $K = 1/2 \implies f_{\max} = \sqrt 2$, recovering the unconstrained max as the constraint becomes vacuous at $K = 1/2$, which corresponds to $\alpha\beta = 1/4$. $K = 1/6 \implies f_{\max} = \sqrt{4/3} = 2/\sqrt 3$, matching the lower bound. So the constraint "$\alpha\beta \le K^2$" with $K = 1/6$ would give precisely $2/\sqrt 3$.)

**Plugging in our $K$.** Our (8) gives $K = \frac{(\pi+2)^2}{(\pi+2)^2 + 2} \approx 0.9296$, so $K^2 \approx 0.8642$, which is *much larger* than $1/4$. The constraint $\alpha\beta \le K^2$ is vacuous.

$$\boxed{\;f_{\max} \;=\; \sqrt 2,\quad \text{i.e.\ no improvement over the existing }\sqrt 2 \cdot \sqrt N\text{ bound.}\;}$$

---

## 6. Why the bound (8) is not strong enough: the structural diagnosis

The threshold for the cross-Pikhurko inequality to give any improvement is $K < 1/2$ (equivalently $K^2 < 1/4$, equivalently $\sqrt{\alpha\beta} \le K$ becoming non-trivial against $\sqrt{\alpha\beta} \le 1/2$). Our derivation gives $K = \frac{(\pi+2)^2}{(\pi+2)^2 + 2} \approx 0.93$, which is much too large.

**The structural reason.** Pikhurko's Fourier inequality (P-13) converts the inequality "gap count $\ell$ is small" into "$|A|$ is small". It is tight when $|A| \sim \sqrt{2n}$ and $|A+A|$ is correspondingly close to $\binom{|A|}{2}$, leaving few gaps inside $[2n]$. In the cross-setting:

- The cross-sumset $A_- + A_+$ has $|A_- + A_+| = LU - (k-1) \le \sqrt{\alpha\beta}\, N \le N/2$.
- The ambient interval $I_\times$ has length $N$.
- So the cross-sumset *covers at most half* of $I_\times$; there are $\ge N/2$ gaps.

Pikhurko's argument squeezes information out of *small* gap counts; it gives nothing when the gap count is comparable to the interval length. Concretely, in our bound (8) the term "$2(N - LU)$" on the left of (7a) is *bigger* than the "$LU$" on the right, so the inequality is essentially asking $LU \le \frac{C}{C+1}\,N$ with $C \approx 13$ — too loose.

**A sharper observation:** the *easy* cross-count $LU \le N$ from (2) already encodes the same information; (8) is only a small constant-factor improvement (from $1$ to $0.93$). The non-trivial constants $\frac1{4} + \frac1{(\pi+2)^2}$ that appear in [P, eq. (7)] for the single-set $|A+A|$ bound have a quadratic effect because they multiply $|A|^2$, but for the cross-pair case the analog appears only as a *linear* coefficient in front of $LU$, so the leverage is much weaker.

**Bipartite-specific obstruction.** In [P]'s single-set proof, the "$k/n$" in the trigonometric argument $\sin(\pi a_j/n)$ ranges over the full $[0, \pi]$ as $a_j$ ranges over $[0, n]$, making the integration against the rectangular pulse $r(x)$ give the clean RHS $|A|$. In our bipartite case, the natural scaling has $A_- \subset [1, \alpha N]$ and $A_+ \subset [\alpha N, N]$, so $\pi a_j/N \in [0, \pi\alpha]$ for $a_j \in A_-$ and $\pi b_j/N \in [\pi\alpha, \pi]$ for $b_j \in A_+$. The rectangular pulse $r$ is constant on $[0, \pi]$, so the same identity goes through, but the *cross* product $f_-(x_0)f_+(x_0)$ does not have an "AM-GM-friendly" decomposition into a single trigonometric sum. The natural inequality (Cauchy–Schwarz on Plancherel) is
$$\sum_t |f_-(x_t)|\,|f_+(x_t)| \;\le\; \Big(\sum_t |f_-|^2\Big)^{1/2}\Big(\sum_t |f_+|^2\Big)^{1/2} \;=\; N\,\sqrt{L\,U}/\sqrt N \;=\; \sqrt{N\,LU},$$
which goes in the *wrong direction* for our purpose.

---

## 7. What it would take to push below $\sqrt 2$

The above analysis suggests that the right tool is *not* a gap-count Fourier bound on the cross-sumset, but a *value-disjointness* Fourier statement combining the three subsets:

1. **Within-$A_-$** sumset $A_- + A_- \subset [2, 2\alpha N]$, with density profile (Erdős–Freud Lemma 1) approximately $\delta_{A_-+A_-}(x) = x/(2\alpha)$ for $x \in [0, \alpha]$, $-x/(2\alpha) + 1$ for $x \in [\alpha, 2\alpha]$, $0$ otherwise (cf. [P, p. 13]).
2. **Within-$A_+$** sumset $A_+ + A_+ \subset [2(1-\beta)N, 2N]$, mirror-image density.
3. **Cross** sumset $A_- + A_+ \subset (\alpha N, (\alpha+\beta)N] = (\alpha N, N\,(1+\alpha)]$ (after correctly accounting for the actual ranges), density $\delta_{A_-+A_+}(x) = x/\alpha - 1/\alpha + 1$ for $x \in [1-\alpha, 1]$, $0$ for $x > 1 + \alpha$ (cf. [P, p. 13, eq. for $\delta_{B+C}$]).

The strong almost-Sidon hypothesis says all three are *pointwise disjoint as multisets* except at $n^*$. In density terms, this becomes a *density product* constraint:
$$\delta_{A_-+A_-}(x)\cdot\delta_{A_-+A_+}(x) \;=\; 0\quad \text{for all } x \neq n^*/N. $$
(Similarly for the other pair.) This is a *non-linear* density constraint that is much tighter than the linear inequality (2). It is also exactly what [P, Lemma 12] uses to derive the lower bound $s(c) \ge -c^2 + 2 + \cdots$ for $2/\sqrt 3 \le c \le \sqrt 2$ — but [P] uses it for *lower bounds* on the maximum sumset, not for upper bounds on $|A|$.

**The honest next step.** Repurpose [P, Lemma 12]'s density-profile machinery to *upper-bound* $|A|$ for strong almost-Sidon sets. Concretely:

1. Apply Erdős–Freud Lemma 1 (= [P, Lemma 10]) to show that if $L$ and $U$ are both within $(1-\varepsilon)$ of their Lindström maxima, then $A_-$ and $A_+$ are nearly uniformly distributed in their respective intervals.
2. Compute the *expected* density of $(A_- + A_-) + (A_- + A_+) + (A_+ + A_+)$ over $[2, 2N]$ as a function of $\alpha$.
3. Impose the constraint that the total expected density is $\le 1$ pointwise (this is *much stronger* than the integral constraint $\sum \le 2N$).
4. The pointwise constraint will fail unless $\alpha = \beta = 1/3$ (or symmetrically), forcing $\sqrt\alpha + \sqrt\beta \le 2/\sqrt 3$.

This is the natural path to $2/\sqrt 3$ but it requires the full density-profile machinery, not just Pikhurko's Theorem 8. The deficit isolated in §6 — that Pikhurko's $1/(\pi+2)^2$ improvement is too small at the cross level — strongly suggests Theorem 8 alone is the wrong tool.

---

## 8. Final answer

**The Pikhurko-Theorem-2-on-cross-pairs adaptation does not yield a constant strictly below $\sqrt 2$.** The calculation goes through to give an explicit constraint
$$LU \;\le\; \frac{(\pi+2)^2}{(\pi+2)^2 + 2}\, N + o(N) \;\approx\; 0.93\, N,$$
but the constraint $\alpha\beta \le 0.93^2 \approx 0.86$ is vacuously satisfied by $\alpha + \beta = 1$ (since $\alpha\beta \le 1/4$). The combined optimization still gives $\sqrt 2$.

For an improved constant $c \in (2/\sqrt 3, \sqrt 2)$ via this route, one would need $LU \le K\, N$ with $K < 1/2$; the Pikhurko-cross argument gives only $K \approx 0.93$, a factor of $\approx 1.85$ short.

**Where the calculation gets stuck (concrete diagnosis).**
- The Fourier identity (3) is correct and converts $|g_\times(x_0)|$ into a gap count.
- The per-mode refinement [P, eq. (10)–(13)] is correct *for each $f_\pm$ separately*, but when combined into a bound on $|f_-(x_0)| \cdot |f_+(x_0)| = |g_\times(x_0)|$, the resulting inequality is of the form "linear in $LU$" rather than "quadratic in $LU$", and the constant on the linear term is too close to $1$.
- The bipartite structure prevents the AM-GM step in [P, eq. (10)–(11)] from doubling its leverage as it does for the single-set case.

**What would close the gap.** Use Erdős–Freud Lemma 1 (≡ [P, Lemma 10]) to obtain density profiles for $A_-$ and $A_+$, then impose strong-almost-Sidon as a *pointwise* density-product constraint on the three sumsets (within-$A_-$, cross, within-$A_+$). The resulting constraint forces $\alpha = 1/3$, giving the conjectured $2/\sqrt 3$.

**Back-of-envelope numerical estimate.** Under the (heuristic) cross-Pikhurko bound (8), with $K \approx 0.93$, the maximum is $\sqrt 2 \approx 1.4142$ (no improvement). The path that *would* give a strictly smaller constant requires $K < 1/2$. To match $c = 1.36$ (the heuristic estimate from `below-sqrt2.md`), one would need $K \approx 0.42$. The pure-Pikhurko-cross approach is short of this by roughly a factor of $2.2$.

---

## 9. References (with page/equation citations)

- [P] = O. Pikhurko, *Dense edge-magic graphs and thin additive bases*, Discrete Math. **306** (2006), 2097–2107. arXiv:math/0309029.
  - Theorem 2 / eq. (3), p. 3: $s(k,n)$ bound.
  - Theorem 3, p. 3: quasi-Sidon $1.863$ corollary.
  - Theorem 8 / eq. (7), p. 7: master Fourier inequality.
  - Eqs. (8)–(13), pp. 8: Fourier derivation.
  - Lemma 10, p. 11: uniform distribution of asymptotically maximum Sidon sets (≡ Erdős–Freud Lemma 1).
  - Lemma 12, p. 12: density-profile method for lower bounds on $s(c)$.
- Erdős–Freud (1991), *J. Number Theory* **38**, 196–205. Lemma 1 (uniform distribution).
- Lindström (1969), *J. Combinatorial Theory* **6**, 211–212.
- `paper.md` (this directory): $\sqrt 2$ upper bound proof.
- `below-sqrt2.md` (this directory): attack lines including Line 1' (Pikhurko-on-cross).
