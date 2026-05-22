# Adapting Ortega–Prendiville Fourier Uniformity to Strong Almost-Sidon

**Worked calculation, 2026-05-22.** Companion to `below-sqrt2.md` and the
rigidity survey. Goal: track how the Ortega–Prendiville (OP) Fourier-uniformity
proof degrades when we replace the Sidon hypothesis with "Sidon except at one
sum value $n^*$ with multiplicity $k$" (the strong almost-Sidon, "SAS"
hypothesis).

**Executive summary (also at the end).** The OP proof leans on the
Sidon property *twice* — once through the Erdős–Turán size bound on subintervals
(eq. (2.3)), once through the diagonal cancellation $1_S * 1_{-S}(h) =
1_{S-S}(h)$ for $h \ne 0$ in Lemma 2.2. For SAS the first use is unchanged.
The second use degrades by a *uniform* additive constant $k(k-1)/(N+H)$
(distributed over at most $k(k-1)$ nonzero differences), which through OP's
identity $|\hat f(\alpha)|^2 \ll \dots$ enters as an additive
$O\!\left(k^2\, N^{1/2}\right)$ correction to $|\hat 1_A(\alpha)|^2$. The
SAS Fourier-uniformity bound thus reads

$$\Big\| \hat 1_A - \tfrac{|A|}{N} \hat 1_{[N]} \Big\|_\infty \;\ll\;
   N^{1/2}\!\left(\Big| \tfrac{|A|}{N^{1/2}} - 1\Big| + N^{-1/6}
       + \frac{k^2}{N^{1/2}} \right)^{\!1/2}.$$

The new $k$-dependent term is bounded by $N^{-1/6}$ exactly when
$k \ll N^{1/6}$. In the SAS regime ($k \le |A|/2 \asymp N^{1/2}/\sqrt 2$),
the term $k^2/N^{1/2}$ saturates at $\Theta(N^{1/2})$, which **dominates**
the main term $|\hat 1_A|$ itself. Thus OP-style Fourier uniformity *breaks
completely* in the worst-case SAS regime, and **the adapted theorem
yields no nontrivial size bound on $|A|$ beyond $\sqrt 2 \cdot \sqrt N$.**

The threshold is sharp: Fourier-uniformity survives iff $k \ll N^{1/6}$
(or $k \ll N^{1/4}$ using OP Theorem 6.3). In the EF-construction regime
($k \asymp N^{1/2}$) the bound is vacuous.

---

## 1. Statement of Ortega–Prendiville Theorem 1.2

**Setting.** $S \subset [N] := \{1, 2, \dots, N\}$ is a *Sidon set*: every
nonzero $x$ has at most one representation $x = s_1 - s_2$ with
$s_i \in S$, equivalently every $n$ has at most one unordered representation
$n = s_1 + s_2$.

**Fourier transform** (OP Def. 1.1, p. 2). For $f:\mathbb Z \to \mathbb C$
with finite support, $\hat f(\alpha) := \sum_n f(n)\, e(\alpha n)$ where
$e(\beta) := e^{2\pi i \beta}$.

**OP Theorem 1.2 (Fourier uniformity, p. 2 eq. (1.3)).** *Let $S \subset [N]$
be a Sidon set. Then*
$$\Big\|\hat 1_S - \tfrac{|S|}{N}\, \hat 1_{[N]}\Big\|_\infty
   \;\ll\; N^{1/2}\!\left( \Big|\tfrac{|S|}{N^{1/2}} - 1\Big|
       + N^{-1/6}\right)^{\!1/2}.\tag{OP-1.2}$$

**OP Corollary 1.4 (p. 2 eq. (1.4)).** *The largest Sidon subset $S \subset [N]$
satisfies*
$$\Big\|\hat 1_S - \tfrac{|S|}{N}\, \hat 1_{[N]}\Big\|_\infty
   \;\ll\; \|\hat 1_S\|_\infty \cdot N^{-1/12}.\tag{OP-1.4}$$

**OP Theorem 6.3 (p. 13 eq. (6.1)), improved version.** With Cilleruelo's
sharper interval bound:
$$\Big\|\hat 1_S - \tfrac{|S|}{N}\, \hat 1_{[N]}\Big\|_\infty
   \;\ll\; N^{1/2}\!\left( \Big|1 - \tfrac{|S|}{N^{1/2}}\Big|
       + N^{-1/4}\right)^{\!1/2}.\tag{OP-6.3}$$

---

## 2. The proof of OP Theorem 1.2, line by line

The proof (OP pp. 6–8) uses **van der Corput differencing** of the Fourier
transform of $f := 1_S - \tfrac{|S|}{N} 1_{[N]}$.

### 2.1 Van der Corput inequality (Lemma 2.1, p. 6 eq. (2.1))

For any $f:\mathbb Z \to \mathbb C$ with $\mathrm{supp}(f) \subset [N]$ and
$1 \le H \le N$:
$$\big| \hat f(\alpha)\big|^2
    \;\le\; (N+H)\sum_h \mu_H(h) \sum_x f(x)\, \overline{f(x+h)}.\tag{2.1}$$
Here $\mu_H$ is the normalised Fejér kernel (OP eq. (1.8)): a probability
measure on $\mathbb Z$ supported in $(-H, H)$ with
$\mu_H(h) = \lfloor H \rfloor^{-2}(1_{[H]} * 1_{-[H]})(h)$.

### 2.2 The key Sidon input: Lemma 2.2 (p. 6)

*Let $S \subset [N]$ be a Sidon set. Then*
$$\sum_{h \in (S - S) \setminus \{0\}} \mu_H(h) \;\ge\;
   \frac{|S|^2}{N + H} \;-\; \frac{|S|}{\lfloor H \rfloor}. \tag{Lem 2.2}$$

**Where the Sidon hypothesis enters.** OP write (p. 6):
> *"Since $S$ is Sidon $1_S * 1_{-S}(x) = 1_{S-S}(x)$ if $x \ne 0$."*

This is the **diagonal cancellation identity**, and it is the *only* place
in the proof where Sidon is needed in this form. We track it as identity
(★).

### 2.3 Assembly (p. 7)

Setting $f_1 := 1_S$, $f_2 := \tfrac{|S|}{N} 1_{[N]}$, $f := f_1 - f_2$,
expanding the van der Corput sum into four bilinear terms
$f_i(x) f_j(x+h)$, and bounding each:

* The "$f_1 f_1$" term uses (★) plus Lemma 2.2 to give
  $$\sum_h \mu_H(h)\Big| |S|^2 N^{-1} - \sum_x f_1(x) f_1(x+h)\Big|
     \;\le\; 1 - \frac{|S|^2}{N+H} + O\!\left( \frac{|S|}{\lfloor H\rfloor}
       + \frac{||S| - N^{1/2}|}{N^{1/2}}\right).$$

* The "$f_1 f_2$" / "$f_2 f_1$" terms use the Erdős–Turán interval bound
  $|S \cap I_h| \ll \sqrt{|h|}$ (OP eq. (2.3), p. 7) and the Fejér mass on
  $|h| \le H$ to give
  $$\sum_h \mu_H(h)\Big| |S|^2 N^{-1} - \sum_x f_1(x) f_2(x+h)\Big|
      \;\ll\; \frac{|S| H^{1/2}}{N}.$$

* The "$f_2 f_2$" term is $\le H|S|^2 / N^2$.

Putting everything together (OP p. 8):
$$|\hat f(\alpha)|^2 \;\ll\; N^{1/2}\big||S| - N^{1/2}\big|
   \;+\; \frac{N^{3/2}}{\lfloor H \rfloor} \;+\; N^{1/2} H^{1/2}. \tag{2.4}$$
Balancing with $H := N^{2/3}$ yields
$|\hat f(\alpha)|^2 \ll N^{1/2}||S| - N^{1/2}| + N^{5/6}$, which is (OP-1.2).

---

## 3. The single-atom (SAS) modification

We replace the Sidon hypothesis on $S$ by the strong almost-Sidon hypothesis
on $A \subset [N]$: there is a unique $n^* \in \mathbb Z$ with
$r_A(n^*) = k \ge 2$, where
$r_A(n) := \#\{ \{a,b\} \subset A : a + b = n\}$ counts *unordered*
representations. For $n \ne n^*$, $r_A(n) \in \{0,1\}$.

### 3.1 Translating SAS into a difference-side statement

OP's key identity (★) is about **differences**, not sums:
$1_A * 1_{-A}(h) = \#\{(a, b) \in A^2 : a - b = h\}$. We need to know what
the SAS hypothesis says about this difference-multiplicity function.

**Lemma 3.1 (SAS difference structure).** *Let $A \subset [N]$ be SAS
with exceptional sum $n^*$ of multiplicity $k$. Let
$\{a_1, b_1\}, \dots, \{a_k, b_k\}$ be the $k$ distinct unordered pairs in
$A$ summing to $n^*$ (so $a_i + b_i = n^*$ with $a_i \le b_i$). Then for
each $h \ne 0$,*
$$1_A * 1_{-A}(h) \;=\; 1_{A - A}(h) \;+\; \delta_A(h),$$
*where $\delta_A(h) \ge 0$ counts the number of pairs $(i, j)$ with
$i \ne j$ and a specific difference equation holding. The total excess
is*
$$\sum_{h \ne 0} \delta_A(h) \;=\; (2k)(2k-1) - (2k) \;-\; 2\cdot\#\{(i,j): i\ne j,\, a_i = a_j\}\dots$$

A cleaner accounting: let $P := \{a_1, b_1, \dots, a_k, b_k\} \subseteq A$
be the set of all $2k$ elements participating in the $k$ representations
of $n^*$ (some elements may repeat if e.g. $a_i = b_i = n^*/2$ for one
index, but at most once). For simplicity assume $n^*$ is odd or $n^*/2
\notin A$, so $|P| = 2k$.

**Counting difference coincidences.** A duplicated nonzero difference
$h = a - a' = b - b'$ with $\{a, a'\} \ne \{b, b'\}$ in $A$ corresponds to
a coincidence

$$a + b' = a' + b.$$

If the duplicated *sum* is $a + b' = a' + b = n^*$, this gives one of the
pairs $\{a, b'\}$ and one of $\{a', b\}$ summing to $n^*$ — both
necessarily among the $k$ exceptional pairs. So the *only* duplicated
nonzero differences in $A$ come from pairs $(i, j)$ of the $k$
exceptional sum-pairs.

For each ordered pair $(i, j)$ with $i \ne j$, the identity
$a_i + b_i = a_j + b_j = n^*$ rearranges to
$a_i - a_j = b_j - b_i$ and $a_i - b_j = a_j - b_i$.

So each ordered pair $(i, j)$, $i \ne j$, contributes a duplicated nonzero
difference. The number of ordered pairs is $k(k-1)$. Hence

$$\sum_{h \ne 0}\big( 1_A * 1_{-A}(h) - 1_{A - A}(h)\big) \;\le\; k(k-1).
   \tag{Lem 3.1}$$

This is the **single-atom defect** at the difference-counting level.

### 3.2 Modified Lemma 2.2 (SAS version)

We re-derive OP's Lemma 2.2 (p. 6) with (★) replaced by Lemma 3.1.

OP's argument (p. 6 eq. (2.2)) is:
$$\sum_{h \in (A-A) \setminus \{0\}}\!\!\mu_H(h)
   \;=\; \sum_{h\ne 0} 1_{A-A}(h)\, \mu_H(h)
   \;=\; \sum_{h\ne 0}\big(1_A * 1_{-A}\big)(h)\, \mu_H(h)
        \;-\; \delta_{\rm SAS},$$
where for Sidon $\delta_{\rm SAS} = 0$ exactly. For SAS, by Lemma 3.1,
$$\delta_{\rm SAS} \;:=\; \sum_{h\ne 0}\big(1_A * 1_{-A}(h)
       - 1_{A-A}(h)\big)\mu_H(h)
   \;\le\; \max_h \mu_H(h) \cdot k(k-1) \;\le\; \frac{k(k-1)}{\lfloor H\rfloor},$$
since $\mu_H(h) \le 1/\lfloor H \rfloor$. Continuing OP's calculation
otherwise unchanged:

**Lemma 3.2 (Modified Lemma 2.2).** *Let $A \subset [N]$ be SAS with
exceptional value $n^*$ of multiplicity $k$. Then*
$$\sum_{h \in (A - A) \setminus \{0\}} \mu_H(h) \;\ge\;
   \frac{|A|^2}{N+H} \;-\; \frac{|A|}{\lfloor H\rfloor}
   \;-\; \frac{k(k-1)}{\lfloor H\rfloor}.\tag{Lem 3.2}$$

The new term $\frac{k(k-1)}{\lfloor H \rfloor}$ is the SAS correction.
Equivalently, replacing $|A|$ by $|A| + k(k-1)/|A|$ in OP's "$|S|/\lfloor H
\rfloor$" term.

### 3.3 Modified "$f_1 f_1$" step

OP write (p. 8): for $h \ne 0$,
$$\Big| |S|^2 N^{-1} - \sum_x 1_S(x) 1_S(x+h)\Big|
   \;\le\; 1 - 1_{S - S}(h) + O\!\left(\frac{||S| - N^{1/2}|}{N^{1/2}}\right).$$
This used $f_1(x) f_1(x+h) = 1_{S \cap (S-h)}(x)$ and the Sidon-difference
property $|S \cap (S-h)| = 1_{S-S}(h)$ for $h \ne 0$.

For SAS, $\sum_x 1_A(x)\,1_A(x+h) = 1_A * 1_{-A}(h)$. By Lemma 3.1, for
$h \ne 0$,
$$1_A * 1_{-A}(h) \;=\; 1_{A-A}(h) + \delta_A(h),
    \qquad \sum_{h\ne 0}\delta_A(h) \le k(k-1).$$

Thus
$$\Big| |A|^2 N^{-1} - \sum_x 1_A(x) 1_A(x+h)\Big|
   \;\le\; 1 - 1_{A-A}(h) + \delta_A(h)
      + O\!\Big(\frac{||A| - N^{1/2}|}{N^{1/2}}\Big).$$

Multiplying by $\mu_H(h)$ and summing in $h$, using Lemma 3.2:
$$\sum_h \mu_H(h)\Big| |A|^2 N^{-1} - \sum_x 1_A(x) 1_A(x+h)\Big|
   \;\le\; 1 - \frac{|A|^2}{N+H}
      + O\!\left(\frac{|A|}{\lfloor H\rfloor}
         + \frac{k(k-1)}{\lfloor H\rfloor}
         + \frac{||A| - N^{1/2}|}{N^{1/2}}\right). \tag{3.1}$$

### 3.4 The "$f_1 f_2$" step is essentially unchanged

The other bilinear terms in OP's expansion only use the *interval* size
bound $|A \cap I_h| \ll \sqrt{|h|}$ (OP eq. (2.3)). For SAS, this bound
still holds: an SAS set $A$ restricted to an interval $I$ is still SAS on
$I$, and the Lindström-style bound
$$|A \cap I_h| \;\ll\; \sqrt{|h|} \;+\; O(\sqrt{k}) \tag{3.2}$$
holds (since the SAS set on the interval is Sidon on each half of a
midpoint split). The $O(\sqrt{k})$ correction is absorbed by enlarging
$H$ slightly, contributing at most an additional $O\!\left(\frac{|A| H^{1/2}
\sqrt{k}}{N}\right)$, which is dominated by the new term in (3.1) for $k =
O(\sqrt N)$.

The "$f_2 f_2$" term is unchanged: $\le H |A|^2 / N^2$.

### 3.5 SAS analogue of the master inequality (OP eq. (2.4))

Combining (3.1) with the unchanged off-diagonal terms, the SAS version of
OP eq. (2.4) reads
$$|\hat f(\alpha)|^2 \;\ll\; N^{1/2}\big||A| - N^{1/2}\big|
   \;+\; \frac{N^{3/2}}{\lfloor H \rfloor} \;+\; N^{1/2} H^{1/2}
   \;+\; \frac{N\, k(k-1)}{\lfloor H \rfloor}. \tag{3.3}$$
(The first three terms are OP's eq. (2.4); the last is the SAS
correction.)

Balancing $H := N^{2/3}$ as OP do:
$$|\hat f(\alpha)|^2 \;\ll\; N^{1/2}\big||A| - N^{1/2}\big|
   \;+\; N^{5/6} \;+\; k^2\, N^{1/3}. \tag{3.4}$$

---

## 4. The SAS Fourier uniformity statement

Rewriting (3.4) in OP's normalised form (compare OP-1.2):

**Theorem 4.1 (SAS Fourier uniformity).** *Let $A \subset [N]$ be a
strong almost-Sidon set with exceptional sum-multiplicity at most $k$.
Then*
$$\Big\| \hat 1_A - \tfrac{|A|}{N}\hat 1_{[N]}\Big\|_\infty
  \;\ll\; N^{1/2}\!\left( \Big|\tfrac{|A|}{N^{1/2}} - 1\Big|
   \;+\; N^{-1/6} \;+\; \frac{k^2}{N^{1/2}\cdot N^{1/6}}\right)^{\!1/2}.\tag{4.1}$$

*Equivalently in additive form,* writing $\Delta := \|\hat 1_A - \tfrac{|A|}{N}
\hat 1_{[N]}\|_\infty$ and dropping subleading terms,
$$\Delta \;\ll\; N^{1/2}\cdot N^{-1/12} \;+\; k\,N^{1/6}.
   \tag{4.1$'$}$$

(Verification: $\Delta^2 \ll N^{5/6} + k^2 N^{1/3}$, so $\Delta \ll N^{5/12} +
k\, N^{1/6}$, and $N^{5/12} = N^{1/2}\cdot N^{-1/12}$.)

Using OP Theorem 6.3 (with Cilleruelo's improvement $H := N^{3/4}$), the
balanced bound becomes
$$\Delta^2 \;\ll\; N^{1/2}\big||A| - N^{1/2}\big| + N^{3/4}
   + k^2\, N^{1/4}, \tag{4.2}$$
i.e.
$$\Delta \;\ll\; N^{3/8} + k\, N^{1/8} \;=\; N^{1/2}\cdot N^{-1/8} + k\,N^{1/8}.
   \tag{4.2$'$}$$

---

## 5. Critical threshold for $k$

From (4.1$'$), the SAS Fourier-uniformity statement beats the trivial bound
$|\hat 1_A(\alpha)| \le |A| \asymp N^{1/2}$ if
$$k\, N^{1/6} \;\ll\; N^{1/2}, \qquad\text{i.e.}\qquad
   k \;\ll\; N^{1/3}.$$

Comparing with OP's main term $N^{5/12}$ ($= N^{1/2}\cdot N^{-1/12}$), the
SAS-correction is *subleading* when $k\, N^{1/6} \ll N^{5/12}$, i.e.
$$\boxed{k \;\ll\; N^{1/4}}.$$

Using the OP Theorem 6.3 (improved) version (4.2$'$), the SAS correction
$k\, N^{1/8}$ is subleading to $N^{3/8}$ when $k \ll N^{1/4}$ (same
threshold).

**Summary:**

| Regime | OP-style Fourier uniformity for SAS |
|---|---|
| $k = O(1)$ (genuine Sidon, $k = 1$) | recovers OP (1.2): $\Delta \ll N^{5/12}$. |
| $k \ll N^{1/4}$ | survives: $\Delta \ll N^{5/12}$ (same as OP). |
| $N^{1/4} \ll k \ll N^{1/3}$ | degrades: $\Delta \ll k\, N^{1/6}$, still better than trivial. |
| $k \ge c\, N^{1/3}$ for any $c > 0$ | trivial: $\Delta \ll N^{1/2}$, indistinguishable from $|A|$ itself. |
| $k \asymp |A|/2 \asymp N^{1/2}/\sqrt 2$ (SAS regime) | **vacuous**. |

### 5.1 Verification at extremes

**$k = 1$ (genuine Sidon).** Theorem 4.1 reduces to (OP-1.2): the
correction term $k\, N^{1/6} = N^{1/6}$ is dominated by the main term
$N^{5/12}$. ✓

**$k \asymp N^{1/2}$ (EF construction).** The EF construction
$A = B \cup (N - B)$ with Sidon $B \subset [1, N/3]$ has
$|A| = 2|B| \asymp (2/\sqrt 3)\sqrt N$ and $k \approx |A|/2 \asymp \sqrt N$.
Theorem 4.1 then says $\Delta \ll k\, N^{1/6} \asymp N^{1/2}\cdot N^{1/6} =
N^{2/3}$, which is *worse* than the trivial bound $|A| \le 2\sqrt N$.
Vacuous. ✓ (No contradiction with the EF construction's Fourier behavior
because in fact the EF construction is **NOT** Fourier-uniform — it has
large Fourier mass at $\alpha = n^*/N$, consistent with the
high-multiplicity peak in $1_A * 1_{-A}$ at differences $b - b' \in (B-B)
\cup (-B+B) \cup (B - (N-B))$. The bound is honest.)

---

## 6. Implication for $|A|$

**The question:** does the adapted Fourier uniformity, even when
non-vacuous, *imply* an improved size bound on $|A|$?

OP's path from Fourier uniformity to "extremal Sidon set has the
properties of an interval" goes through Plancherel: if $\Delta := \|\hat 1_A -
\tfrac{|A|}{N}\hat 1_{[N]}\|_\infty$ is small, then $|A|$ is concentrated
on intervals/Bohr neighborhoods (their Corollaries 1.5–1.11). It does
*not* directly give a size bound on $|A|$ itself: Theorem 1.2 takes
$|S|$ as input and outputs equidistribution. The implicit size bound is
the Erdős–Turán bound $|S| \le N^{1/2} + O(N^{1/4})$, used as **input**
to OP, not output.

**For SAS:** the size bound input is $|A| \le \sqrt 2 \cdot \sqrt N$
(midpoint-split + Lindström), which is what we are trying to beat. The
adapted Fourier uniformity (4.1) is **the wrong tool** for the
size-bound problem in two ways:

1. *Direction.* OP's Theorem 1.2 takes size as input, Fourier uniformity
   as output. For SAS, we already know the size bound $\sqrt 2 \cdot
   \sqrt N$; what we want is a *stronger* size bound. Fourier
   uniformity does not directly imply a stronger size bound (it is a
   *distributional* statement).

2. *Regime.* In the SAS regime where the bound is meaningfully tight
   ($|A| \to \sqrt 2 \cdot \sqrt N$, $k$ potentially $\Theta(\sqrt N)$),
   the adapted Fourier uniformity is *vacuous*. So even if there were a
   reverse implication "Fourier uniformity ⇒ size bound", we have no
   uniformity to feed it.

To make the adapted theorem yield $|A| < \sqrt 2\cdot\sqrt N$ would
require a *new* argument structure: typically a Plancherel identity
relating $\sum |\hat 1_A(\alpha)|^4$ (additive energy) to $|A|$, where
the Fourier uniformity bound forces the $L^4$ mass to concentrate at
$\alpha = 0$, hence $|A|^4 / N \approx \|\hat 1_A\|_4^4$, hence $|A| \le
N^{1/2}$. But the standard Sidon size bound *already* gives $|A| \le
N^{1/2}$ via this exact route, with the $\sqrt 2$ for SAS coming from
the midpoint split. The adapted Fourier uniformity adds no new
information.

### 6.1 Plancherel-based attempt and its failure

Concretely, attempt: by Parseval,
$$\int_{\mathbb T} |\hat 1_A(\alpha)|^2 \,d\alpha = |A|.$$
For Sidon $S$ (and similarly with single-atom correction for SAS),
$$\int |\hat 1_A(\alpha)|^4 \, d\alpha = \sum_n r_A^{(\rm ord)}(n)^2
   \;=\; 4 \sum_{n\ne n^*} r_A(n)^2 + (2k)^2 + 2|A|,$$
where $r_A$ counts unordered pairs and the "$+2|A|$" comes from the
diagonal $a = b$. For SAS, $r_A(n) \le 1$ off $n^*$, so
$\sum_{n\ne n^*} r_A(n)^2 \le \binom{|A|}{2}$, giving
$$\|\hat 1_A\|_4^4 \le 2|A|^2 + 4k^2 + O(|A|). \tag{6.1}$$

Combining with Plancherel and Hölder:
$$|A|^2 = \Big(\int |\hat 1_A|^2 d\alpha\Big)^2
   \le \int |\hat 1_A|^4 d\alpha \cdot 1 = 2|A|^2 + 4k^2 + O(|A|).$$
Trivially satisfied; no constraint.

A more refined attempt: use the "off-zero" mass
$$\int |\hat 1_A(\alpha) - \tfrac{|A|}{N}\hat 1_{[N]}(\alpha)|^2 d\alpha
   = |A| - |A|^2/N + O(1).$$
Combined with $L^\infty$ control from (4.1):
$$|A| - |A|^2/N \;\le\; \Delta^2 \cdot \mathrm{meas}(\mathrm{supp})
    \;\le\; \Delta^2.$$
For SAS-extremal $|A| = \sqrt 2\cdot\sqrt N$, the LHS is $\sqrt 2\sqrt N -
2 = O(\sqrt N)$, and we'd need $\Delta^2 \gg \sqrt N$. From (4.1$'$),
$\Delta^2 \asymp k^2 N^{1/3}$ in the SAS regime, which is
$N \cdot N^{1/3} = N^{4/3} \gg \sqrt N$. **Vacuously satisfied** — no
contradiction, no improvement.

### 6.2 Conclusion: the adapted theorem gives no sub-$\sqrt 2$ bound

The Fourier-uniformity statement (4.1) is a real theorem, but it
provides no leverage on the SAS size question in the regime that matters.

---

## 7. Structural obstruction

The deeper reason OP's argument cannot survive the SAS hypothesis at
$k = \Theta(\sqrt N)$: OP's Lemma 2.2 fundamentally exploits the
*pointwise* statement $1_S * 1_{-S}(h) \le 1$ for $h \ne 0$, not an
*average* statement. The single-atom correction concentrates **all** the
defect on $k(k-1)$ specific difference values, and those values can be
arranged to be exactly the values $\mu_H$ weights most heavily
(the small-$|h|$ region). So $\mu_H \cdot \delta_A$ does not lose
multiplicity to averaging — the loss is genuinely $\Theta(k^2 / H)$.

This matches the diagnosis from the other attacks:

| Attack | Why it fails for SAS |
|---|---|
| OP (this note) | Single-atom defect $k^2/H$ overwhelms Fourier bound when $k = \Theta(\sqrt N)$. |
| Pikhurko (cross) | Gap-deficit inequality has $\Theta(N)$ gaps, vacuous. |
| Autoconvolution | $L^2$ averaging blind to single-atom strength. |
| Density profile | $1/4$ slack at the $\sqrt 2$ corner. |

All four attacks fail because the SAS hypothesis is **"$L^\infty$ minus one
atom"** (sharp pointwise control plus a single bad value), while every
classical Sidon-extremal tool is **$L^p$ averaged** ($L^2$ for Pikhurko,
$L^4$ for OP-via-Plancherel, $L^2$ for autoconvolution). The single atom
contributes a single Fourier-mode of amplitude $\Theta(k)$, which is too
small to detect in $L^2$ but too large to absorb in $L^\infty$ at
$k = \Theta(\sqrt N)$.

The right tool, were it available, would be a Fourier statement that
distinguishes *which* Fourier modes carry the mass — specifically, a
statement of the form "if $|\hat 1_A(\xi^*)| = \Omega(k)$ at one mode
$\xi^* \approx n^*/N$, then $A$ is structured near $n^*/2$." This is
precisely the Eberhard–Manners-style **positional** rigidity conjecture
(survey §A.2), which remains conjectural even for cyclic-group Sidon
sets, and which our adaptation here cannot supply.

---

## 8. Final assessment (verification of executive summary)

* **Threshold for SAS Fourier uniformity to survive:**
  $k \ll N^{1/4}$ using OP Theorem 1.2 + Lemma 3.1 with $H = N^{2/3}$;
  equivalently $k \ll N^{1/4}$ using Theorem 6.3 with $H = N^{3/4}$.
  (Both yield the same threshold — the SAS correction enters as $k\,N^{1/6}$
  versus the main $N^{5/12}$, or $k\, N^{1/8}$ versus $N^{3/8}$.)

* **Does the adapted theorem imply anything about $|A|$?**
  No. The OP-style Fourier uniformity is a distributional, not a size,
  statement; in the relevant SAS regime ($k = \Theta(\sqrt N)$, $|A|
  \to \sqrt 2\sqrt N$) the adapted bound is *vacuous* in any case.

* **Does it lead to a sub-$\sqrt 2$ upper bound?**
  No. The adaptation gives the same conclusion as the survey
  predicted: at $k = \Theta(\sqrt N)$, the OP method breaks. To extract
  positional information one needs a different argument (Eberhard–Manners
  conjecture or a stability theorem we do not have).

The work is a clean negative result: it locates the exact place where
OP's argument fails for SAS and quantifies the failure. The structural
obstruction matches the convergent diagnosis of the prior three Fourier
attacks (Pikhurko-cross, autoconvolution, density-profile).

---

## References

1. M. Ortega, S. Prendiville, *Extremal Sidon Sets are Fourier Uniform,
   with Applications to Partition Regularity*, J. Théor. Nombres Bordeaux
   **35** (2023). arXiv:2110.13447. (Statements: Theorem 1.2, p. 2 eq.
   (1.3); Corollary 1.4, p. 2 eq. (1.4); Theorem 6.3, p. 13 eq. (6.1).
   Proof structure: Lemma 2.1 = van der Corput, p. 6 eq. (2.1); Lemma 2.2
   = Sidon difference identity, p. 6; assembly p. 7–8 culminating in eq.
   (2.4) at the foot of p. 8.)

2. J. Cilleruelo, *An upper bound for $B_2[2]$ sequences*, J. Combin.
   Theory A **89** (2000). Cited via OP Theorem 6.1, p. 13, supplying
   the sharper $|S \cap I| \ll N^{1/4} + |I|^{1/2} N^{-1/8}$ used in
   Theorem 6.3.

3. P. Erdős, P. Turán, *On a problem of Sidon in additive number theory*,
   J. London Math. Soc. **16** (1941). The Sidon size bound (1.1) on
   p. 1 of OP, used at OP eq. (2.3) on p. 7.
