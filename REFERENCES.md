# References

Formal bibliography for the Erdős Problems in Lean 4 project.
Citation keys match doc-comments in the Lean source.

---

## Problem #242: Erdős-Straus Conjecture

- **[Mo67]** Mordell, L. J. (1967). "Diophantine equations."
  Academic Press. Polynomial identities covering all n except finitely
  many residue classes mod 840.

- **[Sc56]** Schinzel, A. (1956). "Sur quelques propriétés des nombres
  3/n et 4/n, où n est un nombre impair." *Mathesis*, 65, 219–222.
  **Fundamental limitation**: no polynomial identity system can cover
  quadratic residue classes.

- **[Va70]** Vaughan, R. C. (1970). "On a problem of Erdős, Straus and
  Schinzel." *Mathematika*, 17, 193–198.
  Exceptions up to N are O(N^{3/4}).

- **[ET13]** Elsholtz, C. & Tao, T. (2013). "Counting the number of
  solutions to the Erdős-Straus equation on unit fractions."
  *J. Aust. Math. Soc.*, 94(1), 50–105.
  [arXiv:1107.1010](https://arxiv.org/abs/1107.1010).
  Solution count: N log²N ≪ Σ f(p) ≪ N log²N · log log N.

- **[Sa14]** Salez, S. (2014). "The Erdős-Straus conjecture: new modular
  equations and checking up to 10^{17}."
  [arXiv:1406.6307](https://arxiv.org/abs/1406.6307).

- **[BE22]** Bloom, T. & Elsholtz, C. (2022). "Egyptian fractions."
  *Nieuw Archief voor Wiskunde*, 23(4), 237–244.
  [Survey](https://www.nieuwarchief.nl/serie5/pdf/naw5-2022-23-4-237.pdf).

- **[Br24]** Bradford, K. (2024). "Elemental patterns from the Erdős
  Straus conjecture."
  [arXiv:2403.16047](https://arxiv.org/abs/2403.16047).

- **[Gh25]** Ghermoul, B. (2025). "Exact polynomial families solving the
  Erdős-Straus equation."
  [arXiv:2508.07383](https://arxiv.org/abs/2508.07383).

- **[PW25]** Pomerance, C. & Weingartner, A. (2025). "Exceptions to the
  Erdős–Straus–Schinzel conjecture."
  [arXiv:2511.16817](https://arxiv.org/abs/2511.16817).

- **[MD25]** Mihnea, S. & Bogdan, D. C. (2025). "Further verification and
  empirical evidence for the Erdős-Straus conjecture."
  [arXiv:2509.00128](https://arxiv.org/abs/2509.00128).
  Verified to 10^{18} using Salez-type modular equations.

- **[Br26]** Bradford, K. (2026). "A solution to the Straus-Erdős
  conjecture."
  [arXiv:2602.11774](https://arxiv.org/abs/2602.11774).
  **Status: CRITICAL GAP** — Schinzel barrier blocks the covering claim.

---

## Problem #470: Weird Numbers

- **[BE74]** Benkoski, S. J. & Erdős, P. (1974). "On weird and
  pseudoperfect numbers." *Mathematics of Computation*, 28(126), 617–623.
  Weird numbers have positive density; pn construction; primitive weird
  numbers defined.

- **[Si65]** Sierpiński, W. (1965). "Sur les nombres pseudoparfaits."
  *Matematički Vesnik*, 2(17), 212–213.
  Original definition of pseudoperfect numbers.

- **[ZZ72]** Zachariou, A. & Zachariou, E. (1972). "Perfect, semiperfect
  and Ore numbers." *Bull. Soc. Math. Grèce*, 13, 12–22.
  Classification and structural results for semiperfect numbers.

- **[Kr76]** Kravitz, S. (1976). "A search for large weird numbers."
  *Journal of Recreational Mathematics*, 9(2), 82–85.
  Large primitive weird number construction via Mersenne primes.

- **[Fr93]** Friedman, C. N. (1993). "Sums of divisors and Egyptian
  fractions." *Journal of Number Theory*, 44(3), 328–339.
  **Key reference for the pseudoperfect ↔ unit-fraction bridge**:
  n is pseudoperfect iff some subset of divisors > 1 has reciprocals
  summing to 1. Used in our `pseudoperfect_iff_unit_sum`.

- **[BJM00]** Butske, W., Jaje, L. M. & Mayernik, D. R. (2000). "On the
  equation ∑_{p|N} 1/p + 1/N = 1, pseudoperfect numbers, and perfectly
  weighted graphs." *Mathematics of Computation*, 69(229), 407–420.

- **[Me15]** Melfi, G. (2015). "On the conditional infiniteness of
  primitive weird numbers." *Journal of Number Theory*, 147, 508–514.

- **[LR18]** Liddy, J. & Riedl, E. (2018). "Odd weird numbers have at
  least 6 distinct prime factors." Preprint.

- **[AHMP19]** Amato, G., Hasler, M. F., Melfi, G. & Parton, M. (2019).
  "Primitive abundant and weird numbers with many prime factors."
  *Journal of Number Theory*, 201, 436–459.
  [arXiv:1802.07178](https://arxiv.org/abs/1802.07178).

- **[Fa22]** Fang, W. (2022). "Searching on the boundary of abundance for
  odd weird numbers."
  [arXiv:2207.12906](https://arxiv.org/abs/2207.12906).
  No odd weird number below 10^{21}.

- **[MS25]** McNew, N. & Setty, J. (2025). "On the densities of covering
  numbers and abundant numbers."
  [arXiv:2507.23041](https://arxiv.org/abs/2507.23041).

---

## Problem #327: Unit Fraction Pairs

- **[EG80]** Erdős, P. & Graham, R. L. (1980). *Old and New Problems and
  Results in Combinatorial Number Theory*. L'Enseignement Mathématique,
  Université de Genève. Original problem statement.

- **[vD]** van Doorn, W. "Upper bound f(N) ≤ (25/28+o(1))N." Contribution
  at [erdosproblems.com](https://www.erdosproblems.com/327).

- **[Ad]** Adenwalla, S. "Positive answer to Q1 implies negative answer
  to Q2." Contribution at
  [erdosproblems.com](https://www.erdosproblems.com/327).

---

## Problem #302: Unit Fraction Triples

- **[EG80]** Erdős & Graham (1980). See above. Original problem statement.

- **[Ca]** Cambie, S. "Lower bound f(N) ≥ (5/8+o(1))N." Contribution at
  [erdosproblems.com](https://www.erdosproblems.com/302).

- **[vD]** van Doorn, W. "Upper bound f(N) ≤ (9/10+o(1))N." Contribution
  at [erdosproblems.com](https://www.erdosproblems.com/302).

- **[BR91]** Brown, T. C. & Rödl, V. (1991). "Monochromatic solutions to
  equations with unit fractions." *Bull. Aust. Math. Soc.*, 43(3),
  387–392. Coloring version (#303): any finite coloring has
  monochromatic 1/a = 1/b + 1/c.

---

## Problem #301: Unit Fraction Sum-Free Sets

- **[EG80]** Erdős & Graham (1980). See above. Original problem statement.

- **[Bl21]** Bloom, T. (2021). "On a density conjecture about unit
  fractions." [arXiv:2112.03726](https://arxiv.org/abs/2112.03726).
  Any set of positive upper density contains finite subset with
  reciprocals summing to 1.

- **[BM]** Bloom, T. & Mehta, B. "Formalisation of Bloom's theorem in
  Lean." [b-mehta.github.io/unit-fractions](https://b-mehta.github.io/unit-fractions/).
  Hardy-Littlewood circle method formalized in Lean.

- **[LS24]** Liu, J. & Sawhney, M. (2024). "On a conjecture of Erdős on
  unit fractions." [arXiv:2404.07113](https://arxiv.org/abs/2404.07113).
  |A| ≥ (1−1/e+ε)N suffices; 1−1/e is sharp.

- **[vD]** van Doorn, W. "Upper bound f(N) ≤ (25/28+o(1))N." Same
  construction works for both #301 and #327. Contribution at
  [erdosproblems.com](https://www.erdosproblems.com/301).
