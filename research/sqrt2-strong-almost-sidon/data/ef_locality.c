/*
 * ef_locality.c — Test whether the Erdős–Freud (EF) reflection construction
 *                 is a *local maximum* for strong almost-Sidon (SAS) sets.
 *
 * For each N in a given set, we:
 *
 *   1. Construct a Sidon set B in [1, ⌊N/3⌋] using Singer / Erdős–Turán
 *      (when N/3 ≈ q²+q+1 or 2p²), augmented by a greedy extension. We
 *      do NOT necessarily achieve the absolute maximum, but the lower
 *      bound matches the EF asymptotic (2/√3)·√N.
 *
 *   2. Form A_EF = B ∪ (N − B), check it is SAS, count the exceptional
 *      sum (should be N with multiplicity |B|).
 *
 *   3. Test local moves:
 *        (a) Single-element add. For each x ∈ [1, N] \ A_EF, test
 *            A_EF ∪ {x}. If SAS, flag.
 *        (b) Single-element swap. For each (a, x) with a ∈ A_EF, x not,
 *            test (A_EF \ {a}) ∪ {x}. If SAS with size ≥ |A_EF|, flag.
 *        (c) Colliding pair. For each pair x + y = N with x, y ∉ A_EF
 *            and x < y, test A_EF ∪ {x, y}. If SAS, flag.
 *
 * SAS check: A set is SAS iff at most one value in the pair-sumset has
 * multiplicity ≥ 2 (and that value still has multiplicity 1 from itself,
 * but actually: "at most one exception" means there is at most one s
 * with r_A(s) ≥ 2). Here r_A(s) counts ordered (or unordered) pairs.
 * We use UNORDERED pairs (i ≤ j) consistent with the existing search.
 *
 * For efficiency at N up to 10000:
 *   - Bitset representation of A and sumset (multiplicity 0/1/many).
 *   - Single-add test in O(N/64) per candidate.
 *   - Total work for single-add test: O(N · N/64) = O(N²/64).
 *   - Swap test is O(N² · N/64) ≈ O(N³/64) — borderline at N=10000.
 *     We'll do a smarter swap by precomputing per-element sum contributions.
 *
 * Compile: cc -O3 -march=native -funroll-loops -o ef_locality ef_locality.c
 *
 * Run:    ./ef_locality 100 200 500 1000 5000 10000
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

/* For N up to 10000 we need bitsets of size 2N+1 ≈ 20001 bits ≈ 313 words. */
#define MAXN 10001
#define MAX_BITS (2 * MAXN + 64)
#define MAX_WORDS ((MAX_BITS + 63) / 64)

typedef struct {
    int n_words;
    uint64_t bits[MAX_WORDS];
} bs_t;

static inline void bs_zero(bs_t *b) { memset(b->bits, 0, sizeof(uint64_t) * b->n_words); }
static inline void bs_set(bs_t *b, int i) { b->bits[i >> 6] |= (1ULL << (i & 63)); }
static inline void bs_clr(bs_t *b, int i) { b->bits[i >> 6] &= ~(1ULL << (i & 63)); }
static inline int bs_test(const bs_t *b, int i) { return (int)((b->bits[i >> 6] >> (i & 63)) & 1ULL); }
static inline void bs_or(bs_t *r, const bs_t *a, const bs_t *b) {
    for (int i = 0; i < r->n_words; i++) r->bits[i] = a->bits[i] | b->bits[i];
}
static inline void bs_and(bs_t *r, const bs_t *a, const bs_t *b) {
    for (int i = 0; i < r->n_words; i++) r->bits[i] = a->bits[i] & b->bits[i];
}
static inline void bs_xor(bs_t *r, const bs_t *a, const bs_t *b) {
    for (int i = 0; i < r->n_words; i++) r->bits[i] = a->bits[i] ^ b->bits[i];
}
static inline void bs_andnot(bs_t *r, const bs_t *a, const bs_t *b) {
    for (int i = 0; i < r->n_words; i++) r->bits[i] = a->bits[i] & ~b->bits[i];
}
static inline int bs_popcount(const bs_t *b) {
    int t = 0;
    for (int i = 0; i < b->n_words; i++) t += __builtin_popcountll(b->bits[i]);
    return t;
}
static inline void bs_copy(bs_t *r, const bs_t *a) {
    r->n_words = a->n_words;
    memcpy(r->bits, a->bits, sizeof(uint64_t) * a->n_words);
}
/* Left-shift by k bits. */
static inline void bs_lshift(bs_t *dst, const bs_t *src, int k) {
    int nw = dst->n_words;
    int ws = k >> 6, bs_ = k & 63;
    if (bs_ == 0) {
        for (int i = nw - 1; i >= 0; i--) {
            int j = i - ws;
            dst->bits[i] = (j >= 0) ? src->bits[j] : 0;
        }
    } else {
        int inv = 64 - bs_;
        for (int i = nw - 1; i >= 0; i--) {
            int j = i - ws;
            uint64_t hi = (j >= 0) ? src->bits[j] : 0;
            uint64_t lo = (j - 1 >= 0) ? src->bits[j - 1] : 0;
            dst->bits[i] = (hi << bs_) | (lo >> inv);
        }
    }
}
/* Pop-count of (a & b), early exit if > 1. Returns 0, 1, or 2 (≥2). */
static inline int bs_and_popcount_le1(const bs_t *a, const bs_t *b) {
    int t = 0;
    for (int i = 0; i < a->n_words; i++) {
        int p = __builtin_popcountll(a->bits[i] & b->bits[i]);
        t += p;
        if (t >= 2) return 2;
    }
    return t;
}

/* ----- Greedy Sidon set in [1, M] starting from a seed ----- */
/* Compute representation multiplicities of A as a sumset (unordered i ≤ j). */
/* For the Sidon check: we need r_A(s) ≤ 1 for all s. */

static int greedy_extend_sidon(int M, int *S, int sz, int n_words_local) {
    bs_t sums; sums.n_words = n_words_local; bs_zero(&sums);
    bs_t A; A.n_words = n_words_local; bs_zero(&A);
    /* Init sums from existing S. */
    for (int i = 0; i < sz; i++) bs_set(&A, S[i]);
    for (int i = 0; i < sz; i++) {
        for (int j = i; j < sz; j++) {
            int s = S[i] + S[j];
            if (bs_test(&sums, s)) {
                /* not Sidon to start with — shouldn't happen */
                fprintf(stderr, "greedy_extend_sidon: seed not Sidon!\n");
                exit(1);
            }
            bs_set(&sums, s);
        }
    }
    bs_t new_sums; new_sums.n_words = n_words_local;
    for (int x = 1; x <= M; x++) {
        if (bs_test(&A, x)) continue;
        /* new_sums = (A << x) with bit 2x set */
        bs_lshift(&new_sums, &A, x);
        new_sums.bits[(2 * x) >> 6] |= (1ULL << ((2 * x) & 63));
        /* Check collision with existing sums. */
        int collide = bs_and_popcount_le1(&sums, &new_sums);
        if (collide > 0) continue;
        /* Accept x. */
        bs_set(&A, x);
        for (int w = 0; w < n_words_local; w++) sums.bits[w] |= new_sums.bits[w];
        S[sz++] = x;
    }
    /* Sort. */
    for (int i = 1; i < sz; i++) {
        int v = S[i], j = i - 1;
        while (j >= 0 && S[j] > v) { S[j+1] = S[j]; j--; }
        S[j+1] = v;
    }
    return sz;
}

/* Erdős–Turán: B = {2pk + (k² mod p) : 0 ≤ k < p}, Sidon in [0, 2p²-p+1].
 * Shift by 1 to get Sidon in [1, 2p²-p+2]. */
static int is_prime(int n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if ((n & 1) == 0) return 0;
    for (int d = 3; d * d <= n; d += 2) if (n % d == 0) return 0;
    return 1;
}
static int erdos_turan(int M, int *out) {
    /* Find largest prime p with 2p² ≤ M. Then |B| = p. */
    int best_p = 0;
    for (int p = 2; 2 * p * p <= M; p++) {
        if (is_prime(p)) best_p = p;
    }
    if (best_p == 0) return 0;
    int p = best_p;
    int sz = 0;
    for (int k = 0; k < p; k++) {
        int v = 2 * p * k + ((k * k) % p) + 1; /* shift by 1 */
        if (v >= 1 && v <= M) out[sz++] = v;
    }
    /* sort */
    for (int i = 1; i < sz; i++) {
        int v = out[i], j = i - 1;
        while (j >= 0 && out[j] > v) { out[j+1] = out[j]; j--; }
        out[j+1] = v;
    }
    return sz;
}

/* Singer perfect difference set construction.
 * For a prime power q, there's a Sidon set of size q+1 inside Z/(q²+q+1).
 * For prime q we can compute it directly: pick a generator g of F_{q^3}*
 * and look at residues mod (q²+q+1). The image gives a (q²+q+1, q+1, 1)
 * difference set.
 *
 * Simpler: hardcode small primes' Singer sets known to exist (we just
 * verify by construction). For our purposes, since we will also brute-force
 * max Sidon for small M, Singer is mainly needed for large M.
 *
 * We construct Singer for prime q by finding a primitive element α of
 * F_{q^3} (represented as F_q[x] / f(x) for irreducible cubic f), then
 * computing the set {i : α^i has degree ≤ 0, i.e., α^i ∈ F_q}.
 * Equivalently, the perfect difference set is the set of i mod (q²+q+1)
 * such that α^i lies in the prime subfield F_q (up to scaling).
 *
 * For simplicity, we use a small DFS to find the Singer set for prime q. */

static int *singer_buf;
static int singer_q;

/* For prime power q, q²+q+1 is the size of the projective line PG(2,q).
 * We compute a planar difference set directly via brute search for small q.
 * To avoid implementing finite field arithmetic over GF(q^3) for non-prime
 * q, we restrict to PRIME q.
 *
 * For prime q, F_{q^3} = F_q[x]/(f(x)) where f is irreducible of degree 3.
 * We try cubic polynomials f(x) = x^3 + a*x + b until we find one
 * irreducible, then take α = x as the generator candidate. We check it
 * has order q^3 - 1, and if so, output the perfect difference set
 * {i mod (q²+q+1) : α^i ∈ F_q} (i.e., α^i = constant). The set has size
 * q + 1.
 *
 * Multiplication: (a + b*x + c*x²) * (d + e*x + f*x²) mod f(x).
 * Implementation: store each element as a triple (a, b, c) ∈ F_q^3.
 */

/* Multiply two elements modulo f(x) = x^3 + A*x + B (over F_q). */
static void gf_mul(int q, int A, int B, int *a, int *b, int *c, int da, int db, int dc) {
    /* (a + b x + c x²) * (da + db x + dc x²) = */
    /* a*da + (a*db + b*da) x + (a*dc + b*db + c*da) x²
       + (b*dc + c*db) x³ + c*dc x⁴ */
    long long t0 = (long long)(*a) * da;
    long long t1 = (long long)(*a) * db + (long long)(*b) * da;
    long long t2 = (long long)(*a) * dc + (long long)(*b) * db + (long long)(*c) * da;
    long long t3 = (long long)(*b) * dc + (long long)(*c) * db;
    long long t4 = (long long)(*c) * dc;
    /* x^3 = -A x - B (mod f), so x^3 = (q-A)%q * x + (q-B)%q (in F_q). */
    /* Actually with f(x) = x^3 + A x + B, we have x^3 = -A x - B. */
    int negA = ((-A) % q + q) % q;
    int negB = ((-B) % q + q) % q;
    /* x^3 → negB + negA * x */
    /* x^4 = x * x^3 = x * (negA x + negB) = negA x² + negB x;
       BUT this requires another reduction if negA x² adds more.
       Actually x^4 = negA x² + negB x — fits in degree ≤ 2 if no further reduction needed.
       OK so x^4 → negB x + negA x². */
    t0 = (t0 + t3 * negB) % q;
    t1 = (t1 + t3 * negA + t4 * negB) % q;
    t2 = (t2 + t4 * negA) % q;
    *a = (int)((t0 % q + q) % q);
    *b = (int)((t1 % q + q) % q);
    *c = (int)((t2 % q + q) % q);
}

static int singer_set(int q, int *out) {
    /* Singer set of size q+1 in [0, q²+q+1 - 1]. We then shift to [1, q²+q+1]. */
    if (!is_prime(q)) return 0;
    int Q = q * q + q + 1;
    int order = q * q * q - 1; /* order of F_{q^3}* */
    /* Find irreducible cubic f(x) = x^3 + A x + B and verify x is a generator. */
    for (int A = 0; A < q; A++) {
        for (int B = 1; B < q; B++) {
            /* Check f irreducible: no roots in F_q. */
            int has_root = 0;
            for (int r = 0; r < q; r++) {
                int v = (((r * r % q) * r) % q + (A * r) % q + B) % q;
                if (v == 0) { has_root = 1; break; }
            }
            if (has_root) continue;
            /* Test that α = x is a generator of order q^3 - 1.
             * Equivalently x^((q^3-1)/p) ≠ 1 for each prime p dividing q^3-1.
             * For small q, just compute the orbit and check it has length order. */
            int a = 0, b = 1, c = 0; /* α = x */
            int got_singer = 0;
            int *log_in_Fq = malloc(sizeof(int) * order);
            for (int i = 0; i < order; i++) log_in_Fq[i] = -1;
            int found_back = 0;
            int sz_count = 0;
            for (int i = 0; i < order; i++) {
                /* element a + b x + c x² */
                if (b == 0 && c == 0) { /* in F_q */
                    log_in_Fq[i] = a;
                    sz_count++;
                }
                if (i + 1 < order) {
                    /* multiply by x: (a + b x + c x²)*x = a x + b x² + c x³
                       = a x + b x² + c*(negA x + negB) = c*negB + (a + c*negA) x + b x². */
                    int negA = ((-A) % q + q) % q;
                    int negB = ((-B) % q + q) % q;
                    int na = (int)(((long long)c * negB) % q + q) % q;
                    int nb = (int)(((long long)a + (long long)c * negA) % q + q) % q;
                    int nc = b;
                    a = na; b = nb; c = nc;
                }
            }
            /* The set of i (mod Q) with log_in_Fq[i] != -1 is the Singer set. */
            /* It must have size q + 1. */
            int sz = 0;
            /* Singer set = {i mod Q : α^i ∈ F_q} (where i ranges over [0, order-1]).
             * Take i mod Q to get the set in [0, Q-1]. */
            int *singer = malloc(sizeof(int) * Q);
            int *seen = calloc(Q, sizeof(int));
            for (int i = 0; i < order; i++) {
                if (log_in_Fq[i] >= 0) {
                    int r = i % Q;
                    if (!seen[r]) {
                        seen[r] = 1;
                        singer[sz++] = r;
                    }
                }
            }
            if (sz == q + 1) {
                /* Sort and shift to 1-based. */
                for (int i = 1; i < sz; i++) {
                    int v = singer[i], j = i - 1;
                    while (j >= 0 && singer[j] > v) { singer[j+1] = singer[j]; j--; }
                    singer[j+1] = v;
                }
                /* Singer is a difference set; shift by 1 to land in [1, Q]. */
                for (int i = 0; i < sz; i++) out[i] = singer[i] + 1;
                got_singer = 1;
            }
            free(seen);
            free(singer);
            free(log_in_Fq);
            if (got_singer) return q + 1;
        }
    }
    return 0;
}

/* Choose the largest prime q with q²+q+1 ≤ M. */
static int choose_singer_q(int M) {
    int best = 0;
    for (int q = 2; q * q + q + 1 <= M; q++) {
        if (is_prime(q)) best = q;
    }
    return best;
}

/* ----- Max-Sidon backtracking (exact) ----- */
static int ms_M, ms_nw;
static uint64_t ms_A_b[MAX_WORDS];
static uint64_t ms_sums[MAX_WORDS];
static int ms_elts[MAXN + 2];
static int ms_size, ms_best;
static int ms_best_set[MAXN + 2];
static long long ms_node_budget;

static void ms_back(int start) {
    ms_node_budget--;
    if (ms_node_budget < 0) return;
    if (ms_size > ms_best) {
        ms_best = ms_size;
        memcpy(ms_best_set, ms_elts, ms_size * sizeof(int));
    }
    if (ms_size + (ms_M - start) <= ms_best) return;
    uint64_t new_sums[MAX_WORDS];
    for (int x = start + 1; x <= ms_M; x++) {
        if (ms_size + 1 + (ms_M - x) <= ms_best) break;
        /* new_sums = (A << x) | bit(2x) */
        int ws = x >> 6, bs_ = x & 63;
        if (bs_ == 0) {
            for (int i = ms_nw - 1; i >= 0; i--) {
                int j = i - ws;
                new_sums[i] = (j >= 0) ? ms_A_b[j] : 0;
            }
        } else {
            int inv = 64 - bs_;
            for (int i = ms_nw - 1; i >= 0; i--) {
                int j = i - ws;
                uint64_t hi = (j >= 0) ? ms_A_b[j] : 0;
                uint64_t lo = (j - 1 >= 0) ? ms_A_b[j - 1] : 0;
                new_sums[i] = (hi << bs_) | (lo >> inv);
            }
        }
        new_sums[(2 * x) >> 6] |= (1ULL << ((2 * x) & 63));
        /* Check collision. */
        int hit = 0;
        for (int i = 0; i < ms_nw; i++) if (ms_sums[i] & new_sums[i]) { hit = 1; break; }
        if (hit) continue;
        /* push */
        uint64_t save_A[MAX_WORDS], save_S[MAX_WORDS];
        memcpy(save_A, ms_A_b, sizeof(uint64_t) * ms_nw);
        memcpy(save_S, ms_sums, sizeof(uint64_t) * ms_nw);
        ms_A_b[x >> 6] |= (1ULL << (x & 63));
        for (int i = 0; i < ms_nw; i++) ms_sums[i] |= new_sums[i];
        ms_elts[ms_size++] = x;
        ms_back(x);
        ms_size--;
        memcpy(ms_A_b, save_A, sizeof(uint64_t) * ms_nw);
        memcpy(ms_sums, save_S, sizeof(uint64_t) * ms_nw);
        if (ms_node_budget < 0) return;
    }
}

static int max_sidon_exact(int M, int *out, long long node_budget) {
    if (M < 1) return 0;
    ms_M = M;
    ms_nw = (2 * M + 64 + 1) / 64;
    if (ms_nw > MAX_WORDS) return -1;
    memset(ms_A_b, 0, sizeof(uint64_t) * ms_nw);
    memset(ms_sums, 0, sizeof(uint64_t) * ms_nw);
    ms_size = 0;
    ms_best = 0;
    ms_node_budget = node_budget;
    ms_back(0);
    if (ms_node_budget < 0) return -1; /* timed out */
    memcpy(out, ms_best_set, ms_best * sizeof(int));
    return ms_best;
}

/* Known optimal Golomb rulers (A003022, A106683).
 * golomb_length[k] = length of optimal k-mark ruler (so size = k, max element = length).
 * A003022: a(k) for k = 1, 2, 3, ...: 0, 1, 3, 6, 11, 17, 25, 34, 44, 55, 72, 85,
 *          106, 127, 151, 177, 199, 216, 246, 283, 333, 356, 372, 425, 480, 492, 553
 * Index by k (size).
 */
static const int golomb_length[28] = {
    -1, 0, 1, 3, 6, 11, 17, 25, 34, 44, 55, 72, 85, 106, 127, 151, 177, 199, 216, 246, 283, 333, 356, 372, 425, 480, 492, 553
};
/* Optimal rulers (0-indexed positions). g_k[0..k-1]. */
static const int g3[]  = {0,1,3};
static const int g4[]  = {0,1,4,6};
static const int g5[]  = {0,1,4,9,11};
static const int g6[]  = {0,1,4,10,12,17};
static const int g7[]  = {0,1,4,10,18,23,25};
static const int g8[]  = {0,1,4,9,15,22,32,34};
static const int g9[]  = {0,1,5,12,25,27,35,41,44};
static const int g10[] = {0,1,6,10,23,26,34,41,53,55};
static const int g11[] = {0,1,4,13,28,33,47,54,64,70,72};
static const int g12[] = {0,2,6,24,29,40,43,55,68,75,76,85};
static const int g13[] = {0,2,5,25,37,43,59,70,85,89,98,99,106};
static const int g14[] = {0,4,6,20,35,52,59,77,78,86,89,99,122,127};
static const int g15[] = {0,4,20,30,57,59,62,76,100,111,123,136,144,145,151};
static const int g16[] = {0,1,4,11,26,32,56,68,76,115,117,134,150,163,168,177};
static const int g17[] = {0,5,7,17,52,56,67,80,81,100,122,138,159,165,168,191,199};
static const int g18[] = {0,2,10,22,53,56,82,83,89,98,130,148,153,167,188,192,205,216};
static const int g19[] = {0,1,6,25,32,72,100,108,120,130,153,169,187,190,204,231,233,242,246};
static const int g20[] = {0,1,8,11,68,77,94,116,121,156,158,179,194,208,212,228,240,253,259,283};
static const int g21[] = {0,2,24,56,77,82,83,95,129,144,179,186,195,255,265,285,293,296,310,329,333};
static const int g22[] = {0,1,9,14,43,70,106,122,124,128,159,179,204,223,253,263,270,291,330,341,353,356};
static const int g23[] = {0,3,7,17,61,66,91,99,114,159,171,199,200,226,235,246,277,316,329,348,350,366,372};
static const int g24[] = {0,9,33,37,38,97,122,129,140,142,152,191,205,208,252,278,286,326,332,353,368,384,403,425};
static const int g25[] = {0,12,29,39,72,91,146,157,160,161,166,191,207,214,258,290,316,354,372,394,396,431,459,467,480};
static const int g26[] = {0,1,33,83,104,110,124,163,185,200,203,249,251,258,314,318,343,356,386,430,440,456,464,475,487,492};
static const int g27[] = {0,3,15,41,66,95,97,106,142,152,220,221,225,242,295,330,338,354,382,388,402,415,486,504,523,546,553};
static const int *g_rulers[28] = {
    NULL, NULL, NULL, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14,
    g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27
};

/* Pick the largest optimal Golomb ruler fitting in [0, M-1], i.e., length ≤ M-1.
 * Return its size (shifted to [1, M]). */
static int golomb_largest_fit(int M, int *out) {
    int best = 0;
    int len_limit = M - 1; /* 0-indexed length */
    for (int k = 27; k >= 3; k--) {
        if (golomb_length[k] <= len_limit) {
            for (int i = 0; i < k; i++) out[i] = g_rulers[k][i] + 1;
            return k;
        }
    }
    if (M >= 1) { out[0] = 1; return 1; }
    return 0;
}

/* Build a "good" Sidon set in [1, M].
 * Strategy:
 *  - Build heuristic candidates: Erdős–Turán seed + greedy; Singer seed + greedy;
 *    plain greedy from {1}; optimal Golomb ruler + greedy. Take the best.
 *  - For M up to ~200, run exact backtracking with large node budget.
 *  - For larger M, return the best heuristic.
 */
static int build_sidon(int M, int *out, int n_words_local) {
    int best_sz = 0;
    int *best_set_p = out;

    /* (1) Erdős–Turán seed + greedy. */
    {
        int tmp[MAXN + 4];
        int et_sz = erdos_turan(M, tmp);
        if (et_sz == 0) { tmp[0] = 1; et_sz = 1; }
        et_sz = greedy_extend_sidon(M, tmp, et_sz, n_words_local);
        if (et_sz > best_sz) {
            best_sz = et_sz;
            memcpy(best_set_p, tmp, et_sz * sizeof(int));
        }
    }

    /* (2) Singer seed + greedy. */
    {
        int q = choose_singer_q(M);
        if (q > 0) {
            int singer_buf[MAXN + 4];
            int s_sz = singer_set(q, singer_buf);
            if (s_sz > 0) {
                int t_sz = greedy_extend_sidon(M, singer_buf, s_sz, n_words_local);
                if (t_sz > best_sz) {
                    best_sz = t_sz;
                    memcpy(best_set_p, singer_buf, t_sz * sizeof(int));
                }
            }
        }
    }

    /* (3) Plain greedy (Mian-Chowla style). */
    {
        int tmp3[MAXN + 4];
        tmp3[0] = 1;
        int g_sz = greedy_extend_sidon(M, tmp3, 1, n_words_local);
        if (g_sz > best_sz) {
            best_sz = g_sz;
            memcpy(best_set_p, tmp3, g_sz * sizeof(int));
        }
    }

    /* (3b) Known optimal Golomb ruler + greedy. */
    {
        int tmp4[MAXN + 4];
        int g_sz = golomb_largest_fit(M, tmp4);
        if (g_sz > 0) {
            int t_sz = greedy_extend_sidon(M, tmp4, g_sz, n_words_local);
            if (t_sz > best_sz) {
                best_sz = t_sz;
                memcpy(best_set_p, tmp4, t_sz * sizeof(int));
            }
        }
    }

    /* (4) Exact backtracking for small/moderate M. */
    if (M <= 200) {
        int tmp4[MAXN + 4];
        long long budget = 2000000000LL; /* 2B nodes */
        int sz = max_sidon_exact(M, tmp4, budget);
        if (sz > best_sz) {
            best_sz = sz;
            memcpy(best_set_p, tmp4, sz * sizeof(int));
        }
    }

    return best_sz;
}

/* ----- SAS check infrastructure ------ */
/* For a set A, maintain bitsets:
 *   sums_once: pair-sums with multiplicity == 1
 *   sums_many: pair-sums with multiplicity ≥ 2
 * SAS iff popcount(sums_many) ≤ 1. */

static int build_sums(const int *A, int sz, bs_t *sums_once, bs_t *sums_many, int n_words_local) {
    sums_once->n_words = n_words_local;
    sums_many->n_words = n_words_local;
    bs_zero(sums_once);
    bs_zero(sums_many);
    /* Maintain a small multiplicity counter on the fly. For SAS check
     * we don't need exact counts beyond "1 vs ≥2": once_to_many. */
    /* Loop over unordered pairs. */
    for (int i = 0; i < sz; i++) {
        for (int j = i; j < sz; j++) {
            int s = A[i] + A[j];
            int wi = s >> 6;
            uint64_t mask = 1ULL << (s & 63);
            if (sums_many->bits[wi] & mask) {
                /* already ≥2; stays ≥2 */
            } else if (sums_once->bits[wi] & mask) {
                /* was 1, now ≥2 */
                sums_once->bits[wi] &= ~mask;
                sums_many->bits[wi] |= mask;
            } else {
                sums_once->bits[wi] |= mask;
            }
        }
    }
    return bs_popcount(sums_many);
}

/* Check SAS: at most one bit in sums_many. */
static int is_sas_from_sums(const bs_t *sums_many) {
    int t = 0;
    for (int i = 0; i < sums_many->n_words; i++) {
        t += __builtin_popcountll(sums_many->bits[i]);
        if (t >= 2) return 0;
    }
    return 1;
}

/* Given current SAS state (A, sums_once, sums_many, exc_val where
 * exc_val = the single exceptional sum value or -1 if none), test
 * adding element x not in A:
 *
 *   new_pair_sums = {x + a : a ∈ A} ∪ {2x}   (as a bitset)
 *   - any value s in new_pair_sums that is already in sums_many → still many
 *   - any value s in new_pair_sums ∩ sums_once → moves to many
 *   - any value s in new_pair_sums \ (sums_once ∪ sums_many) → becomes once
 *   - if 2x appears twice... no, only once.
 *
 * But within new_pair_sums itself, could two values collide? If x + a1 = x + a2
 * then a1 = a2 — no collision among the {x + a} terms. The element 2x is
 * separate; 2x = x + a → a = x, but x ∉ A by assumption. So new_pair_sums has
 * all distinct values (one per element of A plus one for 2x).
 *
 * Therefore: |new_many ∪ existing_many| ≤ 1 iff
 *   existing many bits (which is 0 or 1)
 *   PLUS new bits from collisions (|new_pair_sums ∩ (sums_once ∪ sums_many)|
 *   excluding those already in sums_many)
 *   ≤ 1.
 *
 * Easier: compute new_many = sums_many ∪ (new_pair_sums ∩ sums_once)
 * (those once-bits that get bumped to many). Check popcount(new_many) ≤ 1.
 */
static int test_add_sas(const bs_t *A, const bs_t *sums_once, const bs_t *sums_many,
                        int x, int N_local, bs_t *new_pair_sums) {
    /* new_pair_sums = (A << x) with bit 2x set. */
    bs_lshift(new_pair_sums, A, x);
    int two_x = 2 * x;
    new_pair_sums->bits[two_x >> 6] |= (1ULL << (two_x & 63));
    /* collisions with sums_once (these get bumped to many): */
    /* For SAS to remain, popcount(sums_many ∪ (collisions)) ≤ 1. */
    /* Note collisions and sums_many are disjoint (sums_once disjoint from sums_many). */
    int many_count = bs_popcount(sums_many);
    /* count collisions with sums_once, early exit if total > 1 */
    int t = many_count;
    for (int i = 0; i < A->n_words; i++) {
        uint64_t c = new_pair_sums->bits[i] & sums_once->bits[i];
        t += __builtin_popcountll(c);
        if (t >= 2) return 0;
    }
    return 1;
}

/* In-place: apply adding x to the SAS state (A, sums_once, sums_many).
 * Requires the test to have passed first. */
static void apply_add(bs_t *A, bs_t *sums_once, bs_t *sums_many,
                      int x, const bs_t *new_pair_sums) {
    bs_set(A, x);
    int nw = A->n_words;
    for (int i = 0; i < nw; i++) {
        uint64_t coll = new_pair_sums->bits[i] & sums_once->bits[i];
        uint64_t fresh = new_pair_sums->bits[i] & ~sums_once->bits[i] & ~sums_many->bits[i];
        sums_once->bits[i] = (sums_once->bits[i] & ~coll) | fresh;
        sums_many->bits[i] |= coll;
    }
}

/* Remove an element a from a set, updating sums.
 * For each y ∈ A \ {a}, sum a + y had multiplicity m; now becomes m - 1.
 * Also 2a had multiplicity 1 (assuming a was added once); now becomes 0.
 *
 * We can rebuild the SAS state from scratch for a deletion — it's O(|A|²)
 * which is fine since we do this only for swap tests. For swap tests at
 * large N we want something smarter, but |A| ≈ 2√N/√3 so |A|² ≈ N — manageable.
 *
 * Actually a cleaner approach for swap testing: precompute per-element
 * "ms" — for each element a in A, the multiplicity contribution to sums.
 *
 * For our purposes we'll just rebuild from scratch for swap moves.
 */

/* ---- Main test for one N ---- */

static int g_witness_count;
static int g_witness_examples; /* limit */

static void test_one_N(int N, FILE *out) {
    int M = N / 3;
    int n_words_local = (2 * N + 64 + 1) / 64;
    if (n_words_local > MAX_WORDS) {
        fprintf(out, "N=%d: too large (need %d words, MAX_WORDS=%d)\n",
                N, n_words_local, MAX_WORDS);
        return;
    }
    int *B = malloc(sizeof(int) * (N + 4));
    int *A = malloc(sizeof(int) * (N + 4));
    if (!B || !A) { fprintf(stderr, "malloc fail\n"); exit(1); }

    int B_sz = build_sidon(M, B, n_words_local);

    /* Build A_EF = B ∪ (N − B), keeping distinct, sorted. */
    bs_t in_A; in_A.n_words = n_words_local; bs_zero(&in_A);
    int a_sz = 0;
    for (int i = 0; i < B_sz; i++) {
        if (!bs_test(&in_A, B[i])) { bs_set(&in_A, B[i]); A[a_sz++] = B[i]; }
    }
    for (int i = 0; i < B_sz; i++) {
        int y = N - B[i];
        if (y >= 1 && y <= N && !bs_test(&in_A, y)) {
            bs_set(&in_A, y);
            A[a_sz++] = y;
        }
    }
    /* sort */
    for (int i = 1; i < a_sz; i++) {
        int v = A[i], j = i - 1;
        while (j >= 0 && A[j] > v) { A[j+1] = A[j]; j--; }
        A[j+1] = v;
    }

    /* Build sums. */
    bs_t bs_A; bs_A.n_words = n_words_local; bs_zero(&bs_A);
    for (int i = 0; i < a_sz; i++) bs_set(&bs_A, A[i]);

    bs_t sums_once, sums_many;
    sums_once.n_words = n_words_local;
    sums_many.n_words = n_words_local;
    int many_pop = build_sums(A, a_sz, &sums_once, &sums_many, n_words_local);

    int is_sas = (many_pop <= 1);
    int exc_val = -1;
    if (many_pop == 1) {
        for (int i = 0; i < n_words_local; i++) {
            if (sums_many.bits[i]) {
                exc_val = i * 64 + __builtin_ctzll(sums_many.bits[i]);
                break;
            }
        }
    }

    fprintf(out, "N=%d  M=%d  |B|=%d  |A_EF|=%d  SAS=%s  exc_val=%d\n",
            N, M, B_sz, a_sz, is_sas ? "YES" : "NO", exc_val);
    fflush(out);

    if (!is_sas) {
        fprintf(out, "  EF construction is NOT SAS — abort tests for this N.\n");
        free(B); free(A);
        return;
    }

    /* --- (a) Single-element add. --- */
    bs_t scratch; scratch.n_words = n_words_local;
    int add_witnesses = 0;
    int add_examples_logged = 0;
    int max_examples = 5;
    for (int x = 1; x <= N; x++) {
        if (bs_test(&bs_A, x)) continue;
        if (test_add_sas(&bs_A, &sums_once, &sums_many, x, N, &scratch)) {
            add_witnesses++;
            if (add_examples_logged < max_examples) {
                fprintf(out, "  ADD witness: x=%d  (|A_new|=%d)\n", x, a_sz + 1);
                add_examples_logged++;
            }
        }
    }
    fprintf(out, "  Single-element ADD: %d witnesses (EF %slocally maximal vs add)\n",
            add_witnesses, add_witnesses == 0 ? "" : "NOT ");
    fflush(out);

    /* --- (b) Single-element swap. --- */
    /* For each a in A_EF, build the SAS state of A_EF \ {a}, then test each x. */
    int swap_witnesses = 0;
    int swap_examples_logged = 0;
    int *A_minus = malloc(sizeof(int) * (a_sz + 2));

    for (int idx = 0; idx < a_sz; idx++) {
        int a_rm = A[idx];
        /* Build A_minus. */
        int am_sz = 0;
        for (int i = 0; i < a_sz; i++) if (i != idx) A_minus[am_sz++] = A[i];

        bs_t bs_Am, so_m, sm_m;
        bs_Am.n_words = so_m.n_words = sm_m.n_words = n_words_local;
        bs_zero(&bs_Am);
        for (int i = 0; i < am_sz; i++) bs_set(&bs_Am, A_minus[i]);
        build_sums(A_minus, am_sz, &so_m, &sm_m, n_words_local);

        /* Now test each x not in A_minus. */
        for (int x = 1; x <= N; x++) {
            if (bs_test(&bs_Am, x)) continue;
            /* if x == a_rm, the resulting set is just A_EF; skip — that's not a real swap */
            if (x == a_rm) continue;
            if (test_add_sas(&bs_Am, &so_m, &sm_m, x, N, &scratch)) {
                swap_witnesses++;
                if (swap_examples_logged < max_examples) {
                    fprintf(out, "  SWAP witness: remove %d, add %d (|A|=%d)\n",
                            a_rm, x, a_sz);
                    swap_examples_logged++;
                }
            }
        }
    }
    fprintf(out, "  Single-element SWAP: %d witnesses (same-size moves)\n",
            swap_witnesses);
    fflush(out);
    free(A_minus);

    /* --- (c) Colliding pair x + y = N, x < y, both ∉ A_EF. --- */
    int pair_witnesses = 0;
    int pair_examples_logged = 0;
    for (int x = 1; x <= N / 2; x++) {
        int y = N - x;
        if (y <= x) break;
        if (bs_test(&bs_A, x) || bs_test(&bs_A, y)) continue;
        /* Test adding x first. */
        if (!test_add_sas(&bs_A, &sums_once, &sums_many, x, N, &scratch)) continue;
        /* Apply add of x temporarily. */
        bs_t bs_A2, so2, sm2;
        bs_A2.n_words = so2.n_words = sm2.n_words = n_words_local;
        bs_copy(&bs_A2, &bs_A);
        bs_copy(&so2, &sums_once);
        bs_copy(&sm2, &sums_many);
        apply_add(&bs_A2, &so2, &sm2, x, &scratch);
        /* Now test adding y. */
        if (test_add_sas(&bs_A2, &so2, &sm2, y, N, &scratch)) {
            pair_witnesses++;
            if (pair_examples_logged < max_examples) {
                fprintf(out, "  PAIR witness: add {%d, %d} (sum=%d=N), |A_new|=%d\n",
                        x, y, x + y, a_sz + 2);
                pair_examples_logged++;
            }
        }
    }
    fprintf(out, "  Colliding-pair ADD (x+y=N): %d witnesses\n", pair_witnesses);
    fflush(out);

    /* --- (d) ITERATED greedy colliding-pair augmentation. ---
     * Starting from A_EF, repeatedly find ANY colliding pair (x, y) with
     * x + y = N, both not in current A, and adding {x, y} preserves SAS.
     * Add such pairs greedily (smallest x first) until none remain. */
    {
        bs_t bsA, so, sm;
        bsA.n_words = so.n_words = sm.n_words = n_words_local;
        bs_copy(&bsA, &bs_A);
        bs_copy(&so, &sums_once);
        bs_copy(&sm, &sums_many);
        int aug_size = a_sz;
        int aug_rounds = 0;
        bs_t scratch2; scratch2.n_words = n_words_local;
        while (1) {
            int found = 0;
            for (int x = 1; x <= N / 2; x++) {
                int y = N - x;
                if (y <= x) break;
                if (bs_test(&bsA, x) || bs_test(&bsA, y)) continue;
                if (!test_add_sas(&bsA, &so, &sm, x, N, &scratch2)) continue;
                /* Tentatively add x, then test y. */
                bs_t bsA2, so2, sm2;
                bsA2.n_words = so2.n_words = sm2.n_words = n_words_local;
                bs_copy(&bsA2, &bsA);
                bs_copy(&so2, &so);
                bs_copy(&sm2, &sm);
                apply_add(&bsA2, &so2, &sm2, x, &scratch2);
                bs_t scratch3; scratch3.n_words = n_words_local;
                if (!test_add_sas(&bsA2, &so2, &sm2, y, N, &scratch3)) continue;
                /* Commit. */
                apply_add(&bsA2, &so2, &sm2, y, &scratch3);
                bs_copy(&bsA, &bsA2);
                bs_copy(&so, &so2);
                bs_copy(&sm, &sm2);
                aug_size += 2;
                aug_rounds++;
                found = 1;
                if (aug_rounds <= 5) {
                    fprintf(out, "  AUG round %d: added pair {%d, %d}, |A|=%d\n",
                            aug_rounds, x, y, aug_size);
                }
                break;
            }
            if (!found) break;
        }
        fprintf(out, "  Iterated AUG: %d colliding-pair rounds, final |A|=%d (gain=%d)\n",
                aug_rounds, aug_size, aug_size - a_sz);
    }

    /* Summary */
    int local_max_strict = (add_witnesses == 0); /* no single add improves */
    fprintf(out, "  >>> EF locally maximal vs single ADD?  %s\n",
            local_max_strict ? "YES" : "NO");
    fprintf(out, "  >>> Colliding-pair gives improvement?   %s\n",
            pair_witnesses > 0 ? "YES" : "NO");
    fprintf(out, "\n");
    fflush(out);

    free(B); free(A);
}

int main(int argc, char **argv) {
    FILE *out = fopen("/Users/samuelschlesinger/projects/formalization/erdos-problems/research/sqrt2-strong-almost-sidon/data/ef_locality_results.txt", "w");
    if (!out) { perror("fopen"); return 1; }

    fprintf(out, "# EF Locality Test Results\n");
    fprintf(out, "# Construction: A_EF = B ∪ (N − B), B = Sidon set in [1, ⌊N/3⌋]\n");
    fprintf(out, "# (B built via Erdős–Turán seed + greedy extension; may not be absolute max)\n#\n");
    fflush(out);

    int Ns[] = {100, 200, 500, 1000, 5000, 10000};
    int n_targets = sizeof(Ns) / sizeof(Ns[0]);
    if (argc > 1) {
        n_targets = argc - 1;
        for (int i = 0; i < n_targets; i++) Ns[i] = atoi(argv[i + 1]);
    }

    for (int t = 0; t < n_targets; t++) {
        int N = Ns[t];
        clock_t t0 = clock();
        test_one_N(N, out);
        double dt = (double)(clock() - t0) / CLOCKS_PER_SEC;
        fprintf(out, "# wall: %.2f s for N=%d\n#\n", dt, N);
        fflush(out);
        fprintf(stderr, "N=%d done in %.2fs\n", N, dt);
    }

    fclose(out);
    return 0;
}
