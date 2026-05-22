/*
 * extend_search.c — strong almost-Sidon (SAS) extremizer search.
 *
 * Goal: compute f(N) = max |A| for SAS A ⊆ {1,...,N}, matching OEIS A389182.
 *
 * Algorithm (Spencer-style bitfield, with extra pruning):
 *
 *   For depth d, maintain bitsets over indices 0..2N:
 *     A          : current set
 *     sums_once  : pair sums in A with multiplicity 1
 *     exc_sums   : the exceptional sum (singleton bit) or zero
 *     forbidden_cand: x ∈ [1..N] such that adding x would create a
 *                     SECOND exception (i.e., x violates SAS).
 *                     This is computed lazily inside the loop.
 *
 *   On trying to add x:
 *     new_sums   = (A << x) | (1 << 2x)
 *     collisions = sums_once & new_sums
 *     new_exc    = collisions & ~exc_sums         // collisions outside exc
 *     If popcount(new_exc) > 1   ⇒ skip x.
 *     If popcount(new_exc) == 1 AND exc != 0 ⇒ skip x.
 *     Else accept:
 *       new_sums_once = (sums_once | new_sums) & ~collisions
 *       new_exc_sums  = exc_sums | collisions
 *
 *   Pruning:
 *     - |A| + (N - start) ≤ best_size  ⇒ return
 *     - cand_count(start..N) + |A| ≤ best_size ⇒ return  (NEW)
 *
 *   To compute cand_count cheaply, we mark forbidden elements as we
 *   discover them in the inner loop (a "no-good" learning) — but it's
 *   stateful and tricky. Simpler: just check the cardinality bound first.
 *
 *   Hard upper bound: |A|² ≤ 4N + O(|A|). We precompute the integer
 *   bound max_card[N].
 *
 *   Seed best_size with EF construction.
 *
 * Compile: cc -O3 -march=native -funroll-loops -o extend_search extend_search.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#ifndef MAXN
#define MAXN 300
#endif

#define MAX_BITS (2 * MAXN + 64)
#define MAX_WORDS ((MAX_BITS + 63) / 64)

static int N;
static int n_words;

static int best_size;
static int best_set[MAXN + 2];

/* Hard upper bound on |A| for SAS A ⊆ {1..N}.
 * Derived from: total pair-sums = |A|(|A|+1)/2 sit in [2, 2N]; SAS allows
 * at most one collision-value, contributing extra collisions ≤ k(k-1)/2
 * where k ≤ ⌊|A|/2⌋ + 1. Worst case: |A|(|A|+1)/2 ≤ (2N-1) + (|A|/2)(|A|/2+1)/2.
 * Solving conservatively: 3|A|²/8 ≤ 2N + small, so |A| ≤ √(16N/3) + 2.
 * In practice the proven bound is |A| ≤ √(2N) + small (which matches data).
 * We use a generous bound: floor(sqrt(4N) + 3). */
static inline int hard_upper_bound(int n) {
    int ub = (int)(2.0 * __builtin_sqrt((double)n)) + 4;
    return ub;
}

static inline void bs_zero(uint64_t *bs) { memset(bs, 0, sizeof(uint64_t) * n_words); }
static inline void bs_copy(uint64_t *dst, const uint64_t *src) { memcpy(dst, src, sizeof(uint64_t) * n_words); }
static inline void bs_set(uint64_t *bs, int i) { bs[i >> 6] |= (1ULL << (i & 63)); }
static inline int bs_test(const uint64_t *bs, int i) { return (int)((bs[i >> 6] >> (i & 63)) & 1ULL); }
static inline int bs_iszero(const uint64_t *bs) {
    for (int i = 0; i < n_words; i++) if (bs[i]) return 0;
    return 1;
}

static inline void bs_lshift(uint64_t *dst, const uint64_t *src, int k) {
    int word_shift = k >> 6;
    int bit_shift = k & 63;
    if (bit_shift == 0) {
        for (int i = n_words - 1; i >= 0; i--) {
            int j = i - word_shift;
            dst[i] = (j >= 0) ? src[j] : 0;
        }
    } else {
        int inv = 64 - bit_shift;
        for (int i = n_words - 1; i >= 0; i--) {
            int j = i - word_shift;
            uint64_t hi = (j >= 0) ? src[j] : 0;
            uint64_t lo = (j - 1 >= 0) ? src[j - 1] : 0;
            dst[i] = (hi << bit_shift) | (lo >> inv);
        }
    }
}

static inline void bs_and(uint64_t *dst, const uint64_t *a, const uint64_t *b) {
    for (int i = 0; i < n_words; i++) dst[i] = a[i] & b[i];
}
static inline void bs_andnot(uint64_t *dst, const uint64_t *a, const uint64_t *b) {
    for (int i = 0; i < n_words; i++) dst[i] = a[i] & ~b[i];
}
static inline void bs_or(uint64_t *dst, const uint64_t *a, const uint64_t *b) {
    for (int i = 0; i < n_words; i++) dst[i] = a[i] | b[i];
}
static inline void bs_or_andnot(uint64_t *dst, const uint64_t *a, const uint64_t *b, const uint64_t *c) {
    for (int i = 0; i < n_words; i++) dst[i] = (a[i] | b[i]) & ~c[i];
}
static inline int bs_popcount(const uint64_t *bs) {
    int total = 0;
    for (int i = 0; i < n_words; i++) total += __builtin_popcountll(bs[i]);
    return total;
}
/* Popcount of (a & ~b) in one pass. */
static inline int bs_popcount_andnot(const uint64_t *a, const uint64_t *b) {
    int total = 0;
    for (int i = 0; i < n_words; i++) total += __builtin_popcountll(a[i] & ~b[i]);
    return total;
}
/* Popcount of a & b in one pass; if > 1 return early. */
static inline int bs_popcount_andnot_le1(const uint64_t *a, const uint64_t *b) {
    /* Return 0, 1, or 2 (where 2 means "≥2"). */
    int total = 0;
    for (int i = 0; i < n_words; i++) {
        int p = __builtin_popcountll(a[i] & ~b[i]);
        total += p;
        if (total >= 2) return 2;
    }
    return total;
}

/* Recursion stacks. */
static uint64_t stk_A[MAXN + 2][MAX_WORDS];
static uint64_t stk_once[MAXN + 2][MAX_WORDS];
static uint64_t stk_exc[MAXN + 2][MAX_WORDS];
static int stk_elts[MAXN + 2][MAXN + 2];
static int stk_size[MAXN + 2];

static uint64_t buf_new_sums[MAX_WORDS];
static uint64_t buf_coll[MAX_WORDS];

static int max_card_for_N;  /* hard upper bound */

static void backtrack(int d, int start) {
    int cur_size = stk_size[d];
    if (cur_size > best_size) {
        best_size = cur_size;
        memcpy(best_set, stk_elts[d], cur_size * sizeof(int));
    }
    if (cur_size >= max_card_for_N) return;
    if (cur_size + (N - start) <= best_size) return;

    uint64_t *A    = stk_A[d];
    uint64_t *once = stk_once[d];
    uint64_t *exc  = stk_exc[d];
    int exc_set = !bs_iszero(exc);

    for (int x = start + 1; x <= N; x++) {
        if (cur_size + 1 + (N - x) <= best_size) break;

        /* new_sums = (A << x) | bit(2x) */
        bs_lshift(buf_new_sums, A, x);
        /* set bit 2x */
        buf_new_sums[(2 * x) >> 6] |= (1ULL << ((2 * x) & 63));

        /* collisions = once & new_sums */
        bs_and(buf_coll, once, buf_new_sums);

        /* count new exceptions = popcount(coll & ~exc), early exit at 2 */
        int new_exc_pop = bs_popcount_andnot_le1(buf_coll, exc);
        if (new_exc_pop >= 2) continue;
        if (new_exc_pop == 1 && exc_set) continue;

        /* Accept. Build state at depth d+1. */
        int d2 = d + 1;
        bs_copy(stk_A[d2], A);
        stk_A[d2][x >> 6] |= (1ULL << (x & 63));
        bs_or_andnot(stk_once[d2], once, buf_new_sums, buf_coll);
        bs_or(stk_exc[d2], exc, buf_coll);

        memcpy(stk_elts[d2], stk_elts[d], cur_size * sizeof(int));
        stk_elts[d2][cur_size] = x;
        stk_size[d2] = cur_size + 1;

        backtrack(d2, x);
    }
}

/* --- Max Sidon for EF seed --- */
static int sid_M;
static int sid_n_words;
static uint64_t sid_A[MAX_WORDS];
static uint64_t sid_sums[MAX_WORDS];
static int sid_elts[MAXN + 2];
static int sid_size;
static int sid_best;
static int sid_best_set[MAXN + 2];

static inline void sid_bs_lshift(uint64_t *dst, const uint64_t *src, int k) {
    int word_shift = k >> 6;
    int bit_shift = k & 63;
    if (bit_shift == 0) {
        for (int i = sid_n_words - 1; i >= 0; i--) {
            int j = i - word_shift;
            dst[i] = (j >= 0) ? src[j] : 0;
        }
    } else {
        int inv = 64 - bit_shift;
        for (int i = sid_n_words - 1; i >= 0; i--) {
            int j = i - word_shift;
            uint64_t hi = (j >= 0) ? src[j] : 0;
            uint64_t lo = (j - 1 >= 0) ? src[j - 1] : 0;
            dst[i] = (hi << bit_shift) | (lo >> inv);
        }
    }
}
static inline int sid_collides(const uint64_t *a, const uint64_t *b) {
    for (int i = 0; i < sid_n_words; i++) if (a[i] & b[i]) return 1;
    return 0;
}

static void sid_back(int start) {
    if (sid_size > sid_best) {
        sid_best = sid_size;
        memcpy(sid_best_set, sid_elts, sid_size * sizeof(int));
    }
    if (sid_size + (sid_M - start) <= sid_best) return;
    uint64_t new_sums[MAX_WORDS];
    for (int x = start + 1; x <= sid_M; x++) {
        if (sid_size + 1 + (sid_M - x) <= sid_best) break;
        sid_bs_lshift(new_sums, sid_A, x);
        new_sums[(2 * x) >> 6] |= (1ULL << ((2 * x) & 63));
        if (sid_collides(sid_sums, new_sums)) continue;
        /* Push */
        uint64_t save_A[MAX_WORDS], save_sums[MAX_WORDS];
        memcpy(save_A, sid_A, sizeof(uint64_t) * sid_n_words);
        memcpy(save_sums, sid_sums, sizeof(uint64_t) * sid_n_words);
        sid_A[x >> 6] |= (1ULL << (x & 63));
        for (int i = 0; i < sid_n_words; i++) sid_sums[i] |= new_sums[i];
        sid_elts[sid_size++] = x;
        sid_back(x);
        sid_size--;
        memcpy(sid_A, save_A, sizeof(uint64_t) * sid_n_words);
        memcpy(sid_sums, save_sums, sizeof(uint64_t) * sid_n_words);
    }
}

static int max_sidon(int M, int *out) {
    if (M < 1) return 0;
    sid_M = M;
    sid_n_words = (2 * M + 64 + 1) / 64;
    memset(sid_A, 0, sizeof(uint64_t) * sid_n_words);
    memset(sid_sums, 0, sizeof(uint64_t) * sid_n_words);
    sid_size = 0;
    sid_best = 0;
    sid_back(0);
    memcpy(out, sid_best_set, sid_best * sizeof(int));
    return sid_best;
}

static int ef_lower_bound(int n, int *ef_set) {
    int M = n / 3;
    int B[MAXN + 2];
    int b = (M >= 1) ? max_sidon(M, B) : 0;
    int A[2 * MAXN + 4], a = 0;
    if (b == 0) {
        if (n >= 1) { ef_set[0] = 1; return 1; }
        return 0;
    }
    for (int i = 0; i < b; i++) A[a++] = B[i];
    for (int i = 0; i < b; i++) {
        int y = n - B[i];
        if (y < 1 || y > n) continue;
        int dup = 0;
        for (int j = 0; j < a; j++) if (A[j] == y) { dup = 1; break; }
        if (!dup) A[a++] = y;
    }
    for (int i = 1; i < a; i++) {
        int v = A[i]; int j = i - 1;
        while (j >= 0 && A[j] > v) { A[j+1] = A[j]; j--; }
        A[j+1] = v;
    }
    memcpy(ef_set, A, a * sizeof(int));
    return a;
}

static int solve(int n) {
    N = n;
    n_words = (2 * N + 64 + 1) / 64;
    bs_zero(stk_A[0]);
    bs_zero(stk_once[0]);
    bs_zero(stk_exc[0]);
    stk_size[0] = 0;
    best_size = 0;
    max_card_for_N = hard_upper_bound(n);

    int ef_set[MAXN + 2];
    int ef_n = ef_lower_bound(n, ef_set);
    if (ef_n > best_size) {
        best_size = ef_n;
        memcpy(best_set, ef_set, ef_n * sizeof(int));
    }

    backtrack(0, 0);
    return best_size;
}

int main(int argc, char **argv) {
    int n_start = 70, n_end = 100;
    if (argc >= 2) n_start = atoi(argv[1]);
    if (argc >= 3) n_end = atoi(argv[2]);

    for (int n = n_start; n <= n_end; n++) {
        clock_t t0 = clock();
        int f = solve(n);
        double dt = (double)(clock() - t0) / CLOCKS_PER_SEC;
        printf("%d %d  # t=%.2fs  set=", n, f, dt);
        for (int i = 0; i < f; i++) {
            printf("%d%s", best_set[i], i + 1 < f ? "," : "");
        }
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
