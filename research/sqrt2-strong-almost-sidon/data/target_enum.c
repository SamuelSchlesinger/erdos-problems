/*
 * target_enum.c — given (N, target_size), enumerate ALL SAS sets in
 * {1,..,N} of size exactly target_size, and record the multiplicity invariant
 * 2*r_A(n*) - |A| for each. Used to verify the invariant on large N where
 * the maximum size f(N) is already known or guessed.
 *
 * Compile: cc -O3 -march=native -funroll-loops -o target_enum target_enum.c
 * Usage:   ./target_enum N target_size  (single (N, size) pair)
 *          ./target_enum N target_size MAX_OUT  (limit number of sets)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#ifndef MAXN
#define MAXN 400
#endif

#define MAX_BITS (2 * MAXN + 64)
#define MAX_WORDS ((MAX_BITS + 63) / 64)

static int N;
static int n_words;
static int target_size;
static long max_out = 1000000;
static long n_found;
static long n_skipped_anom = 0;  /* anomalies (inv >= 2) flagged */

static inline void bs_zero(uint64_t *bs) { memset(bs, 0, sizeof(uint64_t) * n_words); }
static inline void bs_copy(uint64_t *dst, const uint64_t *src) { memcpy(dst, src, sizeof(uint64_t) * n_words); }
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
static inline void bs_or(uint64_t *dst, const uint64_t *a, const uint64_t *b) {
    for (int i = 0; i < n_words; i++) dst[i] = a[i] | b[i];
}
static inline void bs_or_andnot(uint64_t *dst, const uint64_t *a, const uint64_t *b, const uint64_t *c) {
    for (int i = 0; i < n_words; i++) dst[i] = (a[i] | b[i]) & ~c[i];
}
static inline int bs_popcount_andnot_le1(const uint64_t *a, const uint64_t *b) {
    int total = 0;
    for (int i = 0; i < n_words; i++) {
        int p = __builtin_popcountll(a[i] & ~b[i]);
        total += p;
        if (total >= 2) return 2;
    }
    return total;
}

static uint64_t stk_A[MAXN + 2][MAX_WORDS];
static uint64_t stk_once[MAXN + 2][MAX_WORDS];
static uint64_t stk_exc[MAXN + 2][MAX_WORDS];
static int stk_elts[MAXN + 2][MAXN + 2];
static int stk_size[MAXN + 2];

static uint64_t buf_new_sums[MAX_WORDS];
static uint64_t buf_coll[MAX_WORDS];

/* On a complete set of size==target_size, compute and emit. */
static void emit_set(int d) {
    int *A = stk_elts[d];
    int sz = stk_size[d];
    /* Compute r(n*) — the multiplicity of the most-frequent pair-sum. */
    static int counts[2 * MAXN + 4];
    int upper = 2 * N + 2;
    for (int i = 0; i < upper; i++) counts[i] = 0;
    for (int i = 0; i < sz; i++) {
        for (int j = i; j < sz; j++) {
            counts[A[i] + A[j]]++;
        }
    }
    int nstar = 0, r = 0;
    for (int v = 0; v < upper; v++) {
        if (counts[v] > r) { r = counts[v]; nstar = v; }
    }
    if (r < 2) { nstar = 0; r = 1; }
    int inv = 2 * r - sz;
    if (inv >= 2) n_skipped_anom++;
    printf("%d\t%d\t%d\t%d\t%d\t", N, sz, nstar, r, inv);
    for (int i = 0; i < sz; i++) {
        printf("%d%s", A[i], i + 1 < sz ? "," : "");
    }
    printf("\n");
    if ((n_found % 5000) == 0) fflush(stdout);
    n_found++;
}

static void backtrack(int d, int start) {
    int cur_size = stk_size[d];
    if (cur_size == target_size) { emit_set(d); return; }
    if (n_found >= max_out) return;
    /* cur_size + (N - start) < target_size: cannot reach. */
    if (cur_size + (N - start) < target_size) return;

    uint64_t *A    = stk_A[d];
    uint64_t *once = stk_once[d];
    uint64_t *exc  = stk_exc[d];
    int exc_set = !bs_iszero(exc);

    for (int x = start + 1; x <= N; x++) {
        if (cur_size + 1 + (N - x) < target_size) break;
        if (n_found >= max_out) return;

        bs_lshift(buf_new_sums, A, x);
        buf_new_sums[(2 * x) >> 6] |= (1ULL << ((2 * x) & 63));

        bs_and(buf_coll, once, buf_new_sums);

        int new_exc_pop = bs_popcount_andnot_le1(buf_coll, exc);
        if (new_exc_pop >= 2) continue;
        if (new_exc_pop == 1 && exc_set) continue;

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

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "Usage: %s N target_size [MAX_OUT]\n", argv[0]);
        return 1;
    }
    N = atoi(argv[1]);
    target_size = atoi(argv[2]);
    if (argc >= 4) max_out = atol(argv[3]);
    n_words = (2 * N + 64 + 1) / 64;

    bs_zero(stk_A[0]);
    bs_zero(stk_once[0]);
    bs_zero(stk_exc[0]);
    stk_size[0] = 0;

    n_found = 0;
    n_skipped_anom = 0;

    clock_t t0 = clock();
    fprintf(stderr, "# Target enum: N=%d, target_size=%d, max_out=%ld\n",
            N, target_size, max_out);
    backtrack(0, 0);
    double dt = (double)(clock() - t0) / CLOCKS_PER_SEC;
    fprintf(stderr, "# Done: found=%ld anomalies=%ld  t=%.2fs\n",
            n_found, n_skipped_anom, dt);
    return 0;
}
