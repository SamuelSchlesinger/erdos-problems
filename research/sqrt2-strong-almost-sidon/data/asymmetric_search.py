#!/usr/bin/env python3
"""
asymmetric_search.py — search asymmetric Erdős–Freud (EF) reflection
constructions for the strong almost-Sidon (SAS) problem.

Construction:
    A = B ∪ (M − B)   for M ∈ [N/2, N] and Sidon B ⊂ [1, αN], α ∈ (1/3, 1/2].

The canonical EF construction is recovered at  M = N, α = 1/3.
We test whether any asymmetric variant beats EF in cardinality for
N ∈ {100, 200}.

Strategy:
  1. Compute |A_EF| = 2 · |B_EF| where B_EF is a maximum Sidon subset of
     [1, ⌊N/3⌋].
  2. For each M, try to construct a Sidon B ⊂ [lo_b, αN] of size > |B_EF|
     such that A = B ∪ (M − B) is SAS in [1, N]. Use combined Sidon +
     SAS backtracking — we prune both within the Sidon DFS and via the
     A-side SAS constraint.
  3. We do this for a coarse M-grid and α-grid.

The combined search prunes very aggressively: at each step we maintain
the pair-sum bitfield of A (not just B), so adding x to B is rejected
unless A ∪ {x, M-x} extends without introducing a second exception.

Reference for the EF baseline: Erdős–Freud 1991, also computer-search-report.md.
"""

from __future__ import annotations
import time
import sys
from pathlib import Path

# ---------- helpers -----------------------------------------------------

def is_strong_almost_sidon(A):
    L = sorted(A)
    mult = {}
    for i in range(len(L)):
        for j in range(i, len(L)):
            s = L[i] + L[j]
            mult[s] = mult.get(s, 0) + 1
    bad = [s for s, m in mult.items() if m > 1]
    if len(bad) > 1:
        return False, None
    return True, (bad[0] if bad else None)


def is_sidon(S):
    L = sorted(S)
    sums = set()
    for i in range(len(L)):
        for j in range(i, len(L)):
            s = L[i] + L[j]
            if s in sums:
                return False
            sums.add(s)
    return True


def max_sidon_in_interval(U):
    """Find one maximum Sidon subset of [1, U] by backtracking."""
    best = []

    def recurse(cur, last, sumbits):
        nonlocal best
        if len(cur) + (U - last) <= len(best):
            return
        for x in range(last + 1, U + 1):
            if len(cur) + (U - x + 1) <= len(best):
                break
            doubled = 2 * x
            if (sumbits >> doubled) & 1:
                continue
            new_pairs = 1 << doubled
            ok = True
            for y in cur:
                s = x + y
                if (sumbits >> s) & 1 or (new_pairs >> s) & 1:
                    ok = False
                    break
                new_pairs |= 1 << s
            if not ok:
                continue
            cur.append(x)
            if len(cur) > len(best):
                best = list(cur)
            recurse(cur, x, sumbits | new_pairs)
            cur.pop()

    recurse([], 0, 0)
    return best


def max_sidon_in_range(lo, hi):
    """Maximum Sidon subset of [lo, hi]. Backtracking with bitfield."""
    best = []

    def recurse(cur, last, sumbits):
        nonlocal best
        if len(cur) + (hi - last) <= len(best):
            return
        for x in range(last + 1, hi + 1):
            if len(cur) + (hi - x + 1) <= len(best):
                break
            doubled = 2 * x
            if (sumbits >> doubled) & 1:
                continue
            new_pairs = 1 << doubled
            ok = True
            for y in cur:
                s = x + y
                if (sumbits >> s) & 1 or (new_pairs >> s) & 1:
                    ok = False
                    break
                new_pairs |= 1 << s
            if not ok:
                continue
            cur.append(x)
            if len(cur) > len(best):
                best = list(cur)
            recurse(cur, x, sumbits | new_pairs)
            cur.pop()

    recurse([], lo - 1, 0)
    return best


# ---------- EF baseline -------------------------------------------------

# Hardcoded EF data — match the slow brute-force exactly. Verified by
# max_sidon_in_interval(U) above. See computer-search-report.md.
# Format: N -> (U=N//3, |B_EF|, B_EF)
_EF_CACHE = {
    100: (33, 7, [1, 2, 4, 8, 13, 21, 31]),
    200: (66, 10, [1, 2, 4, 8, 19, 31, 39, 44, 53, 63]),
}


def ef_baseline(N):
    if N in _EF_CACHE:
        U, k, B = _EF_CACHE[N]
        A = sorted(set(B) | {N - b for b in B})
        ok, exc = is_strong_almost_sidon(A)
        return len(A), B, A, exc, ok
    U = N // 3
    B = max_sidon_in_interval(U)
    A = sorted(set(B) | {N - b for b in B})
    ok, exc = is_strong_almost_sidon(A)
    return len(A), B, A, exc, ok


# ---------- combined Sidon + SAS DFS  ------------------------------------
#
# We are choosing B as a Sidon subset of [lo_b, hi_b], and for each x added
# to B we want to track whether A = B ∪ (M − B) remains strong almost-Sidon.
#
# Maintain bitfields over sum range [0, 2N]:
#   A_bits          : current A
#   sums_once_bits  : pair sums in A with multiplicity exactly 1
#   exc             : the single exception sum (or -1)
#
# Adding b to B means adding {b, M-b} to A. We need to check both extensions
# can be done without creating a second exception.

def add_element_to_A(x, A_bits, sums_once, exc, MAX):
    """Try adding element x to current A.
    Returns (new_A_bits, new_sums_once, new_exc) or None if SAS violated.
    """
    # All pair sums with existing A: A_bits << x (in [0, 2N])
    new_sums = (A_bits << x) | (1 << (2 * x))
    # Mask to valid sum range
    new_sums &= (1 << (MAX + 1)) - 1
    collisions = sums_once & new_sums
    # Possibly multiple bits set; check against exc
    if exc >= 0:
        # Any collision outside exc is a new exception
        new_exc_bits = collisions & ~(1 << exc)
        if new_exc_bits != 0:
            return None  # would create a 2nd exception
        # exc unchanged
        new_exc = exc
    else:
        # exc is unset
        cnt = bin(collisions).count('1')
        if cnt > 1:
            return None
        if cnt == 1:
            new_exc = collisions.bit_length() - 1
        else:
            new_exc = -1
    new_sums_once = (sums_once | new_sums) & ~collisions
    new_A_bits = A_bits | (1 << x)
    return new_A_bits, new_sums_once, new_exc


def search_combined(N, M, lo_b, hi_b, target_size,
                    abort_on_target=True, time_budget=20.0):
    """Backtracking search for Sidon B ⊂ [lo_b, hi_b] such that
    A = B ∪ (M − B) is SAS in [1, N] and |B| ≥ target_size.

    Returns (best_size, best_B, best_A, best_exc) — the largest |B| found,
    along with witness. If abort_on_target is True, exit as soon as a B of
    size target_size is found.

    Pruning:
      - |B| + (hi_b − last) cannot beat target_size: prune.
      - SAS constraint must hold for both b and M−b in A.
      - M − b must be in [1, N].
      - b and M − b must not already be in A (would mean |A| < 2|B|).
    """
    t0 = time.time()
    MAX = 2 * N + 4
    best = [0, None, None, None]
    state = {'abort': False, 'time_exceeded': False}

    def recurse(cur, last, A_bits, sums_once, exc):
        if state['abort'] or state['time_exceeded']:
            return
        if time.time() - t0 > time_budget:
            state['time_exceeded'] = True
            return
        if len(cur) > best[0]:
            best[0] = len(cur)
            best[1] = list(cur)
            # reconstruct A
            A = []
            bits = A_bits
            i = 0
            while bits:
                if bits & 1:
                    A.append(i)
                bits >>= 1
                i += 1
            best[2] = A
            best[3] = exc
            if abort_on_target and len(cur) >= target_size:
                state['abort'] = True
                return
        # Prune: even taking all remaining elements can we beat best?
        if len(cur) + (hi_b - last) < target_size:
            return
        for x in range(last + 1, hi_b + 1):
            if len(cur) + (hi_b - x + 1) < target_size:
                break
            # x must be in valid range; also M - x must be in [1, N]
            mx = M - x
            if mx < 1 or mx > N:
                continue
            # Need b < M - b (else b and M-b coincide or B has duplicates)
            # Equivalently x < M/2. We enforce by checking x < mx.
            if x >= mx:
                continue
            # Need x and mx not already in A.
            if (A_bits >> x) & 1:
                continue
            if (A_bits >> mx) & 1:
                continue

            # Try adding x first
            r = add_element_to_A(x, A_bits, sums_once, exc, MAX)
            if r is None:
                continue
            A_bits1, sums_once1, exc1 = r
            # Then add mx
            r2 = add_element_to_A(mx, A_bits1, sums_once1, exc1, MAX)
            if r2 is None:
                continue
            A_bits2, sums_once2, exc2 = r2

            cur.append(x)
            recurse(cur, x, A_bits2, sums_once2, exc2)
            cur.pop()
            if state['abort']:
                return

    recurse([], lo_b - 1, 0, 0, -1)
    return best[0], best[1], best[2], best[3], state['time_exceeded']


# ---------- main driver -------------------------------------------------

def alpha_to_hi_b(alpha, N, M):
    """Compute hi_b = min(αN, M − 1, M − (M − N)_+ − 1, ...).

    Hard constraint: b ∈ B means M − b ∈ A ⊂ [1, N], so b ≥ M − N if M > N
    (vacuous if M ≤ N) and b ≤ M − 1. Also b < M/2 (so distinct from M − b).
    """
    hi = min(int(alpha * N), N, M - 1, (M - 1) // 2)
    return hi


def lo_b_for(M, N):
    """Lowest allowed b. Need M − b ≤ N, i.e., b ≥ M − N (≥ 1)."""
    return max(1, M - N)


def main():
    out_path = Path(__file__).parent / "asymmetric_results.txt"
    lines = []
    lines.append("# Asymmetric Erdős–Freud (EF) reflection search for SAS sets")
    lines.append("# Construction: A = B ∪ (M − B), B Sidon ⊂ [1, αN], M ∈ [N/2, N]")
    lines.append("#")
    lines.append("# Goal: find any (M, α, B) that beats |A_EF| at N.")
    lines.append("# Run date: 2026-05-22")
    lines.append("")

    overall_summary = []

    for N in (100, 200):
        lines.append("=" * 70)
        lines.append(f"### N = {N}")
        lines.append("=" * 70)
        t0 = time.time()
        ef_card, ef_B, ef_A, ef_exc, ef_ok = ef_baseline(N)
        t_ef = time.time() - t0
        lines.append(f"EF baseline: |A_EF| = {ef_card}")
        lines.append(f"  B_EF = {ef_B}")
        lines.append(f"  |B_EF| = {len(ef_B)} (max Sidon in [1, {N//3}])")
        lines.append(f"  A_EF = {ef_A}")
        lines.append(f"  exc = {ef_exc}, SAS-ok = {ef_ok}")
        lines.append(f"  EF compute time: {t_ef:.2f}s")
        lines.append("")
        # Target: try to find |B| ≥ |B_EF| + 1, i.e., |A| ≥ ef_card + 2.
        target_B = len(ef_B) + 1
        lines.append(f"Search target: |B| ≥ {target_B} (so |A| ≥ {2*target_B} > "
                     f"{ef_card} = |A_EF|).")
        lines.append("")

        # M grid: coarse
        if N == 100:
            M_list = sorted(set([50, 60, 66, 75, 80, 90, 95, 98, 100]))
            alpha_list = [0.34, 0.37, 0.40, 0.45, 0.50]
        else:
            M_list = sorted(set([100, 120, 133, 150, 167, 180, 190, 195, 200]))
            alpha_list = [0.34, 0.37, 0.40, 0.45, 0.50]

        lines.append(f"M grid ({len(M_list)} values): {M_list}")
        lines.append(f"α grid: {[round(a,3) for a in alpha_list]}")
        lines.append("")

        # Per-(M, α) time budget — small to keep total bounded.
        if N == 100:
            tb_per = 5.0
        else:
            tb_per = 12.0

        best_overall = (0, None, None, None, None)
        all_rows = []

        n_combos = len(M_list) * len(alpha_list)
        idx = 0
        for M in M_list:
            for alpha in alpha_list:
                idx += 1
                print(f"[N={N}] {idx}/{n_combos}  M={M} α={alpha:.2f}",
                      flush=True)
                hi_b = alpha_to_hi_b(alpha, N, M)
                lo_b = lo_b_for(M, N)
                if hi_b - lo_b + 1 < target_B:
                    all_rows.append((M, round(alpha,3), lo_b, hi_b,
                                     "skip (too small)"))
                    continue

                t1 = time.time()
                size, B, A, exc, timed_out = search_combined(
                    N, M, lo_b, hi_b, target_B,
                    abort_on_target=True, time_budget=tb_per)
                dt = time.time() - t1
                # Re-verify result
                if B is not None and len(B) >= 1:
                    A_check = sorted(set(B) | {M - b for b in B})
                    ok, exc_check = is_strong_almost_sidon(A_check)
                else:
                    ok = None
                    exc_check = None
                row = (M, round(alpha,3), lo_b, hi_b, size,
                       'T' if timed_out else '.',
                       round(dt, 2),
                       'OK' if ok else ('?' if ok is None else 'BAD'),
                       exc_check)
                all_rows.append(row)

                if size > best_overall[0]:
                    best_overall = (size, M, alpha, B, A, exc)
                    if 2 * size > ef_card:
                        # Found a witness — keep searching other M, α for completeness
                        pass

        for r in all_rows:
            lines.append("  " + str(r))
        lines.append("")

        size, M, alpha, B, A, exc = best_overall[0], *best_overall[1:]
        lines.append(f"Best result: |B| = {size}, |A| = {2*size if size else 0}")
        if B is not None:
            lines.append(f"  M = {M}, α = {alpha}")
            lines.append(f"  B = {B}")
            lines.append(f"  A = {sorted(set(B) | {M - b for b in B})}")
            ok, exc_check = is_strong_almost_sidon(sorted(set(B) | {M - b for b in B}))
            lines.append(f"  SAS-ok = {ok}, exc = {exc_check}")
        lines.append("")

        if size and 2 * size > ef_card:
            verdict = (f"N={N}: ASYMMETRIC BEATS EF  ({2*size} > {ef_card}).  "
                       f"Witness M={M}, α={alpha}, B={B}.")
        elif size and 2 * size == ef_card:
            verdict = (f"N={N}: asymmetric MATCHES EF  ({2*size} = {ef_card}).")
        else:
            verdict = (f"N={N}: asymmetric does NOT beat EF  "
                       f"(best |A| = {2*size if size else 0} vs EF {ef_card}).")
        lines.append("VERDICT: " + verdict)
        lines.append("")
        overall_summary.append(verdict)

    lines.append("=" * 70)
    lines.append("OVERALL SUMMARY")
    lines.append("=" * 70)
    for v in overall_summary:
        lines.append("  " + v)

    out_path.write_text("\n".join(lines))
    print(f"Wrote {out_path}")
    sys.stdout.flush()


if __name__ == "__main__":
    main()
