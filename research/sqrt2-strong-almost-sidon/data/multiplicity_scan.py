#!/usr/bin/env python3
"""
multiplicity_scan.py — scan SAS sets via random-restart hill climb for
N ∈ {100, 110, 120, 150, 200, 300} and record the multiplicity invariant
2*r_A(n*) - |A| for every (near-)extremal candidate found.

For each N:
  - run K random restarts (with kick/swap)
  - keep every set whose size equals best_size or best_size - 1
  - for each kept set A, compute n* = argmax_v |{i<=j : A_i + A_j = v}|,
    r_A(n*), invariant inv = 2*r_A(n*) - |A|.
  - flag any with inv >= 2.

Outputs:
  - data/multiplicity_scan_results.json: full set list per N (top-K).
  - data/multiplicity_scan_summary.txt:  table of (N, size, n*, r, inv) lines.
"""
from __future__ import annotations
import argparse
import json
import math
import os
import random
import sys
import time
from collections import Counter

# Import the SAS hill-climb infrastructure from random_restart.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import random_restart as rr  # noqa: E402


def exception(A):
    cnt = Counter()
    A = sorted(A)
    for i in range(len(A)):
        for j in range(i, len(A)):
            cnt[A[i] + A[j]] += 1
    # SAS: at most one v has count >= 2
    excs = [(v, c) for v, c in cnt.items() if c >= 2]
    if not excs:
        return None, 0
    excs.sort(key=lambda x: -x[1])
    return excs[0]


def scan_N(N, n_restarts, seed=42, keep_within=1, verbose=False):
    """Run hill climb, return list of (size, n*, r, inv, A) sorted by size desc."""
    rng = random.Random(seed + N)
    candidates = []  # list of (size, n*, r, inv, A)
    best_size = 0
    t0 = time.time()
    for trial in range(n_restarts):
        trial_rng = random.Random((seed + N) * 1_000_003 + trial)
        state = rr.random_initial_sidon(N, trial_rng)
        rr.hill_climb(state, trial_rng)
        sz = state.size()
        if sz > best_size:
            best_size = sz
        ns, r = exception(state.A_list)
        if ns is None:
            ns = 0
            r = 1
        inv = 2 * r - sz
        candidates.append((sz, ns, r, inv, sorted(state.A_list)))
        if verbose and (trial + 1) % 20 == 0:
            print(f"  N={N} trial {trial+1}/{n_restarts} best={best_size} "
                  f"elapsed={time.time()-t0:.1f}s", file=sys.stderr)
    # Keep candidates with size >= best_size - keep_within.
    candidates.sort(key=lambda x: (-x[0], -x[2]))
    threshold = best_size - keep_within
    kept = [c for c in candidates if c[0] >= threshold]
    return best_size, kept, time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", default="100,110,120,150",
                    help="comma-separated N values")
    ap.add_argument("--restarts", default="200,200,150,80",
                    help="comma-separated restart counts (matched to --ns)")
    ap.add_argument("--keep-within", type=int, default=2,
                    help="keep sets of size >= best - keep_within")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--out-json", default="multiplicity_scan_results.json")
    ap.add_argument("--out-summary", default="multiplicity_scan_summary.txt")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    ns = [int(x) for x in args.ns.split(",")]
    rs = [int(x) for x in args.restarts.split(",")]
    assert len(ns) == len(rs)

    out_json = {}
    summary_lines = []
    summary_lines.append("# multiplicity_scan_summary  (random-restart hill-climb)\n")
    summary_lines.append("# columns: N <tab> |A| <tab> n* <tab> r(n*) <tab> 2r-|A| <tab> kept_count\n")
    anomalies = []

    for N, R in zip(ns, rs):
        print(f"\n=== N={N}  restarts={R} ===", file=sys.stderr)
        best, kept, elapsed = scan_N(N, R, seed=args.seed,
                                     keep_within=args.keep_within,
                                     verbose=args.verbose)
        print(f"  best_size={best}  kept={len(kept)}  elapsed={elapsed:.1f}s",
              file=sys.stderr)
        # Dedupe by tuple(A)
        seen = set()
        uniq = []
        for sz, ns_v, r, inv, A in kept:
            key = (sz, tuple(A))
            if key in seen:
                continue
            seen.add(key)
            uniq.append((sz, ns_v, r, inv, A))
        out_json[str(N)] = {
            "best_size": best,
            "n_restarts": R,
            "elapsed_s": elapsed,
            "n_unique_kept": len(uniq),
            "sets": [
                {"size": sz, "n_star": ns_v, "r": r, "inv": inv, "A": A}
                for sz, ns_v, r, inv, A in uniq
            ],
        }
        summary_lines.append(f"\n## N={N}  best_size={best}  kept_unique={len(uniq)}  "
                             f"(restarts={R}, t={elapsed:.0f}s)\n")
        # Print top 20 of each
        printed = 0
        for sz, ns_v, r, inv, A in uniq[:30]:
            summary_lines.append(f"  {N}\t{sz}\t{ns_v}\t{r}\t{inv}\n")
            if inv >= 2:
                anomalies.append((N, sz, ns_v, r, inv, A))
            printed += 1
        if len(uniq) > printed:
            summary_lines.append(f"  ... ({len(uniq) - printed} more truncated)\n")

    if anomalies:
        summary_lines.append("\n## ANOMALIES (2r - |A| >= 2) -- POTENTIAL COUNTEREXAMPLES\n")
        for N, sz, ns_v, r, inv, A in anomalies:
            summary_lines.append(f"  N={N} size={sz} n*={ns_v} r={r} inv={inv}\n")
            summary_lines.append(f"    A = {A}\n")
    else:
        summary_lines.append("\n## No anomalies (2r - |A| >= 2) found.\n")

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, args.out_json), "w") as f:
        json.dump(out_json, f, indent=1)
    with open(os.path.join(here, args.out_summary), "w") as f:
        f.writelines(summary_lines)
    print(f"\nWrote {args.out_json} and {args.out_summary}", file=sys.stderr)
    if anomalies:
        print(f"\n*** {len(anomalies)} ANOMALIES FOUND ***", file=sys.stderr)
    else:
        print("\nNo invariant violations found.", file=sys.stderr)


if __name__ == "__main__":
    main()
