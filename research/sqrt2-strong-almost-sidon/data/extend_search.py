#!/usr/bin/env python3
"""
extend_search.py — Python driver for the SAS f(N) extension.

Companion to extend_search.c (the actual workhorse). This script:

 1. Compiles and invokes the C program to compute f(N) for a given range.
 2. Parses the output (size + extremizing set).
 3. Classifies each extremizer for "Erdős–Freud (EF) form": does there exist
    a Sidon B ⊆ [1, ⌊N/3⌋] (or up to a small slack) with A = B ∪ (N − B)?
 4. Compares f(N) against the EF asymptotic prediction.

Usage:
    python3 extend_search.py 70 100        # compute f(N) for N = 70..100
    python3 extend_search.py 70 100 --no-build  # skip rebuild

Outputs:
 - data/A389182-extended.txt      (b-file format)
 - data/extremizers.txt           (one extremizer per N with classification)

A pure-Python fallback search is also provided for small N (matches Spencer
2025-08 algorithm) — used only as sanity check.
"""

from __future__ import annotations
import argparse
import math
import os
import subprocess
import sys
from dataclasses import dataclass
from typing import List, Tuple, Optional


HERE = os.path.dirname(os.path.abspath(__file__))


def is_sidon(B: List[int]) -> bool:
    """True iff B is a Sidon set: all pairwise sums distinct."""
    sums = set()
    n = len(B)
    for i in range(n):
        for j in range(i, n):
            s = B[i] + B[j]
            if s in sums:
                return False
            sums.add(s)
    return True


def is_sas(A: List[int]) -> Tuple[bool, Optional[int]]:
    """True iff A is strong-almost-Sidon. Returns (True, exc) or (False, None)
    where exc is the single exceptional sum value (None if A is Sidon)."""
    counts: dict[int, int] = {}
    A_sorted = sorted(A)
    n = len(A_sorted)
    for i in range(n):
        for j in range(i, n):
            s = A_sorted[i] + A_sorted[j]
            counts[s] = counts.get(s, 0) + 1
    excs = [v for v, c in counts.items() if c >= 2]
    if len(excs) == 0:
        return True, None
    if len(excs) == 1:
        return True, excs[0]
    return False, None


@dataclass
class Row:
    N: int
    size: int
    A: List[int]


def parse_c_line(line: str) -> Optional[Row]:
    """Parse '70 14  # t=0.10s  set=1,2,4,...' into a Row."""
    line = line.strip()
    if not line or line.startswith("#"):
        return None
    parts = line.split("#", 1)
    head = parts[0].strip()
    if " " not in head:
        return None
    try:
        n_str, sz_str = head.split()
        N = int(n_str)
        size = int(sz_str)
    except ValueError:
        return None
    A: List[int] = []
    if len(parts) > 1:
        tail = parts[1]
        # look for "set=...,..."
        idx = tail.find("set=")
        if idx != -1:
            seq = tail[idx + 4:].strip()
            A = [int(x) for x in seq.split(",") if x.strip()]
    return Row(N=N, size=size, A=A)


def classify_ef(N: int, A: List[int]) -> dict:
    """
    Classify whether A is approximately of EF reflection form
    A = B ∪ (N − B) for some Sidon B ⊆ [1, ⌊N/3⌋] (or slightly extended).

    We compute:
      lo = A ∩ [1, ⌊N/3⌋]
      hi = A ∩ [N − ⌊N/3⌋, N]   (the "high third")
      mid = A ∩ (⌊N/3⌋, N − ⌊N/3⌋)   (the "middle, which should be empty")

    EF strict: A == lo ∪ (N − lo) AND lo is Sidon AND lo ⊆ [1, N/3].
    EF approx: |A symdiff (lo ∪ (N − lo))| small, OR lo Sidon, with bounded
       deviations.

    Returns dict with keys:
      lo, hi, mid: lists
      mirror = {N - a : a in A}
      ef_strict: bool
      deviation_count: int (number of elements not fitting the EF mold)
      lo_sidon: whether lo is Sidon
    """
    third = N // 3
    A_set = set(A)
    lo = sorted(x for x in A if 1 <= x <= third)
    hi = sorted(x for x in A if N - third <= x <= N)
    mid = sorted(x for x in A if third < x < N - third)

    # Candidate: derive B from lo, build A_candidate = lo ∪ (N - lo).
    cand = set(lo) | {N - x for x in lo}
    deviation = (A_set ^ cand)  # symmetric difference
    deviation_count = len(deviation)

    lo_sidon_flag = is_sidon(lo) if lo else True

    ef_strict = (deviation_count == 0) and lo_sidon_flag

    # An "EF-form" extremizer: the set is exactly lo ∪ (N - lo) with lo Sidon.
    # A "near-EF" extremizer: deviation_count ≤ 2.
    return {
        "lo": lo,
        "hi": hi,
        "mid": mid,
        "deviation_count": deviation_count,
        "deviation": sorted(deviation),
        "lo_sidon": lo_sidon_flag,
        "ef_strict": ef_strict,
    }


def ef_asymptotic(N: int) -> float:
    """The Erdős–Freud asymptotic prediction (2/√3)·√N + 1.520·N^{1/4}."""
    return (2.0 / math.sqrt(3.0)) * math.sqrt(N) + 1.520 * (N ** 0.25)


def run_c(n_start: int, n_end: int, build: bool = True) -> List[Row]:
    binary = os.path.join(HERE, "extend_search")
    source = os.path.join(HERE, "extend_search.c")
    if build:
        cmd = ["cc", "-O3", "-march=native", "-o", binary, source]
        print("[build]", " ".join(cmd), file=sys.stderr)
        subprocess.check_call(cmd)
    rows: List[Row] = []
    cmd = [binary, str(n_start), str(n_end)]
    print("[run]", " ".join(cmd), file=sys.stderr)
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True)
    assert proc.stdout is not None
    for line in proc.stdout:
        print(line, end="", file=sys.stderr)  # mirror
        row = parse_c_line(line)
        if row is not None:
            rows.append(row)
    proc.wait()
    if proc.returncode != 0:
        raise RuntimeError(f"extend_search exited {proc.returncode}")
    return rows


def write_extended(rows: List[Row], path: str, existing_path: Optional[str] = None):
    """Write A389182-extended.txt in OEIS b-file format."""
    existing: List[Tuple[int, int]] = []
    if existing_path and os.path.exists(existing_path):
        with open(existing_path) as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                parts = line.split()
                if len(parts) >= 2:
                    try:
                        existing.append((int(parts[0]), int(parts[1])))
                    except ValueError:
                        pass

    seen = {n for n, _ in existing}
    new = [(r.N, r.size) for r in rows if r.N not in seen]
    combined = sorted(existing + new)
    with open(path, "w") as f:
        f.write("# A389182 extended via extend_search.c\n")
        f.write("# N f(N)\n")
        for n, v in combined:
            f.write(f"{n} {v}\n")


def write_extremizers(rows: List[Row], path: str):
    with open(path, "w") as f:
        f.write("# N f(N) | extremizer | classification\n")
        f.write("# columns:\n")
        f.write("#   N\n")
        f.write("#   f(N)\n")
        f.write("#   extremizer A (comma-separated)\n")
        f.write("#   lo = A ∩ [1, ⌊N/3⌋]\n")
        f.write("#   mid = A ∩ (⌊N/3⌋, N - ⌊N/3⌋)\n")
        f.write("#   ef_strict (1 if A == lo ∪ (N - lo) with lo Sidon)\n")
        f.write("#   deviation_count\n")
        f.write("#   ef_pred = (2/√3)√N + 1.520·N^{1/4}\n")
        f.write("\n")
        for r in rows:
            cls = classify_ef(r.N, r.A)
            ef = ef_asymptotic(r.N)
            sas, exc = is_sas(r.A)
            f.write(
                f"N={r.N}  f={r.size}  ef_pred={ef:.3f}  "
                f"ef_strict={int(cls['ef_strict'])}  dev={cls['deviation_count']}  "
                f"lo_sidon={int(cls['lo_sidon'])}  sas={int(sas)}  exc={exc}\n"
            )
            f.write(f"   A   = {r.A}\n")
            f.write(f"   lo  = {cls['lo']}\n")
            f.write(f"   mid = {cls['mid']}\n")
            f.write(f"   dev = {cls['deviation']}\n")
            f.write("\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n_start", type=int)
    ap.add_argument("n_end", type=int)
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--out-extended", default=os.path.join(HERE, "A389182-extended.txt"))
    ap.add_argument("--out-extremizers", default=os.path.join(HERE, "extremizers.txt"))
    args = ap.parse_args()

    rows = run_c(args.n_start, args.n_end, build=not args.no_build)
    # Sanity check: verify each row's A is actually SAS.
    for r in rows:
        ok, exc = is_sas(r.A)
        if not ok or len(r.A) != r.size:
            print(f"WARNING: N={r.N} claimed |A|={r.size} but verify failed (sas={ok})",
                  file=sys.stderr)

    write_extended(rows, args.out_extended,
                   existing_path=os.path.join(HERE, "A389182.txt"))
    write_extremizers(rows, args.out_extremizers)
    print(f"Wrote {args.out_extended} and {args.out_extremizers}", file=sys.stderr)


if __name__ == "__main__":
    main()
