#!/usr/bin/env python3
"""Classify insertion-shadow certificates for missing reflections.

For each SAS witness with exception value n*, and each x in A whose reflection
y = n* - x is missing, report whether y is blocked by:

  * self:      2y = b + c away from n*
  * translate: y + a = b + c away from n*
  * both
  * none
  * out_of_range, when y is outside {1, ..., N}

This is the empirical companion to `Erdos/AlmostSidonSets/Maximality.lean`.
"""

from __future__ import annotations

import json
import os
from collections import Counter, defaultdict

from analyze_invariants import exception_value, parse_asymmetric, parse_par_results

HERE = os.path.dirname(os.path.abspath(__file__))


def pair_reps(A):
    reps = defaultdict(list)
    A = sorted(A)
    for i, b in enumerate(A):
        for c in A[i:]:
            reps[b + c].append((b, c))
    return reps


def shadow_rows(N, A, nstar):
    A = sorted(A)
    Aset = set(A)
    reps = pair_reps(A)
    rows = []
    for x in A:
        y = nstar - x
        if y in Aset:
            continue

        self_blockers = []
        translate_blockers = []
        if 1 <= y <= N:
            if 2 * y != nstar:
                self_blockers = reps.get(2 * y, [])
            for a in A:
                s = y + a
                if s == nstar:
                    continue
                for b, c in reps.get(s, []):
                    translate_blockers.append((a, b, c))

        if not (1 <= y <= N):
            kind = "out_of_range"
        elif self_blockers and translate_blockers:
            kind = "both"
        elif self_blockers:
            kind = "self"
        elif translate_blockers:
            kind = "translate"
        else:
            kind = "none"

        rows.append(
            {
                "N": N,
                "size": len(A),
                "nstar": nstar,
                "x": x,
                "y": y,
                "kind": kind,
                "self": self_blockers,
                "translate": translate_blockers,
                "A": A,
            }
        )
    return rows


def parse_target_file(path):
    rows = []
    if not os.path.exists(path):
        return rows
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) < 6:
                continue
            N = int(parts[0])
            size = int(parts[1])
            nstar = int(parts[2])
            A = [int(x) for x in parts[5].split(",") if x]
            if len(A) == size:
                rows.append((N, size, nstar, A))
    return rows


def read_extended_values(path):
    values = {}
    if not os.path.exists(path):
        return values
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) >= 2:
                values[int(parts[0])] = int(parts[1])
    return values


def known_extremizers():
    rows = []
    par_dir = os.path.join(HERE, "par_results")
    if os.path.isdir(par_dir):
        for N, size, A in parse_par_results(par_dir):
            nstar, _ = exception_value(A)
            if nstar is not None:
                rows.append((N, size, nstar, A))
    for N, size, A in parse_asymmetric(os.path.join(HERE, "asymmetric_results.txt")):
        nstar, _ = exception_value(A)
        if nstar is not None:
            rows.append((N, size, nstar, A))
    return dedupe(rows)


def target_rows(N_min=81, N_max=100, delta=0):
    values = read_extended_values(os.path.join(HERE, "A389182-extended-v2.txt"))
    rows = []
    for N in range(N_min, N_max + 1):
        if N not in values or values[N] + delta <= 0:
            continue
        path = os.path.join(HERE, "par_target", f"N{N}_s{values[N] + delta}.txt")
        rows.extend(parse_target_file(path))
    return dedupe(rows)


def multiplicity_scan_rows():
    path = os.path.join(HERE, "multipity_scan_results.json")
    if not os.path.exists(path):
        path = os.path.join(HERE, "multiplicity_scan_results.json")
    if not os.path.exists(path):
        return []
    rows = []
    with open(path) as f:
        data = json.load(f)
    for N_str, payload in data.items():
        N = int(N_str)
        best_size = payload.get("best_size")
        for item in payload.get("sets", []):
            A = item.get("A", [])
            nstar = item.get("n_star")
            if best_size is not None and item.get("size", 0) + 1 < best_size:
                continue
            if A and nstar is not None:
                rows.append((N, len(A), int(nstar), A))
    return dedupe(rows)


def dedupe(rows):
    seen = {}
    for N, size, nstar, A in rows:
        seen[(N, nstar, tuple(sorted(A)))] = (N, size, nstar, sorted(A))
    return sorted(seen.values(), key=lambda r: (r[0], r[1], r[2], r[3]))


def summarize(label, sets):
    all_rows = []
    sets_with_missing = 0
    for N, _size, nstar, A in sets:
        rows = shadow_rows(N, A, nstar)
        if rows:
            sets_with_missing += 1
        all_rows.extend(rows)
    counts = Counter(row["kind"] for row in all_rows)
    in_range = sum(1 for row in all_rows if row["kind"] != "out_of_range")
    return {
        "cohort": label,
        "sets": len(sets),
        "sets_with_missing": sets_with_missing,
        "missing_y": len(all_rows),
        "in_range": in_range,
        "self": counts["self"],
        "translate": counts["translate"],
        "both": counts["both"],
        "none": counts["none"],
        "out": counts["out_of_range"],
        "rows": all_rows,
    }


def blocker_text(row):
    parts = []
    for b, c in row["self"][:2]:
        parts.append(f"2y={b}+{c}")
    for a, b, c in row["translate"][:3]:
        parts.append(f"y+{a}={b}+{c}")
    return "; ".join(parts) if parts else "-"


def main():
    cohorts = [
        ("known extremizers", known_extremizers()),
        ("target max sample N81-100", target_rows(81, 100, 0)),
        ("target one-below N81-100", target_rows(81, 100, -1)),
        ("random/local top", multiplicity_scan_rows()),
    ]
    summaries = [summarize(label, rows) for label, rows in cohorts]

    print("| cohort | sets | sets with missing | missing y | in range | self | translate | both | none | out |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for s in summaries:
        print(
            f"| {s['cohort']} | {s['sets']} | {s['sets_with_missing']} | "
            f"{s['missing_y']} | {s['in_range']} | {s['self']} | "
            f"{s['translate']} | {s['both']} | {s['none']} | {s['out']} |"
        )

    print()
    print("| N | |A| | n* | x | y | kind | blockers |")
    print("|---:|---:|---:|---:|---:|---|---|")
    examples = []
    for s in summaries:
        for row in s["rows"]:
            if row["kind"] in {"both", "translate", "self", "none"}:
                examples.append(row)
    priority = {"both": 0, "translate": 1, "self": 2, "none": 3}
    examples.sort(key=lambda row: (priority[row["kind"]], row["N"], row["x"]))
    for row in examples[:20]:
        print(
            f"| {row['N']} | {row['size']} | {row['nstar']} | {row['x']} | "
            f"{row['y']} | {row['kind']} | `{blocker_text(row)}` |"
        )


if __name__ == "__main__":
    main()
