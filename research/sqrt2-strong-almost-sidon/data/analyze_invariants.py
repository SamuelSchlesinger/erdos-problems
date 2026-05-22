#!/usr/bin/env python3
"""
analyze_invariants.py — extract structural invariants from known SAS extremizers.

For each known extremizer A at N (from data/par_results/ and asymmetric_results.txt),
compute:
  - {m, M, n*}: extreme pair and exception value.
  - {m2, M2}: second-smallest and second-largest.
  - r_A(n*): multiplicity of the exception sum.
  - Gap distribution: a_{i+1} - a_i for consecutive elements.
  - Symmetry test: |{a ∈ A : (n* - a) ∈ A}| / |A|.
  - "EF deficiency": |A △ (B ∪ (n* − B))| for the best Sidon B ⊆ [m, n*/2].
  - R1, R2 verification flags.

Prints a table of invariants per N and a consolidated tally of which
structural properties hold across ALL extremizers.

Outputs (in addition to stdout):
  - empirical-invariants-table.md (in research dir): clean markdown table.
"""
from __future__ import annotations
import os
import re
from collections import Counter
from itertools import combinations_with_replacement

HERE = os.path.dirname(os.path.abspath(__file__))
RESEARCH = os.path.dirname(HERE)


def sumset_counts(A):
    cnt = Counter()
    A = sorted(A)
    for i in range(len(A)):
        for j in range(i, len(A)):
            cnt[A[i] + A[j]] += 1
    return cnt


def exception_value(A):
    c = sumset_counts(A)
    excs = [(v, m) for v, m in c.items() if m >= 2]
    if not excs:
        return None, 0
    # SAS-allowed: at most one exception value.
    excs.sort(key=lambda x: -x[1])
    return excs[0]


def reflection_symmetry(A, n_star):
    Aset = set(A)
    fixed = [a for a in A if (n_star - a) in Aset]
    return len(fixed), len(A)


def is_sidon(B):
    seen = set()
    for i in range(len(B)):
        for j in range(i, len(B)):
            s = B[i] + B[j]
            if s in seen:
                return False
            seen.add(s)
    return True


def best_sidon_subset(A, n_star):
    """Return a maximal Sidon subset B of A ∩ [1, n_star/2] (greedy from small)."""
    lo = sorted(a for a in A if 2 * a <= n_star)
    # Greedy: pick lo[0], add next if still Sidon.
    B = []
    for x in lo:
        cand = B + [x]
        if is_sidon(cand):
            B.append(x)
    return B


def best_ef_deviation(A, n_star):
    """Min over Sidon B ⊆ A∩[1,n_star/2] of |A △ (B ∪ (n_star - B))|, naive
    using best_sidon_subset."""
    B = best_sidon_subset(A, n_star)
    cand = set(B) | {n_star - x for x in B if 1 <= n_star - x}
    return len(set(A) ^ cand), B


def parse_par_results(par_dir):
    rows = []
    for fn in sorted(os.listdir(par_dir)):
        if not (fn.startswith("n_") and fn.endswith(".txt")):
            continue
        with open(os.path.join(par_dir, fn)) as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                parts = line.split("#", 1)
                head_bits = parts[0].split()
                if len(head_bits) < 2:
                    continue
                try:
                    N = int(head_bits[0])
                    size = int(head_bits[1])
                except ValueError:
                    continue
                A = []
                if len(parts) > 1 and "set=" in parts[1]:
                    seq = parts[1].split("set=", 1)[1].strip()
                    A = [int(x) for x in seq.split(",") if x.strip()]
                if A:
                    rows.append((N, size, A))
    rows.sort(key=lambda r: r[0])
    return rows


def parse_asymmetric(path):
    """Pick up the N=100 and N=200 best asymmetric extremizers."""
    rows = []
    if not os.path.exists(path):
        return rows
    with open(path) as f:
        text = f.read()
    # Look for "VERDICT: N=...: ASYMMETRIC BEATS EF" and pull the witness B.
    pattern = re.compile(
        r"### N = (\d+).*?Best result: \|B\| = (\d+), \|A\| = (\d+).*?"
        r"B = (\[[^\]]+\]).*?A = (\[[^\]]+\]).*?SAS-ok = (True|False), exc = (\d+)",
        re.DOTALL,
    )
    for m in pattern.finditer(text):
        N = int(m.group(1))
        size = int(m.group(3))
        A = eval(m.group(5))
        rows.append((N, size, A))
    return rows


def analyze_one(N, A):
    A = sorted(A)
    m_val, M_val = A[0], A[-1]
    m2 = A[1] if len(A) >= 2 else None
    M2 = A[-2] if len(A) >= 2 else None
    nstar, r_nstar = exception_value(A)
    gaps = [A[i + 1] - A[i] for i in range(len(A) - 1)]
    # Symmetry around n*.
    if nstar is None:
        fixed = 0
        total = len(A)
    else:
        fixed, total = reflection_symmetry(A, nstar)
    # R2 check.
    r2 = (nstar is not None) and (m_val + M_val == nstar)
    # Multiplicity check (R1 says r_nstar >= 3 for large A).
    # EF deviation.
    ef_dev = None
    ef_B = None
    if nstar is not None:
        ef_dev, ef_B = best_ef_deviation(A, nstar)
    return {
        "N": N,
        "|A|": len(A),
        "m": m_val,
        "M": M_val,
        "m2": m2,
        "M2": M2,
        "n*": nstar,
        "r(n*)": r_nstar,
        "m+M": m_val + M_val,
        "R2: m+M==n*": r2,
        "gaps": gaps,
        "gap_max": max(gaps) if gaps else 0,
        "gap_min": min(gaps) if gaps else 0,
        "gap_mean": (sum(gaps) / len(gaps)) if gaps else 0.0,
        "sym_fixed": fixed,
        "sym_total": total,
        "sym_full": (fixed == total) if nstar is not None else False,
        "ef_dev": ef_dev,
        "ef_B": ef_B,
        "n*-m == M": (nstar is not None and nstar - m_val == M_val),
        # New invariants to test:
        # I1: m + M2 ?= n* + (M2 - M) etc — explore.
        "m_plus_M2": m_val + M2 if M2 is not None else None,
        "m2_plus_M": m2 + M_val if m2 is not None else None,
        "m_eq_1": m_val == 1,
        "M_eq_Nminus_or_close": M_val,  # we'll show distance from N
    }


def main():
    par_dir = os.path.join(HERE, "par_results")
    rows = parse_par_results(par_dir) if os.path.isdir(par_dir) else []
    rows += parse_asymmetric(os.path.join(HERE, "asymmetric_results.txt"))
    # Deduplicate by (N, tuple(A))
    uniq = {}
    for N, sz, A in rows:
        uniq[(N, tuple(sorted(A)))] = (N, sz, A)
    rows = sorted(uniq.values(), key=lambda r: r[0])

    print(f"Analyzing {len(rows)} extremizers across N values: "
          f"{sorted({r[0] for r in rows})}\n")

    analyses = []
    for N, sz, A in rows:
        a = analyze_one(N, A)
        a["A"] = A
        a["N_orig"] = N
        a["size"] = sz
        analyses.append(a)

    # Print per-N table.
    print(f"{'N':>4} {'|A|':>4} {'m':>3} {'M':>3} {'n*':>4} {'r(n*)':>5} "
          f"{'m+M':>4} {'R2':>3} {'sym':>7} {'ef_dev':>6} {'gap_min':>7} "
          f"{'gap_mean':>8} {'gap_max':>7}")
    for a in analyses:
        sym = f"{a['sym_fixed']}/{a['sym_total']}"
        print(f"{a['N']:>4} {a['|A|']:>4} {a['m']:>3} {a['M']:>3} "
              f"{str(a['n*']):>4} {a['r(n*)']:>5} {a['m+M']:>4} "
              f"{'Y' if a['R2: m+M==n*'] else 'N':>3} {sym:>7} "
              f"{str(a['ef_dev']):>6} {a['gap_min']:>7} {a['gap_mean']:>8.2f} "
              f"{a['gap_max']:>7}")
    print()

    # Tally invariants.
    print("=== Invariant tally across all extremizers ===")
    tally = {}
    tally["m == 1"] = sum(1 for a in analyses if a["m"] == 1)
    tally["m + M == n*"] = sum(1 for a in analyses if a["R2: m+M==n*"])
    tally["r(n*) >= 3"] = sum(1 for a in analyses if a["r(n*)"] >= 3)
    tally["r(n*) >= 4"] = sum(1 for a in analyses if a["r(n*)"] >= 4)
    tally["r(n*) == |A|/2 + ?"] = "see r(n*) values"
    tally["sym_full (a in A => n*-a in A)"] = sum(
        1 for a in analyses if a["sym_full"]
    )
    tally["m2 + M2 == n*"] = sum(
        1 for a in analyses
        if a["m2"] is not None and a["M2"] is not None and a["m2"] + a["M2"] == a["n*"]
    )
    tally["ef_dev <= 2"] = sum(
        1 for a in analyses if a["ef_dev"] is not None and a["ef_dev"] <= 2
    )
    tally["ef_dev == 0"] = sum(
        1 for a in analyses if a["ef_dev"] == 0
    )
    # Anchor + reflect: M == n* - m, M2 == n* - m2.
    tally["M = n* - m AND M2 = n* - m2"] = sum(
        1 for a in analyses
        if a["m2"] is not None and a["M2"] is not None
        and a["n*"] is not None
        and a["M"] == a["n*"] - a["m"]
        and a["M2"] == a["n*"] - a["m2"]
    )
    # Reflection: M2 + m2 = n*.
    # Three reflection pairs:
    tally["3 reflection pairs (m,M), (m2,M2), (m3,M3) all sum to n*"] = 0
    for a in analyses:
        A = a["A"]
        ns = a["n*"]
        if ns is None or len(A) < 6:
            continue
        ok = True
        for k in range(3):
            if A[k] + A[-1 - k] != ns:
                ok = False
                break
        if ok:
            tally["3 reflection pairs (m,M), (m2,M2), (m3,M3) all sum to n*"] += 1
    # All consecutive small/large reflection pairs.
    tally["All reflection pairs sum to n* (full reflection symmetry)"] = sum(
        1 for a in analyses if a["sym_full"]
    )
    # n* equals one of {N-1, N, N+1, N+2}.
    tally["n* in {N-1, N, N+1}"] = sum(
        1 for a in analyses
        if a["n*"] is not None and abs(a["n*"] - a["N"]) <= 1
    )
    # First gap a_2 - a_1 == 1.
    tally["gap[0] == 1 (a_2 - a_1 = 1)"] = sum(
        1 for a in analyses if a["gaps"] and a["gaps"][0] == 1
    )
    # min gap is 1, max gap >= 5.
    tally["gap_min == 1"] = sum(1 for a in analyses if a["gap_min"] == 1)
    # n* is even or odd?
    tally["n* is even"] = sum(
        1 for a in analyses if a["n*"] is not None and a["n*"] % 2 == 0
    )
    tally["n* is odd"] = sum(
        1 for a in analyses if a["n*"] is not None and a["n*"] % 2 == 1
    )

    total = len(analyses)
    for k, v in tally.items():
        if isinstance(v, int):
            print(f"  {k}: {v}/{total} ({100.0*v/total:.0f}%)")
        else:
            print(f"  {k}: {v}")
    print()

    # Detailed: for each extremizer, show "anchor pairs" (a, n* - a) breakdown.
    print("=== Anchor-pair decomposition ===")
    for a in analyses:
        A = a["A"]
        ns = a["n*"]
        if ns is None:
            print(f"N={a['N']}: no exception")
            continue
        Aset = set(A)
        pairs = []
        unpaired = []
        seen = set()
        for x in A:
            if x in seen:
                continue
            y = ns - x
            if y in Aset and y != x:
                pairs.append((min(x, y), max(x, y)))
                seen.add(x)
                seen.add(y)
            elif y == x:
                # fixed point: 2x == n*
                pairs.append((x, x))
                seen.add(x)
            else:
                unpaired.append(x)
                seen.add(x)
        print(f"N={a['N']:3d} n*={ns:3d} |A|={len(A):2d}: "
              f"pairs={len(pairs)} ({pairs})  unpaired={unpaired}")
    print()

    # Output markdown table.
    out_md = os.path.join(RESEARCH, "empirical-invariants-table.md")
    with open(out_md, "w") as f:
        f.write("# Empirical Invariants Across Known SAS Extremizers\n\n")
        f.write("Per-N invariants (N=70..79 from exhaustive search, "
                "N=100, 200 from asymmetric search).\n\n")
        f.write("| N | \\|A\\| | m | M | n* | r(n*) | m+M | R2 | sym | ef_dev |\n")
        f.write("|---|-------|---|---|----|-------|-----|----|----|-------|\n")
        for a in analyses:
            sym = f"{a['sym_fixed']}/{a['sym_total']}"
            f.write(f"| {a['N']} | {a['|A|']} | {a['m']} | {a['M']} | "
                    f"{a['n*']} | {a['r(n*)']} | {a['m+M']} | "
                    f"{'Y' if a['R2: m+M==n*'] else 'N'} | {sym} | "
                    f"{a['ef_dev']} |\n")
        f.write("\n## Anchor-pair decomposition\n\n")
        for a in analyses:
            A = a["A"]
            ns = a["n*"]
            if ns is None:
                continue
            Aset = set(A)
            pairs = []
            seen = set()
            unpaired = []
            for x in A:
                if x in seen:
                    continue
                y = ns - x
                if y in Aset and y != x:
                    pairs.append((min(x, y), max(x, y)))
                    seen.add(x)
                    seen.add(y)
                elif y == x:
                    pairs.append((x, x))
                    seen.add(x)
                else:
                    unpaired.append(x)
                    seen.add(x)
            f.write(f"- **N={a['N']}, n*={ns}**: {len(pairs)} reflection pairs "
                    f"{pairs}; unpaired = {unpaired}\n")
    print(f"Wrote {out_md}")


if __name__ == "__main__":
    main()
