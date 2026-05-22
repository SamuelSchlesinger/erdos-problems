#!/usr/bin/env python3
"""
analyze_extended.py — post-process extend_search.c output.

Reads:
  data/par_results/n_*.txt        (per-N parallel run results)
  data/A389182.txt                (canonical OEIS values N=1..69)

Produces:
  data/A389182-extended.txt       (b-file-format extended sequence)
  data/extremizers.txt            (per-N extremizer + EF classification)

Also prints a summary table to stdout.

Classifies each extremizer A by examining whether
   A = B ∪ (a - B) ∪ E
for some Sidon B in [1, threshold], reflection axis a near N, and a small
set E of "extras". Specifically we report
   dev_strict := |A △ (lo ∪ (N - lo))| with lo = A ∩ [1, ⌊N/3⌋]
   dev_best   := min over (axis_shift ∈ {-2..+2}, third_offset ∈ {-3..+3})
                 of |A △ (lo ∪ (a - lo))|.
A perfect EF means dev_best = 0; the OEIS-tracking minor deviation (dev=±1)
shows as dev_best = 1; "EF with one extra pair" (which we observe at
N=70..78) shows as dev_best = 2.
"""

from __future__ import annotations
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def is_sidon(B):
    sums = set()
    for i in range(len(B)):
        for j in range(i, len(B)):
            s = B[i] + B[j]
            if s in sums:
                return False
            sums.add(s)
    return True


def is_sas(A):
    counts = {}
    A_sorted = sorted(A)
    for i in range(len(A_sorted)):
        for j in range(i, len(A_sorted)):
            s = A_sorted[i] + A_sorted[j]
            counts[s] = counts.get(s, 0) + 1
    excs = [v for v, c in counts.items() if c >= 2]
    if len(excs) == 0:
        return True, None
    if len(excs) == 1:
        return True, excs[0]
    return False, None


def parse_c_line(line: str):
    line = line.strip()
    if not line or line.startswith("#"):
        return None
    parts = line.split("#", 1)
    head = parts[0].strip()
    bits = head.split()
    if len(bits) < 2:
        return None
    try:
        N = int(bits[0]); size = int(bits[1])
    except ValueError:
        return None
    A = []
    if len(parts) > 1:
        tail = parts[1]
        idx = tail.find("set=")
        if idx != -1:
            seq = tail[idx + 4:].strip()
            A = [int(x) for x in seq.split(",") if x.strip()]
    return N, size, A


def classify_ef(N, A):
    third = N // 3
    A_set = set(A)
    lo = sorted(x for x in A if 1 <= x <= third)
    hi = sorted(x for x in A if N - third <= x <= N)
    mid = sorted(x for x in A if third < x < N - third)
    cand = set(lo) | {N - x for x in lo}
    dev = A_set ^ cand
    lo_sidon_flag = is_sidon(lo) if lo else True
    return {
        "lo": lo, "hi": hi, "mid": mid,
        "deviation": sorted(dev),
        "deviation_count": len(dev),
        "lo_sidon": lo_sidon_flag,
        "ef_strict": (len(dev) == 0) and lo_sidon_flag,
    }


def try_alternate_ef_form(N, A):
    """Min over (axis_shift, third_offset) of deviation count."""
    best = None
    A_set = set(A)
    for axis_shift in range(-3, 4):
        a_axis = N + axis_shift
        for third_offset in range(-5, 6):
            third = N // 3 + third_offset
            if third < 0:
                continue
            lo = sorted(x for x in A if 1 <= x <= third)
            cand = set(lo) | {a_axis - x for x in lo if 1 <= a_axis - x <= N}
            dev = A_set ^ cand
            sidon = is_sidon(lo) if lo else True
            entry = (len(dev), axis_shift, third_offset, sorted(dev), sidon, lo, a_axis)
            if best is None or entry[:1] < best[:1]:
                best = entry
    return best


def extras_pair_to_axis(A, axis):
    """If exactly 2 elements of A don't fit the form lo ∪ (axis - lo) for the
    canonical lo, check whether those 2 sum to axis."""
    # Helper used in interpretation: if dev_best = 2 and the 2 extras
    # sum to `axis`, that's the "EF + colliding pair" pattern.
    pass


def ef_asymptotic(N):
    return (2.0 / math.sqrt(3.0)) * math.sqrt(N) + 1.520 * (N ** 0.25)


def collect_rows():
    par_dir = os.path.join(HERE, "par_results")
    rows = []
    if os.path.isdir(par_dir):
        for fn in sorted(os.listdir(par_dir)):
            if not fn.startswith("n_") or not fn.endswith(".txt"):
                continue
            with open(os.path.join(par_dir, fn)) as f:
                for line in f:
                    parsed = parse_c_line(line)
                    if parsed:
                        rows.append(parsed)
    rows.sort(key=lambda r: r[0])
    return rows


def main():
    existing = {}
    with open(os.path.join(HERE, "A389182.txt")) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) >= 2:
                existing[int(parts[0])] = int(parts[1])

    rows = collect_rows()
    print(f"Read {len(rows)} extended rows.")

    # Verify each extremizer.
    print("\nVerifying extremizers...")
    for N, size, A in rows:
        if len(A) != size:
            print(f"  BAD: N={N}, claimed size={size}, |A|={len(A)}")
            continue
        ok, exc = is_sas(A)
        if not ok:
            print(f"  BAD: N={N} is not SAS")
    print("Done.")

    # Build extended b-file.
    all_pts = dict(existing)
    for N, size, _ in rows:
        all_pts[N] = size
    ext_path = os.path.join(HERE, "A389182-extended.txt")
    with open(ext_path, "w") as f:
        f.write("# A389182 extended via extend_search.c\n")
        f.write("# columns: N f(N)\n")
        for N in sorted(all_pts):
            f.write(f"{N} {all_pts[N]}\n")
    print(f"Wrote {ext_path}")

    # Per-N extremizer file.
    extrm_path = os.path.join(HERE, "extremizers.txt")
    with open(extrm_path, "w") as f:
        f.write("# Extremizing SAS sets for N = 70..78.\n")
        f.write("# Columns:\n")
        f.write("#   N, f(N), EF_pred, ratio, exc\n")
        f.write("#   ef_strict = whether A = lo ∪ (N-lo) exactly with lo = A ∩ [1, ⌊N/3⌋]\n")
        f.write("#   dev_strict = |A △ (lo ∪ (N-lo))|\n")
        f.write("#   dev_best = min over (axis_shift, third_offset) of deviation\n")
        f.write("#\n")
        f.write("# A 'dev_best = 0' or '= 1' is a strict EF-form extremizer.\n")
        f.write("# A 'dev_best = 2' is 'EF + one extra colliding pair' (still EF-like).\n\n")

        for N, size, A in rows:
            ok, exc = is_sas(A)
            cls = classify_ef(N, A)
            best = try_alternate_ef_form(N, A)
            pred = ef_asymptotic(N)
            ratio = size / pred
            # check if the 2 dev elements (if any) sum to the axis
            dev_pair_sums_to_axis = "n/a"
            if best[0] == 2:
                dev = best[3]
                a_axis = N + best[1]
                if len(dev) == 2 and sum(dev) == a_axis:
                    dev_pair_sums_to_axis = "yes"
                else:
                    dev_pair_sums_to_axis = "no"
            f.write(
                f"N={N:3d}  f={size:2d}  pred={pred:7.3f}  ratio={ratio:.4f}  "
                f"exc={exc}  "
                f"ef_strict={int(cls['ef_strict'])}  "
                f"dev_strict={cls['deviation_count']:2d}  "
                f"dev_best={best[0]:2d} (axis_shift={best[1]:+d}, third_off={best[2]:+d})  "
                f"dev_pair_sums_to_axis={dev_pair_sums_to_axis}\n"
            )
            f.write(f"   A   = {A}\n")
            f.write(f"   lo  = {cls['lo']}  (third = {N//3})\n")
            f.write(f"   hi  = {cls['hi']}\n")
            f.write(f"   mid = {cls['mid']}\n")
            f.write(f"   dev_strict_set = {cls['deviation']}\n")
            f.write(f"   dev_best_set   = {best[3]}  (axis={N + best[1]}, threshold={N//3 + best[2]})\n")
            f.write(f"   best lo = {best[5]} (length {len(best[5])}), lo_sidon={int(best[4])}\n")
            f.write("\n")
    print(f"Wrote {extrm_path}")

    # Print summary.
    print()
    print("Summary table (N=70..):")
    print(f"{'N':>4} {'f(N)':>5} {'pred':>7} {'ratio':>7} {'exc':>5} {'ef_strict':>10} "
          f"{'dev_strict':>11} {'dev_best':>9} {'pair_sums?':>10}")
    for N, size, A in rows:
        ok, exc = is_sas(A)
        cls = classify_ef(N, A)
        best = try_alternate_ef_form(N, A)
        pred = ef_asymptotic(N)
        ratio = size / pred
        pair_ok = "n/a"
        if best[0] == 2:
            dev = best[3]
            a_axis = N + best[1]
            if len(dev) == 2 and sum(dev) == a_axis:
                pair_ok = "yes"
            else:
                pair_ok = "no"
        print(f"{N:>4} {size:>5} {pred:>7.3f} {ratio:>7.4f} {str(exc):>5} "
              f"{int(cls['ef_strict']):>10} {cls['deviation_count']:>11} {best[0]:>9} {pair_ok:>10}")


if __name__ == "__main__":
    sys.exit(main() or 0)
