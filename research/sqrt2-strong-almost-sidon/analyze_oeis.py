#!/usr/bin/env python3
"""
Analyze OEIS A389182 (strong almost-Sidon extremizers) to estimate the
asymptotic constant c in f(N) = c·√N + o(√N).

Key questions:
- Is the data consistent with c → 2/√3 ≈ 1.155 (Erdős–Freud lower-bound construction)?
- Is the data consistent with c → √2 ≈ 1.414 (DesmondWeisenberg / our upper bound)?
- Or does it suggest an intermediate constant?

Data: /tmp/A389182.txt
"""
import math
from pathlib import Path


def load_data(path: str) -> list[tuple[int, int]]:
    data = []
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        n_str, val_str = line.split()
        data.append((int(n_str), int(val_str)))
    return data


def main() -> None:
    # Try local data first, then /tmp fallback.
    import os
    here = Path(__file__).parent
    candidates = [here / "data" / "A389182.txt", Path("/tmp/A389182.txt")]
    path = next((p for p in candidates if p.exists()), None)
    if path is None:
        raise FileNotFoundError("A389182.txt not found in data/ or /tmp/")
    data = load_data(str(path))
    print(f"Loaded {len(data)} data points (N from {data[0][0]} to {data[-1][0]}).")

    sqrt2 = math.sqrt(2)
    two_over_sqrt3 = 2 / math.sqrt(3)

    print()
    print(f"Reference constants:")
    print(f"  2/√3 (Erdős–Freud lower bound)     = {two_over_sqrt3:.4f}")
    print(f"  √2  (DesmondWeisenberg upper bound) = {sqrt2:.4f}")
    print()

    print("Ratio f(N) / √N at selected N:")
    print(f"  {'N':>5} {'f(N)':>5} {'f(N)/√N':>10}")
    for n, fn in data:
        if n in {1, 4, 9, 16, 25, 36, 49, 64, 69} or n == data[-1][0]:
            ratio = fn / math.sqrt(n)
            print(f"  {n:>5} {fn:>5} {ratio:>10.4f}")
    print()

    print("Jumps (N where f(N) > f(N-1)):")
    print(f"  {'k':>4} {'N(k)':>5} {'k/√N(k)':>9} {'(k-1)/√(N(k)-1)':>16}")
    prev = 0
    for n, fn in data:
        if fn > prev:
            ratio = fn / math.sqrt(n)
            prev_ratio = (fn - 1) / math.sqrt(n - 1) if n > 1 else float("inf")
            print(f"  {fn:>4} {n:>5} {ratio:>9.4f} {prev_ratio:>16.4f}")
            prev = fn
    print()

    # Linear regression: f(N) = a·√N + b
    # Use the JUMP points only (cleanest signal — these are where f saturates).
    jumps = []
    prev = 0
    for n, fn in data:
        if fn > prev:
            jumps.append((n, fn))
            prev = fn

    # Regress f vs √N
    xs = [math.sqrt(n) for n, _ in jumps]
    ys = [float(fn) for _, fn in jumps]
    n_pts = len(xs)
    mean_x = sum(xs) / n_pts
    mean_y = sum(ys) / n_pts
    num = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    den = sum((x - mean_x) ** 2 for x in xs)
    slope = num / den
    intercept = mean_y - slope * mean_x

    # R² for the linear fit
    ss_res = sum((y - (slope * x + intercept)) ** 2 for x, y in zip(xs, ys))
    ss_tot = sum((y - mean_y) ** 2 for y in ys)
    r_sq = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")

    print("Linear regression f = a·√N + b on jump points only:")
    print(f"  slope (a)     = {slope:.4f}")
    print(f"  intercept (b) = {intercept:.4f}")
    print(f"  R²            = {r_sq:.6f}")
    print()

    # Regress all data
    xs = [math.sqrt(n) for n, _ in data]
    ys = [float(fn) for _, fn in data]
    n_pts = len(xs)
    mean_x = sum(xs) / n_pts
    mean_y = sum(ys) / n_pts
    num = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    den = sum((x - mean_x) ** 2 for x in xs)
    slope_all = num / den
    intercept_all = mean_y - slope_all * mean_x
    ss_res = sum((y - (slope_all * x + intercept_all)) ** 2 for x, y in zip(xs, ys))
    ss_tot = sum((y - mean_y) ** 2 for y in ys)
    r_sq_all = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")

    print("Linear regression f = a·√N + b on ALL data:")
    print(f"  slope (a)     = {slope_all:.4f}")
    print(f"  intercept (b) = {intercept_all:.4f}")
    print(f"  R²            = {r_sq_all:.6f}")
    print()

    # Try f = a·√N (no intercept)
    num = sum(x * y for x, y in zip(xs, ys))
    den = sum(x * x for x in xs)
    slope_only = num / den
    ss_res = sum((y - slope_only * x) ** 2 for x, y in zip(xs, ys))
    r_sq_only = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    print("Forced-zero-intercept regression f = a·√N on ALL data:")
    print(f"  slope (a) = {slope_only:.4f}")
    print(f"  R²        = {r_sq_only:.6f}")
    print()

    # Where does the slope sit relative to 2/√3 and √2?
    print("Interpretation:")
    print(f"  Best estimate of asymptotic constant (slope, all-data, no intercept):")
    print(f"    {slope_only:.4f}")
    print(f"  Compare to:")
    print(f"    2/√3 ≈ {two_over_sqrt3:.4f}  (Erdős–Freud LB; conjecture)")
    print(f"    √2   ≈ {sqrt2:.4f}            (DesmondWeisenberg UB; our work)")
    diff_lb = slope_only - two_over_sqrt3
    diff_ub = sqrt2 - slope_only
    print(f"  Excess over LB: {diff_lb:+.4f}")
    print(f"  Gap to UB:      {diff_ub:+.4f}")
    print()

    # Last-50 vs last-25 trend (if data is dense enough)
    if len(data) >= 50:
        recent_xs = [math.sqrt(n) for n, _ in data[-25:]]
        recent_ys = [float(fn) for _, fn in data[-25:]]
        num = sum(x * y for x, y in zip(recent_xs, recent_ys))
        den = sum(x * x for x in recent_xs)
        slope_recent = num / den
        print(f"  Forced-zero-intercept regression on LAST 25 points: {slope_recent:.4f}")
        print(f"  (If this is smaller than the all-data slope, the constant may be")
        print(f"   converging toward the LB. If larger, the constant trends up.)")
    print()

    # Test the Erdős–Freud construction hypothesis:
    # f(N) ≈ 2·|B(⌊N/3⌋)| where B(M) is the max Sidon set in [1,M].
    # |B(M)| sequence: OEIS A005282. Hardcode small values.
    B_max = [
        # M=0: 0 (empty); M=1..30 from A005282
        0, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5,
        6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8,
    ]
    print("Erdős–Freud construction hypothesis: f(N) ≈ 2·|B(⌊N/3⌋)|")
    print(f"  {'N':>5} {'N/3':>5} {'2·B(N/3)':>10} {'f(N)':>5} {'gap':>4}")
    for n, fn in data:
        m = n // 3
        if m < len(B_max):
            ef = 2 * B_max[m]
            gap = fn - ef
            if n in {3, 6, 9, 12, 15, 21, 24, 27, 30, 36, 45, 48, 51, 54, 57, 60, 63, 66, 69}:
                print(f"  {n:>5} {m:>5} {ef:>10} {fn:>5} {gap:>+4}")
    print()
    print("If the gap (f(N) − 2·B(N/3)) is consistently small (0 or 1), the")
    print("Erdős–Freud reflection construction is essentially asymptotically tight,")
    print("strongly supporting the conjectured constant 2/√3.")
    print()

    # If f(N) = c·√N + d·N^{1/4}, fit c and d.
    # Using all data, OLS with two features.
    n_pts = len(data)
    sum_x1 = sum(math.sqrt(n) for n, _ in data)
    sum_x2 = sum(n ** 0.25 for n, _ in data)
    sum_x1_sq = sum(n for n, _ in data)
    sum_x2_sq = sum(n ** 0.5 for n, _ in data)
    sum_x1x2 = sum(math.sqrt(n) * n ** 0.25 for n, _ in data)
    sum_y = sum(float(fn) for _, fn in data)
    sum_x1y = sum(math.sqrt(n) * fn for n, fn in data)
    sum_x2y = sum((n ** 0.25) * fn for n, fn in data)
    # Normal equations:
    # [x1·x1  x1·x2] [c]   [x1·y]
    # [x1·x2  x2·x2] [d] = [x2·y]
    # (No intercept term.)
    a11, a12, a22 = sum_x1_sq, sum_x1x2, sum_x2_sq
    b1, b2 = sum_x1y, sum_x2y
    det = a11 * a22 - a12 * a12
    if det != 0:
        c = (b1 * a22 - b2 * a12) / det
        d = (a11 * b2 - a12 * b1) / det
        print(f"Two-parameter fit f = c·√N + d·N^{{1/4}}:")
        print(f"  c = {c:.4f}")
        print(f"  d = {d:.4f}")
        ss_res = sum((fn - c * math.sqrt(n) - d * n ** 0.25) ** 2 for n, fn in data)
        ss_tot = sum((fn - sum_y / n_pts) ** 2 for _, fn in data)
        r_sq = 1 - ss_res / ss_tot
        print(f"  R² = {r_sq:.6f}")
        # Predict at large N
        for N_pred in [100, 1000, 10000, 100000, 1000000]:
            pred = c * math.sqrt(N_pred) + d * N_pred ** 0.25
            ratio = pred / math.sqrt(N_pred)
            print(f"  predict N={N_pred:>7}: f ≈ {pred:>10.2f}, ratio f/√N = {ratio:.4f}")
    print()
    print("If c ≈ 2/√3 in the two-parameter fit, the EF construction is")
    print("asymptotically tight and the conjecture is correct.")


if __name__ == "__main__":
    main()
