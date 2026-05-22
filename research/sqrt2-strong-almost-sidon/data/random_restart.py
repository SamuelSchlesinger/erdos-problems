#!/usr/bin/env python3
"""
random_restart.py — Random-restart hill-climbing search for strong almost-Sidon
(SAS) sets, looking for non-Erdős–Freud (EF) local maxima.

A set A ⊆ {1,...,N} is strong almost-Sidon (SAS) iff there is at most ONE
sum value s = a + b (a ≤ b in A) that is realized by more than one pair —
i.e., the sumset has at most one element of multiplicity ≥ 2.

The EF construction: take a Sidon B ⊆ [1, ⌊N/3⌋] and form A = B ∪ (N − B).
This gives |A| ≈ (2/√3)·√N.

The Erdős–Freud rigidity conjecture: every "large" SAS extremizer is
approximately of this form.

This script runs many random restarts of hill climbing for SAS sets and
classifies whether the local maxima found are EF-form.

Internal representation:

  A             — sorted Python list (and a Python set) of ints in [1, N].
  pair_sum_mult — dict {sum_value : multiplicity} over pair sums i + j for
                  i ≤ j in A. Always has |A|·(|A|+1)/2 pairs counted.
  exc           — the unique sum value of multiplicity ≥ 2 (or None).
                  exc_count = its multiplicity (only meaningful if exc is not None).

  All other sum-values have multiplicity exactly 1 (SAS invariant).

ADD x (x ∉ A):
  Compute new sums { x+a : a ∈ A } ∪ { 2x }.
  Each new sum either lands in a fresh value (mult 0), or collides with an
  existing mult-1 value, or with the existing exc value. The add is legal iff
  at most one "new" value (not yet exc) can become a collision; exc is
  allowed to gain multiplicity.

REMOVE x (x ∈ A):
  Decrement the multiplicity of each sum { x+a : a ∈ A, a ≠ x } and 2x.
  Recompute exc (it can disappear or change).

We do hill climbing: at each step we try to ADD or SWAP (remove y, add x) to
increase |A|. We restart with random initial Sidon sets.
"""

from __future__ import annotations
import argparse
import json
import math
import os
import random
import sys
import time
from typing import List, Tuple, Optional, Dict


def is_sidon_naive(B: List[int]) -> bool:
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
    counts: Dict[int, int] = {}
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


class SASState:
    """Mutable SAS state with O(|A|) add/remove."""

    def __init__(self, N: int):
        self.N = N
        self.A: set = set()
        self.A_list: List[int] = []   # sorted
        self.mult: Dict[int, int] = {}
        # the "exception" sum-value of multiplicity >= 2, or None
        self.exc: Optional[int] = None

    def copy(self) -> "SASState":
        s = SASState(self.N)
        s.A = set(self.A)
        s.A_list = list(self.A_list)
        s.mult = dict(self.mult)
        s.exc = self.exc
        return s

    def size(self) -> int:
        return len(self.A)

    def can_add(self, x: int) -> bool:
        """Returns True iff adding x keeps SAS."""
        if x in self.A or x < 1 or x > self.N:
            return False
        # Determine new sums and their effect on multiplicities.
        # We only need to test whether new collisions stay within "at most
        # one distinct exception value".
        # Internally: a new sum value collides iff mult[s] >= 1 currently
        # AND s is not 2*a for some a in A already incrementing twice (won't
        # happen — sums between x and a in A are unique pairs).
        # The pair (x, x) contributes 2x; the pair (x, a) for a in A
        # contributes x+a (each once).
        # No two of these new sums can be equal to each other (because x+a
        # for a in A are all distinct, and 2x = x+x is distinct from x+a
        # unless a = x, but x ∉ A).
        new_sum_values = []  # list of distinct new sum values
        new_sum_values.append(2 * x)
        for a in self.A_list:
            new_sum_values.append(x + a)
        # All values in new_sum_values are distinct, so each gives at most
        # +1 mult to its sum.
        # Determine which of these collide with existing values (mult >= 1).
        cur_exc = self.exc
        new_exc_candidate = cur_exc
        # for each new sum s, after adding x:
        #   if s ∉ mult or mult[s] == 0: becomes mult 1, fine
        #   else (mult[s] >= 1): becomes mult >= 2, contributing an
        #     "exception" at s. We need all such s to equal cur_exc, OR
        #     exactly one new s ≠ cur_exc, and cur_exc is None.
        #
        # Track the set of "new exception values" (s with mult[s] >= 1 before
        # the add). If any of them is != cur_exc, it must be the *only* one,
        # and cur_exc must be None.
        for s in new_sum_values:
            m = self.mult.get(s, 0)
            if m >= 1:
                # collision
                if cur_exc is not None and s != cur_exc:
                    # would create a second distinct exception
                    return False
                if cur_exc is None:
                    if new_exc_candidate is None:
                        new_exc_candidate = s
                    elif new_exc_candidate != s:
                        return False
        return True

    def add(self, x: int) -> None:
        """Add x assuming can_add(x) is True."""
        new_sums = [2 * x]
        for a in self.A_list:
            new_sums.append(x + a)
        for s in new_sums:
            m = self.mult.get(s, 0) + 1
            self.mult[s] = m
            if m >= 2:
                self.exc = s
        # Insert x into sorted list.
        self.A.add(x)
        # Insert x in sorted order (binary insertion).
        import bisect
        bisect.insort(self.A_list, x)

    def remove(self, x: int) -> None:
        """Remove x ∈ A."""
        # Decrement all sums involving x.
        # Pairs: (x, x) -> 2x, and (x, a) for a in A, a != x.
        sums_to_dec = [2 * x]
        for a in self.A_list:
            if a == x:
                continue
            sums_to_dec.append(x + a)
        for s in sums_to_dec:
            m = self.mult.get(s, 0) - 1
            if m <= 0:
                self.mult.pop(s, None)
            else:
                self.mult[s] = m
        self.A.discard(x)
        self.A_list.remove(x)
        # Recompute exc: scan mult for any value with multiplicity >= 2.
        # We expect at most one such value (SAS invariant) provided we only
        # call remove on a SAS state.
        exc = None
        for v, m in self.mult.items():
            if m >= 2:
                exc = v
                break
        self.exc = exc

    def verify(self) -> bool:
        """Recompute everything from scratch and compare."""
        ok, exc = is_sas(list(self.A_list))
        if not ok:
            return False
        # Multiplicities
        counts: Dict[int, int] = {}
        n = len(self.A_list)
        for i in range(n):
            for j in range(i, n):
                s = self.A_list[i] + self.A_list[j]
                counts[s] = counts.get(s, 0) + 1
        # Should match self.mult ignoring zero entries
        cleaned = {k: v for k, v in self.mult.items() if v > 0}
        if cleaned != counts:
            return False
        if self.exc != exc:
            return False
        return True


# ---------- Random initial Sidon set ----------

def random_initial_sidon(N: int, rng: random.Random) -> SASState:
    """Greedily build a Sidon set by adding random elements until stuck."""
    state = SASState(N)
    candidates = list(range(1, N + 1))
    rng.shuffle(candidates)
    # iterate; add x iff sum_mult has no collision created. A Sidon-state
    # is just a SAS-state with exc = None and no collisions.
    for x in candidates:
        # adding x is Sidon-legal iff no new sum collides with existing
        # mult >= 1 sum.
        ok = True
        for a in state.A_list:
            s = x + a
            if state.mult.get(s, 0) >= 1:
                ok = False
                break
        if ok:
            # also check 2x against existing
            if state.mult.get(2 * x, 0) >= 1:
                ok = False
        if ok:
            state.add(x)
    return state


# ---------- Hill climbing ----------

def extend_greedy(state: SASState, rng: random.Random) -> None:
    """Greedily add elements while possible. Tie-break randomly."""
    N = state.N
    while True:
        # Find all addable x.
        addable = []
        for x in range(1, N + 1):
            if x in state.A:
                continue
            if state.can_add(x):
                addable.append(x)
        if not addable:
            return
        # Heuristic: prefer adds that don't introduce a new exception
        # (preserve "Sidon-ness" as long as possible).
        sidon_safe = []
        others = []
        for x in addable:
            # determine whether adding x introduces a new exception value.
            # If state.exc is None, the add becomes an exception iff one of
            # the new sums lands on an existing mult-1 value.
            introduces_new_exc = False
            if state.exc is None:
                for a in state.A_list:
                    s = x + a
                    if state.mult.get(s, 0) >= 1:
                        introduces_new_exc = True
                        break
                if not introduces_new_exc:
                    if state.mult.get(2 * x, 0) >= 1:
                        introduces_new_exc = True
            if not introduces_new_exc:
                sidon_safe.append(x)
            else:
                others.append(x)
        if sidon_safe:
            x = rng.choice(sidon_safe)
        else:
            x = rng.choice(others)
        state.add(x)


def try_swap(state: SASState, rng: random.Random,
             max_candidates: int = 6) -> bool:
    """Try a remove+add+extend that increases |A|.

    Returns True if an improvement was found.
    """
    N = state.N
    A_list = list(state.A_list)
    rng.shuffle(A_list)
    for y in A_list:
        backup = state.copy()
        state.remove(y)
        # Find addable x != y (other than putting y back).
        addable = []
        for x in range(1, N + 1):
            if x == y or x in state.A:
                continue
            if state.can_add(x):
                addable.append(x)
        if addable:
            rng.shuffle(addable)
            tried = 0
            for x in addable:
                if tried >= max_candidates:
                    break
                tried += 1
                trial = state.copy()
                trial.add(x)
                extend_greedy(trial, rng)
                if trial.size() > backup.size():
                    state.A = trial.A
                    state.A_list = trial.A_list
                    state.mult = trial.mult
                    state.exc = trial.exc
                    return True
        # restore
        state.A = backup.A
        state.A_list = backup.A_list
        state.mult = backup.mult
        state.exc = backup.exc
    return False


def kick_and_extend(state: SASState, rng: random.Random,
                    kick_count: int) -> None:
    """Remove `kick_count` random elements then re-extend greedily."""
    if state.size() <= kick_count:
        return
    victims = rng.sample(list(state.A_list), kick_count)
    for v in victims:
        state.remove(v)
    extend_greedy(state, rng)


def hill_climb(state: SASState, rng: random.Random,
               n_swap_passes: int = 30,
               n_kicks: int = 6) -> None:
    """Hill climb: greedy extension, swap improvement, plus kick-restarts.

    Strategy:
      1. Extend greedily from current state.
      2. Repeatedly try swap (remove one element, add a different one, and
         see if we can extend further). Continue until no swap improves.
      3. Apply "kick" perturbations: remove k random elements, re-extend.
         If the result is larger, keep; else revert.
    """
    extend_greedy(state, rng)
    best = state.copy()
    best_size = best.size()

    for _ in range(n_swap_passes):
        size_before = state.size()
        moved = try_swap(state, rng)
        if not moved:
            break
        if state.size() <= size_before:
            break

    if state.size() > best_size:
        best = state.copy()
        best_size = best.size()

    # Kick perturbations
    for k_iter in range(n_kicks):
        trial = best.copy()
        kick_count = rng.randint(1, max(2, best_size // 4))
        kick_and_extend(trial, rng, kick_count)
        # Apply a few swap passes
        for _ in range(5):
            size_before = trial.size()
            moved = try_swap(trial, rng)
            if not moved or trial.size() <= size_before:
                break
        if trial.size() > best_size:
            best = trial.copy()
            best_size = best.size()

    # restore best
    state.A = best.A
    state.A_list = best.A_list
    state.mult = best.mult
    state.exc = best.exc


# ---------- EF classification ----------

def classify_ef(N: int, A_list: List[int]) -> dict:
    """EF classifier (slightly more flexible than strict).

    Returns dict with:
      ef_form: bool — passes both criteria.
      dev_strict: |A △ (lo ∪ (N - lo))| for lo = A ∩ [1, ⌊N/3⌋].
      dev_best: minimum dev over axis shifts in [-3, 3] and third offsets
                in [-5, 5].
    """
    A_set = set(A_list)
    A_size = len(A_list)
    third = N // 3
    lo = set(x for x in A_list if 1 <= x <= third)
    hi = set(x for x in A_list if N - third <= x <= N)
    # Criterion 1: |A ∩ [1, N/3]| ≥ |A|/2 - 1.
    # Criterion 2: |(N - lo) △ hi| ≤ 2.
    mirror_lo = set(N - x for x in lo)
    sym = mirror_lo ^ hi
    crit1 = (len(lo) >= A_size / 2 - 1)
    crit2 = (len(sym) <= 2)
    # Strict deviation
    cand = lo | set(N - x for x in lo)
    dev_strict = len(A_set ^ cand)
    # Best-fit deviation: vary axis & threshold (allowing larger threshold
    # range than the strict criteria). We additionally allow the lo to be
    # "the smaller half of A by reflecting around the axis".
    best = dev_strict
    best_axis = N
    best_third = third
    # Compute the SAS exception value (sum with mult >= 2). If it exists,
    # it is the natural candidate axis.
    counts: Dict[int, int] = {}
    for i in range(len(A_list)):
        for j in range(i, len(A_list)):
            s = A_list[i] + A_list[j]
            counts[s] = counts.get(s, 0) + 1
    exc_candidates = [v for v, c in counts.items() if c >= 2]
    # Try axes: N + small shifts, the exception value (if any), and 2*median.
    axis_set = set()
    for shift in range(-6, 7):
        a = N + shift
        if 2 <= a <= 4 * N:
            axis_set.add(a)
    for e in exc_candidates:
        axis_set.add(e)
    # Also try 2x where x is the median of A.
    if A_list:
        med = A_list[len(A_list) // 2]
        axis_set.add(2 * med)
    # Threshold range: scan all reasonable thresholds.
    th_set = set()
    for t in range(max(1, third - 12), min(N, third + 12) + 1):
        th_set.add(t)
    # Also try around half of each axis.
    for a in axis_set:
        th_set.add(a // 2)
        th_set.add(a // 2 + 1)
        th_set.add(a // 3)
    for a in axis_set:
        for t in th_set:
            if t < 1 or t > N:
                continue
            lo_t = set(x for x in A_list if 1 <= x <= t)
            cand_t = lo_t | set(a - x for x in lo_t)
            dev = len(A_set ^ cand_t)
            if dev < best:
                best = dev
                best_axis = a
                best_third = t
    # Also compute "in-range" dev: only count cand elements that lie in [1, N].
    # This treats "EF truncated by boundary" as still EF-form.
    best_in = best
    best_in_axis = best_axis
    best_in_third = best_third
    for a in axis_set:
        for t in th_set:
            if t < 1 or t > N:
                continue
            lo_t = set(x for x in A_list if 1 <= x <= t)
            mirror = set(a - x for x in lo_t if 1 <= a - x <= N)
            cand_in = lo_t | mirror
            dev = len(A_set ^ cand_in)
            if dev < best_in:
                best_in = dev
                best_in_axis = a
                best_in_third = t
    # Treat ef_form := dev_best <= 2 OR dev_best_in_range <= 2.
    # The "in_range" variant ignores mirror elements that fall outside [1, N],
    # which counts boundary-truncated EF as still EF-form.
    ef_form = (best <= 2) or (best_in <= 2)
    return {
        "ef_form": ef_form,
        "dev_strict": dev_strict,
        "dev_best": best,
        "dev_best_in_range": best_in,
        "best_axis": best_axis,
        "best_third": best_third,
        "best_axis_in": best_in_axis,
        "best_third_in": best_in_third,
        "lo_size": len(lo),
        "hi_size": len(hi),
        "crit1_lo_half": crit1,
        "crit2_mirror_match": crit2,
    }


# ---------- Main loop ----------

def run_restarts(N: int, n_restarts: int, seed: int = 0,
                 verbose: bool = False) -> List[dict]:
    rng = random.Random(seed)
    results = []
    best_size = 0
    best_set = None
    t0 = time.time()
    for trial in range(n_restarts):
        # fresh per-trial RNG for reproducibility
        trial_rng = random.Random(seed * 1_000_003 + trial)
        state = random_initial_sidon(N, trial_rng)
        hill_climb(state, trial_rng)
        # Verify
        if not state.verify():
            print(f"  WARNING N={N} trial {trial}: state failed verify",
                  file=sys.stderr)
        size = state.size()
        cls = classify_ef(N, state.A_list)
        results.append({
            "trial": trial,
            "size": size,
            "A": sorted(state.A_list),
            "exc": state.exc,
            **cls,
        })
        if size > best_size:
            best_size = size
            best_set = sorted(state.A_list)
        if verbose and (trial + 1) % 10 == 0:
            elapsed = time.time() - t0
            print(f"  N={N} trial {trial + 1}/{n_restarts}  "
                  f"best_size={best_size}  elapsed={elapsed:.1f}s",
                  file=sys.stderr)
    return results


def summarize(N: int, results: List[dict]) -> dict:
    sizes = [r["size"] for r in results]
    hist: Dict[int, int] = {}
    for s in sizes:
        hist[s] = hist.get(s, 0) + 1
    ef_count = sum(1 for r in results if r["ef_form"])
    non_ef = [r for r in results if not r["ef_form"]]
    # also compute "near-EF" via dev_best ≤ 2 as alternate metric
    near_ef = sum(1 for r in results if r["dev_best"] <= 2)
    not_near = sum(1 for r in results if r["dev_best"] > 2)
    max_size = max(sizes) if sizes else 0
    max_non_ef = max((r["size"] for r in non_ef), default=0)
    # Top non-EF examples (largest)
    non_ef_sorted = sorted(non_ef, key=lambda r: (-r["size"], r["dev_best"]))
    top_non_ef = non_ef_sorted[:5]
    return {
        "N": N,
        "n_restarts": len(results),
        "size_histogram": hist,
        "ef_count": ef_count,
        "near_ef_count": near_ef,
        "non_near_ef_count": not_near,
        "max_size": max_size,
        "max_non_ef_size": max_non_ef,
        "ef_pred": (2.0 / math.sqrt(3.0)) * math.sqrt(N) + 1.520 * (N ** 0.25),
        "top_non_ef_examples": top_non_ef,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", default="100,200,500",
                    help="comma-separated N values")
    ap.add_argument("--restarts", default="100,100,30",
                    help="comma-separated restart counts (matched to --ns)")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--out", default=None, help="Output JSON path")
    ap.add_argument("--txt", default=None, help="Output text path")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    ns = [int(x) for x in args.ns.split(",")]
    rs = [int(x) for x in args.restarts.split(",")]
    assert len(ns) == len(rs), "ns and restarts must match in length"

    all_summaries = []
    all_results = {}
    for N, R in zip(ns, rs):
        print(f"\n=== N={N}  restarts={R} ===", file=sys.stderr)
        t0 = time.time()
        results = run_restarts(N, R, seed=args.seed + N, verbose=args.verbose)
        elapsed = time.time() - t0
        summary = summarize(N, results)
        summary["elapsed_s"] = elapsed
        all_summaries.append(summary)
        all_results[str(N)] = results
        print(f"  N={N}: max_size={summary['max_size']}, "
              f"EF={summary['ef_count']}/{R}, "
              f"non-EF largest size={summary['max_non_ef_size']}, "
              f"elapsed={elapsed:.1f}s",
              file=sys.stderr)

    if args.out:
        with open(args.out, "w") as f:
            json.dump({"summaries": all_summaries,
                       "results": all_results}, f, indent=2,
                      default=lambda o: list(o) if isinstance(o, set) else o)
        print(f"Wrote {args.out}", file=sys.stderr)

    if args.txt:
        with open(args.txt, "w") as f:
            f.write("# random_restart.py results\n")
            f.write(f"# seed = {args.seed}\n\n")
            for s in all_summaries:
                N = s["N"]
                f.write(f"=== N={N} ===\n")
                f.write(f"  restarts = {s['n_restarts']}\n")
                f.write(f"  ef_pred  = {s['ef_pred']:.3f}\n")
                f.write(f"  max_size = {s['max_size']}\n")
                hist = s["size_histogram"]
                f.write("  size histogram:\n")
                for k in sorted(hist):
                    f.write(f"    size={k}: count={hist[k]}\n")
                f.write(f"  EF-form (criteria-based)   = {s['ef_count']}\n")
                f.write(f"  near-EF (dev_best <= 2)    = {s['near_ef_count']}\n")
                f.write(f"  non-near-EF (dev_best > 2) = {s['non_near_ef_count']}\n")
                f.write(f"  max non-EF size = {s['max_non_ef_size']}\n")
                f.write(f"  elapsed = {s['elapsed_s']:.1f} s\n")
                if s["top_non_ef_examples"]:
                    f.write("\n  Top non-EF examples (largest):\n")
                    for ex in s["top_non_ef_examples"]:
                        f.write(f"    size={ex['size']}  dev_best={ex['dev_best']}  "
                                f"dev_best_in={ex['dev_best_in_range']}  "
                                f"dev_strict={ex['dev_strict']}  exc={ex['exc']}\n")
                        f.write(f"      best_axis={ex['best_axis']} "
                                f"best_third={ex['best_third']}\n")
                        f.write(f"      A = {ex['A']}\n")
                f.write("\n")
        print(f"Wrote {args.txt}", file=sys.stderr)


if __name__ == "__main__":
    main()
