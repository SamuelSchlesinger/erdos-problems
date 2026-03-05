#!/usr/bin/env python3
"""
Gadget Mining for Unit Fraction Packing Bounds

Searches for high-τ multiplier sets (gadgets) that can be used in packing
bound proofs for unit fraction density problems (#302 triples, #327 pairs).

Usage:
  python3 scripts/gadget_mine.py --triples --max 60
  python3 scripts/gadget_mine.py --pairs --max 30
  python3 scripts/gadget_mine.py --triples --max 100 --top 20
  python3 scripts/gadget_mine.py --triples --max 120 --max-families 4 --connected-only
"""

import argparse
import json
import random
import sys
from fractions import Fraction
from itertools import combinations
from math import gcd
from pathlib import Path

# Try z3, fall back to brute force
try:
    from z3 import Int, Optimize, Sum, sat
    HAS_Z3 = True
except ImportError:
    HAS_Z3 = False


def find_triples(M):
    """Find all (a,b,c) with 1 ≤ a < b < c ≤ M satisfying 1/a = 1/b + 1/c,
    i.e. a*(b+c) = b*c, i.e. (b-a)*(c-a) = a²."""
    triples = []
    for a in range(1, M + 1):
        a2 = a * a
        # (b-a)*(c-a) = a², so enumerate divisors of a²
        for d1 in range(1, a2 + 1):
            if a2 % d1 != 0:
                continue
            d2 = a2 // d1
            b = a + d1
            c = a + d2
            if b < c and c <= M:
                triples.append((a, b, c))
    return triples


def find_pairs(M):
    """Find all (a,b) with 1 ≤ a < b ≤ M satisfying 1/a = 1/b + 1/c for some c,
    i.e. (a+b) | (a*b)."""
    pairs = []
    for a in range(1, M + 1):
        for b in range(a + 1, M + 1):
            if (a * b) % (a + b) == 0:
                pairs.append((a, b))
    return pairs


def hitting_number_z3(elements, hyperedges):
    """Compute τ(H) = minimum hitting set size via z3 ILP."""
    if not HAS_Z3:
        return hitting_number_brute(elements, hyperedges)
    opt = Optimize()
    x = {e: Int(f"x_{e}") for e in elements}
    for e in elements:
        opt.add(x[e] >= 0, x[e] <= 1)
    for edge in hyperedges:
        opt.add(Sum([x[e] for e in edge if e in x]) >= 1)
    opt.minimize(Sum([x[e] for e in elements]))
    if opt.check() == sat:
        m = opt.model()
        return sum(1 for e in elements if m[x[e]].as_long() >= 1)
    return len(elements)  # fallback


def hitting_number_brute(elements, hyperedges):
    """Compute τ(H) by brute force (small sets only)."""
    elts = list(elements)
    for k in range(1, len(elts) + 1):
        for subset in combinations(elts, k):
            s = set(subset)
            if all(any(e in s for e in edge) for edge in hyperedges):
                return k
    return len(elts)


def hitting_number(elements, hyperedges):
    """Compute minimum hitting set size."""
    if HAS_Z3:
        return hitting_number_z3(elements, hyperedges)
    return hitting_number_brute(elements, hyperedges)


def padic_val(n, p):
    """Compute v_p(n)."""
    if n == 0:
        return float('inf')
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v


def signature(c, primes_mods):
    """Compute signature tuple (v_p(c) mod k, ...) for given (p, k) pairs."""
    return tuple(padic_val(c, p) % k for p, k in primes_mods)


def signature_analysis(multipliers, primes_mods=None):
    """Check if a signature function is injective on multipliers.
    Try common (p, k) combinations if none specified."""
    if primes_mods is None:
        # Try all reasonable combinations
        candidates = [
            [(2, 2)],
            [(3, 2)],
            [(5, 2)],
            [(2, 2), (3, 2)],
            [(2, 2), (5, 2)],
            [(3, 2), (5, 2)],
            [(2, 3)],
            [(2, 3), (3, 2)],
            [(2, 4)],
            [(2, 4), (5, 2)],
            [(2, 2), (3, 2), (5, 2)],
            [(2, 3), (3, 2), (5, 2)],
            [(2, 4), (3, 2), (5, 2)],
            [(7, 2)],
            [(2, 2), (7, 2)],
            [(2, 2), (3, 2), (7, 2)],
        ]
    else:
        candidates = [primes_mods]

    results = []
    for pm in candidates:
        sigs = {}
        for c in multipliers:
            s = signature(c, pm)
            sigs[c] = s
        vals = list(sigs.values())
        is_injective = len(vals) == len(set(vals))
        results.append((pm, sigs, is_injective))
    return results


def gadget_from_triple(triple):
    """Extract multiplier set from a triple (a,b,c) = (m*d, m2*d, m3*d).
    Returns (gcd, multipliers) where triple_i = multiplier_i * gcd."""
    a, b, c = triple
    g = gcd(gcd(a, b), c)
    return g, (a // g, b // g, c // g)


def families_are_disjoint(families):
    """Return True if no element appears in two different families."""
    seen = set()
    for fam in families:
        s = set(fam)
        if seen & s:
            return False
        seen |= s
    return True


def families_overlap_connected(families):
    """Return True if family-overlap graph is connected.

    Vertices are family hyperedges; edges join families with nonempty intersection.
    """
    if len(families) <= 1:
        return True
    fam_sets = [set(f) for f in families]
    stack = [0]
    seen = {0}
    while stack:
        i = stack.pop()
        for j in range(len(fam_sets)):
            if j in seen:
                continue
            if fam_sets[i] & fam_sets[j]:
                seen.add(j)
                stack.append(j)
    return len(seen) == len(fam_sets)


def enumerate_gadgets(mult_list, max_families, disjoint_only=False, connected_only=False):
    """Enumerate gadget candidates by combining base families."""
    gadgets = []
    upper = min(max_families, len(mult_list))
    for r in range(2, upper + 1):
        for fams in combinations(mult_list, r):
            if disjoint_only and not families_are_disjoint(fams):
                continue
            if connected_only and not families_overlap_connected(fams):
                continue
            union_elts = set().union(*(set(f) for f in fams))
            tau = hitting_number(union_elts, fams)
            ratio = tau / len(union_elts)
            gadgets.append((union_elts, list(fams), tau, ratio, fams))
    gadgets.sort(key=lambda x: (-x[3], -x[2], len(x[0])))
    return gadgets


def search_triple_gadgets(M, top_n=10, max_families=3, disjoint_only=False, connected_only=False):
    """Search for high-τ/|G| gadget configurations from triples."""
    triples = find_triples(M)
    print(f"Found {len(triples)} triples with max element ≤ {M}")
    print()

    # Group triples by their multiplier set
    # Each triple (a,b,c) with gcd g gives multipliers (a/g, b/g, c/g)
    multiplier_triples = {}
    for t in triples:
        g, mults = gadget_from_triple(t)
        if mults not in multiplier_triples:
            multiplier_triples[mults] = []
        multiplier_triples[mults].append((g, t))

    print(f"Unique multiplier patterns: {len(multiplier_triples)}")
    print()

    # For each multiplier set, the elements of the gadget are the multipliers
    # The hyperedge is the full triple (all 3 must be hit)
    # τ = 1 always for a single triple (just pick any element)
    # Interest: unions of triples sharing elements

    print("=== Individual Triple Families ===")
    print(f"{'Multipliers':<25} {'|G|':>4} {'τ':>3} {'τ/|G|':>8} {'#params':>8}")
    print("-" * 55)

    for mults, params in sorted(multiplier_triples.items()):
        elements = set(mults)
        tau = 1  # single triple always has τ=1
        ratio = tau / len(elements)
        print(f"{str(mults):<25} {len(elements):>4} {tau:>3} {ratio:>8.4f} {len(params):>8}")

    print()
    print("=== Multi-Triple Gadgets ===")
    mode_parts = [f"up to {max_families} families"]
    if disjoint_only:
        mode_parts.append("disjoint only")
    if connected_only:
        mode_parts.append("overlap-connected only")
    print("Mode:", ", ".join(mode_parts))
    print()

    mult_list = sorted(multiplier_triples.keys())
    gadgets = enumerate_gadgets(
        mult_list,
        max_families=max_families,
        disjoint_only=disjoint_only,
        connected_only=connected_only,
    )

    print(f"{'Gadget elements':<40} {'|G|':>4} {'τ':>3} {'τ/|G|':>8} {'Families'}")
    print("-" * 85)
    seen = set()
    count = 0
    for elts, hyp, tau, ratio, fams in gadgets:
        key = frozenset(elts)
        if key in seen:
            continue
        seen.add(key)
        elts_str = str(sorted(elts))
        fams_str = " + ".join(str(f) for f in fams)
        print(f"{elts_str:<40} {len(elts):>4} {tau:>3} {ratio:>8.4f} {fams_str}")
        count += 1
        if count >= top_n:
            break

    # Signature analysis for top gadgets
    print()
    print("=== Signature Analysis for Top Gadgets ===")
    print()
    seen = set()
    count = 0
    for elts, hyp, tau, ratio, fams in gadgets:
        key = frozenset(elts)
        if key in seen:
            continue
        seen.add(key)
        if ratio < 0.3:  # only analyze interesting ones
            continue
        mults = sorted(elts)
        print(f"Gadget {mults} (τ/|G| = {ratio:.4f}):")
        results = signature_analysis(mults)
        for pm, sigs, inj in results:
            if inj:
                pm_str = ", ".join(f"v_{p} mod {k}" for p, k in pm)
                print(f"  INJECTIVE via ({pm_str}):")
                for c, s in sorted(sigs.items()):
                    print(f"    {c:>3} → {s}")
                break
        else:
            print("  No injective signature found among standard candidates")
        print()
        count += 1
        if count >= 5:
            break


def search_pair_gadgets(M, top_n=10, max_families=3, disjoint_only=False, connected_only=False):
    """Search for pair gadgets."""
    pairs = find_pairs(M)
    print(f"Found {len(pairs)} pairs with max element ≤ {M}")
    print()

    multiplier_pairs = {}
    for p in pairs:
        g = gcd(p[0], p[1])
        mults = (p[0] // g, p[1] // g)
        if mults not in multiplier_pairs:
            multiplier_pairs[mults] = []
        multiplier_pairs[mults].append((g, p))

    print(f"Unique multiplier patterns: {len(multiplier_pairs)}")
    print()
    print("=== Pair Families ===")
    print(f"{'Multipliers':<20} {'|G|':>4} {'τ':>3} {'τ/|G|':>8} {'#params':>8}")
    print("-" * 50)

    for mults, params in sorted(multiplier_pairs.items()):
        tau = 1
        ratio = tau / len(set(mults))
        print(f"{str(mults):<20} {len(set(mults)):>4} {tau:>3} {ratio:>8.4f} {len(params):>8}")

    # Multi-pair gadgets
    mult_list = sorted(multiplier_pairs.keys())
    gadgets = enumerate_gadgets(
        mult_list,
        max_families=max_families,
        disjoint_only=disjoint_only,
        connected_only=connected_only,
    )

    print()
    print("=== Multi-Pair Gadgets ===")
    mode_parts = [f"up to {max_families} families"]
    if disjoint_only:
        mode_parts.append("disjoint only")
    if connected_only:
        mode_parts.append("overlap-connected only")
    print("Mode:", ", ".join(mode_parts))
    print(f"{'Gadget elements':<35} {'|G|':>4} {'τ':>3} {'τ/|G|':>8} {'Families'}")
    print("-" * 75)
    seen = set()
    count = 0
    for elts, hyp, tau, ratio, fams in gadgets:
        key = frozenset(elts)
        if key in seen:
            continue
        seen.add(key)
        elts_str = str(sorted(elts))
        fams_str = " + ".join(str(f) for f in fams)
        print(f"{elts_str:<35} {len(elts):>4} {tau:>3} {ratio:>8.4f} {fams_str}")
        count += 1
        if count >= top_n:
            break


def _reciprocal_subset_sum_one_witness(ks):
    """Find a nonempty subset of ks with reciprocal sum exactly 1, if one exists.
    Returns a sorted tuple, or None.
    """
    sums = {Fraction(0, 1): tuple()}
    for k in ks:
        rk = Fraction(1, k)
        # Iterate over a snapshot to avoid chaining with same k
        items = list(sums.items())
        for s, subset in items:
            t = s + rk
            if t > 1:
                continue
            if t not in sums:
                sums[t] = subset + (k,)
    witness = sums.get(Fraction(1, 1))
    if witness is None or len(witness) == 0:
        return None
    return tuple(sorted(witness))


def _best_reciprocal_sum_below_one(ks):
    """Largest reciprocal subset sum <= 1 over subsets of ks."""
    reachable = {Fraction(0, 1)}
    for k in ks:
        rk = Fraction(1, k)
        new_vals = set()
        for s in reachable:
            t = s + rk
            if t <= 1:
                new_vals.add(t)
        reachable |= new_vals
    return max(reachable)


def _search_sumfree_witnesses_for_a(a, N, max_rhs_size, recips):
    """Enumerate all witnesses S with 1/a = sum_{b in S} 1/b, b > a, |S| <= max_rhs_size."""
    target = Fraction(1, a)
    candidates = list(range(a + 1, N + 1))
    out = set()

    # Fast impossible case
    if not candidates:
        return out

    # Precompute reciprocal list for candidates
    cand_recips = [recips[b] for b in candidates]

    def max_add_from(start, r):
        if r == 0:
            return Fraction(0, 1)
        if start + r > len(candidates):
            return None
        # Largest reciprocal mass from start with r picks: take smallest denominators available.
        return sum(cand_recips[start : start + r], Fraction(0, 1))

    def min_add_global(r):
        if r == 0:
            return Fraction(0, 1)
        if r > len(candidates):
            return None
        # Smallest reciprocal mass with r picks: take largest denominators.
        return sum(cand_recips[-r:], Fraction(0, 1))

    def backtrack(k, start, chosen, cur_sum):
        chosen_count = len(chosen)
        remaining = k - chosen_count
        if remaining == 0:
            if cur_sum == target:
                out.add(tuple(chosen))
            return

        if start >= len(candidates):
            return
        if len(candidates) - start < remaining:
            return

        max_add = max_add_from(start, remaining)
        if max_add is None or cur_sum + max_add < target:
            return

        min_add = min_add_global(remaining)
        if min_add is not None and cur_sum + min_add > target:
            return

        end = len(candidates) - remaining + 1
        for i in range(start, end):
            b = candidates[i]
            next_sum = cur_sum + recips[b]
            if next_sum > target:
                continue
            chosen.append(b)
            backtrack(k, i + 1, chosen, next_sum)
            chosen.pop()

    for k in range(1, max_rhs_size + 1):
        backtrack(k, 0, [], Fraction(0, 1))
    return out


def _witness_cache_key(N, max_rhs_size):
    return f"N={N};rhs={max_rhs_size}"


def _load_witness_cache(path):
    p = Path(path)
    if not p.exists():
        return {}
    try:
        with p.open("r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def _save_witness_cache(path, cache):
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open("w", encoding="utf-8") as f:
        json.dump(cache, f, indent=2, sort_keys=True)


def _encode_witnesses(witnesses):
    return [[a, list(S)] for a, S in witnesses]


def _decode_witnesses(data):
    out = []
    for item in data:
        if len(item) != 2:
            continue
        a, S = item
        out.append((int(a), tuple(int(x) for x in S)))
    return out


def find_sumfree_witnesses(N, max_rhs_size, progress_every=0):
    """Enumerate witness equations (a, S) up to RHS size bound:
    1/a = sum_{b in S} 1/b with S nonempty and all b in [1, N].
    """
    recips = {n: Fraction(1, n) for n in range(1, N + 1)}
    witnesses = []
    for a in range(1, N + 1):
        sets_for_a = _search_sumfree_witnesses_for_a(a, N, max_rhs_size, recips)
        for S in sorted(sets_for_a):
            witnesses.append((a, S))
        if progress_every and (a % progress_every == 0 or a == N):
            print(f"  witness progress: a={a}/{N}, total={len(witnesses)}", flush=True)
    return witnesses


def _find_witness_for_a_in_candidates(a, candidates, max_rhs_size, recips):
    """Find one witness tuple S from candidates with 1/a = sum_{b in S} 1/b."""
    target = Fraction(1, a)
    candidates = sorted(candidates)
    cand_recips = [recips[b] for b in candidates]

    def max_add_from(start, r):
        if r == 0:
            return Fraction(0, 1)
        if start + r > len(candidates):
            return None
        return sum(cand_recips[start : start + r], Fraction(0, 1))

    def min_add_global(r):
        if r == 0:
            return Fraction(0, 1)
        if r > len(candidates):
            return None
        return sum(cand_recips[-r:], Fraction(0, 1))

    def backtrack(k, start, chosen, cur_sum):
        chosen_count = len(chosen)
        remaining = k - chosen_count
        if remaining == 0:
            if cur_sum == target:
                return tuple(chosen)
            return None
        if start >= len(candidates):
            return None
        if len(candidates) - start < remaining:
            return None
        max_add = max_add_from(start, remaining)
        if max_add is None or cur_sum + max_add < target:
            return None
        min_add = min_add_global(remaining)
        if min_add is not None and cur_sum + min_add > target:
            return None
        end = len(candidates) - remaining + 1
        for i in range(start, end):
            b = candidates[i]
            next_sum = cur_sum + recips[b]
            if next_sum > target:
                continue
            chosen.append(b)
            ans = backtrack(k, i + 1, chosen, next_sum)
            if ans is not None:
                return ans
            chosen.pop()
        return None

    for k in range(1, max_rhs_size + 1):
        ans = backtrack(k, 0, [], Fraction(0, 1))
        if ans is not None:
            return ans
    return None


def find_sumfree_violation_in_set(A, N, max_rhs_size):
    """Find one witness (a, S) inside A up to RHS size bound, or None."""
    Aset = set(A)
    recips = {n: Fraction(1, n) for n in range(1, N + 1)}
    for a in sorted(Aset):
        candidates = [b for b in A if b != a]
        S = _find_witness_for_a_in_candidates(a, candidates, max_rhs_size, recips)
        if S is not None:
            return (a, S)
    return None


def _solve_sumfree_max_set(N, witnesses, forbid_one=False, z3_timeout_ms=30000):
    """Solve for a maximum witness-free subset using z3 when available."""
    if HAS_Z3:
        try:
            A = max_sumfree_set_z3(
                N,
                witnesses,
                forbid_one=forbid_one,
                timeout_ms=z3_timeout_ms,
            )
            return A, "z3-optimal"
        except RuntimeError as e:
            print(f"z3 path failed ({e}); falling back to greedy-restart")
            A = max_sumfree_set_greedy(
                N,
                witnesses,
                restarts=400,
                seed=0,
                forbid_one=forbid_one,
            )
            return A, "greedy-fallback-after-z3"
    print("z3 unavailable: using greedy-restart fallback")
    A = max_sumfree_set_greedy(N, witnesses, restarts=400, seed=0, forbid_one=forbid_one)
    return A, "greedy-fallback"


def _canonical_witness(w):
    a, S = w
    return (int(a), tuple(sorted(int(x) for x in S)))


def optimize_with_cut_loop(
    N,
    base_witnesses,
    forbid_one=False,
    z3_timeout_ms=30000,
    audit_max_rhs_size=0,
    max_cut_rounds=5,
):
    """Iterative strengthening:
    solve under current witness set, audit, and add one violating witness as a cut.
    """
    witnesses = [_canonical_witness(w) for w in base_witnesses]
    witness_set = set(witnesses)
    added_cuts = []
    rounds = 0

    while True:
        A, solver_tag = _solve_sumfree_max_set(
            N,
            witnesses,
            forbid_one=forbid_one,
            z3_timeout_ms=z3_timeout_ms,
        )

        if not audit_max_rhs_size or audit_max_rhs_size <= 0:
            return A, solver_tag, witnesses, added_cuts, None, rounds

        v = find_sumfree_violation_in_set(A, N, audit_max_rhs_size)
        if v is None:
            return A, solver_tag, witnesses, added_cuts, None, rounds

        v = _canonical_witness(v)
        if v in witness_set:
            # Should be impossible if solver is correct on current witness set.
            return A, solver_tag, witnesses, added_cuts, v, rounds

        if rounds >= max_cut_rounds:
            return A, solver_tag, witnesses, added_cuts, v, rounds

        witnesses.append(v)
        witness_set.add(v)
        added_cuts.append(v)
        rounds += 1
        print(
            f"  cut-loop round {rounds}: added witness a={v[0]}, |S|={len(v[1])}",
            flush=True,
        )


def max_sumfree_set_z3(N, witnesses, forbid_one=False, timeout_ms=30000):
    """Compute max A ⊆ [1, N] avoiding all witness hyperedges."""
    if not HAS_Z3:
        raise RuntimeError("z3 is required for --sumfree-fibers mode")
    opt = Optimize()
    if timeout_ms and timeout_ms > 0:
        opt.set(timeout=timeout_ms)
    x = {n: Int(f"x_{n}") for n in range(1, N + 1)}
    for n in range(1, N + 1):
        opt.add(x[n] >= 0, x[n] <= 1)
    if forbid_one and 1 in x:
        opt.add(x[1] == 0)
    for a, S in witnesses:
        edge = [a] + list(S)
        opt.add(Sum([x[n] for n in edge]) <= len(edge) - 1)
    total = Sum([x[n] for n in range(1, N + 1)])
    opt.maximize(total)
    result = opt.check()
    if result != sat:
        raise RuntimeError(f"z3 optimize failed (result={result})")
    m = opt.model()
    selected = sorted(n for n in range(1, N + 1) if m[x[n]].as_long() == 1)
    return selected


def max_sumfree_set_greedy(N, witnesses, restarts=200, seed=0, forbid_one=False):
    """Greedy-restart fallback when z3 is unavailable."""
    rng = random.Random(seed)
    edges = [set([a, *S]) for a, S in witnesses]
    incident = {n: [] for n in range(1, N + 1)}
    for i, edge in enumerate(edges):
        for n in edge:
            incident[n].append(i)

    def can_add(n, chosen):
        for i in incident[n]:
            edge = edges[i]
            if all((x == n) or (x in chosen) for x in edge):
                return False
        return True

    base_orders = [
        list(range(N, 0, -1)),  # upper-half biased
        list(range(1, N + 1)),  # small-denominator biased
        sorted(range(1, N + 1), key=lambda x: len(incident[x])),  # low-conflict first
        sorted(range(1, N + 1), key=lambda x: -len(incident[x])),  # high-conflict first
    ]

    best = []
    all_orders = []
    all_orders.extend(base_orders)
    for _ in range(max(0, restarts - len(base_orders))):
        order = list(range(1, N + 1))
        rng.shuffle(order)
        all_orders.append(order)

    for order in all_orders:
        chosen = set()
        for n in order:
            if forbid_one and n == 1:
                continue
            if can_add(n, chosen):
                chosen.add(n)
        if len(chosen) > len(best):
            best = sorted(chosen)
    return best


def analyze_sumfree_fibers(
    N,
    max_rhs_size=5,
    top_n=10,
    witness_cache=None,
    progress_every=0,
    forbid_one=False,
    z3_timeout_ms=30000,
    analyze_min_a=1,
    fiber_dp_max_size=18,
    audit_max_rhs_size=0,
    cut_loop=False,
    max_cut_rounds=5,
):
    """Experimental analyzer for #301:
    build a max set under bounded witness constraints, then inspect fibers.
    """
    print(f"Building witness list for N={N}, rhs_size<= {max_rhs_size} ...")
    cache = {}
    cache_key = _witness_cache_key(N, max_rhs_size)
    if witness_cache:
        cache = _load_witness_cache(witness_cache)
        if cache_key in cache:
            witnesses = _decode_witnesses(cache[cache_key])
            print(f"Loaded witnesses from cache: {witness_cache}")
        else:
            witnesses = find_sumfree_witnesses(N, max_rhs_size, progress_every=progress_every)
            cache[cache_key] = _encode_witnesses(witnesses)
            _save_witness_cache(witness_cache, cache)
            print(f"Saved witnesses to cache: {witness_cache}")
    else:
        witnesses = find_sumfree_witnesses(N, max_rhs_size, progress_every=progress_every)
    print(f"Witness equations found: {len(witnesses)}")
    print()

    cut_violation = None
    if cut_loop:
        A, solver_tag, witnesses, added_cuts, cut_violation, cut_rounds = optimize_with_cut_loop(
            N,
            witnesses,
            forbid_one=forbid_one,
            z3_timeout_ms=z3_timeout_ms,
            audit_max_rhs_size=audit_max_rhs_size,
            max_cut_rounds=max_cut_rounds,
        )
        print(
            f"cut-loop summary: rounds={cut_rounds}, added_cuts={len(added_cuts)}",
            flush=True,
        )
        if cut_violation is not None:
            print(f"cut-loop unresolved violation at cap: {cut_violation}")
    else:
        A, solver_tag = _solve_sumfree_max_set(
            N,
            witnesses,
            forbid_one=forbid_one,
            z3_timeout_ms=z3_timeout_ms,
        )

    Aset = set(A)
    density = len(A) / N if N > 0 else 0.0
    print("=== Bounded-Constraint Max Set ===")
    print(f"method: {solver_tag}")
    print(f"|A| = {len(A)} / {N} = {density:.4f}")
    if forbid_one:
        print("constraint: 1 not allowed in A")
    print(f"A = {A}")
    print()

    # Validate model against enumerated witnesses
    violated = []
    for a, S in witnesses:
        edge = {a, *S}
        if edge.issubset(Aset):
            violated.append((a, S))
            break
    print("Witness-check:", "PASS" if not violated else f"FAIL ({violated[0]})")
    if audit_max_rhs_size and audit_max_rhs_size > max_rhs_size and not cut_loop:
        print(f"Audit-check (rhs_size<= {audit_max_rhs_size}): running...")
        v = find_sumfree_violation_in_set(A, N, audit_max_rhs_size)
        if v is None:
            print("Audit-check: PASS")
        else:
            print(f"Audit-check: FAIL ({v})")
    print()

    # Fiber analysis
    recips = {n: Fraction(1, n) for n in range(1, N + 1)}
    fiber_rows = []
    bad_rows = []
    skipped_dp = 0
    for a in A:
        if a < analyze_min_a:
            continue
        ks = [k for k in range(2, N // a + 1) if a * k in Aset]
        rec_sum = sum((recips[k] for k in ks), Fraction(0, 1))
        if len(ks) > fiber_dp_max_size:
            best_below = None
            gap = None
            eq_one = None
            skipped_dp += 1
        else:
            best_below = _best_reciprocal_sum_below_one(ks)
            gap = Fraction(1, 1) - best_below
            eq_one = _reciprocal_subset_sum_one_witness(ks)
        row = (a, ks, rec_sum, best_below, gap, eq_one)
        fiber_rows.append(row)
        if eq_one is not None:
            bad_rows.append(row)

    print("=== Fiber Summary ===")
    print(f"Fibers with exact reciprocal-sum-1 subset: {len(bad_rows)}")
    if skipped_dp > 0:
        print(f"Fibers skipped in exact DP check (|K_a|>{fiber_dp_max_size}): {skipped_dp}")
    if bad_rows:
        for a, ks, _, _, _, eq_one in bad_rows[:5]:
            print(f"  a={a:>3}: K_a={ks}, witness={eq_one}")
    print()

    print("=== Top Fibers by Reciprocal Mass ===")
    fiber_rows.sort(key=lambda r: (-float(r[2]), -len(r[1]), r[0]))
    print(f"{'a':>4} {'|K_a|':>6} {'sum_{k in K_a} 1/k':>20} {'best<=1':>12} {'gap':>12}")
    print("-" * 64)
    for a, ks, rec_sum, best_below, gap, _ in fiber_rows[:top_n]:
        best_str = str(best_below) if best_below is not None else "NA"
        gap_str = str(gap) if gap is not None else "NA"
        print(f"{a:>4} {len(ks):>6} {str(rec_sum):>20} {best_str:>12} {gap_str:>12}")
    print()

    print("=== Candidate Near-Threshold Fibers (best<=1 close to 1) ===")
    near = sorted(
        [r for r in fiber_rows if r[4] is not None],
        key=lambda r: (r[4], -len(r[1]), r[0]),
    )
    for a, ks, rec_sum, best_below, gap, _ in near[:top_n]:
        print(f"a={a:>3}, |K_a|={len(ks):>2}, gap={gap}, K_a={ks}")


def main():
    parser = argparse.ArgumentParser(description="Gadget mining for unit fraction bounds")
    parser.add_argument("--triples", action="store_true", help="Search for triple gadgets")
    parser.add_argument("--pairs", action="store_true", help="Search for pair gadgets")
    parser.add_argument("--sumfree-fibers", action="store_true",
                        help="Experimental #301 fiber-density diagnostics")
    parser.add_argument("--max", type=int, default=30, help="Maximum element value M")
    parser.add_argument("--top", type=int, default=10, help="Number of top results to show")
    parser.add_argument("--max-rhs-size", type=int, default=5,
                        help="Maximum RHS witness size for --sumfree-fibers")
    parser.add_argument("--witness-cache", type=str, default="",
                        help="Optional JSON cache file for witness equations")
    parser.add_argument("--progress-every", type=int, default=0,
                        help="Print witness generation progress every k values of a")
    parser.add_argument("--forbid-one", action="store_true",
                        help="For --sumfree-fibers, enforce 1 ∉ A")
    parser.add_argument("--z3-timeout-ms", type=int, default=30000,
                        help="Per-optimization timeout for z3 in --sumfree-fibers")
    parser.add_argument("--analyze-min-a", type=int, default=1,
                        help="Only analyze fibers for a >= this value")
    parser.add_argument("--fiber-dp-max-size", type=int, default=18,
                        help="Skip exact subset-DP checks when |K_a| exceeds this")
    parser.add_argument("--audit-max-rhs-size", type=int, default=0,
                        help="Optional stronger post-check bound on RHS size")
    parser.add_argument("--cut-loop", action="store_true",
                        help="Iteratively add violating audit witnesses and re-optimize")
    parser.add_argument("--max-cut-rounds", type=int, default=5,
                        help="Maximum cut-loop rounds for --cut-loop")
    parser.add_argument("--max-families", type=int, default=3,
                        help="Maximum number of base families to combine")
    parser.add_argument("--disjoint-only", action="store_true",
                        help="Only combine families with disjoint multipliers")
    parser.add_argument("--connected-only", action="store_true",
                        help="Require overlap-connected family combinations")

    args = parser.parse_args()

    if not args.triples and not args.pairs and not args.sumfree_fibers:
        parser.print_help()
        sys.exit(1)

    print(f"z3 available: {HAS_Z3}")
    print()

    if args.triples:
        search_triple_gadgets(
            args.max,
            args.top,
            max_families=args.max_families,
            disjoint_only=args.disjoint_only,
            connected_only=args.connected_only,
        )

    if args.pairs:
        if args.triples:
            print("\n" + "=" * 80 + "\n")
        search_pair_gadgets(
            args.max,
            args.top,
            max_families=args.max_families,
            disjoint_only=args.disjoint_only,
            connected_only=args.connected_only,
        )

    if args.sumfree_fibers:
        if args.triples or args.pairs:
            print("\n" + "=" * 80 + "\n")
        analyze_sumfree_fibers(
            args.max,
            max_rhs_size=args.max_rhs_size,
            top_n=args.top,
            witness_cache=(args.witness_cache or None),
            progress_every=args.progress_every,
            forbid_one=args.forbid_one,
            z3_timeout_ms=args.z3_timeout_ms,
            analyze_min_a=args.analyze_min_a,
            fiber_dp_max_size=args.fiber_dp_max_size,
            audit_max_rhs_size=args.audit_max_rhs_size,
            cut_loop=args.cut_loop,
            max_cut_rounds=args.max_cut_rounds,
        )


if __name__ == "__main__":
    main()
