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
import sys
from itertools import combinations
from math import gcd

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


def main():
    parser = argparse.ArgumentParser(description="Gadget mining for unit fraction bounds")
    parser.add_argument("--triples", action="store_true", help="Search for triple gadgets")
    parser.add_argument("--pairs", action="store_true", help="Search for pair gadgets")
    parser.add_argument("--max", type=int, default=30, help="Maximum element value M")
    parser.add_argument("--top", type=int, default=10, help="Number of top results to show")
    parser.add_argument("--max-families", type=int, default=3,
                        help="Maximum number of base families to combine")
    parser.add_argument("--disjoint-only", action="store_true",
                        help="Only combine families with disjoint multipliers")
    parser.add_argument("--connected-only", action="store_true",
                        help="Require overlap-connected family combinations")

    args = parser.parse_args()

    if not args.triples and not args.pairs:
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


if __name__ == "__main__":
    main()
