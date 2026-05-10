#!/usr/bin/env python3
"""
Weighted forbidden-hyperedge packing for Problem #301.

This is a research tool for the overlap-aware route.  It enumerates identities

    1/a = sum_{b in S} 1/b

inside [1,N], then greedily assigns nonnegative rational weights to forbidden
hyperedges {a} ∪ S subject to vertex load <= 1.  Any such certificate proves
that every sum-free A subset [1,N] omits at least the total weight.

The greedy search is only a heuristic; the certificate verifier is the important
part.  The template mode additionally searches finite p-adic multiplier grids,
computes exact prefix hitting numbers, and can compress the resulting identity
pool into a smaller Lean-facing certificate.
"""

from __future__ import annotations

import argparse
import json
import random
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path


@dataclass(frozen=True)
class Witness:
    target: int
    rhs: tuple[int, ...]

    @property
    def edge(self) -> tuple[int, ...]:
        return tuple(sorted((self.target, *self.rhs)))


@dataclass(frozen=True)
class WeightedWitness:
    witness: Witness
    weight: Fraction


def fraction_to_str(q: Fraction) -> str:
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def fraction_from_str(s: str) -> Fraction:
    return Fraction(s)


def reciprocal_sum(ns: tuple[int, ...]) -> Fraction:
    return sum((Fraction(1, n) for n in ns), Fraction(0))


def is_valid_witness(w: Witness) -> bool:
    if w.target <= 0 or any(b <= 0 for b in w.rhs):
        return False
    if len(set((w.target, *w.rhs))) != 1 + len(w.rhs):
        return False
    return Fraction(1, w.target) == reciprocal_sum(w.rhs)


def find_witnesses_in(
    denominators: list[int] | tuple[int, ...],
    max_rhs_size: int,
    progress_every: int = 0,
) -> list[Witness]:
    """Enumerate witnesses inside a finite denominator set.

    The restriction b > a is not a loss: if b <= a and b != a, then 1/b > 1/a,
    so a positive reciprocal sum cannot equal 1/a; b = a is forbidden by erase.
    """
    ds = tuple(sorted(set(denominators)))
    recips = {n: Fraction(1, n) for n in ds}
    witnesses: list[Witness] = []

    for pos, a in enumerate(ds, start=1):
        candidates = [b for b in ds if b > a]
        cand_recips = [recips[b] for b in candidates]
        target = recips[a]

        def max_add_from(start: int, count: int) -> Fraction | None:
            if count == 0:
                return Fraction(0)
            if start + count > len(candidates):
                return None
            return sum(cand_recips[start : start + count], Fraction(0))

        def min_add_global(count: int) -> Fraction | None:
            if count == 0:
                return Fraction(0)
            if count > len(candidates):
                return None
            return sum((cand_recips[-i] for i in range(1, count + 1)), Fraction(0))

        def backtrack(k: int, start: int, chosen: list[int], cur_sum: Fraction) -> None:
            remaining = k - len(chosen)
            if remaining == 0:
                if cur_sum == target:
                    witnesses.append(Witness(a, tuple(chosen)))
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
            backtrack(k, 0, [], Fraction(0))

        if progress_every and (pos % progress_every == 0 or pos == len(ds)):
            print(f"witness progress: {pos}/{len(ds)}, total={len(witnesses)}", flush=True)

    return witnesses


def find_witnesses(N: int, max_rhs_size: int, progress_every: int = 0) -> list[Witness]:
    """Enumerate witnesses in the interval [1,N]."""
    return find_witnesses_in(tuple(range(1, N + 1)), max_rhs_size, progress_every)


def degree_table(N: int, witnesses: list[Witness]) -> list[int]:
    deg = [0] * (N + 1)
    for w in witnesses:
        for x in w.edge:
            deg[x] += 1
    return deg


def greedy_fractional_pack(
    N: int,
    witnesses: list[Witness],
    restarts: int,
    seed: int,
    capacity: Fraction = Fraction(1),
) -> tuple[Fraction, list[WeightedWitness], list[Fraction]]:
    rng = random.Random(seed)
    deg = degree_table(N, witnesses)

    orders: list[list[Witness]] = [
        sorted(witnesses, key=lambda w: (max(w.edge), len(w.edge), w.edge)),
        sorted(witnesses, key=lambda w: (sum(deg[x] for x in w.edge), max(w.edge), w.edge)),
        sorted(witnesses, key=lambda w: (len(w.edge), max(w.edge), w.edge)),
        sorted(witnesses, key=lambda w: (-len(w.edge), max(w.edge), w.edge)),
    ]

    best_total = Fraction(-1)
    best_chosen: list[WeightedWitness] = []
    best_load: list[Fraction] = [Fraction(0)] * (N + 1)

    for restart in range(restarts):
        if restart < len(orders):
            order = orders[restart]
        else:
            order = witnesses[:]
            rng.shuffle(order)

        load = [Fraction(0)] * (N + 1)
        chosen: list[WeightedWitness] = []
        total = Fraction(0)

        for w in order:
            edge = w.edge
            remaining = min(capacity - load[x] for x in edge)
            if remaining <= 0:
                continue
            for x in edge:
                load[x] += remaining
            chosen.append(WeightedWitness(w, remaining))
            total += remaining

        if total > best_total:
            best_total = total
            best_chosen = chosen
            best_load = load

    return best_total, best_chosen, best_load


def certificate_dict(
    N: int,
    max_rhs_size: int,
    chosen: list[WeightedWitness],
    capacity: Fraction = Fraction(1),
) -> dict:
    return {
        "problem": 301,
        "kind": "weighted_sumfree_forbidden_hyperedge_packing",
        "N": N,
        "max_rhs_size": max_rhs_size,
        "capacity": fraction_to_str(capacity),
        "objective": fraction_to_str(sum((c.weight for c in chosen), Fraction(0))),
        "witnesses": [
            {
                "target": c.witness.target,
                "rhs": list(c.witness.rhs),
                "weight": fraction_to_str(c.weight),
            }
            for c in chosen
        ],
    }


def load_certificate(path: Path) -> tuple[int, int, Fraction, list[WeightedWitness]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    N = int(data["N"])
    max_rhs_size = int(data.get("max_rhs_size", 0))
    capacity = fraction_from_str(data.get("capacity", "1"))
    chosen = []
    for item in data["witnesses"]:
        w = Witness(int(item["target"]), tuple(int(x) for x in item["rhs"]))
        chosen.append(WeightedWitness(w, fraction_from_str(item["weight"])))
    return N, max_rhs_size, capacity, chosen


def verify_certificate(
    N: int,
    chosen: list[WeightedWitness],
    capacity: Fraction = Fraction(1),
) -> tuple[bool, str, Fraction, list[Fraction]]:
    load = [Fraction(0)] * (N + 1)
    total = Fraction(0)
    for c in chosen:
        w = c.witness
        if c.weight < 0:
            return False, f"negative weight on {w}", total, load
        if not is_valid_witness(w):
            return False, f"invalid witness {w}", total, load
        if any(x < 1 or x > N for x in w.edge):
            return False, f"edge outside [1,N]: {w.edge}", total, load
        total += c.weight
        for x in w.edge:
            load[x] += c.weight
            if load[x] > capacity:
                return False, f"load overflow at {x}: {load[x]} > {capacity}", total, load
    return True, "ok", total, load


def summarize(N: int, chosen: list[WeightedWitness], load: list[Fraction], total: Fraction) -> None:
    saturated = sum(1 for x in range(1, N + 1) if load[x] == 1)
    nonzero = sum(1 for x in range(1, N + 1) if load[x] > 0)
    print(f"weighted omissions: {fraction_to_str(total)}")
    print(f"density upper bound: {fraction_to_str(Fraction(N) - total)} / {N}")
    print(f"  decimal: {float(1 - total / N):.6f}")
    print(f"weighted witnesses: {len(chosen)}")
    print(f"loaded vertices: {nonzero}/{N}; saturated: {saturated}/{N}")
    print("first witnesses:")
    for c in chosen[:12]:
        rhs = ", ".join(str(x) for x in c.witness.rhs)
        print(f"  {fraction_to_str(c.weight):>5} * [1/{c.witness.target} = sum 1/[{rhs}]]")


def parse_moduli(s: str) -> dict[int, int]:
    moduli: dict[int, int] = {}
    if not s:
        return moduli
    for part in s.split(","):
        p_text, q_text = part.split(":", 1)
        p = int(p_text)
        q = int(q_text)
        if p <= 1 or q <= 0:
            raise ValueError(f"bad modulus entry: {part!r}")
        if q > 1:
            moduli[p] = q
    return dict(sorted(moduli.items()))


def signature_density(moduli: dict[int, int]) -> Fraction:
    """Density of the class v_p(a) == 0 mod q_p for every p."""
    ans = Fraction(1)
    for p, q in moduli.items():
        ans *= Fraction((p ** (q - 1)) * (p - 1), (p**q) - 1)
    return ans


def grid_multipliers(moduli: dict[int, int], include_one: bool = False) -> list[int]:
    primes = list(moduli)
    values: list[int] = []
    for exponents in product(*(range(moduli[p]) for p in primes)):
        n = 1
        for p, e in zip(primes, exponents, strict=True):
            n *= p**e
        if include_one or n != 1:
            values.append(n)
    return sorted(values)


def _mask_bits(mask: int) -> list[int]:
    bits: list[int] = []
    while mask:
        bit = mask & -mask
        bits.append(bit)
        mask -= bit
    return bits


def _canonical_edges(edges: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(set(edges), key=lambda e: (e.bit_count(), e)))


def _greedy_disjoint_edge_bound(edges: tuple[int, ...]) -> int:
    used = 0
    count = 0
    for edge in sorted(edges, key=lambda e: (e.bit_count(), e)):
        if edge & used == 0:
            used |= edge
            count += 1
    return count


def min_vertex_cover_size(
    vertices: list[int],
    witnesses: list[Witness],
    max_states: int = 0,
) -> tuple[int, int]:
    """Exact minimum hitting set size for witnessed forbidden edges.

    This is the integral local obstruction used by the existing Lean proof:
    every admissible prefix subset must omit at least this many vertices.
    """
    index = {v: i for i, v in enumerate(vertices)}
    edges: list[int] = []
    for w in witnesses:
        if all(x in index for x in w.edge):
            mask = 0
            for x in w.edge:
                mask |= 1 << index[x]
            edges.append(mask)
    start_edges = _canonical_edges(tuple(edges))
    states = 0

    @lru_cache(maxsize=None)
    def search(edge_state: tuple[int, ...]) -> int:
        nonlocal states
        states += 1
        if max_states and states > max_states:
            raise RuntimeError(f"template exact cover exceeded {max_states} states")
        if not edge_state:
            return 0

        lower = _greedy_disjoint_edge_bound(edge_state)
        degrees: dict[int, int] = {}
        min_size = min(edge.bit_count() for edge in edge_state)
        candidates = [edge for edge in edge_state if edge.bit_count() == min_size]
        for edge in edge_state:
            for bit in _mask_bits(edge):
                degrees[bit] = degrees.get(bit, 0) + 1
        branch_edge = max(candidates, key=lambda e: sum(degrees.get(bit, 0) for bit in _mask_bits(e)))
        branch_bits = sorted(_mask_bits(branch_edge), key=lambda bit: degrees.get(bit, 0), reverse=True)

        best = len(vertices)
        for bit in branch_bits:
            reduced = _canonical_edges(tuple(edge for edge in edge_state if edge & bit == 0))
            best = min(best, 1 + search(reduced))
            if best == lower:
                break
        return best

    return search(start_edges), states


def template_profile(
    multipliers: list[int],
    witnesses: list[Witness],
    density: Fraction,
    max_states: int,
) -> tuple[Fraction, list[dict]]:
    band_sum = Fraction(0)
    rows: list[dict] = []
    for i, cutoff in enumerate(multipliers):
        prefix = multipliers[: i + 1]
        deficit, states = min_vertex_cover_size(prefix, witnesses, max_states)
        next_cutoff = multipliers[i + 1] if i + 1 < len(multipliers) else None
        width = Fraction(1, cutoff) - (Fraction(1, next_cutoff) if next_cutoff else Fraction(0))
        contribution = deficit * width
        band_sum += contribution
        rows.append(
            {
                "cutoff": cutoff,
                "prefix_size": len(prefix),
                "keep": len(prefix) - deficit,
                "deficit": deficit,
                "width": fraction_to_str(width),
                "band_contribution": fraction_to_str(contribution),
                "cover_states": states,
            }
        )
    return density * band_sum, rows


def _max_independent_mask(n: int, edge_masks: tuple[int, ...]) -> int:
    """Return one maximum subset of the first n vertices avoiding edge_masks."""
    prefix_mask = (1 << n) - 1
    active = tuple(sorted((e for e in edge_masks if e & prefix_mask == e), key=lambda e: (e.bit_count(), e)))

    @lru_cache(maxsize=None)
    def first_edge(mask: int) -> int:
        for edge in active:
            if mask & edge == edge:
                return edge
        return 0

    @lru_cache(maxsize=None)
    def search(candidates: int) -> int:
        edge = first_edge(candidates)
        if edge == 0:
            return candidates
        degrees: dict[int, int] = {}
        for active_edge in active:
            if active_edge & candidates == active_edge:
                for bit in _mask_bits(active_edge):
                    degrees[bit] = degrees.get(bit, 0) + 1
        best = 0
        for bit in sorted(_mask_bits(edge), key=lambda b: degrees.get(b, 0), reverse=True):
            candidate = search(candidates & ~bit)
            if candidate.bit_count() > best.bit_count():
                best = candidate
        return best

    return search(prefix_mask)


def compress_template_witnesses(
    multipliers: list[int],
    witnesses: list[Witness],
    rows: list[dict],
) -> list[Witness]:
    """Greedily compress a template to a smaller prefix-hitting certificate.

    The exact profile may use thousands of possible identities.  This cutting
    pass repeatedly finds a too-large set avoiding the current compressed list
    and adds one genuine identity contained in that set.
    """
    index = {m: i for i, m in enumerate(multipliers)}
    by_mask: dict[int, Witness] = {}
    for w in witnesses:
        mask = 0
        for x in w.edge:
            mask |= 1 << index[x]
        by_mask.setdefault(mask, w)
    witness_masks = tuple(sorted(by_mask))

    widths = [fraction_from_str(row["width"]) for row in rows]
    future_score: dict[int, Fraction] = {}
    for mask in witness_masks:
        first_full = max(index[x] for x in by_mask[mask].edge)
        future_score[mask] = sum(widths[first_full:], Fraction(0)) / mask.bit_count()

    selected: set[int] = set()
    for n, row in enumerate(rows, start=1):
        target_keep = int(row["keep"])
        if target_keep == n:
            continue
        while True:
            independent = _max_independent_mask(n, tuple(selected))
            if independent.bit_count() <= target_keep:
                break
            prefix_mask = (1 << n) - 1
            candidates = [
                mask
                for mask in witness_masks
                if mask not in selected and mask & prefix_mask == mask and mask & independent == mask
            ]
            if not candidates:
                raise RuntimeError(
                    f"could not compress cutoff {row['cutoff']}: "
                    f"found avoiding set of size {independent.bit_count()}"
                )
            candidates.sort(
                key=lambda mask: (
                    -future_score[mask],
                    mask.bit_count(),
                    max(index[x] for x in by_mask[mask].edge),
                    by_mask[mask].edge,
                )
            )
            selected.add(candidates[0])

    selected_tuple = tuple(selected)
    for n, row in enumerate(rows, start=1):
        independent = _max_independent_mask(n, selected_tuple)
        if independent.bit_count() > int(row["keep"]):
            raise RuntimeError(
                f"compressed certificate failed at cutoff {row['cutoff']}: "
                f"{independent.bit_count()} > {row['keep']}"
            )

    return [by_mask[mask] for mask in sorted(selected, key=lambda m: by_mask[m].edge)]


def template_report(
    moduli: dict[int, int],
    max_rhs_size: int,
    include_one: bool,
    max_states: int,
    compress: bool,
) -> dict:
    multipliers = grid_multipliers(moduli, include_one)
    witnesses = find_witnesses_in(multipliers, max_rhs_size)
    dens = signature_density(moduli)
    deficit, rows = template_profile(multipliers, witnesses, dens, max_states)
    compressed = compress_template_witnesses(multipliers, witnesses, rows) if compress else []
    return {
        "problem": 301,
        "kind": "same_signature_multiplier_template",
        "moduli": moduli,
        "include_one": include_one,
        "max_rhs_size": max_rhs_size,
        "density": fraction_to_str(dens),
        "multipliers": multipliers,
        "witness_count": len(witnesses),
        "asymptotic_forced_deficit": fraction_to_str(deficit),
        "asymptotic_upper_bound": fraction_to_str(Fraction(1) - deficit),
        "rows": rows,
        "compressed_witness_count": len(compressed),
        "compressed_witnesses": [
            {"target": w.target, "rhs": list(w.rhs), "edge": list(w.edge)}
            for w in compressed
        ],
        "witnesses": [
            {"target": w.target, "rhs": list(w.rhs), "edge": list(w.edge)}
            for w in witnesses
        ],
    }


def print_template_report(report: dict) -> None:
    print(f"template moduli: {report['moduli']}")
    print(f"multipliers ({len(report['multipliers'])}): {report['multipliers']}")
    print(f"witnesses found: {report['witness_count']}")
    print(f"signature density: {report['density']}")
    print(f"forced asymptotic deficit: {report['asymptotic_forced_deficit']}")
    print(f"asymptotic upper bound: {report['asymptotic_upper_bound']}")
    if report["compressed_witness_count"]:
        print(f"compressed witnesses: {report['compressed_witness_count']}")
    print("prefix rows:")
    for row in report["rows"]:
        if row["deficit"]:
            print(
                f"  c={row['cutoff']:>4} size={row['prefix_size']:>2} "
                f"keep={row['keep']:>2} omit={row['deficit']:>2} "
                f"contrib={row['band_contribution']} states={row['cover_states']}"
            )


def _template_edge_masks_from_report(report: dict, use_compressed: bool) -> tuple[list[int], list[dict[int, Witness]]]:
    multipliers = [int(x) for x in report["multipliers"]]
    index = {m: i for i, m in enumerate(multipliers)}
    witness_key = "compressed_witnesses" if use_compressed else "witnesses"
    row_edges: list[dict[int, Witness]] = []
    all_by_mask: dict[int, Witness] = {}
    for item in report[witness_key]:
        w = Witness(int(item["target"]), tuple(int(x) for x in item["rhs"]))
        mask = 0
        for x in w.edge:
            mask |= 1 << index[x]
        all_by_mask.setdefault(mask, w)
    for row in report["rows"]:
        n = int(row["prefix_size"])
        prefix_mask = (1 << n) - 1
        active = {
            mask: w
            for mask, w in all_by_mask.items()
            if mask & prefix_mask == mask
        }
        row_edges.append(active)
    return multipliers, row_edges


def build_branch_certificate_for_row(
    n: int,
    keep: int,
    edge_masks: tuple[int, ...],
    max_nodes: int = 0,
) -> dict:
    """Build a finite branch certificate for one prefix hitting statement.

    The certificate proves that every subset of `{0, ..., n-1}` of size
    `keep + 1` contains one of the listed edge masks.  It branches over the next
    vertex, and a branch closes as soon as the partial subset already contains
    an edge.
    """
    nodes: list[dict] = []
    ordered_edges = tuple(sorted(edge_masks, key=lambda e: (e.bit_count(), e)))

    def first_edge(mask: int) -> int:
        for edge in ordered_edges:
            if edge & mask == edge:
                return edge
        return 0

    def add(node: dict) -> int:
        if max_nodes and len(nodes) >= max_nodes:
            raise RuntimeError(f"branch certificate exceeded {max_nodes} nodes")
        nodes.append(node)
        return len(nodes) - 1

    def go(fuel: int, pos: int, need: int, mask: int) -> int:
        edge = first_edge(mask)
        if edge:
            return add({"kind": "edge", "edge": edge})
        if need == 0:
            raise RuntimeError(f"uncovered subset reached: mask={mask}")
        if fuel < need:
            return add({"kind": "short"})
        skip = go(fuel - 1, pos + 1, need, mask)
        take = go(fuel - 1, pos + 1, need - 1, mask | (1 << pos))
        return add({"kind": "branch", "skip": skip, "take": take})

    root = go(n, 0, keep + 1, 0)
    return {"n": n, "keep": keep, "root": root, "nodes": nodes}


def verify_branch_certificate_for_row(cert: dict, edge_masks: tuple[int, ...]) -> tuple[bool, str]:
    nodes = cert["nodes"]
    seen: set[tuple[int, int, int, int]] = set()

    def go(node_id: int, fuel: int, pos: int, need: int, mask: int) -> tuple[bool, str]:
        key = (node_id, fuel, need, mask)
        if key in seen:
            return True, "ok"
        seen.add(key)
        if node_id < 0 or node_id >= len(nodes):
            return False, f"bad node id {node_id}"
        node = nodes[node_id]
        kind = node.get("kind")
        if kind == "edge":
            edge = int(node["edge"])
            if edge not in edge_masks:
                return False, f"unknown edge mask {edge}"
            if edge & mask != edge:
                return False, f"edge leaf not contained: edge={edge}, mask={mask}"
            return True, "ok"
        if kind == "short":
            if fuel < need:
                return True, "ok"
            return False, f"short leaf with fuel={fuel}, need={need}"
        if kind == "branch":
            if need == 0:
                return False, f"branch after complete uncovered mask={mask}"
            if fuel < need:
                return False, f"branch where short leaf would suffice: fuel={fuel}, need={need}"
            ok, msg = go(int(node["skip"]), fuel - 1, pos + 1, need, mask)
            if not ok:
                return ok, msg
            return go(int(node["take"]), fuel - 1, pos + 1, need - 1, mask | (1 << pos))
        return False, f"unknown node kind {kind!r}"

    return go(int(cert["root"]), int(cert["n"]), 0, int(cert["keep"]) + 1, 0)


def build_template_branch_certificate(
    report: dict,
    use_compressed: bool = True,
    max_nodes_per_row: int = 0,
) -> dict:
    multipliers, row_edges = _template_edge_masks_from_report(report, use_compressed)
    rows = []
    for row, active in zip(report["rows"], row_edges, strict=True):
        n = int(row["prefix_size"])
        keep = int(row["keep"])
        if keep + 1 > n:
            continue
        cert = build_branch_certificate_for_row(
            n,
            keep,
            tuple(active),
            max_nodes=max_nodes_per_row,
        )
        ok, msg = verify_branch_certificate_for_row(cert, tuple(active))
        if not ok:
            raise RuntimeError(f"internal branch certificate verification failed: {msg}")
        rows.append(
            {
                "cutoff": int(row["cutoff"]),
                "prefix_size": n,
                "keep": keep,
                "edge_count": len(active),
                "node_count": len(cert["nodes"]),
                "certificate": cert,
            }
        )
    return {
        "problem": 301,
        "kind": "template_prefix_branch_certificate",
        "moduli": report["moduli"],
        "multipliers": multipliers,
        "source": "compressed_witnesses" if use_compressed else "witnesses",
        "witness_count": len(report["compressed_witnesses"] if use_compressed else report["witnesses"]),
        "rows": rows,
    }


def verify_template_branch_certificate(cert: dict, report: dict) -> tuple[bool, str]:
    _, row_edges = _template_edge_masks_from_report(report, cert.get("source") == "compressed_witnesses")
    by_cutoff = {int(row["cutoff"]): tuple(active) for row, active in zip(report["rows"], row_edges, strict=True)}
    for row_cert in cert["rows"]:
        cutoff = int(row_cert["cutoff"])
        if cutoff not in by_cutoff:
            return False, f"unknown cutoff {cutoff}"
        ok, msg = verify_branch_certificate_for_row(row_cert["certificate"], by_cutoff[cutoff])
        if not ok:
            return False, f"cutoff {cutoff}: {msg}"
    return True, "ok"


def summarize_template_branch_certificate(cert: dict) -> None:
    print(f"branch certificate source: {cert['source']}")
    print(f"witnesses: {cert['witness_count']}")
    print("prefix branch rows:")
    for row in cert["rows"]:
        print(
            f"  c={row['cutoff']:>4} size={row['prefix_size']:>2} "
            f"keep={row['keep']:>2} edges={row['edge_count']:>3} nodes={row['node_count']:>7}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max", type=int, default=120, help="finite interval [1,N]")
    parser.add_argument("--max-rhs-size", type=int, default=4, help="maximum RHS size")
    parser.add_argument("--restarts", type=int, default=400, help="greedy restarts")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--progress-every", type=int, default=0)
    parser.add_argument("--emit-certificate", type=Path)
    parser.add_argument("--verify-certificate", type=Path)
    parser.add_argument(
        "--template-moduli",
        help="evaluate a same-signature multiplier grid, e.g. 2:3,3:4,5:2",
    )
    parser.add_argument("--template-include-one", action="store_true")
    parser.add_argument("--template-max-states", type=int, default=0)
    parser.add_argument("--template-compress", action="store_true")
    parser.add_argument("--emit-template", type=Path)
    parser.add_argument("--branch-cert-from-template", type=Path)
    parser.add_argument("--emit-branch-certificate", type=Path)
    parser.add_argument("--verify-branch-certificate", type=Path)
    parser.add_argument("--branch-certificate-use-all-witnesses", action="store_true")
    parser.add_argument("--branch-certificate-max-nodes-per-row", type=int, default=0)
    args = parser.parse_args()

    if args.branch_cert_from_template:
        report = json.loads(args.branch_cert_from_template.read_text(encoding="utf-8"))
        if args.verify_branch_certificate:
            cert = json.loads(args.verify_branch_certificate.read_text(encoding="utf-8"))
            ok, msg = verify_template_branch_certificate(cert, report)
            print(f"branch certificate: {'PASS' if ok else 'FAIL'} ({msg})")
            if ok:
                summarize_template_branch_certificate(cert)
            raise SystemExit(0 if ok else 1)
        cert = build_template_branch_certificate(
            report,
            use_compressed=not args.branch_certificate_use_all_witnesses,
            max_nodes_per_row=args.branch_certificate_max_nodes_per_row,
        )
        summarize_template_branch_certificate(cert)
        if args.emit_branch_certificate:
            args.emit_branch_certificate.write_text(json.dumps(cert, indent=2, sort_keys=True), encoding="utf-8")
            print(f"wrote branch certificate: {args.emit_branch_certificate}")
        raise SystemExit(0)

    if args.template_moduli:
        report = template_report(
            parse_moduli(args.template_moduli),
            args.max_rhs_size,
            args.template_include_one,
            args.template_max_states,
            args.template_compress,
        )
        print_template_report(report)
        if args.emit_template:
            args.emit_template.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
            print(f"wrote template: {args.emit_template}")
        raise SystemExit(0)

    if args.verify_certificate:
        N, _, capacity, chosen = load_certificate(args.verify_certificate)
        ok, msg, total, load = verify_certificate(N, chosen, capacity)
        print(f"certificate: {'PASS' if ok else 'FAIL'} ({msg})")
        if ok:
            summarize(N, chosen, load, total)
        raise SystemExit(0 if ok else 1)

    witnesses = find_witnesses(args.max, args.max_rhs_size, args.progress_every)
    print(f"witnesses found: {len(witnesses)}")
    total, chosen, load = greedy_fractional_pack(args.max, witnesses, args.restarts, args.seed)
    ok, msg, checked_total, checked_load = verify_certificate(args.max, chosen)
    if not ok:
        raise RuntimeError(msg)
    summarize(args.max, chosen, checked_load, checked_total)

    if args.emit_certificate:
        cert = certificate_dict(args.max, args.max_rhs_size, chosen)
        args.emit_certificate.write_text(json.dumps(cert, indent=2, sort_keys=True), encoding="utf-8")
        print(f"wrote certificate: {args.emit_certificate}")


if __name__ == "__main__":
    main()
