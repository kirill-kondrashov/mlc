#!/usr/bin/env python3
"""Exact calibrations of the conditional modulus bridge; no MLC instance."""

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from graphlib import CycleError, TopologicalSorter
import json
from pathlib import Path


@dataclass(frozen=True)
class Edge:
    source: str
    target: str
    alpha: Q
    beta: Q


def certificate(vertices, edges):
    """Return the sufficient eventual lower bound, or None for a zero cycle."""
    if not vertices or len(set(vertices)) != len(vertices):
        raise ValueError("Vertices must be nonempty and distinct")
    predecessors = {v: set() for v in vertices}
    for e in edges:
        if e.source not in predecessors or e.target not in predecessors:
            raise ValueError("Unknown endpoint")
        if e.alpha <= 0 or e.beta < 0:
            raise ValueError("Need alpha > 0 and beta >= 0")
        if e.beta == 0:
            predecessors[e.target].add(e.source)
    try:
        tuple(TopologicalSorter(predecessors).static_order())
    except CycleError:
        return None
    positive = [e.beta for e in edges if e.beta > 0]
    if not positive:
        return None
    a = min([Q(1)] + [e.alpha for e in edges])
    return min(positive) * a ** (len(vertices) - 1)


def check_all_finite_paths(vertices, edges, mu):
    """Check the bound on all paths up to length 10, starting with b=0."""
    frontier = {(v, Q(0)) for v in vertices}
    for length in range(1, 11):
        frontier = {(e.target, e.alpha * b + e.beta)
                    for v, b in frontier for e in edges if e.source == v}
        if length >= len(vertices):
            assert all(b >= mu for _, b in frontier)


def report():
    vertices = ["A", "B"]
    edges = [Edge("A", "B", Q(1, 2), Q(0)),
             Edge("B", "A", Q(1), Q(1, 3))]
    mu = certificate(vertices, edges)
    assert mu == Q(1, 6)
    check_all_finite_paths(vertices, edges, mu)
    # Branching paths and more than one consecutive zero edge.
    branching = [Edge("A", "B", Q(1, 2), Q(0)),
                 Edge("B", "C", Q(1, 3), Q(0)),
                 Edge("A", "C", Q(2), Q(0)),
                 Edge("C", "A", Q(1, 4), Q(2, 5)),
                 Edge("C", "B", Q(1), Q(1, 7))]
    branch_mu = certificate(["A", "B", "C"], branching)
    assert branch_mu == Q(1, 112)
    check_all_finite_paths(["A", "B", "C"], branching, branch_mu)
    assert certificate(["A"], [Edge("A", "A", Q(1, 2), Q(0))]) is None
    assert certificate(vertices, [Edge("A", "B", Q(1), Q(0)),
                                  Edge("B", "A", Q(1), Q(0))]) is None
    # A rejected graph may still have a divergent positive solution.
    assert certificate(["A"], [Edge("A", "A", Q(2), Q(0))]) is None
    assert all(Q(2) ** j >= 1 for j in range(20))
    values = [Q(0)]
    for j in range(10):
        e = edges[j % 2]
        values.append(e.alpha * values[-1] + e.beta)
    # Annulus moduli in units log(2)/(2*pi); exact telescoping identity.
    annuli = [Q(1, 2) ** (j + 1) for j in range(16)]
    assert sum(annuli) == 1 - Q(1, 2) ** 16
    # Constant dynamic bound with exponentially growing parameter distortion.
    assert sum(Q(1, 2) ** j for j in range(16)) == 2 - Q(1, 2) ** 15
    return {
        "scope": "Finite rational calibrations only; no quadratic return class or MLC instance",
        "reset_cycle": {"vertices": vertices, "eventual_lower_bound": str(mu),
                        "values_from_zero": [str(x) for x in values]},
        "branching_lower_bound": str(branch_mu),
        "zero_self_loop_rejected": True,
        "two_edge_zero_cycle_rejected": True,
        "expanding_zero_loop_rejected_but_divergence_possible": True,
        "z_squared_annuli": {"normalized_first_moduli": [str(x) for x in annuli[:6]],
                             "normalized_infinite_sum": "1",
                             "intersection": "closed unit disk"},
        "growing_distortion": {"b_j": "1", "K_j": "2^j", "infinite_sum": "2"},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = report()
    if args.check:
        expected = json.loads(Path(__file__).with_name(
            "MLC_bridge_calibration.json").read_text(encoding="utf-8"))
        assert result == expected
        print("Verified graph bounds, zero-cycle obstructions and annulus/distortion calibrations.")
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
