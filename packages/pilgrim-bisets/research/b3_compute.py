#!/usr/bin/env python3
"""Exact initial data for the five-puncture candidate; no curve-attractor claim."""

import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


def number(a=0, b=0):
    """a + b*lambda in Q[lambda]/(lambda^2-lambda+1)."""
    return Fraction(a), Fraction(b)


ZERO, ONE, LAMBDA = number(), number(1), number(0, 1)
INFINITY = None


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def neg(x):
    return -x[0], -x[1]


def multiply(x, y):
    a, b = x
    c, d = y
    return a*c - b*d, a*d + b*c + b*d


def inverse(x):
    a, b = x
    norm = a*a + a*b + b*b
    if norm == 0:
        raise ZeroDivisionError
    return (a+b)/norm, -b/norm


def evaluate(point):
    if point is INFINITY:
        return ONE
    square = multiply(point, point)
    denominator = add(square, neg(ONE))
    return INFINITY if denominator == ZERO else multiply(
        add(square, LAMBDA), inverse(denominator))


def report():
    assert add(add(multiply(LAMBDA, LAMBDA), neg(LAMBDA)), ONE) == ZERO
    minus_lambda = neg(LAMBDA)
    one_minus_lambda = add(ONE, minus_lambda)
    lambda_minus_one = neg(one_minus_lambda)
    marked = [ZERO, minus_lambda, one_minus_lambda, INFINITY, ONE]
    names = ["0", "-lambda", "1-lambda", "infinity", "1"]
    labels = dict(zip(marked, names))
    assert len(labels) == 5
    assert [evaluate(p) for p in marked] == [
        minus_lambda, one_minus_lambda, ZERO, ONE, INFINITY]
    critical = {ZERO, INFINITY}
    fibers = [
        (ZERO, [(one_minus_lambda, 1), (lambda_minus_one, 1)]),
        (minus_lambda, [(ZERO, 2)]),
        (one_minus_lambda, [(minus_lambda, 1), (LAMBDA, 1)]),
        (INFINITY, [(ONE, 1), (neg(ONE), 1)]),
        (ONE, [(INFINITY, 2)]),
    ]
    labels.update({lambda_minus_one: "lambda-1", LAMBDA: "lambda", neg(ONE): "-1"})
    for target, points in fibers:
        assert sum(multiplicity for _, multiplicity in points) == 2
        for point, multiplicity in points:
            assert evaluate(point) == target
            assert multiplicity == (2 if point in critical else 1)
    full_preimage = {point for _, points in fibers for point, _ in points}
    assert full_preimage == set(marked) | {lambda_minus_one, LAMBDA, neg(ONE)}
    assert len(full_preimage) == 8
    invariant_sizes = set()
    for size in range(6):
        for subset in combinations(marked, size):
            if all(evaluate(p) in subset for p in subset):
                invariant_sizes.add(size)
    assert invariant_sizes == {0, 2, 3, 5}
    iterates = []
    for n in range(1, 13):
        fixed_degrees = []
        for initial in marked:
            point, degree = initial, 1
            for _ in range(n):
                degree *= 2 if point in critical else 1
                point = evaluate(point)
            if point == initial:
                fixed_degrees.append(degree)
        maximum = max([1] + fixed_degrees)
        expected = max([1] + ([2**(n//2)] if n % 2 == 0 else [])
                       + ([2**(n//3)] if n % 3 == 0 else []))
        assert maximum == expected
        assert 2*maximum-2 < 2**n
        iterates.append({"n": n, "degree": 2**n,
                         "max_fixed_local_degree": maximum,
                         "two_polynomial_gluing_upper_bound": 2*maximum-2})
    # An explicit nonfixed critical point of every F^n, n >= 2.
    assert lambda_minus_one not in marked and evaluate(lambda_minus_one) == ZERO
    faces = [(0, 2, 1), (0, 3, 2), (4, 0, 1),
             (4, 1, 2), (4, 2, 3), (4, 3, 0)]
    edges = defaultdict(list)
    for face_index, triangle in enumerate(faces):
        for u, v in zip(triangle, triangle[1:] + triangle[:1]):
            edges[tuple(sorted((u, v)))].append((face_index, 1 if u < v else -1))
    assert len(edges) == 9 and 5-len(edges)+len(faces) == 2
    assert all(len(uses) == 2 and sum(sign for _, sign in uses) == 0
               for uses in edges.values())
    neighbors = defaultdict(set)
    for uses in edges.values():
        first, second = (face for face, _ in uses)
        neighbors[first].add(second)
        neighbors[second].add(first)
    visited, queue = {0}, [0]
    for face in queue:
        for neighbor in neighbors[face] - visited:
            visited.add(neighbor)
            queue.append(neighbor)
    assert len(visited) == 6
    return {
        "field": "Q(lambda), lambda^2-lambda+1=0; Im(lambda)>0",
        "map": "F(z)=(z^2+lambda)/(z^2-1)",
        "critical_cycles": [["0", "-lambda", "1-lambda"], ["infinity", "1"]],
        "fibers_over_postcritical_set": [
            {"target": labels[target], "points": [
                {"point": labels[point], "local_degree": multiplicity}
                for point, multiplicity in points]} for target, points in fibers],
        "forward_invariant_subset_sizes": sorted(invariant_sizes),
        "iterate_checks": iterates,
        "triangulation": {"vertices": ["0", "1", "1-lambda", "-lambda", "infinity"],
                          "oriented_faces": faces, "edges": sorted(edges),
                          "dual_spine_rank": len(edges)-len(faces)+1},
        "scope": "exact initial algebra and triangulation checks; no biset sections or curve attractor computed",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = json.loads(json.dumps(report()))
    if args.check:
        expected = json.loads(Path(__file__).with_name(
            "B3_initial_data.json").read_text(encoding="utf-8"))
        assert result == expected
        print("Verified critical cycles, fibers, iterate degree bounds and triangulation.")
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
