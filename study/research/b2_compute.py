#!/usr/bin/env python3
"""Exact checks for the class-two novelty audit; standard library only."""

import argparse
from itertools import product
import json
from pathlib import Path

from b1_compute import (
    abelian, act, inverse, lift_section_pair, power, rank_over_q,
    reduce_word, schreier_generators, section, transition,
)


ONE = (0, 0, 0)
A, B = (1, 0, 0), (0, 1, 0)


def multiply(u, v):
    x, y, z = u
    p, q, r = v
    return x + p, y + q, z + r + x * q


def inv(u):
    x, y, z = u
    return -x, -y, -z + x * y


def heisenberg(word):
    value = ONE
    for letter in word:
        base = A if abs(letter) == 1 else B
        value = multiply(value, base if letter > 0 else inv(base))
    return value


def commutator(u, v):
    return multiply(multiply(multiply(inv(u), inv(v)), u), v)


def free_commutator(u, v):
    return reduce_word(inverse(u) + inverse(v) + u + v)


def reconstruct(u, v):
    x, t, z = u
    y, other_t, w = v
    if t != other_t:
        raise ValueError("The b-exponents of the sections differ")
    return 2 * t, x + y, x + 2 * t * (x + y) - 2 * (z + w)


def leaf_commutator_word(depth):
    if depth == 0:
        return free_commutator((1,), (2,))
    if depth % 2 == 0:
        exponent = 2 ** (depth // 2)
        u, v = power((1,), exponent), power((2,), exponent)
    else:
        u = power((2,), 2 ** ((depth - 1) // 2))
        v = power((1,), 2 ** ((depth + 1) // 2))
    assert all(act(u, leaf) == leaf and act(v, leaf) == leaf
               for leaf in product((0, 1), repeat=depth))
    return free_commutator(u, v)


def orbit_transversal(depth):
    origin = (1,) * depth
    paths, queue = {origin: ()}, [origin]
    for vertex in queue:
        for generator in (1, 2):
            image = act((generator,), vertex)
            if image not in paths:
                paths[image] = paths[vertex] + (generator,)
                queue.append(image)
    assert len(paths) == 2 ** depth
    return paths


def check_reconstruction():
    # Check the displayed polynomial identity, independently of free words.
    domain = [(x, t, z, y, w) for x, t, z, y, w
              in product((-1, 0, 1), repeat=5)]
    for left in domain:
        u, v = (left[0], left[1], left[2]), (left[3], left[1], left[4])
        for right in domain:
            p, q = (right[0], right[1], right[2]), (right[3], right[1], right[4])
            assert reconstruct(multiply(u, p), multiply(v, q)) == multiply(
                reconstruct(u, v), reconstruct(p, q))
    words = [tuple(w) for n in range(3)
             for w in product((1, -1, 2, -2), repeat=n)]
    for u in words:
        for v in words:
            if abelian(u)[1] == abelian(v)[1]:
                lift = lift_section_pair(u, v)
                assert heisenberg(lift) == reconstruct(heisenberg(u), heisenberg(v))


def magnus(word, degree=3):
    """Truncated noncommutative Magnus expansion, with x_i -> 1+X_i."""
    result = {(): 1}
    for letter in word:
        variable = abs(letter)
        factor = {(): 1, (variable,): 1} if letter > 0 else {
            (variable,) * n: (-1) ** n for n in range(degree + 1)}
        new = {}
        for u, a in result.items():
            for v, b in factor.items():
                if len(u + v) <= degree:
                    new[u + v] = new.get(u + v, 0) + a * b
        result = {key: value for key, value in new.items() if value}
    return result


def report():
    check_reconstruction()
    levels = []
    for depth in range(4):
        leaves = list(product((0, 1), repeat=depth))
        _, generators = schreier_generators(depth)
        rows = [[coordinate for leaf in leaves
                 for coordinate in heisenberg(section(word, leaf))[:2]]
                for word in generators]
        rank = rank_over_q(rows)
        # Integral witnesses for each central basis vector; each is a conjugate
        # of a commutator of two elements fixing the full level.
        witness = leaf_commutator_word(depth)
        paths = orbit_transversal(depth)
        for target, path in paths.items():
            conjugate = reduce_word(inverse(path) + witness + path)
            portrait = [heisenberg(section(conjugate, leaf)) for leaf in leaves]
            expected = [(0, 0, 1) if leaf == target else ONE for leaf in leaves]
            assert portrait == expected
            # All ancestor coordinates reconstruct the actual root coordinate.
            values = dict(zip(leaves, portrait))
            for j in reversed(range(depth)):
                for prefix in product((0, 1), repeat=j):
                    values[prefix] = reconstruct(values[prefix + (0,)],
                                                 values[prefix + (1,)])
            assert values[()] == heisenberg(conjugate)
        levels.append({
            "depth": depth,
            "abelian_rank": rank,
            "independent_integral_commutator_witnesses": len(paths),
            "hirsch_length": rank + len(paths),
        })
    relation = free_commutator((2,), (1, 2, -1))
    assert transition(relation, 0) == ((), 0)
    assert transition(relation, 1) == ((), 1)
    expansion = magnus(relation)
    assert all(len(key) == 3 for key in expansion if key)
    assert {key: value for key, value in expansion.items() if key} == {
        (2, 1, 2): 2, (2, 2, 1): -1, (1, 2, 2): -1}
    return {
        "convention": "(x,y,z)(u,v,w)=(x+u,y+v,z+w+x*v)",
        "levels": levels,
        "class_three_boundary_word": "commutator(b, a*b*a^-1)",
        "boundary_magnus_degree_three": {
            "".join("A" if x == 1 else "B" for x in key): value
            for key, value in expansion.items() if key},
        "scope": "exact finite checks; the all-depth proof and source reduction are separate",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = json.loads(json.dumps(report()))
    if args.check:
        expected = json.loads(Path(__file__).with_name(
            "B2_calculations.json").read_text(encoding="utf-8"))
        assert result == expected
        print("Verified reconstruction, integral central witnesses, ranks and Magnus boundary.")
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
