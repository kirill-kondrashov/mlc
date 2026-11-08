#!/usr/bin/env python3
"""Exact computations for the worked B1 example; Python standard library only.

The base group is FREE on a,b. Words are never identified using relations
of its faithful tree-action quotient. Products act on words on the right.
"""

import argparse
from collections import deque
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from pathlib import Path


def reduce_word(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def inverse(word):
    return tuple(-letter for letter in reversed(word))


# s*g = section(g,s) * s^g, in the left-free biset.
# a=(1,b)(01), b=(1,a). Inverse transitions are derived by inversion.
POSITIVE = {
    1: (((), (2,)), (1, 0)),
    2: (((), (1,)), (0, 1)),
}


def letter_step(letter, digit):
    labels, perm = POSITIVE[abs(letter)]
    if letter > 0:
        return labels[digit], perm[digit]
    preimage = perm.index(digit)
    return inverse(labels[preimage]), preimage


@lru_cache(maxsize=None)
def transition(word, digit):
    label = ()
    position = digit
    for letter in word:
        state, position = letter_step(letter, position)
        label = reduce_word(label + state)
    return label, position


def section(word, vertex):
    for digit in vertex:
        word, _ = transition(word, digit)
    return word


def abelian(word):
    return tuple(sum((1 if x > 0 else -1) for x in word if abs(x) == i)
                 for i in (1, 2))


def display(word):
    return " ".join({1: "a", -1: "a^-1", 2: "b", -2: "b^-1"}[x]
                    for x in word) or "1"


def power(word, exponent):
    if exponent < 0:
        return power(inverse(word), -exponent)
    return reduce_word(word * exponent)


def lift_section_pair(left, right):
    """Lift a pair with equal b-exponent to H_1, as in the novelty audit."""
    exponent = abelian(left)[1]
    if abelian(right)[1] != exponent:
        raise ValueError("The sections must have equal b-exponent")
    result = ()
    for word, lift_a in ((left, (1, 2, -1)), (right, (2,))):
        b_exponent = 0
        for letter in word:
            if abs(letter) == 2:
                b_exponent += 1 if letter > 0 else -1
            else:
                conjugator = power((1, 1), b_exponent)
                lift = power(lift_a, 1 if letter > 0 else -1)
                result = reduce_word(result + conjugator + lift
                                     + inverse(conjugator))
    return reduce_word(result + power((1, 1), exponent))


def act(word, vertex):
    if not vertex:
        return ()
    label, image = transition(word, vertex[0])
    return (image,) + act(label, vertex[1:])


def act_direct(word, vertex):
    """Independent letter-by-letter action; no word-transition folding."""
    for letter in word:
        if vertex:
            label, image = letter_step(letter, vertex[0])
            vertex = (image,) + act_direct(label, vertex[1:])
    return vertex


def permutation(word, depth):
    vertices = list(product((0, 1), repeat=depth))
    indices = {v: i for i, v in enumerate(vertices)}
    return tuple(indices[act(word, v)] for v in vertices)


def compose_right(p, q):
    return tuple(q[i] for i in p)


def schreier_generators(depth):
    identity = tuple(range(2 ** depth))
    generator_images = {g: permutation((g,), depth) for g in (1, 2)}
    representatives = {identity: ()}
    queue = deque([identity])
    while queue:
        p = queue.popleft()
        for g in (1, 2):
            q = compose_right(p, generator_images[g])
            if q not in representatives:
                representatives[q] = representatives[p] + (g,)
                queue.append(q)
    words = []
    for p, word in representatives.items():
        for g in (1, 2):
            q = compose_right(p, generator_images[g])
            candidate = reduce_word(word + (g,) + inverse(representatives[q]))
            if candidate:
                assert permutation(candidate, depth) == identity
                words.append(candidate)
    assert len(words) == len(representatives) + 1
    return len(representatives), words


def rank_over_q(rows):
    basis = {}
    for values in rows:
        row = list(map(Fraction, values))
        for pivot in sorted(basis):
            if row[pivot]:
                multiplier = row[pivot]
                row = [x - multiplier * y for x, y in zip(row, basis[pivot])]
        pivot = next((i for i, x in enumerate(row) if x), None)
        if pivot is not None:
            divisor = row[pivot]
            basis[pivot] = [x / divisor for x in row]
    return len(basis)


def rank_mod_p(rows, prime):
    basis = {}
    for values in rows:
        row = [x % prime for x in values]
        for pivot in sorted(basis):
            multiplier = row[pivot]
            row = [(x - multiplier * y) % prime
                   for x, y in zip(row, basis[pivot])]
        pivot = next((i for i, x in enumerate(row) if x), None)
        if pivot is not None:
            inverse_pivot = pow(row[pivot], -1, prime)
            basis[pivot] = [x * inverse_pivot % prime for x in row]
    return len(basis)


def haar_relations(depth):
    leaves = list(product((0, 1), repeat=depth))
    rows = []
    for j in range(depth):
        coordinate = 1 if (depth - j - 1) % 2 == 0 else 0
        for vertex in product((0, 1), repeat=j):
            row = [0] * (2 * len(leaves))
            for i, leaf in enumerate(leaves):
                if leaf[:j] == vertex:
                    row[2 * i + coordinate] = 1 if leaf[j] == 0 else -1
            rows.append(row)
    return rows


def check_identities():
    short = [tuple(w) for n in range(3)
             for w in product((1, -1, 2, -2), repeat=n)]
    for u in short:
        for v in short:
            for s in (0, 1):
                left, middle = transition(u, s)
                right, end = transition(v, middle)
                assert transition(reduce_word(u + v), s) == (
                    reduce_word(left + right), end)
            if abelian(u)[1] == abelian(v)[1]:
                lift = lift_section_pair(u, v)
                assert transition(lift, 0) == (reduce_word(u), 0)
                assert transition(lift, 1) == (reduce_word(v), 1)
    for n in range(4):
        for word in product((1, -1, 2, -2), repeat=n):
            word = tuple(word)
            for depth in range(5):
                for vertex in product((0, 1), repeat=depth):
                    assert act(word, vertex) == act_direct(word, vertex)
                    assert act(word + inverse(word), vertex) == vertex
    commutator = (-1, -2, 1, 2)
    assert transition(commutator, 0) == ((-2, -1, 2), 0)
    assert transition(commutator, 1) == ((1,), 1)


def report(max_depth):
    commutator = (-1, -2, 1, 2)
    levels = []
    for depth in range(max_depth + 1):
        index, generators = schreier_generators(depth)
        vertices = [v for j in range(depth + 1)
                    for v in product((0, 1), repeat=j)]
        rows = [[coordinate for v in vertices
                 for coordinate in abelian(section(word, v))]
                for word in generators]
        rank = rank_over_q(rows)
        leaf_offset = 2 * (2 ** depth - 1)
        leaf_rows = [row[leaf_offset:] for row in rows]
        leaf_rank = rank_over_q(leaf_rows)
        assert rank == leaf_rank
        relations = haar_relations(depth)
        assert len(relations) == 2 ** depth - 1
        for i, relation in enumerate(relations):
            assert sum(x * x for x in relation) > 0
            for earlier in relations[:i]:
                assert sum(x * y for x, y in zip(relation, earlier)) == 0
            for row in leaf_rows:
                assert sum(x * y for x, y in zip(relation, row)) == 0
        modular = {str(p): rank_mod_p(rows, p) for p in (101, 103)}
        assert all(value == rank for value in modular.values())
        levels.append({
            "depth": depth,
            "level_action_image_order": index,
            "schreier_basis_size": len(generators),
            "portrait_coordinates": 2 * len(vertices),
            "rational_portrait_rank": rank,
            "rational_leaf_portrait_rank": leaf_rank,
            "independent_haar_constraints": len(relations),
            "ranks_mod_primes": modular,
        })
    return {
        "base_group": "free group F(a,b); not the faithful tree-action quotient",
        "convention": "right action; (gh)|s = (g|s)(h|s^g)",
        "recursion": {"a": "(1,b)(01)", "b": "(1,a)"},
        "commutator": {
            "word": display(commutator),
            "permutation": list(permutation(commutator, 1)),
            "sections": [display(transition(commutator, s)[0]) for s in (0, 1)],
            "section_abelianizations": [
                abelian(transition(commutator, s)[0]) for s in (0, 1)],
        },
        "first_level_generators": [{
            "word": display(word),
            "sections": [display(transition(word, s)[0]) for s in (0, 1)],
            "portrait": [coordinate for v in ((), (0,), (1,))
                         for coordinate in abelian(section(word, v))],
        } for word in ((2,), (1, 1), (1, 2, -1))],
        "finite_portraits": levels,
        "scope": "finite exact computations; no infinite-rank formula or novelty claim",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-depth", type=int, default=3, choices=range(4))
    parser.add_argument("--check", action="store_true",
                        help="also compare with the committed calculation report")
    args = parser.parse_args()
    check_identities()
    result = json.loads(json.dumps(report(args.max_depth)))
    if args.check:
        expected = json.loads(Path(__file__).with_name(
            "B1_calculations.json").read_text(encoding="utf-8"))
        assert result == expected, "calculation report differs; inspect before replacing"
        print("Verified identities, fiber lifts, direct tree actions, exact ranks and report.")
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
