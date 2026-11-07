#!/usr/bin/env python3
"""Exact algebra and marked-point counts for the B3 audit, not an attractor."""

import argparse
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path

import b3_compute as initial


def phi(s, t):
    return t*t, (s*s-t*t)/(s*s-1)


def family(point, x):
    if point is None:
        return Q(1)
    return None if point*point == 1 else (point*point-x)/(point*point-1)


def report():
    sample = [Q(-3), Q(-2), Q(-1, 2), Q(1, 2), Q(2), Q(3)]
    checked = 0
    for s, t in product(sample, repeat=2):
        if s == t or s == -t:
            continue
        x, y = phi(s, t)
        assert x not in (0, 1) and y not in (0, 1) and x != y
        assert family(Q(0), x) == x
        assert family(s, x) == y
        assert family(t, x) == 0
        assert family(None, x) == 1
        assert family(Q(1), x) is None
        assert t*t == x
        assert s*s == (y-x)/(y-1)
        checked += 1

    # Check the marked fixed point in Q(lambda), independently of floats.
    s0 = initial.neg(initial.LAMBDA)
    t0 = initial.add(initial.ONE, s0)
    s2, t2 = initial.multiply(s0, s0), initial.multiply(t0, t0)
    phi_second = initial.multiply(
        initial.add(s2, initial.neg(t2)),
        initial.inverse(initial.add(s2, initial.neg(initial.ONE))))
    assert t2 == s0 and phi_second == t0

    s, t, radius = Q(101, 100), Q(-99, 100), Q(1, 4)
    x, y = phi(s, t)
    lemniscate_radius = (1-x)/radius
    assert (x, y, lemniscate_radius) == (Q(9801, 10000), Q(400, 201), Q(199, 2500))
    assert 0 < lemniscate_radius < 1
    assert abs(x-1) < radius < 1 and abs(y-1) > radius
    assert abs(s*s-1) < lemniscate_radius and s > 0
    assert abs(t*t-1) < lemniscate_radius and t < 0
    assert abs(Q(0)*Q(0)-1) > lemniscate_radius

    distributions = []
    for critical_values_inside, marked_in_disks in ((0, 2), (2, 3)):
        for first_disk in range(marked_in_disks+1):
            second_disk = marked_in_disks-first_disk
            essential_count = sum(2 <= n <= 3 for n in (first_disk, second_disk))
            assert essential_count <= 1
            if critical_values_inside == 2:
                assert essential_count == 1
            distributions.append({
                "critical_values_on_two_point_side": critical_values_inside,
                "marked_points_in_two_disks": [first_disk, second_disk],
                "essential_preimage_count": essential_count,
                "essential_degree_if_present": 1 if essential_count else None,
            })
    distributions.append({
        "critical_values_on_two_point_side": 1,
        "marked_points_in_connected_disk": 2,
        "essential_preimage_count": 1,
        "essential_degree_if_present": 2,
    })
    return {
        "sample_family_identities_checked": checked,
        "moduli_cover_degree": 4,
        "fixed_marking": ["-lambda", "1-lambda"],
        "obstructed_hurwitz_representative_cover": {
            "s": str(s), "t": str(t), "x": str(x), "y": str(y),
            "target_curve_center": "1", "target_curve_radius": str(radius),
            "source_lemniscate_radius": str(lemniscate_radius),
            "target_two_point_side_labels": ["a1", "b1"],
            "source_positive_disk_labels": ["a1", "b1"],
            "source_negative_disk_labels": ["a2"],
            "source_annulus_labels": ["a0", "b0"],
            "boundary_degrees": [1, 1],
        },
        "all_marked_point_distributions": distributions,
        "scope": (
            "exact algebra and possible marked-point counts only; "
            "Hurwitz markings, arbitrary parent chains and rho>=1 are proved in the Markdown; "
            "no full dynamical-biset recursion or global curve attractor computed"
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = report()
    if args.check:
        expected = json.loads(Path(__file__).with_name(
            "B3_audit_data.json").read_text(encoding="utf-8"))
        assert result == expected
        print("Verified moduli identities, fixed marking, Levy-cover data and component counts.")
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
