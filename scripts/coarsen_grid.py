#!/usr/bin/env python3
"""Replace refined regions of the certified grid by single coarser certificates.

A square that the grid subdivided because one certificate failed may still have
an inside certificate that needs many steps of the model. Near the border of a
hyperbolic component the number of steps grows like the inverse of the distance,
and a coarse square costs the kernel about as much as a fine one while covering
four times (sixteen times) the area. So the search of ``refine_grid.py``, which
caps the steps per level, leaves coarse squares subdivided that an equal cap
scaled by the area would certify.

This program takes the squares of the chosen levels that hold no outside
certificate and at least one unresolved cell, and searches an inside certificate
for each of them with ``gridhints`` (mode 2, so that squares with an escaping
center cost nothing). A square of level ``k`` may use ``mu * 4^(finest - k)``
steps of the model, which makes every accepted certificate worth at least the
area per step of a cell of the finest level with ``mu`` steps. Each success
replaces the whole subtree of its square. The result is a file of hint streams
in the format of ``refine_grid.py``; run

    python3 scripts/generate_grid_tiles.py --hints FILE

to write the modules for the kernel check.

    python3 scripts/coarsen_grid.py --output /tmp/hints.txt --levels 10,11 --mu 60
"""

from __future__ import annotations

from pathlib import Path
import argparse
import subprocess
import sys

from refine_grid import CHILDREN, ORDER, ROOT_LEVEL, count_cells, read_tiles, root_streams, steps_of


def collect(streams, levels):
    """Squares of the levels without an outside certificate and with unresolved cells."""
    found = {k: [] for k in levels}

    def visit(stream, pos, x, y, k, fuel):
        hint = stream[pos]
        if hint == 0 or (hint == 1 and fuel == 0):
            return pos + 1, False, 4**fuel
        if hint >= 2:
            return pos + 1, hint % 2 == 0, 0
        cursor = pos + 1
        outside, unresolved = False, 0
        for dx, dy in CHILDREN:
            cursor, out, cells = visit(stream, cursor, 2 * x + dx, 2 * y + dy, k + 1, fuel - 1)
            outside = outside or out
            unresolved += cells
        if k in found and not outside and unresolved:
            found[k].append((x, y))
        return cursor, outside, unresolved

    for xy in ORDER:
        fuel, stream = streams[xy]
        visit(stream, 0, xy[0], xy[1], ROOT_LEVEL, fuel)
    return found


def skip(stream, pos, fuel):
    """The position after the subtree that starts at ``pos``."""
    if stream[pos] != 1 or fuel == 0:
        return pos + 1
    cursor = pos + 1
    for _ in CHILDREN:
        cursor = skip(stream, cursor, fuel - 1)
    return cursor


def rewrite(stream, pos, x, y, k, fuel, chosen, out):
    """Copy the subtree at ``pos`` to ``out``, replacing the squares of ``chosen``."""
    hint = stream[pos]
    if (x, y, k) in chosen:
        out.append(chosen[(x, y, k)])
        return skip(stream, pos, fuel)
    if hint != 1 or fuel == 0:
        out.append(hint)
        return pos + 1
    out.append(1)
    cursor = pos + 1
    for dx, dy in CHILDREN:
        cursor = rewrite(stream, cursor, 2 * x + dx, 2 * y + dy, k + 1, fuel - 1, chosen, out)
    return cursor


def run_search(binary, squares, level, cap, pmax, jobs, work, reuse):
    """Hints of the squares that have an inside certificate within ``cap`` steps."""
    outputs = [work / f"coarse_k{level}_{i}.txt" for i in range(jobs)]
    if not reuse:
        leaf_file = work / f"coarse_k{level}.txt"
        leaf_file.write_text("".join(f"{x} {y} {level}\n" for x, y in squares), encoding="utf-8")
        procs = []
        for i, path in enumerate(outputs):
            with path.open("w", encoding="utf-8") as handle:
                procs.append(
                    subprocess.Popen(
                        [
                            str(binary), "0", str(pmax), str(cap), str(cap),
                            "2", str(i), str(jobs), str(leaf_file),
                        ],
                        text=True,
                        stdout=handle,
                    )
                )
        for proc in procs:
            if proc.wait() != 0:
                sys.exit("the search failed")
    found = {}
    for path in outputs:
        for line in path.read_text(encoding="utf-8").splitlines():
            fields = line.split()
            if len(fields) >= 6 and fields[0] == "L" and int(fields[5]) >= 2:
                found[(int(fields[1]), int(fields[2]))] = int(fields[5])
    return found


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--levels", default="10,11", help="levels of the squares, coarsest first")
    parser.add_argument("--mu", type=int, default=60, help="steps allowed at the finest level")
    parser.add_argument("--pmax", type=int, default=8)
    parser.add_argument("--jobs", type=int, default=22)
    parser.add_argument("--keep", type=Path, help="directory for the search files")
    parser.add_argument("--reuse", action="store_true", help="read the search files of --keep")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    binary = repo / ".lake" / "build" / "bin" / "gridhints"
    if not binary.exists() and not args.reuse:
        sys.exit("build the search first: lake build gridhints")

    streams = root_streams(read_tiles(repo))
    finest = ROOT_LEVEL + max(fuel for fuel, _ in streams.values())
    levels = sorted(int(v) for v in args.levels.split(","))
    work = args.keep or args.output.parent
    work.mkdir(parents=True, exist_ok=True)
    candidates = collect(streams, levels)

    chosen: dict[tuple[int, int, int], int] = {}
    for level in levels:
        cap = args.mu * 4 ** (finest - level)
        squares = [
            (x, y)
            for x, y in candidates[level]
            if not any(
                (x >> (level - j), y >> (level - j), j) in chosen for j in levels if j < level
            )
        ]
        found = run_search(binary, squares, level, cap, args.pmax, args.jobs, work, args.reuse)
        for (x, y), hint in found.items():
            chosen[(x, y, level)] = hint
        steps = sum(steps_of(h) for h in found.values())
        print(
            f"level {level}: {len(squares)} squares searched with up to {cap} steps, "
            f"{len(found)} certified ({steps} steps of the model)",
            flush=True,
        )

    lines = []
    new_total = old_total = 0
    for xy in ORDER:
        fuel, stream = streams[xy]
        old_total += count_cells(stream, 0, fuel)[0] * 4 ** (16 - ROOT_LEVEL - fuel)
        out: list[int] = []
        end = rewrite(stream, 0, xy[0], xy[1], ROOT_LEVEL, fuel, chosen, out)
        assert end == len(stream)
        cells, used = count_cells(out, 0, fuel)
        assert used == len(out)
        new_total += cells * 4 ** (16 - ROOT_LEVEL - fuel)
        lines.append(f"R {xy[0]} {xy[1]} {fuel} {cells} " + " ".join(map(str, out)))
    args.output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    steps = sum(steps_of(h) for h in chosen.values())
    print(
        f"area bound {2 * old_total / 4 ** 16:.4f} -> {2 * new_total / 4 ** 16:.4f} with "
        f"{len(chosen)} new certificates ({steps} steps of the model); written to {args.output}\n"
        f"next: python3 scripts/generate_grid_tiles.py --hints {args.output}"
    )


if __name__ == "__main__":
    main()
