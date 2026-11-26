#!/usr/bin/env python3
"""Refine the certified grid by one level.

The unresolved cells of the finest level of the current grid (read from the tile
modules ``Mlc/GridTiles/Part*.lean``) are subdivided and searched again by the
native program ``gridhints`` (``lake build gridhints``, source
``scripts/grid_hints.lean``). The result is a file of hint streams, one line
``R x y count hint...`` per root square, for a grid that is one level deeper. Then

    1. set ``gridFuel`` in ``Mlc/GridParams.lean`` to the printed new value, and
    2. run ``python3 scripts/generate_grid_tiles.py --hints FILE``

to write the tile modules for the kernel check.

    python3 scripts/refine_grid.py --output /tmp/hints.txt

Only inside certificates of at most ``--cap`` steps are used: a certificate costs
the kernel as many steps as it has, and an inside certificate near the border of
a hyperbolic component needs hundreds. Squares that are certified inside or
outside by the earlier grid keep their certificates.
"""

from __future__ import annotations

from pathlib import Path
import argparse
import re
import subprocess
import sys

CHILDREN = ((0, 0), (1, 0), (0, 1), (1, 1))
ROOT_LEVEL = 3
TILE_ENTRY = re.compile(r"\(⟨(-?\d+), (-?\d+), (\d+)⟩,\s*\[([^\]]*)\]\)")


def read_tiles(repo: Path) -> list[tuple[int, int, int, list[int]]]:
    """Tiles of all modules in the order of the depth-first traversal."""
    files = sorted(
        (repo / "Mlc" / "GridTiles").glob("Part*.lean"), key=lambda p: int(p.stem[4:])
    )
    tiles = []
    for path in files:
        for entry in TILE_ENTRY.finditer(path.read_text(encoding="utf-8")):
            hints = [int(v) for v in entry[4].split(",") if v.strip()]
            tiles.append((int(entry[1]), int(entry[2]), int(entry[3]), hints))
    return tiles


def root_streams(tiles: list[tuple[int, int, int, list[int]]]) -> dict[tuple[int, int], list[int]]:
    """The hint stream of every root square, rebuilt from its tiles."""
    cursor = 0

    def build(x: int, y: int, k: int, out: list[int]) -> None:
        nonlocal cursor
        tx, ty, tk, hints = tiles[cursor]
        if (tx, ty, tk) == (x, y, k):
            out.extend(hints)
            cursor += 1
            return
        assert k < tk, f"tile ({tx}, {ty}, {tk}) outside the square ({x}, {y}, {k})"
        out.append(1)
        for dx, dy in CHILDREN:
            build(2 * x + dx, 2 * y + dy, k + 1, out)

    streams = {}
    for x in range(-16, 16):
        for y in range(16):
            out: list[int] = []
            build(x, y, ROOT_LEVEL, out)
            streams[(x, y)] = out
    assert cursor == len(tiles), "unused tiles"
    return streams


def expand(x, y, k, fuel, on_leaf):
    """The stream of an unresolved leaf: its finest cells (``fuel`` levels below) are
    replaced one by one by ``on_leaf``, so that a leaf of a coarser level (all its cells
    stayed unresolved) is refined like the others."""
    if fuel == 0:
        return on_leaf(x, y, k)
    out = [1]
    for dx, dy in CHILDREN:
        out += expand(2 * x + dx, 2 * y + dy, k + 1, fuel - 1, on_leaf)
    return out


def walk(stream, pos, x, y, k, fuel, on_leaf):
    """Rebuild the subtree of ``(x, y, k)``; ``on_leaf`` replaces the finest cells."""
    hint = stream[pos]
    if hint == 0 or (hint == 1 and fuel == 0):
        return expand(x, y, k, fuel, on_leaf), pos + 1
    if hint >= 2:
        return [hint], pos + 1
    out = [1]
    cursor = pos + 1
    for dx, dy in CHILDREN:
        sub, cursor = walk(stream, cursor, 2 * x + dx, 2 * y + dy, k + 1, fuel - 1, on_leaf)
        out += sub
    return out, cursor


def count_cells(stream, pos, fuel):
    """Unresolved finest cells of a subtree, as ``verifyTree`` counts them."""
    hint = stream[pos]
    if hint == 0 or (hint == 1 and fuel == 0):
        return 4**fuel, pos + 1
    if hint >= 2:
        return 0, pos + 1
    total, cursor = 0, pos + 1
    for _ in CHILDREN:
        cells, cursor = count_cells(stream, cursor, fuel - 1)
        total += cells
    return total, cursor


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pmax", type=int, default=8)
    parser.add_argument("--steps", type=int, default=160, help="outside certificates: largest step count")
    parser.add_argument("--cap", type=int, default=160, help="inside certificates: largest step count")
    parser.add_argument("--jobs", type=int, default=22)
    parser.add_argument("--keep", type=Path, help="directory for the search output")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    binary = repo / ".lake" / "build" / "bin" / "gridhints"
    if not binary.exists():
        sys.exit("build the search first: lake build gridhints")
    params = (repo / "Mlc" / "GridParams.lean").read_text(encoding="utf-8")
    fuel = int(re.search(r"def gridFuel : Nat := (\d+)", params).group(1))
    streams = root_streams(read_tiles(repo))

    leaves: list[tuple[int, int, int]] = []

    def collect(x, y, k):
        leaves.append((x, y, k))
        return [0]

    for (x, y), stream in streams.items():
        walk(stream, 0, x, y, ROOT_LEVEL, fuel, collect)
    total = sum(count_cells(s, 0, fuel)[0] for s in streams.values())
    print(f"grid of fuel {fuel}: {total} unresolved cells, {len(leaves)} finest leaves", flush=True)

    work = args.keep or args.output.parent
    work.mkdir(parents=True, exist_ok=True)
    leaf_file = work / "leaves.txt"
    leaf_file.write_text("".join(f"{x} {y} {k}\n" for x, y, k in leaves), encoding="utf-8")
    outputs = [work / f"search_{i}.txt" for i in range(args.jobs)]
    procs = []
    for i, path in enumerate(outputs):
        with path.open("w", encoding="utf-8") as handle:
            procs.append(
                subprocess.Popen(
                    [
                        str(binary), "1", str(args.pmax), str(args.steps), str(args.cap), "0",
                        str(i), str(args.jobs), str(leaf_file),
                    ],
                    text=True,
                    stdout=handle,
                )
            )
    refined: dict[tuple[int, int, int], list[int]] = {}
    for proc, path in zip(procs, outputs):
        if proc.wait() != 0:
            sys.exit("the search failed")
        for line in path.read_text(encoding="utf-8").splitlines():
            fields = line.split()
            if fields and fields[0] == "L":
                hints = [int(v) for v in fields[5:]]
                refined[(int(fields[1]), int(fields[2]), int(fields[3]))] = hints
    assert len(refined) == len(leaves), "missing refinements"

    def replace(x, y, k):
        return refined[(x, y, k)]

    lines = []
    new_total = 0
    for x in range(-16, 16):
        for y in range(16):
            stream, _ = walk(streams[(x, y)], 0, x, y, ROOT_LEVEL, fuel, replace)
            cells, end = count_cells(stream, 0, fuel + 1)
            assert end == len(stream)
            new_total += cells
            lines.append(f"R {x} {y} {cells} " + " ".join(map(str, stream)))
    args.output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(
        f"grid of fuel {fuel + 1}: {new_total} unresolved cells, area "
        f"{2 * new_total / 4 ** (fuel + 1 + ROOT_LEVEL):.4f}; written to {args.output}"
    )
    print(f"next: set gridFuel := {fuel + 1} in Mlc/GridParams.lean and run "
          f"python3 scripts/generate_grid_tiles.py --hints {args.output}")


if __name__ == "__main__":
    main()
