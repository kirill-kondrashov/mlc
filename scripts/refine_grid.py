#!/usr/bin/env python3
"""Refine the certified grid by one level, block by block.

The unresolved cells of the finest level of the selected blocks (read from the
tile modules ``Mlc/GridTiles``) are subdivided and searched again by the native
program ``gridhints`` (``lake build gridhints``, source ``scripts/grid_hints.lean``).
The result is a file of hint streams, one line ``R x y fuel count hint...`` per
root square, in which the selected blocks are one level deeper. Then run

    python3 scripts/generate_grid_tiles.py --hints FILE

to write the tile modules for the kernel check. The modules of the blocks that
are not selected stay unchanged, so Lake builds only the refined blocks.

    python3 scripts/refine_grid.py --output /tmp/hints.txt                  # all blocks
    python3 scripts/refine_grid.py --output /tmp/hints.txt --blocks 40:80   # blocks 40..79
    python3 scripts/refine_grid.py --keep DIR --plan 3                      # balanced ranges

A block is a run of four consecutive root squares (``BLOCK`` in the generator).
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
BLOCK = 4
LADDER = 40
PERIODS = 8
TILE_ENTRY = re.compile(r"\(⟨(-?\d+), (-?\d+), (\d+)⟩,\s*\[([^\]]*)\]\)")
MODULE_DEPTH = re.compile(r"cellsH \((\d+) - p\.1\.k\)")
ORDER = [(x, y) for x in range(-16, 16) for y in range(16)]


def read_tiles(repo: Path) -> list[tuple[int, int, int, int, list[int]]]:
    """Tiles ``(x, y, k, depth, hints)`` of all modules in depth-first order."""
    directory = repo / "Mlc" / "GridTiles"
    blocks = sorted(
        directory.glob("G*_*.lean"),
        key=lambda p: tuple(int(v) for v in p.stem[1:].split("_")),
    )
    legacy = sorted(directory.glob("Part*.lean"), key=lambda p: int(p.stem[4:]))
    tiles = []
    if blocks:
        for path in blocks:
            text = path.read_text(encoding="utf-8")
            depth = int(MODULE_DEPTH.search(text).group(1))
            for entry in TILE_ENTRY.finditer(text):
                hints = [int(v) for v in entry[4].split(",") if v.strip()]
                tiles.append((int(entry[1]), int(entry[2]), int(entry[3]), depth, hints))
        return tiles
    params = (repo / "Mlc" / "GridParams.lean").read_text(encoding="utf-8")
    depth = ROOT_LEVEL + int(re.search(r"def gridFuel : Nat := (\d+)", params).group(1))
    for path in legacy:
        for entry in TILE_ENTRY.finditer(path.read_text(encoding="utf-8")):
            hints = [int(v) for v in entry[4].split(",") if v.strip()]
            tiles.append((int(entry[1]), int(entry[2]), int(entry[3]), depth, hints))
    return tiles


def root_streams(tiles) -> dict[tuple[int, int], tuple[int, list[int]]]:
    """Fuel and hint stream of every root square, rebuilt from its tiles."""
    cursor = 0

    def build(x: int, y: int, k: int, out: list[int]) -> int:
        nonlocal cursor
        tx, ty, tk, depth, hints = tiles[cursor]
        if (tx, ty, tk) == (x, y, k):
            out.extend(hints)
            cursor += 1
            return depth
        assert k < tk, f"tile ({tx}, {ty}, {tk}) outside the square ({x}, {y}, {k})"
        out.append(1)
        depths = {build(2 * x + dx, 2 * y + dy, k + 1, out) for dx, dy in CHILDREN}
        assert len(depths) == 1, "a root square mixes depths"
        return depths.pop()

    streams = {}
    for x, y in ORDER:
        out: list[int] = []
        depth = build(x, y, ROOT_LEVEL, out)
        streams[(x, y)] = (depth - ROOT_LEVEL, out)
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


def steps_of(hint: int) -> int:
    """Kernel steps of a certificate hint (see ``Sq.certify``)."""
    if hint % 2 == 0:
        return hint // 2 - 1
    v = hint // 2 - 1
    rest = v // LADDER
    return rest // PERIODS + rest % PERIODS + 1 + 1


def parse_search(paths) -> dict[tuple[int, int, int], list[int]]:
    refined = {}
    for path in paths:
        for line in Path(path).read_text(encoding="utf-8").splitlines():
            fields = line.split()
            if fields and fields[0] == "L":
                refined[(int(fields[1]), int(fields[2]), int(fields[3]))] = [
                    int(v) for v in fields[5:]
                ]
    return refined


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--blocks", help="first:last+1 block indices to refine (default: all)")
    parser.add_argument("--pmax", type=int, default=8)
    parser.add_argument("--steps", type=int, default=160, help="outside certificates: largest step count")
    parser.add_argument("--cap", type=int, default=160, help="inside certificates: largest step count")
    parser.add_argument("--jobs", type=int, default=22)
    parser.add_argument("--keep", type=Path, help="directory for the search files")
    parser.add_argument("--reuse", action="store_true", help="read the search files of --keep")
    parser.add_argument("--plan", type=int, help="print this many balanced block ranges and stop")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    streams = root_streams(read_tiles(repo))
    nblocks = len(ORDER) // BLOCK
    first, last = 0, nblocks
    if args.blocks:
        first, last = (int(v) for v in args.blocks.split(":"))
    selected = {
        ORDER[i] for i in range(BLOCK * first, BLOCK * last)
    }
    fuels = {fuel for fuel, _ in streams.values()}
    print(f"depths of the roots: {sorted(ROOT_LEVEL + f for f in fuels)}", flush=True)

    def finest(roots):
        leaves = []

        def collect(x, y, k):
            leaves.append((x, y, k))
            return [0]

        for xy in roots:
            fuel, stream = streams[xy]
            walk(stream, 0, xy[0], xy[1], ROOT_LEVEL, fuel, collect)
        return leaves

    work = args.keep or (args.output.parent if args.output else Path("."))
    work.mkdir(parents=True, exist_ok=True)
    if args.plan or args.reuse:
        refined = parse_search(sorted(work.glob("search_*.txt")))
    else:
        leaves = finest([xy for xy in ORDER if xy in selected])
        total = sum(
            count_cells(streams[xy][1], 0, streams[xy][0])[0] for xy in selected
        )
        print(f"selected blocks {first}:{last}: {len(leaves)} finest cells", flush=True)
        binary = repo / ".lake" / "build" / "bin" / "gridhints"
        if not binary.exists():
            sys.exit("build the search first: lake build gridhints")
        leaf_file = work / "leaves.txt"
        leaf_file.write_text("".join(f"{x} {y} {k}\n" for x, y, k in leaves), encoding="utf-8")
        outputs = [work / f"search_{i}.txt" for i in range(args.jobs)]
        procs = []
        for i, path in enumerate(outputs):
            with path.open("w", encoding="utf-8") as handle:
                procs.append(
                    subprocess.Popen(
                        [
                            str(binary), "1", str(args.pmax), str(args.steps), str(args.cap),
                            "0", str(i), str(args.jobs), str(leaf_file),
                        ],
                        text=True,
                        stdout=handle,
                    )
                )
        for proc in procs:
            if proc.wait() != 0:
                sys.exit("the search failed")
        refined = parse_search(outputs)

    if args.plan:
        cost = []
        for b in range(nblocks):
            steps = 0
            for xy in ORDER[BLOCK * b : BLOCK * (b + 1)]:
                for leaf in finest([xy]):
                    for hint in refined.get(leaf, [1, 0, 0, 0, 0])[1:]:
                        if hint >= 2:
                            steps += steps_of(hint)
            cost.append(steps)
        goal = sum(cost) / args.plan
        ranges, start, acc = [], 0, 0.0
        for b, steps in enumerate(cost):
            acc += steps
            if acc >= goal and len(ranges) < args.plan - 1:
                ranges.append((start, b + 1, acc))
                start, acc = b + 1, 0.0
        ranges.append((start, nblocks, acc))
        for a, b, steps in ranges:
            print(f"--blocks {a}:{b}  new kernel steps {steps:.0f}")
        return

    lines = []
    new_total = 0
    for xy in ORDER:
        fuel, stream = streams[xy]
        if xy in selected:
            missing = []

            def replace(x, y, k):
                if (x, y, k) not in refined:
                    missing.append((x, y, k))
                    return [1, 0, 0, 0, 0]
                return refined[(x, y, k)]

            stream, _ = walk(stream, 0, xy[0], xy[1], ROOT_LEVEL, fuel, replace)
            assert not missing, f"no search result for {missing[:3]}"
            fuel += 1
        cells, end = count_cells(stream, 0, fuel)
        assert end == len(stream)
        new_total += cells * 4 ** (16 - ROOT_LEVEL - fuel)
        lines.append(f"R {xy[0]} {xy[1]} {fuel} {cells} " + " ".join(map(str, stream)))
    args.output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(
        f"area bound of the new grid {2 * new_total / 4 ** 16:.4f}; written to {args.output}\n"
        f"next: python3 scripts/generate_grid_tiles.py --hints {args.output}"
    )


if __name__ == "__main__":
    main()
