#!/usr/bin/env python3
"""Generate the kernel-check modules of the certified grid.

The search program ``scripts/grid_hints.lean`` subdivides the upper half of the
box ``[-2, 2]^2`` and writes, for every root square of side ``1/8``, a stream of
hints (``0`` unresolved finest cell, ``1`` split, ``h >= 2`` certificate). This
script cuts the streams into *tiles* (subtrees of bounded cost), distributes the
tiles over independent modules ``Mlc/GridTiles/PartN.lean`` (Lake builds
independent modules in parallel) and writes ``Mlc/GridCertified.lean``, which
combines the per-module equalities into the final bound.

The kernel evaluates ``cellsH`` on every tile, so the hints are not trusted: a
wrong certificate only enlarges the count, and the count of every module is
checked by ``decide +kernel``.

    python3 scripts/generate_grid_tiles.py                 # run the search first
    python3 scripts/generate_grid_tiles.py --hints FILE    # reuse its output
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import argparse
import re
import subprocess

CHAINS = 8  # import chains: at most this many modules are checked at once
MODULE_COST = 4000.0  # kernel work of a module, in steps of the model
MODULE_HINTS = 6000  # hints of a module
LADDER = 40  # Lean: ladderLen
PERIODS = 8  # Lean: periodLen
LEAF_COST = 0.02  # a hint without certificate costs little


def decode(hint: int) -> tuple[str, int]:
    """Kind and number of model steps of a hint (see ``Sq.certify``)."""
    if hint == 0:
        return "leaf", 0
    if hint == 1:
        return "split", 0
    if hint % 2 == 0:
        return "out", hint // 2 - 1
    v = hint // 2 - 1
    rest = v // LADDER
    p, n = rest % PERIODS, rest // PERIODS
    return "in", n + p + 1


@dataclass
class Node:
    x: int
    y: int
    k: int
    start: int
    end: int
    cost: float
    cells: int
    children: list["Node"] = field(default_factory=list)


def parse(
    stream: list[int], pos: int, x: int, y: int, k: int, fuel: int
) -> tuple[Node, int]:
    """The subtree below the square ``(x, y, k)``; mirrors ``verifyTree``."""
    kind, steps = decode(stream[pos])
    if kind == "leaf" or (kind == "split" and fuel == 0):
        return Node(x, y, k, pos, pos + 1, LEAF_COST, 4**fuel), pos + 1
    if kind in ("out", "in"):
        return Node(x, y, k, pos, pos + 1, steps + 1.0, 0), pos + 1
    children = []
    cursor = pos + 1
    for dx, dy in ((0, 0), (1, 0), (0, 1), (1, 1)):
        child, cursor = parse(stream, cursor, 2 * x + dx, 2 * y + dy, k + 1, fuel - 1)
        children.append(child)
    node = Node(
        x,
        y,
        k,
        pos,
        cursor,
        LEAF_COST + sum(c.cost for c in children),
        sum(c.cells for c in children),
        children,
    )
    return node, cursor


def collect_tiles(node: Node, limit: float, out: list[Node]) -> None:
    if node.cost <= limit or not node.children:
        out.append(node)
    else:
        for child in node.children:
            collect_tiles(child, limit, out)


def run_search(repo: Path, fuel: int, pmax: int, steps: int, jobs: int) -> list[str]:
    procs = [
        subprocess.Popen(
            [
                "lake", "env", "lean", "--run", "scripts/grid_hints.lean",
                str(fuel), str(pmax), str(steps), str(i), str(jobs),
            ],
            cwd=repo,
            text=True,
            stdout=subprocess.PIPE,
        )
        for i in range(jobs)
    ]
    lines: list[str] = []
    for proc in procs:
        out, _ = proc.communicate()
        if proc.returncode != 0:
            raise RuntimeError("the search failed")
        lines += out.splitlines()
    return lines


def write_if_changed(path: Path, text: str) -> None:
    """Keep the modification time of unchanged files, so that Lake keeps their builds."""
    if not path.exists() or path.read_text(encoding="utf-8") != text:
        path.write_text(text, encoding="utf-8")


def format_list(values: list[int], indent: str) -> str:
    lines, line = [], ""
    for value in values:
        piece = f"{value}, "
        if len(line) + len(piece) > 96:
            lines.append(line.rstrip())
            line = ""
        line += piece
    lines.append(line.rstrip().rstrip(","))
    return ("\n" + indent).join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hints", type=Path, help="output of the search program")
    parser.add_argument("--pmax", type=int, default=8)
    parser.add_argument("--steps", type=int, default=640)
    parser.add_argument("--jobs", type=int, default=20)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    params = (repo / "Mlc" / "GridParams.lean").read_text(encoding="utf-8")
    fuel = int(re.search(r"def gridFuel : Nat := (\d+)", params).group(1))
    if args.hints:
        lines = args.hints.read_text(encoding="utf-8").splitlines()
    else:
        lines = run_search(repo, fuel, args.pmax, args.steps, args.jobs)
    roots: dict[tuple[int, int], tuple[int, list[int]]] = {}
    for line in lines:
        fields = line.split()
        if fields and fields[0] == "R":
            roots[(int(fields[1]), int(fields[2]))] = (
                int(fields[3]),
                [int(v) for v in fields[4:]],
            )
    assert len(roots) == 512, f"expected 512 roots, found {len(roots)}"
    tiles: list[tuple[Node, list[int]]] = []
    total = 0
    for x in range(-16, 16):
        for y in range(16):
            count, stream = roots[(x, y)]
            node, end = parse(stream, 0, x, y, 3, fuel)
            assert end == len(stream), f"unused hints at {x} {y}"
            assert node.cells == count, f"count mismatch at {x} {y}"
            total += count
            found: list[Node] = []
            collect_tiles(node, MODULE_COST, found)
            tiles += [(n, stream[n.start : n.end]) for n in found]
    modules: list[list[tuple[Node, list[int]]]] = [[]]
    cost = 0.0
    hints = 0
    for node, stream in tiles:
        if modules[-1] and (
            cost + node.cost > MODULE_COST or hints + len(stream) > MODULE_HINTS
        ):
            modules.append([])
            cost = 0.0
            hints = 0
        modules[-1].append((node, stream))
        cost += node.cost
        hints += len(stream)
    tile_dir = repo / "Mlc" / "GridTiles"
    tile_dir.mkdir(parents=True, exist_ok=True)
    for old in tile_dir.glob("Part*.lean"):
        if int(old.stem[4:]) >= len(modules):
            old.unlink()
    for index, members in enumerate(modules):
        entries = ",\n  ".join(
            f"(⟨{n.x}, {n.y}, {n.k}⟩,\n    [{format_list(s, '     ')}])"
            for n, s in members
        )
        cells = sum(n.cells for n, _ in members)
        chain_import = (
            f"import Mlc.GridTiles.Part{index - CHAINS}\n" if index >= CHAINS else ""
        )
        write_if_changed(tile_dir / f"Part{index}.lean",
            "import Mlc.GridDefs\n"
            "import Mlc.GridParams\n" + chain_import + "\n"
            "/-!\n"
            "Generated by `scripts/generate_grid_tiles.py`. The tiles are squares with the\n"
            "hint streams of the search program `scripts/grid_hints.lean`; the kernel\n"
            f"verifies every certificate. Modules form {CHAINS} import chains, which bounds\n"
            "the number of kernel checks that run at the same time.\n"
            "-/\n\n"
            "namespace MLC.Certified\n\n"
            f"def partTiles_{index} : List (Sq × List ℕ) :=\n  [{entries}]\n\n"
            "set_option maxRecDepth 100000000 in\n"
            f"theorem part_{index} :\n"
            f"    (partTiles_{index}.map fun p => cellsH (gridDepth - p.1.k) p.1 p.2).sum"
            f" = {cells} := by\n"
            "  decide +kernel\n\n"
            "end MLC.Certified\n",
        )
    count = len(modules)
    imports = "\n".join(f"import Mlc.GridTiles.Part{i}" for i in range(count))
    flat = ",\n     ".join(
        ", ".join(f"partTiles_{i}" for i in range(start, min(start + 6, count)))
        for start in range(0, count, 6)
    )
    lemmas = ", ".join(f"part_{i}" for i in range(count))
    write_if_changed(
        repo / "Mlc" / "GridCertified.lean",
        f"""import Mlc.GridTMCertificate
import Mlc.GridParams
{imports}

/-!
# The checked grid bound

The upper half of the box `[-2, 2]²` is covered by tiles, squares of the dyadic
grid with streams of hints (see `Mlc.GridDefs`, `Sq.certify`). The kernel checks
every certificate in the generated modules `Mlc.GridTiles.Part*` (see
`scripts/generate_grid_tiles.py`), and the soundness theorems of
`Mlc.GridTMCertificate` turn the sum of the unresolved cells into an area bound.
The theorem below is an unconditional upper bound for the area of the set of
parameters of `M` that are not interior points.
-/

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace MLC.Certified

open MeasureTheory

/-- Number of unresolved finest cells of the upper half at depth `gridDepth`. -/
def gridCells : ℕ := {total}

/-- The tiles of all modules, in the order of a depth-first traversal of the root squares. -/
def gridTiles : List (Sq × List ℕ) :=
  List.flatten [{flat}]

set_option maxRecDepth 100000000 in
theorem gridTiles_cover : coverAll gridDepth rootsUp (gridTiles.map Prod.fst) = true := by
  decide +kernel

set_option maxRecDepth 100000000 in
theorem gridTiles_level : ∀ p ∈ gridTiles, p.1.k ≤ gridDepth := by
  decide +kernel

set_option maxRecDepth 100000000 in
theorem gridCells_eq :
    (gridTiles.map fun p => cellsH (gridDepth - p.1.k) p.1 p.2).sum = gridCells := by
  simp only [gridTiles, List.map_flatten, List.sum_flatten, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, {lemmas}]
  decide +kernel

/-- The certified area bound for the non-interior part of the Mandelbrot set. -/
theorem unresolved_volume_le_grid :
    volume Unresolved ≤ ENNReal.ofReal (2 * (gridCells : ℝ) / 4 ^ gridDepth) := by
  have h := unresolved_volume_le_symG gridDepth gridTiles gridTiles_level gridTiles_cover
  rw [gridCells_eq] at h
  have e : 2 * ENNReal.ofReal ((gridCells : ℝ) / 4 ^ gridDepth) =
      ENNReal.ofReal (2 * (gridCells : ℝ) / 4 ^ gridDepth) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rwa [e] at h

end MLC.Certified
""",
    )
    work = sum(n.cost for members in modules for n, _ in members)
    print(
        f"{len(tiles)} tiles in {count} modules; cells {total}; fuel {fuel}; "
        f"estimated kernel work {work:.0f} model steps"
    )


if __name__ == "__main__":
    main()
