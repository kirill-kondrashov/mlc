#!/usr/bin/env python3
"""Generate the kernel-check modules of the certified grid.

The search program ``scripts/grid_hints.lean`` (driven by ``scripts/refine_grid.py``)
subdivides the unresolved cells of the upper half of the box ``[-2, 2]^2`` and
writes, for every root square of side ``1/8``, a stream of hints (``0``
unresolved finest cell, ``1`` split, ``h >= 2`` certificate). This script cuts
the streams into *tiles* (subtrees of bounded cost) and writes independent
modules ``Mlc/GridTiles/G<block>_<part>.lean``: a block is a run of four
consecutive root squares, which share one depth, and a heavy block is split into
several modules. The modules of a block depend only on the streams of its
roots, so refining some blocks leaves the other modules unchanged and Lake
keeps their builds. ``Mlc/GridCertified.lean`` combines the per-module equalities
into the final bound; it works in chunks of ``CHUNK`` modules, because ``simp``
and the kernel recurse once per element of a list and overflow the stack on a list
of thousands of modules, and its two membership checks are Boolean ``all`` loops
for the same reason. The elaboration of its 12000 bridge theorems needs a thread
stack larger than the default of 8 MB; the lakefile sets it with ``weakLeanArgs``,
which keep the traces of the modules.

The kernel evaluates ``cellsH`` on every tile, so the hints are not trusted: a
wrong certificate only enlarges the count, and the count of every module is
checked by ``decide +kernel``.

    python3 scripts/generate_grid_tiles.py --hints FILE    # FILE: output of refine_grid.py
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import argparse

BLOCK = 4  # consecutive root squares of a block
SCALE = 16  # the weights of the final bound count cells of side 2^-SCALE
MODULE_COST = 4000.0  # kernel work of a module, in steps of the model
MODULE_HINTS = 6000  # hints of a module
CHUNK = 500  # modules per chunk of the aggregator
LADDER = 40  # Lean: ladderLen
PERIODS = 8  # Lean: periodLen
LEAF_COST = 0.02  # a hint without certificate costs little
ROOT_LEVEL = 3
CHILDREN = ((0, 0), (1, 0), (0, 1), (1, 1))


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
    for dx, dy in CHILDREN:
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


def read_roots(path: Path) -> dict[tuple[int, int], tuple[int, int, list[int]]]:
    """Root squares of the file ``R x y fuel count hint...``: fuel, count and stream."""
    roots = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        fields = line.split()
        if fields and fields[0] == "R":
            roots[(int(fields[1]), int(fields[2]))] = (
                int(fields[3]),
                int(fields[4]),
                [int(v) for v in fields[5:]],
            )
    assert len(roots) == 512, f"expected 512 roots, found {len(roots)}"
    return roots


def module_text(block: int, part: int, depth: int, entries: list[tuple[Node, list[int]]]) -> str:
    body = ",\n  ".join(
        f"(⟨{n.x}, {n.y}, {n.k}⟩,\n    [{format_list(s, '     ')}])" for n, s in entries
    )
    cells = sum(n.cells for n, _ in entries)
    name = f"{block}_{part}"
    return (
        "import Mlc.GridDefs\n\n"
        "/-!\n"
        "Generated by `scripts/generate_grid_tiles.py`. The tiles are squares with the\n"
        "hint streams of the search program `scripts/grid_hints.lean`; the kernel\n"
        f"verifies every certificate. Block {block}, part {part}: the unresolved cells are\n"
        f"counted at depth {depth}.\n"
        "-/\n\n"
        "namespace MLC.Certified\n\n"
        f"def tiles_{name} : List (Sq × List ℕ) :=\n  [{body}]\n\n"
        "set_option maxRecDepth 100000000 in\n"
        f"theorem part_{name} :\n"
        f"    (tiles_{name}.map fun p => cellsH ({depth} - p.1.k) p.1 p.2).sum"
        f" = {cells} := by\n"
        "  decide +kernel\n\n"
        "end MLC.Certified\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--hints", type=Path, required=True, help="output of scripts/refine_grid.py"
    )
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    roots = read_roots(args.hints)
    order = [(x, y) for x in range(-16, 16) for y in range(16)]
    tile_dir = repo / "Mlc" / "GridTiles"
    tile_dir.mkdir(parents=True, exist_ok=True)
    modules: list[tuple[int, int, int, list[tuple[Node, list[int]]]]] = []
    total = 0
    tiles_count = 0
    work = 0.0
    for block in range(len(order) // BLOCK):
        members = order[BLOCK * block : BLOCK * (block + 1)]
        fuels = {roots[xy][0] for xy in members}
        assert len(fuels) == 1, f"block {block} mixes depths {fuels}"
        fuel = fuels.pop()
        depth = ROOT_LEVEL + fuel
        tiles: list[tuple[Node, list[int]]] = []
        for x, y in members:
            _, count, stream = roots[(x, y)]
            node, end = parse(stream, 0, x, y, ROOT_LEVEL, fuel)
            assert end == len(stream), f"unused hints at {x} {y}"
            assert node.cells == count, f"count mismatch at {x} {y}"
            total += count * 4 ** (SCALE - depth)
            found: list[Node] = []
            collect_tiles(node, MODULE_COST, found)
            tiles += [(n, stream[n.start : n.end]) for n in found]
        parts: list[list[tuple[Node, list[int]]]] = [[]]
        cost = 0.0
        hints = 0
        for node, stream in tiles:
            if parts[-1] and (
                cost + node.cost > MODULE_COST or hints + len(stream) > MODULE_HINTS
            ):
                parts.append([])
                cost = 0.0
                hints = 0
            parts[-1].append((node, stream))
            cost += node.cost
            hints += len(stream)
        for part, entries in enumerate(parts):
            modules.append((block, part, depth, entries))
        tiles_count += len(tiles)
        work += sum(n.cost for n, _ in tiles)
    wanted = set()
    for block, part, depth, entries in modules:
        path = tile_dir / f"G{block}_{part}.lean"
        wanted.add(path.name)
        write_if_changed(path, module_text(block, part, depth, entries))
    for old in tile_dir.glob("*.lean"):
        if old.name not in wanted:
            old.unlink()
    names = [f"{block}_{part}" for block, part, _, _ in modules]
    imports = "\n".join(f"import Mlc.GridTiles.G{name}" for name in names)
    # The aggregator works in chunks: `simp` and the kernel recurse once per module of a
    # list, which overflows the stack on thousands of modules.
    chunks = [
        list(range(start, min(start + CHUNK, len(names))))
        for start in range(0, len(names), CHUNK)
    ]

    def chunk_pairs(ids: list[int]) -> str:
        return ",\n     ".join(
            ", ".join(
                f"({modules[i][2]}, tiles_{names[i]})" for i in ids[start : start + 6]
            )
            for start in range(0, len(ids), 6)
        )

    def module_cells(i: int) -> int:
        return sum(n.cells for n, _ in modules[i][3])

    parts = "\n\n".join(
        f"set_option maxRecDepth 100000 in\n"
        f"noncomputable def gridPart_{k} : List TileModule :=\n  [{chunk_pairs(ids)}]"
        for k, ids in enumerate(chunks)
    )
    union = " ++ ".join(f"gridPart_{k}" for k in range(len(chunks)))
    bridges = "\n\n".join(
        f"theorem w_{names[i]} :\n"
        f"    moduleWeight {SCALE} ({modules[i][2]}, tiles_{names[i]}) =\n"
        f"      {module_cells(i)} * 4 ^ ({SCALE} - {modules[i][2]}) :=\n"
        f"  (moduleWeight_eq {SCALE} {modules[i][2]} tiles_{names[i]}).trans\n"
        f"    (congrArg (· * 4 ^ ({SCALE} - {modules[i][2]})) part_{names[i]})"
        for i in range(len(names))
    )
    sums = "\n\n".join(
        f"set_option maxRecDepth 100000 in\n"
        f"theorem gridSum_{k} :\n"
        f"    ((gridPart_{k}).map (moduleWeight gridDepth)).sum = "
        f"{sum(module_cells(i) * 4 ** (SCALE - modules[i][2]) for i in ids)} := by\n"
        f"  simp only [gridPart_{k}, gridDepth, List.map_cons, List.map_nil, List.sum_cons,\n"
        f"    List.sum_nil, {', '.join('w_' + names[i] for i in ids)}]\n"
        f"  decide +kernel"
        for k, ids in enumerate(chunks)
    )
    chunk_lemmas = ", ".join(f"gridSum_{k}" for k in range(len(chunks)))
    write_if_changed(
        repo / "Mlc" / "GridCertified.lean",
        f"""import Mlc.GridTMCertificate
{imports}

/-!
# The checked grid bound

The upper half of the box `[-2, 2]²` is covered by tiles, squares of the dyadic
grid with streams of hints (see `Mlc.GridDefs`, `Sq.certify`). The tiles are
grouped in modules, each with the depth at which its unresolved cells are
counted. The kernel checks every certificate in the generated modules
`Mlc.GridTiles.G*` (see `scripts/generate_grid_tiles.py`), and the soundness
theorems of `Mlc.GridTMCertificate` turn the weighted sum of the unresolved
cells into an area bound. The theorem below is an unconditional upper bound for
the area of the set of parameters of `M` that are not interior points.
-/

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace MLC.Certified

open MeasureTheory

/-- The cells of the weights have side `2 ^ (-gridDepth)`. -/
def gridDepth : ℕ := {SCALE}

/-- Number of unresolved cells of the upper half, in units of the cells of side
`2 ^ (-gridDepth)`: a cell counted at a coarser depth weighs `4 ^ (gridDepth - depth)`. -/
def gridCells : ℕ := {total}

{parts}

/-- The modules of tiles, each with the depth at which its cells are counted, in the
order of a depth-first traversal of the root squares. -/
noncomputable def gridModules : List TileModule :=
  {union}

set_option maxRecDepth 100000000 in
theorem gridModules_cover :
    coverAll 20 rootsUp ((moduleTiles gridModules).map Prod.fst) = true := by
  decide +kernel

-- The two checks below run over a list of thousands of modules: a Boolean `all` is
-- evaluated by the kernel in a loop, while `decide` on a bounded quantifier recurses
-- once per module and overflows the stack.
set_option maxRecDepth 100000000 in
theorem gridModules_level_check :
    gridModules.all (fun m => m.2.all fun p => decide (p.1.k ≤ m.1)) = true := by
  decide +kernel

theorem gridModules_level : ∀ m ∈ gridModules, ∀ p ∈ m.2, p.1.k ≤ m.1 := by
  intro m hm p hp
  have h := List.all_eq_true.mp gridModules_level_check m hm
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

set_option maxRecDepth 100000000 in
theorem gridModules_depth_check :
    gridModules.all (fun m => decide (m.1 ≤ gridDepth)) = true := by
  decide +kernel

theorem gridModules_depth : ∀ m ∈ gridModules, m.1 ≤ gridDepth := by
  intro m hm
  exact of_decide_eq_true (List.all_eq_true.mp gridModules_depth_check m hm)

/-- The weights of the modules, from the counts that the kernel checked in the modules. -/
{bridges}

-- The weights of the chunks of modules.
{sums}

theorem gridCells_eq : (gridModules.map (moduleWeight gridDepth)).sum = gridCells := by
  simp only [gridModules, gridCells, List.map_append, List.sum_append, {chunk_lemmas}] <;>
    decide +kernel

/-- The certified area bound for the non-interior part of the Mandelbrot set. -/
theorem unresolved_volume_le_grid :
    volume Unresolved ≤ ENNReal.ofReal (2 * (gridCells : ℝ) / 4 ^ gridDepth) := by
  have h := unresolved_volume_le_symM gridDepth 20 gridModules gridModules_level
    gridModules_depth gridModules_cover
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
    print(
        f"{tiles_count} tiles in {len(modules)} modules; weighted cells {total} "
        f"(side 2^-{SCALE}); estimated kernel work {work:.0f} model steps"
    )


if __name__ == "__main__":
    main()
