#!/usr/bin/env python3
"""The proof of `MLC.mlc_conjecture` as one 2D figure: a spine with branches.

The spine climbs from the kernel axioms (bottom) to the statement of MLC (the
head). Its vertebrae are milestone theorems of the Lean library; the order is
checked against the declaration graph, so a vertebra never uses a higher one.
Every other declaration hangs on the branch of the lowest vertebra that needs
it (grouped by file). The tips of the branches are the open problems of the
root, the targets of Dudko's programme that are not formalized, the kernel
axioms, and the checked machinery.

The figure is laid out here, so the page needs no layout code: it is an inline
SVG with about sixty elements. The script of the page only adds hover, search,
the side panel, zoom and the theme.
"""

from __future__ import annotations

import html
import json
import math
import re
import subprocess
import textwrap
from dataclasses import dataclass, field
from pathlib import Path

from progress_report import PROGRESS_CSS, PROGRESS_ROUTES
from programme import (
    ANNULUS_ROOTS,
    COLLAR_ROOTS,
    CRITERION_ROOTS,
    DIMENSION_ROOTS,
    LEVEL_GEOMETRY_ROOTS,
    LEVEL_JUMP_ROOTS,
    LEVEL_TRANSFER_ROOTS,
    MULTIPLICITY_ROOTS,
    NEST_ROOTS,
    PEANO_ROOTS,
    RECTANGLE_ROOTS,
    STACKING_ROOTS,
    CLASSES,
    GROTZSCH_ROOT,
    LEMMAS,
    PARALLEL_ROOT,
    PROGRAMME_ROOT,
    PSEUDO_SIEGEL,
    PULLBACK_ROOT,
    QUASI_INVARIANCE_ROOTS,
    SHARPNESS_ROOT,
    TAIL_ROOTS,
    VIRTUAL_SHRINKING_ROOTS,
    check_catalogue,
    class_shares,
    open_lemmas,
    proved_lemmas,
)

# Geometry of the figure, in user units of the SVG.
WIDTH = 1500.0
CENTER = WIDTH / 2
VERTEBRA_W = 300.0
NODE_W = 204.0
LINK_GAP = 44.0
CHAIN_GAP = 24.0
ROW_PAD = 20.0
MIN_LEAF_H = 62.0
HEAD_W, HEAD_H = 500.0, 128.0
MIN_BUD = 3  # smaller groups of declarations are listed in the vertebra panel only
TILE_NAME = re.compile(
    r"^MLC\.Certified\.(?:(?:tiles|part|w)_\d+_\d+|(?:gridPart|gridSum)_\d+)$"
)
# Declaration kinds of the Lean source, grouped for the counts of the figure. In Lean
# `lemma` and `theorem` declare the same thing, so both count as theorems.
KIND_GROUP = {
    "theorem": "thm",
    "lemma": "thm",
    "def": "def",
    "abbrev": "def",
    "instance": "def",
    "structure": "str",
    "inductive": "str",
    "class": "str",
    "axiom": "ax",
}
STAT_KEYS = ("thm", "def", "str", "ax")
KIND_WORDS = {
    "thm": ("theorem", "theorems"),
    "def": ("definition", "definitions"),
    "str": ("structure", "structures"),
    "ax": ("axiom", "axioms"),
}
GRID_FILES = {
    "Mlc/GridCertified.lean": "tiles",
    "Mlc/GridTiles/*": "tiles",
    "Mlc/GridTMCertificate.lean": "soundness",
    "Mlc/GridCertificate.lean": "soundness",
    "Mlc/GridDefs.lean": "models",
}


@dataclass(frozen=True)
class Vertebra:
    key: str
    title: str
    lean: str
    claim: str


# Bottom to top. Each vertebra is a theorem or definition of the library.
SPINE = (
    Vertebra(
        "budgets",
        "Return budgets",
        "MLC.Research.ReturnBudget.unbounded_of_linearLossControl",
        "A return budget with linear loss has unbounded total cost.",
    ),
    Vertebra(
        "nests",
        "Connected nests",
        "MLC.Research.ParameterRealization.locallyConnectedAt",
        "A connected parameter nest with a divergent budget gives "
        "local connectivity at c.",
    ),
    Vertebra(
        "candidates",
        "Candidate systems",
        "MLC.Research.CandidateSystem.locallyConnectedSpace_of_realization_coverage",
        "Realization and coverage make M locally connected.",
    ),
    Vertebra(
        "phase",
        "Phase–parameter transfer",
        "MLC.Research.VirtualPhaseParameter.parameterSeparationEstimate",
        "A separation estimate of a virtual hull transfers to the parameter nest.",
    ),
    Vertebra(
        "control",
        "A priori control",
        "MLC.Research.VirtualMoleculeAPrioriControl.parameterRealization",
        "A priori control data give a parameter realization.",
    ),
    Vertebra(
        "virtual",
        "Virtual realization",
        "MLC.Research.CandidateSystem.withVirtualMolecule_realization",
        "The realization of Problem 4.3 extends to every virtual a priori control.",
    ),
    Vertebra(
        "completion",
        "Completion ⇔ coverage",
        "MLC.Research.CandidateSystem.withVirtualMolecule_coverage_iff_completion",
        "Global coverage is the virtual-Molecule completion, "
        "with the checked area envelope.",
    ),
    Vertebra(
        "dudko",
        "Dudko's frontier",
        "MLC.mlc_of_problem43_problem44",
        "Problems 4.3 and 4.4 imply local connectivity of M.",
    ),
    Vertebra(
        "root",
        "Root input",
        "MLC.RootInput.locallyConnectedSpace",
        "RootInput, the pair of Problems 4.3 and 4.4, makes M locally connected.",
    ),
    Vertebra(
        "category",
        "Categorical form",
        "MLC.Categorical.categorical_mlc_conjecture",
        "The categorical statement MLCConjecture holds under RootInput.",
    ),
)
HEAD_LEAN = "MLC.mlc_conjecture"
# Results that no vertebra needs: checked in Lean, but not part of the proof of MLC. They
# hang on the programme's open targets and must be connected to the graph like the rest.
SIDE_ROOTS = (
    "MLC.Research.unresolved_volume_eq_zero_of_porous",
    PROGRAMME_ROOT,
    SHARPNESS_ROOT,
    GROTZSCH_ROOT,
    PARALLEL_ROOT,
    PULLBACK_ROOT,
    *TAIL_ROOTS,
    *ANNULUS_ROOTS,
    *RECTANGLE_ROOTS,
    *NEST_ROOTS,
    *MULTIPLICITY_ROOTS,
    *VIRTUAL_SHRINKING_ROOTS,
    *QUASI_INVARIANCE_ROOTS,
    *COLLAR_ROOTS,
    *LEVEL_JUMP_ROOTS,
    *LEVEL_TRANSFER_ROOTS,
    *STACKING_ROOTS,
    *DIMENSION_ROOTS,
    *PEANO_ROOTS,
    *CRITERION_ROOTS,
    *LEVEL_GEOMETRY_ROOTS,
)

# Titles of the support branches, by file; a pair (vertebra, file) overrides them.
BUD_TITLES = {
    "Mlc/Research/ReturnBudget.lean": (
        "Return-budget arithmetic",
        "weights, costs, harmonic divergence",
    ),
    "Mlc/Research/ParameterGeometry.lean": (
        "Connected parameter nests",
        "kernel, closure basis, separation",
    ),
    "Mlc/Research/Programme.lean": (
        "Candidate systems",
        "eligibility, realization, coverage",
    ),
    "Mlc/FilledJuliaConnected.lean": (
        "Filled Julia sets",
        "compact and connected for c ∈ M",
    ),
    "Mlc/Research/ConnectedHull.lean": (
        "Minimal connected hulls",
        "directed intersections of continua",
    ),
    "Mlc/MandelbrotCompact.lean": (
        "The set M",
        "compact, M ⊆ B̄(0,2), B(0,¼) ⊆ int M",
    ),
    "Mlc/Research/VirtualMolecule.lean": (
        "Virtual Julia nests",
        "first returns, carriers, phase parameters",
    ),
    "Mlc/CategoricalRoot.lean": (
        "Categorical statement",
        "TopCat object, MLCConjecture",
    ),
}
BUD_OVERRIDES = {
    ("control", "Mlc/Research/VirtualMolecule.lean"): (
        "A priori control package",
        "hull in J, partial invariance, budget",
    ),
    ("completion", "Mlc/Research/VirtualMolecule.lean"): (
        "Residual set and area envelope",
        "outer area ≤ 4π, ≤ 63π/16, ≤ grid bound",
    ),
}
GRID_TITLES = {
    "tiles": ("Kernel-checked tiles", "certified cells and their count"),
    "soundness": ("Soundness of the certificates", "Taylor models, disks, area"),
    "models": ("Fixed-point models", "orbit enclosures and the search"),
}

OPEN_PROBLEMS = {
    "MLC.Problem43PseudoSiegelAPrioriBoundsData": {
        "title": "Problem 4.3",
        "sub": "Route 1 · pseudo-Siegel a priori bounds",
        "text": (
            "Dudko, Problem 4.3: establish pseudo-Siegel a priori bounds in the "
            "remaining unbounded satellite quasi-linear cases. In Lean it is a "
            "candidate system together with the realization of its admissible "
            "returns, an explicit hypothesis of mlc_conjecture."
        ),
        "route": "1",
    },
    "MLC.Problem44VirtualMoleculeData": {
        "title": "Problem 4.4",
        "sub": "Routes 2, 3 · virtual Molecule",
        "text": (
            "Dudko, Interpolation Problem 4.4: develop a Virtual Molecule version "
            "of the Near-Degenerate Regime. In Lean it is the virtual-Molecule "
            "completion of the candidate system, an explicit hypothesis of "
            "mlc_conjecture."
        ),
        "route": "2",
    },
}


def route(identifier: str) -> dict[str, object]:
    return next(r for r in PROGRESS_ROUTES if r["id"] == identifier)


def prior(identifier: str) -> str:
    return f"{float(route(identifier)['probability']) * 100:.0f}%"


def new_stats() -> dict[str, int]:
    """Counts of declarations: by kind, in all (n), generated (gen*), and lines of source."""
    return {
        **{key: 0 for key in STAT_KEYS},
        "n": 0,
        "gen": 0,
        "gen_thm": 0,
        "gen_def": 0,
        "lines": 0,
    }


def add_stats(total: dict[str, int], names, fq_index) -> dict[str, int]:
    """Add the declarations of ``names`` to ``total``; generated ones count apart from lines."""
    for name in names:
        decl = fq_index[name]
        group = KIND_GROUP.get(decl.kind, "def")
        total[group] += 1
        total["n"] += 1
        if TILE_NAME.match(name):
            total["gen"] += 1
            total["gen_thm" if group == "thm" else "gen_def"] += 1
        else:
            total["lines"] += max(1, decl.end_line - decl.line + 1)
    return total


STAT_WORDS = {"thm": "thm", "def": "def", "str": "struct"}


def stat_line(stats: dict[str, int]) -> str:
    """``17 thm · 2 def``: the non-zero counts by kind."""
    parts = [f"{stats[key]:,} {word}" for key, word in STAT_WORDS.items() if stats[key]]
    return " · ".join(parts)


@dataclass
class Node:
    id: str
    kind: str  # head | vertebra | bud | tip | ground
    cat: str  # checked | num | open | informal | axiom | spine | head
    title: str
    sub: str = ""
    text: str = ""
    lean: str = ""
    file: str = ""
    line: int = 0
    count: int = 0
    parent: str = ""
    side: int = 0
    below: bool = False  # drawn under its parent instead of beyond it
    stats: dict[str, int] = field(default_factory=lambda: new_stats())
    level: dict[str, int] = field(default_factory=lambda: new_stats())
    stat: str = ""
    children: list["Node"] = field(default_factory=list)
    members: list[dict[str, object]] = field(default_factory=list)
    x: float = 0.0
    y: float = 0.0
    w: float = NODE_W
    h: float = 0.0
    lines: list[str] = field(default_factory=list)
    sublines: list[str] = field(default_factory=list)


def wrap(text: str, width: int, limit: int = 3) -> list[str]:
    lines = textwrap.wrap(text, width=width, break_long_words=True) or [""]
    if len(lines) > limit:
        lines = lines[:limit]
        lines[-1] = lines[-1].rstrip(".,; ") + "…"
    return lines


def closure(edges: dict[str, set[str]], start: str) -> set[str]:
    seen = {start}
    stack = [start]
    while stack:
        current = stack.pop()
        for nxt in edges.get(current, ()):
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    return seen


def docstring(repo_root: Path, file: str, line: int) -> str:
    """The docstring directly above a declaration, flattened to one paragraph."""
    path = repo_root / file
    if not path.is_file() or line <= 0:
        return ""
    lines = path.read_text(encoding="utf-8").splitlines()
    index = line - 2
    while index >= 0 and lines[index].lstrip().startswith("@["):
        index -= 1
    if index < 0 or not lines[index].rstrip().endswith("-/"):
        return ""
    end = index
    while index >= 0 and "/--" not in lines[index]:
        index -= 1
    if index < 0:
        return ""
    body = " ".join(lines[index : end + 1])
    body = body.replace("/--", "").replace("-/", "")
    return re.sub(r"\s+", " ", body).strip()


def repository_url(repo_root: Path) -> tuple[str, str]:
    """GitHub base URL and the commit of the working tree, for source links."""
    try:
        remote = subprocess.run(
            ["git", "remote", "get-url", "origin"],
            cwd=repo_root, check=True, text=True, capture_output=True,
        ).stdout.strip()
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo_root, check=True, text=True, capture_output=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "", ""
    found = re.search(r"github[^:/]*[:/]+([^/:]+)/([^/.]+?)(?:\.git)?$", remote)
    if not found:
        return "", ""
    return f"https://github.com/{found.group(1)}/{found.group(2)}", commit


def short(name: str) -> str:
    return name[4:] if name.startswith("MLC.") else name


def member_row(decl) -> dict[str, object]:
    kind = "theorem" if decl.kind == "lemma" else decl.kind
    return {"n": short(decl.fq_name), "k": kind, "f": decl.file, "l": decl.line}


def check_spine(fq_index, edges, reachable: set[str]) -> list[set[str]]:
    """Every milestone exists, is reachable from the head, and no vertebra uses a higher one."""
    names = [v.lean for v in SPINE] + [HEAD_LEAN]
    for name in names:
        if name not in fq_index:
            raise RuntimeError(f"Spine milestone not found: {name}")
        if name not in reachable:
            raise RuntimeError(f"Spine milestone is not reachable from the root: {name}")
    closures = [closure(edges, name) for name in names]
    for low, name in enumerate(names):
        for high in range(low + 1, len(names)):
            if names[high] in closures[low]:
                raise RuntimeError(
                    f"Spine order violated: {name} depends on the higher milestone {names[high]}"
                )
    return closures


def build_model(fq_index, edges, reachable, axioms, metrics, repo_root: Path) -> dict[str, object]:
    closures = check_spine(fq_index, edges, reachable)
    spine_names = {v.lean for v in SPINE} | {HEAD_LEAN}
    open_names = set(OPEN_PROBLEMS)

    owner_index: dict[str, int] = {}
    for name in sorted(reachable):
        if name in spine_names:
            continue
        for index, members in enumerate(closures):
            if name in members:
                owner_index[name] = index
                break

    grid = metrics.get("grid") or {}
    tile_modules = len(list((repo_root / "Mlc" / "GridTiles").glob("G*.lean")))
    base_url, commit = repository_url(repo_root)

    nodes: dict[str, Node] = {}
    extras: list[Node] = []

    def make(node: Node) -> Node:
        nodes[node.id] = node
        return node

    def from_decl(name: str) -> tuple[str, int, str]:
        decl = fq_index[name]
        return decl.file, decl.line, docstring(repo_root, decl.file, decl.line)

    head_decl = fq_index[HEAD_LEAN]
    head = make(
        Node(
            id="head",
            kind="head",
            cat="head",
            title="MLC",
            sub="M is locally connected",
            text=(
                "The theorem mlc_conjecture proves LocallyConnectedSpace for the "
                "Mandelbrot set from RootInput, the two open problems of Dudko. "
                "The kernel uses only propext, Quot.sound and Classical.choice."
            ),
            lean=HEAD_LEAN,
            file=head_decl.file,
            line=head_decl.line,
        )
    )
    vertebrae: list[Node] = []
    for index, spec in enumerate(SPINE):
        file, line, doc = from_decl(spec.lean)
        vertebrae.append(
            make(
                Node(
                    id=f"v:{spec.key}",
                    kind="vertebra",
                    cat="spine",
                    title=spec.title,
                    sub=spec.claim,
                    text=spec.claim + (" " + doc if doc and doc not in spec.claim else ""),
                    lean=spec.lean,
                    file=file,
                    line=line,
                    w=VERTEBRA_W,
                )
            )
        )
    for node in vertebrae:
        node.members.append(member_row(fq_index[node.lean]))
    head.members.append(member_row(head_decl))
    for node in [*vertebrae, head]:
        add_stats(node.stats, [node.lean], fq_index)

    def owner_node(index: int) -> Node:
        return head if index == len(SPINE) else vertebrae[index]

    def owner_key(owner: Node) -> str:
        return owner.id.split(":", 1)[-1]

    # Totals of a level: the milestone with everything that first hangs on it.
    for index, owner in enumerate([*vertebrae, head]):
        add_stats(owner.level, [owner.lean], fq_index)
    for name, index in owner_index.items():
        add_stats(owner_node(index).level, [name], fq_index)

    # Groups of declarations: (owner, file) -> names
    groups: dict[tuple[int, str], list[str]] = {}
    for name, index in owner_index.items():
        file = fq_index[name].file
        if "GridTiles" in file:
            file = "Mlc/GridTiles/*"
        groups.setdefault((index, file), []).append(name)

    drawn_buds: dict[int, list[Node]] = {}
    search: list[dict[str, object]] = []

    def register(names: list[str], owner: Node) -> None:
        add_stats(owner.stats, names, fq_index)
        for name in sorted(names):
            if TILE_NAME.match(name):
                continue
            decl = fq_index[name]
            row = member_row(decl)
            owner.members.append(row)
            search.append({**row, "o": owner.id})

    for node in [*vertebrae, head]:
        search.append({**node.members[0], "o": node.id})

    grid_owner = next(
        (index for (index, file) in groups if file == "Mlc/GridCertified.lean"), None
    )
    grid_nodes: dict[str, Node] = {}
    for (index, file), names in sorted(groups.items()):
        owner = owner_node(index)
        if file == "Mlc/Dudko.lean":
            for name in names:
                if name in open_names:
                    continue
                register([name], owner)
            continue
        if file in GRID_FILES:
            part = GRID_FILES[file]
            title, sub = GRID_TITLES[part]
            node = grid_nodes.get(part)
            if node is None:
                node = make(
                    Node(
                        id=f"b:{owner_key(owner)}:grid-{part}",
                        kind="bud",
                        cat="num",
                        title=title,
                        sub=sub,
                        file=file,
                        parent=owner.id,
                        side=1,
                    )
                )
                grid_nodes[part] = node
            node.count += len(names)
            register(names, node)
            continue
        key = (SPINE[index].key if index < len(SPINE) else "head", file)
        listed = key in BUD_OVERRIDES or (
            file in BUD_TITLES and len([n for n in names if not TILE_NAME.match(n)]) >= MIN_BUD
        )
        if not listed:
            register(names, owner)
            continue
        title, sub = BUD_OVERRIDES.get(key) or BUD_TITLES[file]
        node = make(
            Node(
                id=f"b:{owner_key(owner)}:{Path(file).stem}",
                kind="bud",
                cat="checked",
                title=title,
                sub=sub,
                text=f"Declarations of {file} that the milestone "
                f"“{owner.title}” needs first.",
                file=file,
                count=len(names),
                parent=owner.id,
            )
        )
        register(names, node)
        drawn_buds.setdefault(index, []).append(node)

    for part, node in grid_nodes.items():
        node.members.sort(key=lambda row: (str(row["f"]), int(row["l"])))
    if "tiles" in grid_nodes:
        tiles = grid_nodes["tiles"]
        percent = 100.0 - float(metrics.get("area_upper_percent", 100.0))
        tiles.sub = (
            f"{tile_modules:,} modules · {percent:.3f}% resolved"
            if tile_modules
            else tiles.sub
        )
        tiles.text = (
            f"The grid is stored as {tile_modules:,} Lean modules generated by a script. "
            "Each module lists squares of the grid with their certificates (one "
            "definition) and proves, by kernel computation, how many unresolved cells "
            "they leave (one theorem); the aggregator adds one more theorem per module. "
            f"Together they are {tiles.stats['gen']:,} of the declarations of the library. "
            f"Unresolved area ≤ {float(grid.get('area', 0.0)):.4f}, "
            f"which is {percent:.3f}% of the envelope 4π resolved. "
            "The limit of finer grids is the area of ∂M, whose vanishing is the open "
            "Area problem in the Problem 4.3 branch."
        )
        tiles.lean = "MLC.Certified.unresolved_volume_le_grid"
        if tiles.lean in fq_index:
            tiles.file, tiles.line = fq_index[tiles.lean].file, fq_index[tiles.lean].line
    for part, text in (
        ("soundness", "The theorems that make a certificate imply membership in M, "
         "outside M, and a bound on the area."),
        ("models", "Definitions of the fixed-point Taylor models, the escape and "
         "closure tests, and the verifier of hint streams."),
    ):
        if part in grid_nodes:
            grid_nodes[part].text = text

    # Branch trees: left and right of every vertebra.
    left: dict[int, list[Node]] = {}
    right: dict[int, list[Node]] = {}

    def attach(index: int, node: Node, side: int) -> None:
        node.side = side
        (left if side < 0 else right).setdefault(index, []).append(node)

    def add_child(parent: Node, child: Node, below: bool = False) -> Node:
        make(child)
        child.parent = parent.id
        child.side = parent.side
        child.below = below
        parent.children.append(child)
        return child

    # Support branches alternate between the sides, the larger ones first.
    for index in range(len(SPINE) + 1):
        buds = sorted(drawn_buds.get(index, []), key=lambda n: -n.count)
        side = -1
        for bud in buds:
            attach(index, bud, side)
            side = -side

    if grid_owner is not None and grid_nodes:
        order = [grid_nodes[p] for p in ("tiles", "soundness", "models") if p in grid_nodes]
        attach(grid_owner, order[0], 1)
        for index, (upper, lower) in enumerate(zip(order, order[1:])):
            add_child(upper, lower, below=index > 0)

    # Open problems and the targets that the programme attaches to them.
    dudko = next(i for i, v in enumerate(SPINE) if v.key == "dudko")
    problem_nodes: dict[str, Node] = {}
    for name, info in OPEN_PROBLEMS.items():
        file, line, doc = from_decl(name)
        problem = make(
            Node(
                id=f"open:{info['title'].split()[-1]}",
                kind="tip",
                cat="open",
                title=f"{info['title']} · open",
                sub=str(info["sub"]),
                text=f"{info['text']} Planning prior of route {info['route']}: "
                f"{prior(str(info['route']))}.",
                lean=name,
                file=file,
                line=line,
                parent=vertebrae[dudko].id,
            )
        )
        problem.members.append(member_row(fq_index[name]))
        add_stats(problem.stats, [name], fq_index)
        search.append({**problem.members[0], "o": problem.id})
        problem_nodes[name] = problem

    p43 = problem_nodes["MLC.Problem43PseudoSiegelAPrioriBoundsData"]
    p44 = problem_nodes["MLC.Problem44VirtualMoleculeData"]
    attach(dudko, p43, -1)
    attach(dudko, p44, 1)
    conjecture = add_child(
        p43,
        Node(
            id="paper:conj36",
            kind="tip",
            cat="informal",
            title="Conjecture 3.6",
            sub="hyperbolic Molecule renormalization",
            text=(
                "Dudko §3.8: there is a hyperbolic renormalization with "
                "one-dimensional unstable manifolds parametrized by the sped-up "
                "Molecule map. The completion of Problem 4.3 is required for it. "
                "Not formalized."
            ),
        ),
    )
    area = add_child(
        conjecture,
        Node(
            id="paper:area",
            kind="tip",
            cat="informal",
            title="Area of ∂M = 0",
            sub="expected · gives a 100% share",
            text=(
                "Dudko §3.8: Conjecture 3.6 is likely required for the satellite "
                "cases of MLC and for the Area Problem of ∂M, whose area is "
                "expected to be 0. A zero-area boundary makes the unresolved set "
                "null, so the certified share of the grid becomes 100%; it does "
                "not give MLC. Not formalized; the measure step of the route "
                "proposed in ROADMAP.md is checked in Lean (below)."
            ),
        ),
        below=True,
    )
    add_child(
        area,
        Node(
            id="paper:porosity",
            kind="tip",
            cat="informal",
            title="Porosity of ∂M",
            sub="holes at all scales · from the programme",
            text=(
                "Route Z, geometric step (proposed in ROADMAP.md; the survey does not "
                "state it). At every point of ∂M and at arbitrarily small scales r, "
                "a ball of radius αr inside B(c, r) misses ∂M. The Molecule regime "
                "expects substantial hyperbolic components at all scales (Dudko §3), "
                "the quadratic-like regime needs the a priori bounds of Problems 4.3 "
                "and 4.4, and the renorm-expanding regime transfers the porosity of "
                "J_c to M by the almost-linear puzzle–parapuzzle relation. "
                "Not formalized."
            ),
        ),
        below=True,
    )
    side_names: dict[str, set[str]] = {}
    claimed: set[str] = set()
    for side in SIDE_ROOTS:
        if side not in fq_index:
            raise RuntimeError(f"Side result not found: {side}")
        names = closure(edges, side) - set(owner_index) - spine_names - claimed
        side_names[side] = names & set(reachable)
        claimed |= side_names[side]
    area_root = SIDE_ROOTS[0]
    area_names = side_names[area_root]
    if area_names:
        side_decl = fq_index[area_root]
        measure = Node(
            id="z:measure",
            kind="bud",
            cat="checked",
            title="Measure step",
            sub="porous at each point ⇒ area 0",
            text=(
                "Checked in Lean: a measurable set that is porous at each of its points "
                "has measure zero, by Lebesgue's density theorem; applied to the "
                "unresolved set it gives volume 0 (MLC.Research.unresolved_volume_"
                "eq_zero_of_porous). The geometric input, the porosity of ∂M, is the "
                "open part of Route Z."
            ),
            lean=area_root,
            file=side_decl.file,
            line=side_decl.line,
            count=len(area_names),
        )
        register(sorted(area_names), measure)
        measure.stat = stat_line(measure.stats)
        measure.members.sort(key=lambda row: (str(row["f"]), int(row["l"])))
        add_child(area, measure, below=True)
        extras.append(measure)

    # The programme: the statements of Problems 4.3 and 4.4 as nodes, then the checked assembly.
    root_text = ""
    root_file = repo_root / "Mlc" / "ProgrammeRoot.lean"
    if root_file.is_file():
        root_text = root_file.read_text(encoding="utf-8")
    issues = check_catalogue(root_text) if root_text else ["Mlc/ProgrammeRoot.lean is missing"]
    if issues:
        raise RuntimeError("Programme catalogue out of date: " + "; ".join(issues))
    open_keys = set(open_lemmas(root_text))
    lemma_nodes: dict[str, Node] = {}
    for lemma in LEMMAS:
        if lemma.lean not in fq_index:
            raise RuntimeError(f"Lemma not found in the sources: {lemma.lean}")
        file, line, doc = from_decl(lemma.lean)
        is_open = lemma.key in open_keys
        node = make(
            Node(
                id=f"lemma:{lemma.key}",
                kind="tip",
                cat=(
                    "checked"
                    if not is_open
                    else "published" if lemma.kind == "published" else "lemma"
                ),
                title=lemma.title,
                sub=lemma.sub,
                text=f"{lemma.text} Source: {lemma.source}. "
                + ("Open: a field of ProgrammeInput." if is_open else "Proved."),
                lean=lemma.lean,
                file=file,
                line=line,
            )
        )
        node.members.append(member_row(fq_index[lemma.lean]))
        add_stats(node.stats, [lemma.lean], fq_index)
        search.append({**node.members[0], "o": node.id})
        lemma_nodes[lemma.key] = node

    def add_lemma(parent: Node, key: str, below: bool = False) -> Node:
        return add_child(parent, lemma_nodes[key], below=below)

    add_lemma(p43, "unboundedTeichmuller")
    add_lemma(p43, "unboundedJumpCap")
    ps_nodes: dict[str, Node] = {}
    for sid, title, sub, text in PSEUDO_SIEGEL:
        ps_nodes[sid] = add_child(
            lemma_nodes["unboundedJumpCap"],
            Node(id=f"paper:{sid}", kind="tip", cat="informal", title=title, sub=sub, text=text),
            below=True,
        )
    add_lemma(p43, "unboundedDichotomy")

    def side_bud(
        root: str | tuple[str, ...],
        node_id: str,
        title: str,
        sub: str,
        text: str,
        parent: Node,
    ) -> Node | None:
        """A checked branch: the declarations that only these side results need."""
        roots = (root,) if isinstance(root, str) else root
        names = set().union(*(side_names[r] for r in roots))
        if not names:
            return None
        decl = fq_index[roots[0]]
        bud = make(
            Node(
                id=node_id,
                kind="bud",
                cat="checked",
                title=title,
                sub=sub,
                text=text,
                lean=roots[0],
                file=decl.file,
                line=decl.line,
                count=len(names),
            )
        )
        register(sorted(names), bud)
        bud.stat = stat_line(bud.stats)
        bud.members.sort(key=lambda row: (str(row["f"]), int(row["l"])))
        add_child(parent, bud, below=True)
        extras.append(bud)
        return bud

    side_bud(
        SHARPNESS_ROOT,
        "prog:sharpness",
        "Why both G and D are needed",
        "cap ⇔ a priori bounds; two counterexamples",
        "Checked in Lean (WidthTower.uniformities_necessary, "
        "WidthTower.aPrioriBounds_iff_jumpCap). Given the linear dichotomy, a "
        "tower has a priori bounds if and only if its jumps are capped, so the "
        "cap of Lemma G is the weakest hypothesis of its kind. Neither lemma "
        "can be dropped. (1) A tower of unbounded relative periods with a "
        "uniform growth bound (which caps the jumps) and the dichotomy (4.6) with "
        "the error p·h(p), h unbounded (a quadratic error, for instance), has "
        "unbounded degeneration: a linear error is the threshold (Lemma D). "
        "(2) The tower of widths (k+1)! satisfies the Teichmüller contraction and "
        "the dichotomy with a linear error, has uncapped jumps and unbounded "
        "degeneration (Lemma G).",
        lemma_nodes["unboundedDichotomy"],
    )
    side_bud(
        PARALLEL_ROOT,
        "prog:parallel",
        "Parallel law (4.1)",
        "p families in disjoint regions ⇒ widths add",
        "Checked in Lean (extWidth_parallel_finset, extWidth_parallel). The extremal "
        "width of a family of curves is defined for length measures with an area "
        "measure. The widths of families that live in pairwise disjoint regions add up: "
        "with p small Julia sets of equal degeneration W(f₁) in disjoint neighbourhoods, "
        "the total degeneration around them is at least p·W(f₁), the main term of (4.1) "
        "and the source of the factor p in the amplification (4.3). The thin–thick "
        "decomposition (the additive error) and the vertical proportion of Kahn stay open.",
        lemma_nodes["unboundedDichotomy"],
    )
    side_bud(
        GROTZSCH_ROOT,
        "prog:grotzsch",
        "Grötzsch step (4.6)",
        "series law ⇒ W(G ∖ G′) ≥ δ⁻¹ W(G)",
        "Checked in Lean (extWidth_ge_of_series, extLength_series, extLength_mono, "
        "extWidth_ge_of_complement). Curves that cross two disjoint regions in succession "
        "have extremal length at least the sum of the extremal lengths of the two pieces "
        "(the Grötzsch inequality). If the lift G′ carries the fraction 1 − δ of the "
        "extremal length of the rectangle G, the subcurves G ∖ G′ through the "
        "preperiodic Julia sets have width at least δ⁻¹ W(G): the estimate (4.6) with "
        "C_δ = δ⁻¹ → ∞. This is the conformal-geometry foundation of PS4; the dynamical "
        "input, the families G ∖ G′ and G′ for the pseudo-Siegel disks, stays open.",
        ps_nodes["ps4"],
    )
    side_bud(
        LEVEL_JUMP_ROOTS,
        "prog:level_jump",
        "Lemma G from collars",
        "bounded dilatation ⇒ cap on the jumps",
        "Checked in Lean (LevelTower, LevelTower.width_le_of_collar, "
        "LevelTower.jumpCap_of_collars, LevelTower.aPrioriBounds_of_collars, "
        "LevelTower.width_eq_of_round, WidthTower.exists_levelTower). A LevelTower "
        "records that the degeneration of the level k is W(f_k) = 1 / mod(V_k ∖ K_k), the "
        "reciprocal modulus of the annulus between the filled Julia set and the range domain "
        "of the level (the survey (3.2), (4.1)), the modulus being the extremal width of the "
        "C¹ loops that separate K_k from the complement of V_k: at most the classical "
        "modulus, and equal to it for round annuli (for a round level K = B̄(c, r), "
        "V = B(c, R) the degeneration is exactly 2π / log(R/r)). The sets are data of the "
        "dictionary: every width tower is realized by round levels "
        "(WidthTower.exists_levelTower), so a LevelTower has no dynamical content by itself, "
        "and the hypotheses below are meaningful for the sets that the dictionary provides "
        "(the filled Julia sets and range domains of quadratic-like restrictions, or the "
        "regularized sets of the pseudo-Siegel levels). If this annulus has a collar of "
        "dilatation "
        "Kd and modulus log(R/r) / 2π (see \"Collars bound the modulus\"), the degeneration is "
        "at most 2π Kd / log(R/r). So if at every level that follows a jump by the factor C₀ "
        "the annulus has a collar of dilatation at most K₀ and modulus at least μ₀ / 2π, the "
        "jumps are capped by the ceiling 2π K₀ / μ₀: Lemma G, in the reading of PS4 that the "
        "invariant degeneration is bounded by the uniform quasiconformal geometry of the "
        "pseudo-Siegel disks. With the linear dichotomy this gives a priori bounds; with the "
        "Teichmüller contraction for the levels of small relative period (Lemma TC′), collars "
        "at the jumps at the levels of large relative period suffice "
        "(LevelTower.aPrioriBounds_of_tails_collars), the three lemmas of Problem 4.3. "
        "That the "
        "pseudo-Siegel disks give such collars at the jumps is the proposed content of PS4 and "
        "stays open; the same theorem applies to the virtual levels of Lemma VG2.",
        ps_nodes["ps4"],
    )
    side_bud(
        STACKING_ROOTS,
        "prog:stacking",
        "Lemma D from stacked annuli",
        "p disjoint sub-annuli ⇒ linear dichotomy",
        "Checked in Lean (LevelTower.StackedAnnuli, LevelTower.linearDichotomy_of_stacked, "
        "sum_extWidth_loopFamily_le, WidthTower.linearDichotomy_iff_stacked). The linear "
        "dichotomy asks, for every threshold C, for "
        "constants c and A such that for every pair of levels k, k+n of relative period p "
        "either c p W_{k+n} − A p ≤ W_k or the degeneration jumps at the level k+n. A proposed "
        "sufficient geometric form, an analogue of the quasi-additivity mechanism of the "
        "survey (§4.2, (4.5)), which the survey does not state in this form: for every pair "
        "of levels and every threshold C, with uniform constants c′ > 0 and A′ ≥ 0, either "
        "the degeneration jumps by the factor C at the level k+n, or the annulus of the "
        "level k+n contains p pairwise disjoint sub-annuli, each of modulus at least "
        "c′/(W_k + A′ p). The moduli of disjoint sub-annuli "
        "add up (Grötzsch's inequality, the parallel law), so the modulus of the deeper "
        "annulus is at least p c′/(W_k + A′ p), that is c′ p W_{k+n} ≤ W_k + A′ p, the "
        "amplification, and the linear dichotomy follows. In the round model the converse "
        "holds, the sub-annuli being concentric, so Lemma D is equivalent there to the "
        "stacked annuli; with a loss A′ that does not grow with p the form would be "
        "strictly stronger and fails for a tower of constant degeneration without jumps. "
        "That the annuli of the dynamical levels contain such sub-annuli, pullbacks of the "
        "shallower annulus along the critical orbit, is the proposed content of "
        "Lemma D and stays open.",
        ps_nodes["ps4"],
    )
    side_bud(
        PULLBACK_ROOT,
        "prog:pullback",
        "Pullback law (contraction)",
        "W(ΓX) ≤ d · W(ΓY) for a map of degree d",
        "Checked in Lean (extWidth_pullback_le, extLength_pullback_le). If a map φ carries "
        "the curves of a family ΓX to curves of ΓY and its area multiplicity is at most d "
        "(the area formula for a holomorphic map of degree d), then W(ΓX) ≤ d · W(ΓY). "
        "This is the shape of the growth bound of the Teichmüller contraction: p iterations "
        "of a quadratic-like map have multiplicity at most 2^p, so the width of a pulled-back "
        "family grows by at most 2^p; for d = 1 it is the monotonicity of the width under a "
        "conformal map. The "
        "tower-level statement, W(f_{m+1}) ≤ Δ_P W(f_m), needs the families of the "
        "renormalization levels and stays open.",
        lemma_nodes["unboundedTeichmuller"],
    )
    side_bud(
        MULTIPLICITY_ROOTS,
        "prog:multiplicity",
        "Area multiplicity of f_c^p",
        "W(ΓX) ≤ 2^p · W(ΓY) for the iterates of z² + c",
        "Checked in Lean (extWidth_le_pow_two_mul_fc_iterate, areaMultiplicity_fc_iterate, "
        "areaMultiplicity_fc, loopMeasure_comp). The hypothesis of the pullback law, the area "
        "formula with multiplicity at most d, is proved for the quadratic polynomials: z ↦ z² + c "
        "is injective on each of the two half planes that z ↦ −z swaps, so by the area formula "
        "of Mathlib (with the determinant |w|² of the multiplication by w) it has area "
        "multiplicity 2; the multiplicity is additive over a partition of the domain and "
        "multiplicative under composition, so f_c^p has multiplicity 2^p with the stretching "
        "|(f_c^p)′|. Hence, if f_c^p maps the curves of a family ΓX to curves of ΓY, then "
        "W(ΓX) ≤ 2^p · W(ΓY): the width of a pulled-back family grows by at most 2^p, which "
        "has the shape of the Teichmüller contraction of §4.3 (growth at most exponential in "
        "the relative period). For a C¹ loop the image curve has the "
        "length measure of the pushed-forward loop (loopMeasure_comp). The families of the "
        "renormalization levels to which the estimate applies, and the quadratic-like "
        "restrictions, stay open.",
        lemma_nodes["unboundedTeichmuller"],
    )
    side_bud(
        TAIL_ROOTS,
        "prog:tail",
        "Tail invariance (tuning)",
        "the statements pass to tails",
        "Checked in Lean (WidthTower.lemmas_shift_iff, aPrioriBounds_shift_iff, "
        "aPrioriBounds_of_shift_tails, shift_shift). Tuning with an n-step prefix maps M "
        "onto a little copy of itself, and the tower of the tuned parameter is the prefix "
        "followed by the tower of the original, so untuning is the shift T.shift n of the "
        "tower. The Teichmüller contraction, the cap on the jumps and the dichotomy with a "
        "linear error hold for a tower exactly when they hold for the shifted tower, and the "
        "three of them for the tail give a priori bounds for the tower. This is the exact, "
        "combinatorial self-similarity of M under tuning; the constants depend on the "
        "prefix. The uniform metric comparison of a parameter with its tuned copies, the "
        "content of the open statements, stays open.",
        lemma_nodes["unboundedTeichmuller"],
    )
    satellite = add_child(
        p44,
        Node(
            id="paper:satellite",
            kind="tip",
            cat="informal",
            title="Virtual bounded-type satellite",
            sub=f"Route 2 · prior {prior('2')}",
            text=(
                "Dudko §4.5, first subcase of the virtual Molecule: n ≫ 1 with "
                "bounded relative periods of M(s+1) rel M(s). Planning route 2: "
                + str(route("2")["next"]).replace("$", "")
            ),
        ),
    )
    add_lemma(satellite, "virtualDichotomy", below=True)
    neutral = add_child(
        p44,
        Node(
            id="paper:neutral",
            kind="tip",
            cat="informal",
            title="Virtual near-Neutral",
            sub=f"Route 3 · prior {prior('3')}",
            text=(
                "Dudko §4.5, second subcase of the virtual Molecule: n = 0. "
                "Planning route 3: " + str(route("3")["next"]).replace("$", "")
            ),
        ),
    )
    add_lemma(neutral, "virtualJumpCap", below=True)
    add_lemma(neutral, "virtualLinearDichotomy", below=True)
    add_lemma(p44, "virtualTeichmuller")
    add_lemma(p44, "virtualJulia")
    add_lemma(p44, "virtualTransfer")
    side_bud(
        VIRTUAL_SHRINKING_ROOTS,
        "prog:virtual_shrinking",
        "What VT says about the hulls",
        "separation estimate ⇔ hulls shrink",
        "Checked in Lean (VirtualJuliaNest.separationEstimate_iff, "
        "Geometry.virtualTransfer_hulls_shrink). For a cost with non-negative terms and "
        "divergent partial sums, such as the canonical cost of a degeneration bound, the "
        "dynamical separation estimate of Lemma VT is equivalent to the shrinking of the "
        "virtual hulls to their origins: for every ε the closure of the n-th hull lies in the "
        "ε-ball around its origin for n large. So the dynamical content of Lemma VT is that "
        "the diameters of the virtual hulls tend to zero, the analogue of the shrinking of "
        "the parameter pieces for Lemma T. The nest in the parameter plane, the "
        "phase–parameter chart and the proof that the hulls shrink stay open.",
        lemma_nodes["virtualTransfer"],
    )

    published = make(
        Node(
            id="pub:cases",
            kind="tip",
            cat="published",
            title="Published cases",
            sub="§4.1–§4.4 · literature",
            text=(
                "The classes of boundary parameters and the estimates that the literature "
                "treats by published theorems: the parameters that are not infinitely "
                "renormalizable (Yoccoz, Hubbard), the Teichmüller contraction for bounded "
                "type (§4.3), bounded type (Theorem 4.1), the anti-Molecule condition "
                "(Kahn–Lyubich), neutral parameters (Theorem 4.2) and the satellite types of "
                "quadratic growth (Cheraghi–Shishikura, Theorem D). Each is one statement "
                "about the geometric dictionary, a field of ProgrammeInput; none is "
                "formalized."
            ),
            parent=vertebrae[dudko].id,
        )
    )
    attach(dudko, published, -1)
    for key in (
        "yoccoz",
        "teichmuller",
        "boundedType",
        "antiMolecule",
        "neutral",
        "quadraticGrowth",
    ):
        add_lemma(published, key, below=True)

    programme_names = side_names[PROGRAMME_ROOT] - {lemma.lean for lemma in LEMMAS}
    if programme_names:
        root_decl = fq_index[PROGRAMME_ROOT]
        shares = class_shares(proved_lemmas(root_text))
        assembly = make(
            Node(
                id="prog:assembly",
                kind="bud",
                cat="checked",
                title="Programme assembly",
                sub=f"{len(LEMMAS)} statements ⇒ Problems 4.3, 4.4",
                text=(
                    "Checked in Lean (MLC.mlc_of_programme): for every geometric dictionary, "
                    f"the {len(LEMMAS)} statements of ProgrammeInput give RootInput, that is "
                    "the candidate system with its realization (Problem 4.3) and the "
                    "virtual-Molecule completion (Problem 4.4), hence MLC. The degeneration "
                    "recursion of §4.1–§4.3 is proved: a cap on the jumps of the degeneration "
                    "and a dichotomy with an error at most linear in the period give a priori "
                    "bounds for every tower (WidthTower.aPrioriBounds_of_jumpCap), and bounded "
                    "type needs the Teichmüller contraction and the dichotomy "
                    "(WidthTower.aPrioriBounds_of_bounded). "
                    f"{len(CLASSES)} classes of parameters, "
                    f"{sum(shares.values()):.2f} of them certified, with {len(open_keys)} "
                    "open statements of the programme."
                ),
                lean=PROGRAMME_ROOT,
                file=root_decl.file,
                line=root_decl.line,
                count=len(programme_names),
                parent=vertebrae[dudko].id,
            )
        )
        register(sorted(programme_names), assembly)
        assembly.stat = stat_line(assembly.stats)
        assembly.members.sort(key=lambda row: (str(row["f"]), int(row["l"])))
        attach(dudko, assembly, 1)
        extras.append(assembly)
        side_bud(
            LEVEL_GEOMETRY_ROOTS,
            "prog:level_geometry",
            "Geometric form of the programme",
            "collars, stacked annuli, comparison ⇒ MLC",
            "Checked in Lean (MLC.mlc_of_levelGeometry, LevelGeometry, "
            "LevelGeometry.UnboundedCollars, LevelGeometry.UnboundedStacked, "
            "LevelGeometry.VirtualCollars, LevelGeometry.VirtualStacked, "
            "LevelGeometry.Comparison). A LevelGeometry is a dictionary together with the "
            "level sets of its towers, the sets that define the degeneration of the levels. "
            "Lemma G is stated for them as collars of bounded dilatation and definite modulus "
            "at the jumps at the levels of large relative period, and Lemma D as stacked "
            "annuli, for the tower of unbounded satellite type (Problem 4.3) and for the "
            "virtual near-neutral tower (Problem 4.4); Lemma T is the phase–parameter "
            "comparison of the moduli of the levels with those of a nest in M. The abstract "
            "fields UnboundedJumpCap, UnboundedDichotomy, VirtualJumpCap, "
            "VirtualLinearDichotomy and Transfer are derived from them "
            "(LevelTower.largePeriodJumpCap_of_collars, LevelTower.linearDichotomy_of_stacked, "
            "Geometry.transfer_of_comparison), and MLC follows from the six published lemmas, "
            "the Teichmüller contraction for the pseudo-Siegel and for the virtual levels, the "
            "virtual Julia sets, the dichotomy for the virtual bounded type, the virtual "
            "transfer and these five geometric statements. That the level sets are the "
            "dynamical ones (the filled Julia sets and range domains of quadratic-like "
            "restrictions of f_c, or the regularized sets of the pseudo-Siegel levels whose "
            "degeneration is the width of the class of Problem 4.3) is the "
            "faithfulness of the dictionary and is not part of the structure; the statements "
            "depend on the dictionary (for a dictionary without towers the five are vacuous, "
            "and the comparison is more than a bound on widths); none of the "
            "statements is proved.",
            assembly,
        )
    phase = next(i for i, v in enumerate(SPINE) if v.key == "phase")
    unified = make(
        Node(
            id="paper:unified",
            kind="tip",
            cat="informal",
            title="Unified phase–parameter transfer",
            sub=f"Route 4 · prior {prior('4')}",
            text=(
                "Planning route 4, conditional on genuine geometry: "
                + str(route("4")["next"]).replace("$", "")
            ),
            parent=vertebrae[phase].id,
        )
    )
    attach(phase, unified, 1)
    add_lemma(unified, "transfer", below=True)
    side_bud(
        (*ANNULUS_ROOTS, *RECTANGLE_ROOTS),
        "prog:modulus",
        "Moduli of the model domains",
        "round annulus and rectangle",
        "Checked in Lean (extLength_radialFamily, extLength_circleFamily, "
        "extLength_radialFamily_mul_circleFamily, extLength_radialFamily_add_le, "
        "extLength_horizFamily, extWidth_horizFamily). In the plane with Lebesgue measure, the "
        "extremal length of the radial segments of the annulus {r < |z| < R}, the curves that "
        "join its boundary circles, is log(R/r)/2π, and that of the circles that separate "
        "them is 2π/log(R/r); the extremal length of the horizontal segments of a rectangle, "
        "which join its vertical sides, is width/height. So the extremal-length theory of "
        "ExtremalLength.lean agrees with the classical modulus on both model domains "
        "(Cauchy–Schwarz and Fubini for the upper bounds, a characteristic metric for the "
        "lower bounds), and its series law gives the Grötzsch inequality for concentric "
        "annuli. This is the first step of the transfer lemma and the model of the rectangles "
        "of the survey (Figure 13). The modulus of domains that are not round, the conformal "
        "invariance and the Teichmüller bound that turn moduli into shrinking stay open.",
        lemma_nodes["transfer"],
    )
    side_bud(
        NEST_ROOTS,
        "prog:nest",
        "Moduli ⇒ shrinking",
        "Grötzsch–Teichmüller · T ⇔ phase–parameter",
        "Checked in Lean (ConnectedNest.sum_extWidth_loops_le, DivergentModuli.shrinking, "
        "ConnectedNest.sum_extWidth_loops_le_coarse, ConnectedNest.exists_divergentSubnest, "
        "Geometry.transfer_iff_phaseParameter, concentricNest_divergentModuli, "
        "extWidth_loopFamily_round). The loops of "
        "the annulus between two consecutive pieces of a nest are the C¹ closed curves in it "
        "that separate the next piece from the complement of the piece (every path from one "
        "to the other meets the loop); their extremal width is the modulus of the annulus, "
        "which for the round annulus r < |z − c| ≤ R is exactly the classical log(R/r)/2π "
        "(the circles bound it below, and the metric 1/|z − c| of area 2π log(R/r) bounds it "
        "above). If "
        "the piece n of the nest keeps a point at distance δ from c, the moduli of the first n "
        "annuli add up to at most 2π log(4(R + δ)/δ) / (log 2)², where R bounds the first "
        "piece. Each loop has length at least log 2 for the metric 1/|z − c| on the ring "
        "δ/2 ≤ |z − c| ≤ R + δ (a loop that stays outside the disk of radius δ/2 meets every "
        "ray from c, so the argument of z − c sweeps (−π, π); a loop that enters the disk "
        "crosses the ring δ/2 ≤ |z − c| ≤ δ; both by the area inequality for real "
        "functions), the ring has area at most 2π log(4(R + δ)/δ), and the annuli are "
        "disjoint (the parallel law). So a nest whose moduli add up to infinity shrinks to c "
        "and gives the separation estimate of every budget. Grötzsch's inequality for a "
        "coarsening: the modulus of Pₙ ∖ cl P_m is at least the sum of the moduli of the "
        "annuli Pⱼ ∖ cl P_{j+1} with n ≤ j < m, so grouping the levels of a nest can only "
        "increase the moduli. Conversely, a shrinking nest has "
        "a subnest whose annuli contain round annuli of modulus log(3/2)/2π, so Lemma T is "
        "equivalent to the phase–parameter relation in moduli form (Geometry.PhaseParameter), "
        "and the concentric disks give an example of a nest with divergent moduli, so the "
        "notion is satisfiable (the relation over the parameters of M is the open statement). The "
        "construction of the nest from an a priori bound stays open.",
        lemma_nodes["transfer"],
    )
    phase_parameter = add_child(
        lemma_nodes["transfer"],
        Node(
            id="paper:phase_parameter",
            kind="tip",
            cat="informal",
            title="Phase–parameter moduli",
            sub="open · equivalent to Lemma T",
            text=(
                "Lyubich's phase–parameter relation, in the form that Lemma T needs "
                "(Geometry.PhaseParameter): an a priori bound on the degeneration of the tower "
                "of c gives a connected nest of parameter pieces around c in M whose annuli "
                "have moduli with an infinite sum. The quasi-additivity law of Kahn–Lyubich "
                "carries the moduli of the dynamical annuli of the tower to the parameter "
                "plane. This statement is equivalent to Lemma T (checked in Lean, below): the "
                "geometric half, from the moduli to the shrinking of the pieces, and the "
                "converse, a subnest with moduli bounded below, are theorems. What is open is "
                "the construction of the nest from the bound. The root theorem keeps the "
                "hypothesis Transfer."
            ),
        ),
        below=True,
    )
    quasi_invariance = side_bud(
        QUASI_INVARIANCE_ROOTS,
        "prog:quasi_invariance",
        "Moduli under a change of chart",
        "C¹ charts of dilatation ≤ K",
        "Checked in Lean (QcEmbedding, extWidth_le_of_qcEmbedding, Separates.image, "
        "extWidth_loopFamily_le_map, ConnectedNest.extWidth_loops_le_map, "
        "ConnectedNest.DivergentModuli.map, QcEmbedding.of_holomorphic). A C¹ embedding φ of "
        "an open set with dilatation at most K (‖Dφ‖² ≤ K |det Dφ|; K = 1 for an injective "
        "holomorphic map with non-vanishing derivative) multiplies the extremal width by at "
        "most K: if φ carries every curve of ΓX to a curve that dominates a curve of ΓY, then "
        "W(ΓX) ≤ K W(ΓY) (the area formula of Mathlib and the pullback law). A map that is "
        "continuous and injective on the compact closure of O, with φ(O) open, carries a loop "
        "that separates K from the complement of O to a loop that separates φ(K) from the "
        "complement of φ(O) (the first exit time of a path from φ(O)). So the modulus of an "
        "annular region, the extremal width of the C¹ loops in it that separate K from the "
        "complement of O, is at most K times the modulus of every annular region that "
        "contains the image of the first. For the annuli of a nest this gives that the "
        "modulus of each annulus of the image nest is at least 1/K times that of the original, "
        "and that a nest with divergent moduli has an image with divergent moduli. This is the "
        "form that the transport of the moduli takes in the phase–parameter relation, as "
        "proposed here: the correspondence between the dynamical and the parameter annuli is "
        "quasi-conformal and is not given as a C¹ chart, and neither the chart nor the phase "
        "nest is constructed. What is open is the construction of the nest from the a priori "
        "bound.",
        phase_parameter,
    )
    collar = side_bud(
        COLLAR_ROOTS,
        "prog:collar",
        "Collars bound the modulus",
        "quasi-round annulus ⇒ definite modulus",
        "Checked in Lean (IsCollar, IsCollar.ofReal_le_extWidth, "
        "ConnectedNest.divergentModuli_of_collars, "
        "ConnectedNest.closure_piece_subset_closedBall_of_collars). The modulus of the "
        "annulus V ∖ E is the "
        "extremal width of the C¹ loops in it that separate E from the complement of V; for a "
        "level f : U → V with filled Julia set E = K_f it is the C¹ version of mod⁺(f), the "
        "reciprocal of the degeneration W(f) of the survey (4.1): at most the classical "
        "modulus, and equal to it for round annuli; the identification in general belongs to "
        "the dictionary. A collar of V ∖ E is a C¹ embedding ψ of "
        "dilatation at most Kd of a neighbourhood of the closed disk of radius R, such that E "
        "lies in the image of the disk of radius r and the image of the disk of radius R lies "
        "in V. The loops of the round annulus r < |w| ≤ R go to loops of V ∖ E, so the "
        "modulus of V ∖ E is at least log(R/r) / (2π Kd): Grötzsch's monotonicity of the "
        "modulus together with the quasi-invariance. A nest whose annuli all have collars of "
        "dilatation at most K₀ and modulus at least μ₀/2π has moduli bounded below by "
        "μ₀/(2π K₀), so they add up to infinity and the pieces shrink to the point, at a "
        "geometric rate: if the first piece lies in the disk of radius R around c and the "
        "first n annuli have total modulus at least s, with κ s ≥ log 8 for κ = (log 2)²/2π, "
        "the piece n lies in the disk of radius 8R e^(−κ s) (a Teichmüller-type estimate "
        "with non-optimal constants, "
        "closure_piece_subset_closedBall_of_sum), so uniform collars give the decay "
        "exp(−κ μ₀ n / (2π K₀)): this is the form that bounded geometry takes here. The "
        "collars of the levels of a tower and "
        "the charts between dynamical and parameter annuli are not constructed.",
        quasi_invariance or phase_parameter,
    )
    level_transfer = side_bud(
        LEVEL_TRANSFER_ROOTS,
        "prog:level_transfer",
        "Lemma T from the comparison",
        "level moduli ≤ Kd · nest moduli ⇒ T",
        "Checked in Lean (Geometry.PhaseParameterComparison, Geometry.transfer_of_comparison). "
        "The levels of the tower of c, with a degeneration bound B, have moduli at least 1/B. "
        "If a connected nest in M around c has annuli whose moduli are at least 1/Kd times the "
        "moduli of the corresponding levels (the comparison; a quasi-conformal chart from the "
        "dynamical annulus to the parameter annulus gives it, and for a C¹ chart this is "
        "extWidth_loopFamily_le_map), the moduli of the nest are bounded below by 1/(B Kd), so "
        "they add up to infinity, the pieces shrink to c, and Lemma T holds. This is the form "
        "in which the phase–parameter relation of Lyubich is used at the renormalization "
        "levels, as proposed here. The realization of the tower by the annuli of its levels, "
        "the nest and the chart are not constructed; the root theorem keeps the hypothesis "
        "Transfer.",
        collar or quasi_invariance or phase_parameter,
    )
    side_bud(
        CRITERION_ROOTS,
        "prog:criterion",
        "Collars ⇒ local connectivity at c",
        "the Yoccoz criterion, with a logarithmic depth bound",
        "Checked in Lean (ConnectedNest.locallyConnectedAt_of_divergent, "
        "ConnectedNest.locallyConnectedAt_of_collars, "
        "ConnectedNest.exists_relativePiece_of_collars, "
        "Geometry.exists_relativePiece_of_comparison, "
        "Geometry.locallyConnectedAt_of_collars_and_comparison, "
        "Geometry.locallyConnectedAt_of_tails_collars_and_comparison, concentricNest_collars). "
        "A set "
        "is locally connected at the center of a connected nest whose moduli add up to "
        "infinity (the Yoccoz criterion). If the moduli have a uniform lower bound w and the "
        "first piece lies in the disk of radius R around c, then for every ε > 0 some piece "
        "of depth at most max(log 8, log(8R/ε)) / (κ w) + 1, κ = (log 2)²/2π, is a connected "
        "neighbourhood of c inside the disk of radius ε: the depth grows like log(1/ε), a "
        "logarithmic bound on the depth, not on the size of the neighbourhood. Uniform "
        "collars of dilatation at most K₀ "
        "and modulus at least μ₀/2π give w = μ₀/(2π K₀); the phase–parameter comparison with a "
        "degeneration bound B gives w = 1/(B Kd). The whole chain in one statement: collars "
        "of bounded dilatation and definite modulus at the jumps of a level tower of c (the "
        "content proposed for PS4), the linear dichotomy (Lemma D) and the phase–parameter "
        "comparison give the local connectivity of M at c; in the form that follows the three "
        "lemmas of Problem 4.3, the Teichmüller contraction (TC′), collars at the jumps at "
        "the levels of large relative period (G), the linear dichotomy (D) and the "
        "comparison, and with Lemma D in the form of stacked annuli (see \"Lemma D from "
        "stacked annuli\") every hypothesis but TC′ is a statement about sets of the plane "
        "(collars, sub-annuli, a nest) and their moduli, while TC′ is an inequality between "
        "the widths of consecutive levels. "
        "These hypotheses are "
        "explicit geometric statements and none is proved; the concentric nest, whose annuli "
        "are their own collars, shows that the hypotheses of the collar criterion are "
        "satisfiable.",
        level_transfer or collar or quasi_invariance or phase_parameter,
    )
    rays = add_child(
        unified,
        Node(
            id="paper:rays",
            kind="tip",
            cat="informal",
            title="Rays and the lamination",
            sub="the form in which MLC is read",
            text=(
                "Carathéodory, Douady–Hubbard, Thurston, Schleicher: M is locally connected "
                "exactly when every parameter ray lands and the landing map is continuous, "
                "exactly when M is the quotient of the closed disk by the quadratic minor "
                "lamination, exactly when every fiber of M is a point. The fibers of the "
                "parameters that are not infinitely renormalizable are points (Yoccoz, "
                "Hubbard), and the statements of the published classes give the same for "
                "those classes, so the rays land at points where local connectivity is "
                "known, except possibly at the infinitely renormalizable parameters of "
                "Problems 4.3 and 4.4. The formalization uses connected parameter nests "
                "that shrink to the point and needs no ray. The rays and the lamination are "
                "not formalized; see ROADMAP.md, “Rays, the lamination and tuning”. Checked "
                "below: the form of local connectivity as a parametrization by the interval, "
                "in the category of compact Hausdorff spaces, and the dimension of the "
                "fractal boundary against the smooth curves of the moduli."
            ),
        ),
        below=True,
    )
    dimension = side_bud(
        DIMENSION_ROOTS,
        "prog:dimension",
        "Fractal against smooth curves",
        "dim_H of loops, charts and kernels",
        "Checked in Lean (IsLoop.dimH_range_le, QcEmbedding.dimH_image, "
        "dimH_le_inv_of_holderOnWith, ShishikuraDimension.holder_exponent_le_half, "
        "ConnectedNest.sum_extWidth_loops_bounded_of_dimH_kernel_pos). The loops with which the "
        "moduli are measured are C¹ curves, of Hausdorff dimension at most 1, while the sets "
        "that they go around are fractals: the boundary of the Mandelbrot set has topological "
        "dimension 1 and Hausdorff dimension 2 (Shishikura 1998, a published hypothesis here). "
        "Countably many loops cover no set of dimension above 1. A C¹ embedding with "
        "invertible derivative is locally bi-Lipschitz, so it preserves the Hausdorff "
        "dimension of every subset, whatever its dilatation, so no C¹ chart carries a smooth "
        "curve onto a fractal. A K-quasi-conformal map distorts the dimension within the bound "
        "of Astala (1994, not formalized), dimension d goes to at most 2Kd/(2+(K−1)d), which "
        "is below 2 for d < 2: a quasi-conformal map of finite dilatation never carries a set "
        "of dimension below 2 onto a set of dimension 2. The charts of the quasi-invariance "
        "and of the collars compare the moduli of annuli, which are open sets, and say "
        "nothing about the dimension of the sets that the annuli go around. An α-Hölder "
        "parametrization of a set of dimension d by "
        "an interval has α d ≤ 1: given Shishikura, a parametrization of the boundary of M, "
        "such as the landing map of the external rays that exists when M is locally "
        "connected, has exponent at most 1/2, and the boundary is not the C¹ image of any set "
        "of smaller dimension. For the kernel of a nest: divergent moduli leave a "
        "point, of dimension 0; a kernel of positive dimension forces a finite total modulus "
        "(it contains a point other than c, and the Grötzsch–Teichmüller estimate bounds the "
        "moduli).",
        rays,
    )
    side_bud(
        PEANO_ROOTS,
        "prog:peano",
        "Peano parametrization of M",
        "epimorphisms of CompHaus from the interval",
        "Checked in Lean (IsPeanoObject, IsPeanoObject.locallyConnectedSpace, "
        "IsPeanoObject.exists_regularEpi, mlc_iff_regularEpi, "
        "ShishikuraDimension.holder_exponent_le_half_of_epi). An object of the category of "
        "compact Hausdorff spaces is a Peano object if it is an epimorphic image of the "
        "interval. Such an object is locally connected: an epimorphism is a surjection, "
        "hence a quotient map, and a quotient of the locally connected interval is locally "
        "connected. In this category the epimorphisms are the effective ones, so the "
        "parametrization is a regular epimorphism, the coequalizer of its kernel pair: the "
        "object is the quotient of the interval by a closed equivalence relation (for M, some "
        "closed equivalence relation on the interval, the kernel pair of the chosen "
        "parametrization; the landing relation of the external rays lives on the circle of "
        "angles and belongs to the pinched-disk model of Thurston and Douady–Hubbard, a "
        "different statement that is not formalized). The Hahn–Mazurkiewicz theorem "
        "(published, not formalized) is the converse for continua, so, given the "
        "connectedness of M (Douady–Hubbard), MLC holds exactly when the Mandelbrot object is "
        "a regular quotient of the interval (mlc_iff_regularEpi). Given "
        "Shishikura's theorem, no epimorphism from the interval onto the boundary object is "
        "better than 1/2-Hölder: the parametrization of a fractal is wild.",
        dimension or rays,
    )
    # Ground: the kernel axioms below the first vertebra.
    ground = [
        make(
            Node(
                id=f"axiom:{name}",
                kind="ground",
                cat="axiom",
                title=name,
                sub="kernel axiom",
                text=f"{name} is one of the three axioms that the kernel uses. "
                "The proof of mlc_conjecture depends on no other axiom.",
                lean=name,
                parent=vertebrae[0].id,
            )
        )
        for name in sorted(axioms)
    ]
    for node in ground:
        search.append({"n": node.title, "k": "axiom", "f": "[Lean core]", "l": 0, "o": node.id})
    ground.append(
        make(
            Node(
                id="ground:mathlib",
                kind="ground",
                cat="axiom",
                title="Mathlib · Yoccoz",
                sub="imported libraries",
                text="The library imports Mathlib and the Yoccoz package; their "
                "declarations are not part of this graph, and they add no axioms "
                "beyond the three of the kernel.",
                parent=vertebrae[0].id,
            )
        )
    )
    # Text layout and the heights of the nodes.
    for index, node in enumerate([*vertebrae, head]):
        hand = node.level["n"] - node.level["gen"]
        node.stat = f"{hand:,} declarations · {node.level['lines']:,} lines" + (
            f" + {node.level['gen']:,} generated" if node.level["gen"] else ""
        )
    for node in nodes.values():
        if node.kind == "bud":
            node.stat = stat_line(node.stats)
    for node in nodes.values():
        if node.kind == "vertebra":
            node.lines = wrap(node.title, 30, 1)
            node.sublines = wrap(node.sub, 40, 3)
            node.h = 16 + 19 * len(node.lines) + 15 * len(node.sublines) + 17
        elif node.kind == "head":
            node.w, node.h = HEAD_W, HEAD_H
        else:
            node.lines = wrap(node.title, 23, 2)
            node.sublines = wrap(node.sub, 29, 2)
            node.h = 14 + 17 * len(node.lines) + 14 * len(node.sublines) + 6
            if node.stat:
                node.h += 15
            if node.kind == "ground":
                node.w = 168.0

    totals = add_stats(new_stats(), list(fq_index), fq_index)
    generated_bytes = sum(
        path.stat().st_size for path in (repo_root / "Mlc" / "GridTiles").glob("G*.lean")
    )
    aggregator = repo_root / "Mlc" / "GridCertified.lean"
    if aggregator.is_file():
        generated_bytes += aggregator.stat().st_size
    parameters = {
        "tile_modules": tile_modules,
        "totals": totals,
        "generated_mb": generated_bytes / 1e6,
    }
    return {
        "nodes": nodes,
        "vertebrae": vertebrae,
        "head": head,
        "ground": ground,
        "left": left,
        "right": right,
        "search": search,
        "base_url": base_url,
        "commit": commit,
        "parameters": parameters,
        "owner_index": owner_index,
        "extras": extras,
    }


def tree_height(node: Node) -> float:
    own = max(MIN_LEAF_H, node.h + 14)
    if not node.children:
        return own
    if node.children[0].below:
        return own + sum(tree_height(child) for child in node.children)
    return max(own, sum(tree_height(child) for child in node.children))


def place_tree(node: Node, depth: int, top: float) -> None:
    """Place a node and its subtree; children go beyond it, or under it when `below`."""
    own = max(MIN_LEAF_H, node.h + 14)
    offset = VERTEBRA_W / 2 + LINK_GAP + NODE_W / 2 + depth * (NODE_W + CHAIN_GAP)
    node.x = CENTER + node.side * offset
    if node.children and node.children[0].below:
        node.y = top + own / 2
        cursor = top + own
        for child in node.children:
            place_tree(child, depth, cursor)
            cursor += tree_height(child)
        return
    cursor = top
    centers = []
    for child in node.children:
        place_tree(child, depth + 1, cursor)
        centers.append(child.y)
        cursor += tree_height(child)
    node.y = sum(centers) / len(centers) if centers else top + tree_height(node) / 2


def layout(model: dict[str, object]) -> tuple[float, float]:
    head: Node = model["head"]
    vertebrae: list[Node] = model["vertebrae"]
    ground: list[Node] = model["ground"]
    left, right = model["left"], model["right"]

    head.x, head.y = CENTER, 40 + HEAD_H / 2
    cursor = head.y + HEAD_H / 2 + 54
    count = len(vertebrae)
    for index in range(count - 1, -1, -1):
        node = vertebrae[index]
        # A side with one tree is aligned on the root of the tree, so that the link from
        # the vertebra is level; several trees are centered on the vertebra.
        sides = []
        for trees in (left.get(index, []), right.get(index, [])):
            total = sum(tree_height(t) for t in trees)
            anchor = total / 2
            if len(trees) == 1:
                place_tree(trees[0], 0, 0.0)
                anchor = trees[0].y
            sides.append((trees, total, anchor))
        used = [(total, anchor) for trees, total, anchor in sides if trees]
        up = max([node.h / 2 + ROW_PAD] + [anchor + 4 for _, anchor in used])
        down = max([node.h / 2 + ROW_PAD] + [total - anchor + 4 for total, anchor in used])
        node.x, node.y = CENTER, cursor + up
        for trees, total, anchor in sides:
            top = node.y - anchor
            for tree in trees:
                place_tree(tree, 0, top)
                top += tree_height(tree)
        cursor += up + down
    base = cursor + 40
    spacing = 22.0
    total = sum(n.w for n in ground) + spacing * (len(ground) - 1)
    start = CENTER - total / 2
    for node in ground:
        node.x = start + node.w / 2
        node.y = base + node.h / 2
        start += node.w + spacing
    height = base + max((n.h for n in ground), default=0) + 48
    return WIDTH, height


def link_path(parent: Node, child: Node) -> str:
    if child.kind == "ground":
        x0, y0 = parent.x, parent.y + parent.h / 2
        x1, y1 = child.x, child.y - child.h / 2
        mid = (y0 + y1) / 2
        return f"M{x0:.1f},{y0:.1f} C{x0:.1f},{mid:.1f} {x1:.1f},{mid:.1f} {x1:.1f},{y1:.1f}"
    if child.below:
        x0, y0 = parent.x, parent.y + parent.h / 2
        x1, y1 = child.x, child.y - child.h / 2
        return f"M{x0:.1f},{y0:.1f} L{x1:.1f},{y1:.1f}"
    side = child.side
    x0 = parent.x + side * parent.w / 2
    y0 = parent.y
    x1 = child.x - side * child.w / 2
    y1 = child.y
    dx = abs(x1 - x0) * 0.5
    return (
        f"M{x0:.1f},{y0:.1f} C{x0 + side * dx:.1f},{y0:.1f} "
        f"{x1 - side * dx:.1f},{y1:.1f} {x1:.1f},{y1:.1f}"
    )


def path_to_head(model: dict[str, object], node: Node) -> list[str]:
    """Node ids from a node to the head along the branch and the spine."""
    nodes: dict[str, Node] = model["nodes"]
    vertebrae: list[Node] = model["vertebrae"]
    if node.kind == "head":
        return [node.id]
    path = [node.id]
    current = node
    while current.parent:
        current = nodes[current.parent]
        path.append(current.id)
    if current.kind == "vertebra":
        index = vertebrae.index(current)
        path.extend(v.id for v in vertebrae[index + 1 :])
    if path[-1] != "head":
        path.append("head")
    return path


def text_block(node: Node, title_size: float, sub_size: float) -> str:
    title_lh = title_size + 3
    sub_lh = sub_size + 2.5
    stat_lh = 14.0
    total = title_lh * len(node.lines) + sub_lh * len(node.sublines)
    if node.stat:
        total += stat_lh + 2
    y = node.y - total / 2 + title_size
    out = []
    for line in node.lines:
        out.append(
            f'<text class="t" x="{node.x:.1f}" y="{y:.1f}" font-size="{title_size}">'
            f"{html.escape(line)}</text>"
        )
        y += title_lh
    y += 0.5
    for line in node.sublines:
        out.append(
            f'<text class="s" x="{node.x:.1f}" y="{y:.1f}" font-size="{sub_size}">'
            f"{html.escape(line)}</text>"
        )
        y += sub_lh
    if node.stat:
        out.append(
            f'<text class="st" x="{node.x:.1f}" y="{y + 3:.1f}" font-size="{sub_size - 0.5}">'
            f"{html.escape(node.stat)}</text>"
        )
    return "".join(out)


def compact(count: int) -> str:
    """``15k`` for 15074, ``1.2k`` for 1234, the number itself below a thousand."""
    if count >= 10000:
        return f"{round(count / 1000)}k"
    if count >= 1000:
        return f"{count / 1000:.1f}k"
    return str(count)


def stats_title(stats: dict[str, int], what: str) -> str:
    """Tooltip of a bubble: the count with the split by kind."""
    kinds = ", ".join(
        f"{stats[key]:,} {KIND_WORDS[key][0 if stats[key] == 1 else 1]}"
        for key in STAT_KEYS
        if stats[key]
    )
    return f"{stats['n']:,} {what}: {kinds}"


def bubble(node: Node, stats: dict[str, int], what: str) -> str:
    """A badge on the outer top corner of a node; its radius grows with the log of the count."""
    count = stats["n"]
    if count <= 0:
        return ""
    radius = 8.5 + 3.4 * math.log10(1 + count)
    outward = node.side or (-1 if node.kind == "vertebra" else 1)
    cx = node.x + outward * (node.w / 2 - 4)
    cy = node.y - node.h / 2 + 3
    label = compact(count)
    size = 10.5 if len(label) <= 3 else 9.5
    return (
        f'<g class="bubble"><title>{html.escape(stats_title(stats, what))}</title>'
        f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{radius:.1f}"/>'
        f'<text x="{cx:.1f}" y="{cy + size * 0.36:.1f}" font-size="{size}">{label}</text></g>'
    )


def node_svg(model: dict[str, object], node: Node) -> str:
    path = path_to_head(model, node)
    cat = node.cat
    attrs = (
        f'class="node {node.kind} cat-{cat}" data-id="{html.escape(node.id)}" '
        f'data-cat="{cat}" data-path="{html.escape(" ".join(path))}" '
        f'tabindex="0" role="button" aria-label="{html.escape(node.title)}"'
    )
    if node.kind == "head":
        shape = (
            f'<rect class="shape" x="{node.x - node.w / 2:.1f}" y="{node.y - node.h / 2:.1f}" '
            f'width="{node.w}" height="{node.h}" rx="56"/>'
        )
        body = (
            f'<text class="t head-t" x="{node.x:.1f}" y="{node.y - 14:.1f}">MLC</text>'
            f'<text class="s" x="{node.x:.1f}" y="{node.y + 10:.1f}" font-size="15">'
            "The Mandelbrot set is locally connected</text>"
            f'<text class="m" x="{node.x:.1f}" y="{node.y + 30:.1f}" font-size="12">'
            "mlc_conjecture (h : RootInput) : LocallyConnectedSpace M</text>"
            f'<text class="cond" x="{node.x:.1f}" y="{node.y + 49:.1f}" font-size="12">'
            "conditional on Problems 4.3 and 4.4</text>"
        )
        everything = bubble(node, model["parameters"]["totals"], "declarations in the library")
        return f"<g {attrs}>{shape}{body}{everything}</g>"
    radius = 14 if node.kind == "vertebra" else 12
    shape = (
        f'<rect class="shape" x="{node.x - node.w / 2:.1f}" y="{node.y - node.h / 2:.1f}" '
        f'width="{node.w}" height="{node.h:.1f}" rx="{radius}"/>'
    )
    if node.kind == "vertebra":
        body = text_block(node, 15.5, 12.5)
        number = model["vertebrae"].index(node) + 1
        body += (
            f'<text class="num" x="{node.x - node.w / 2 + 15:.1f}" y="{node.y + 4:.1f}">{number}</text>'
        )
        body += bubble(node, node.level, "declarations on this level")
    else:
        body = text_block(node, 13.5, 11.5)
        if node.kind == "bud":
            body += bubble(node, node.stats, "declarations")
    return f"<g {attrs}>{shape}{body}</g>"


def render_svg(model: dict[str, object], width: float, height: float) -> str:
    nodes: dict[str, Node] = model["nodes"]
    vertebrae: list[Node] = model["vertebrae"]
    head: Node = model["head"]
    ground: list[Node] = model["ground"]

    cord_top = head.y + head.h / 2
    cord_bottom = ground[0].y - ground[0].h / 2 - 8 if ground else height - 40
    parts = [
        f'<svg id="spine" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width:.0f} {height:.0f}" '
        f'width="{width:.0f}" height="{height:.0f}" role="group" '
        'aria-label="Proof spine from the kernel axioms to MLC">'
    ]
    parts.append(
        f'<path class="cord" d="M{CENTER},{cord_top:.1f} L{CENTER},{cord_bottom:.1f}"/>'
        f'<path class="cord-core" d="M{CENTER},{cord_top:.1f} L{CENTER},{cord_bottom:.1f}"/>'
    )
    # Direction marks on the cord: the argument climbs towards the head.
    ordered = [*vertebrae[::-1], head]
    for upper, lower in zip(ordered, ordered[1:]):
        gap_top = upper.y + upper.h / 2
        gap_bottom = lower.y - lower.h / 2
        if gap_bottom - gap_top > 18:
            mid = (gap_top + gap_bottom) / 2
            parts.append(
                f'<path class="chevron" d="M{CENTER - 7},{mid + 4:.1f} L{CENTER},{mid - 5:.1f} '
                f'L{CENTER + 7},{mid + 4:.1f}"/>'
            )
    # Links.
    links = []
    for node in nodes.values():
        if not node.parent:
            continue
        parent = nodes[node.parent]
        links.append(
            f'<path class="link cat-{node.cat}" data-to="{html.escape(node.id)}" '
            f'd="{link_path(parent, node)}"/>'
        )
    parts.append(f'<g class="links">{"".join(links)}</g>')
    parts.append(
        '<g class="nodes">'
        + "".join(node_svg(model, node) for node in nodes.values())
        + "</g>"
    )
    parts.append("</svg>")
    return "".join(parts)


LEGEND = (
    ("open", "Open problem", "open"),
    ("lemma", "Open statement of the programme", "lemma"),
    ("published", "Published, not formalized", "published"),
    ("informal", "Not formalized", "informal"),
    ("checked", "Checked in Lean", "checked"),
    ("num", "Certified computation", "num"),
    ("axiom", "Kernel axiom", "axiom"),
)


def model_json(model: dict[str, object], width: float, height: float) -> str:
    nodes: dict[str, Node] = model["nodes"]
    vertebrae: list[Node] = model["vertebrae"]
    head: Node = model["head"]
    parameters = model["parameters"]
    levels = [
        {"id": node.id, "title": node.title, "stats": node.level}
        for node in [head, *vertebrae[::-1]]
    ]
    levels.extend(
        {
            "id": node.id,
            "title": (
                f"Route Z · {node.title.lower()}"
                if node.id.startswith("z:")
                else f"Programme · {node.title.lower()}"
            ),
            "stats": node.stats,
        }
        for node in model["extras"]
    )
    payload = {
        "width": width,
        "height": height,
        "base": model["base_url"],
        "commit": model["commit"],
        "totals": parameters["totals"],
        "modules": parameters["tile_modules"],
        "generated_mb": round(parameters["generated_mb"], 1),
        "levels": levels,
        "nodes": {
            node.id: {
                "id": node.id,
                "kind": node.kind,
                "cat": node.cat,
                "title": node.title,
                "sub": node.sub,
                "text": node.text,
                "lean": node.lean,
                "file": node.file,
                "line": node.line,
                "count": node.count,
                "stats": node.stats,
                "level": node.level if node.kind in ("vertebra", "head") else None,
                "path": path_to_head(model, node),
                "members": node.members[:120],
                "more": max(0, len(node.members) - 120),
            }
            for node in nodes.values()
        },
        "search": model["search"],
    }
    text = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    return text.replace("</", "<\\/")


STYLE = """
:root {
  --bg: #f5f7fb; --panel: #ffffff; --text: #0f172a; --muted: #475569; --border: #dbe2ea;
  --button-bg: #f8fafc; --stage: #fbfcfe;
  --cord: #94a3b8; --cord-core: #e2e8f0; --link: #94a3b8;
  --spine: #0369a1; --spine-bg: #e0f2fe;
  --head: #6d28d9; --head-bg: #ede9fe;
  --checked: #15803d; --checked-bg: #dcfce7;
  --num: #0e7490; --num-bg: #cffafe;
  --open: #dc2626; --open-bg: #fee2e2;
  --lemma: #ea580c; --lemma-bg: #ffedd5;
  --published: #0f766e; --published-bg: #ccfbf1;
  --informal: #b45309; --informal-bg: #fef3c7;
  --axiom: #475569; --axiom-bg: #e2e8f0;
}
:root[data-theme="dark"] {
  --bg: #0b1220; --panel: #101a2d; --text: #dbe7ff; --muted: #9db0cf; --border: #20304d;
  --button-bg: #13203a; --stage: #070e1c;
  --cord: #3b5a86; --cord-core: #1d2f4d; --link: #4b6288;
  --spine: #7dd3fc; --spine-bg: #0c2a45;
  --head: #c4b5fd; --head-bg: #2a1f55;
  --checked: #4ade80; --checked-bg: #0f2e1c;
  --num: #22d3ee; --num-bg: #0b2f3a;
  --open: #f87171; --open-bg: #3a1216;
  --lemma: #fb923c; --lemma-bg: #3a1e0c;
  --published: #2dd4bf; --published-bg: #0b2f2c;
  --informal: #fbbf24; --informal-bg: #35260a;
  --axiom: #cbd5e1; --axiom-bg: #1c2940;
}
* { box-sizing: border-box; }
body { margin: 0; font-family: "IBM Plex Sans", "Segoe UI", sans-serif; background: var(--bg); color: var(--text); }
.wrap { display: grid; grid-template-rows: auto minmax(0, 1fr); height: 100vh; }
.toolbar {
  display: flex; flex-wrap: wrap; align-items: center; gap: 10px 14px; padding: 10px 16px;
  border-bottom: 1px solid var(--border); background: var(--panel);
}
.toolbar h1 { margin: 0; font-size: 17px; font-weight: 600; }
.toolbar .meta { color: var(--muted); font-size: 13px; }
.toolbar label.search { position: relative; display: inline-flex; align-items: center; gap: 6px; font-size: 13px; color: var(--muted); }
.toolbar input, .toolbar button {
  font: inherit; font-size: 13px; color: var(--text); background: var(--button-bg);
  border: 1px solid var(--border); border-radius: 6px; padding: 5px 9px;
}
.toolbar input { width: 250px; }
.toolbar button { cursor: pointer; }
.toolbar button:hover { border-color: var(--muted); }
.btns { display: inline-flex; gap: 6px; margin-left: auto; }
#results {
  position: absolute; top: 100%; left: 48px; z-index: 20; width: 380px; max-height: 320px; overflow: auto;
  margin: 4px 0 0; padding: 4px; list-style: none; background: var(--panel); color: var(--text);
  border: 1px solid var(--border); border-radius: 8px; box-shadow: 0 8px 24px rgba(0, 0, 0, 0.22);
}
#results[hidden] { display: none; }
#results li { padding: 5px 8px; border-radius: 5px; cursor: pointer; font-size: 12.5px; }
#results li:hover, #results li.on { background: var(--button-bg); }
#results .where { display: block; color: var(--muted); font-size: 11.5px; }
.legend { display: flex; flex-wrap: wrap; gap: 6px; margin: 0; padding: 0; list-style: none; flex-basis: 100%; }
.legend button {
  display: inline-flex; align-items: center; gap: 6px; font-size: 12px; padding: 3px 9px; border-radius: 999px;
}
.legend .dot { width: 11px; height: 11px; border-radius: 50%; border: 2px solid var(--c); background: var(--cb); }
.legend .dot.dashed { border-style: dashed; }
.legend button[aria-pressed="false"] { opacity: 0.45; }
.content { display: grid; grid-template-columns: minmax(0, 1fr) 360px; min-height: 0; }
.stage { overflow: auto; min-height: 0; background: var(--stage); cursor: grab; }
.stage.drag { cursor: grabbing; user-select: none; }
.stage svg { display: block; margin: 0 auto; }
.panel { overflow: auto; padding: 16px 18px 28px; border-left: 1px solid var(--border); background: var(--panel); font-size: 13.5px; line-height: 1.5; }
.panel h2 { margin: 0 0 6px; font-size: 16px; }
.panel h3 { margin: 16px 0 6px; font-size: 12px; text-transform: uppercase; letter-spacing: 0.04em; color: var(--muted); }
.panel p { margin: 6px 0; }
.panel code { font-family: "IBM Plex Mono", "SFMono-Regular", monospace; font-size: 12px; overflow-wrap: anywhere; }
.panel .badge {
  display: inline-block; margin-bottom: 8px; padding: 1px 9px; border-radius: 999px; font-size: 11.5px; font-weight: 600;
  color: var(--n); background: var(--nb); border: 1px solid var(--n);
}
.panel ol.trail { margin: 0; padding-left: 20px; color: var(--muted); font-size: 12.5px; }
.panel ol.trail li { cursor: pointer; }
.panel ol.trail li:hover { color: var(--text); }
.panel ul.members { margin: 0; padding: 0; list-style: none; max-height: 340px; overflow: auto; border: 1px solid var(--border); border-radius: 8px; }
.panel ul.members li { padding: 3px 9px; font-size: 12px; border-bottom: 1px solid var(--border); overflow-wrap: anywhere; }
.panel ul.members li:last-child { border-bottom: 0; }
.panel ul.members li.hit { background: var(--informal-bg); }
.panel ul.members .k { display: inline-block; min-width: 54px; color: var(--muted); font-size: 11px; }
.panel a { color: var(--spine); }
.hint { color: var(--muted); font-size: 12.5px; }
.cat-checked { --n: var(--checked); --nb: var(--checked-bg); }
.cat-num { --n: var(--num); --nb: var(--num-bg); }
.cat-open { --n: var(--open); --nb: var(--open-bg); }
.cat-lemma { --n: var(--lemma); --nb: var(--lemma-bg); }
.cat-published { --n: var(--published); --nb: var(--published-bg); }
.cat-informal { --n: var(--informal); --nb: var(--informal-bg); }
.cat-axiom { --n: var(--axiom); --nb: var(--axiom-bg); }
.cat-spine { --n: var(--spine); --nb: var(--spine-bg); }
.cat-head { --n: var(--head); --nb: var(--head-bg); }
#spine .cord { fill: none; stroke: var(--cord); stroke-width: 22; stroke-linecap: round; }
#spine .cord-core { fill: none; stroke: var(--cord-core); stroke-width: 8; stroke-linecap: round; }
#spine .chevron { fill: none; stroke: var(--muted); stroke-width: 2.4; stroke-linecap: round; stroke-linejoin: round; opacity: 0.7; }
#spine .link { fill: none; stroke: var(--n, var(--link)); stroke-width: 2.6; opacity: 0.75; transition: opacity .12s, stroke-width .12s; }
#spine .link.cat-informal, #spine .link.cat-published { stroke-dasharray: 7 5; }
#spine .node { cursor: pointer; transition: opacity .15s; outline: none; }
#spine .node .shape { fill: var(--nb); stroke: var(--n); stroke-width: 1.8; transition: stroke-width .12s; }
#spine .node .t { fill: var(--text); font-weight: 600; text-anchor: middle; }
#spine .node .s { fill: var(--muted); text-anchor: middle; }
#spine .node .m { fill: var(--muted); text-anchor: middle; font-family: "IBM Plex Mono", "SFMono-Regular", monospace; }
#spine .node .num { fill: var(--n); font-size: 13px; font-weight: 700; text-anchor: middle; opacity: 0.85; }
#spine .node .cond { fill: var(--informal); text-anchor: middle; font-weight: 600; }
#spine .node .st { fill: var(--n); text-anchor: middle; font-weight: 600; }
#spine .bubble circle { fill: var(--n); stroke: var(--stage); stroke-width: 2.2; }
#spine .bubble text { fill: var(--bg); font-weight: 700; text-anchor: middle; }
.zoombox { display: inline-flex; gap: 6px; }
.progress-mode .spine-only { display: none !important; }
.panel table.scale { width: 100%; border-collapse: collapse; font-size: 12px; margin-top: 6px; }
.panel table.scale th { text-align: right; font-weight: 600; color: var(--muted); padding: 2px 4px; font-size: 11px; }
.panel table.scale th:first-child, .panel table.scale td:first-child { text-align: left; }
.panel table.scale td { padding: 3px 4px; border-top: 1px solid var(--border); text-align: right; font-variant-numeric: tabular-nums; vertical-align: top; }
.panel table.scale tr[data-go] { cursor: pointer; }
.panel table.scale tr[data-go]:hover { background: var(--button-bg); }
.panel .bar { height: 4px; border-radius: 2px; background: var(--border); margin-top: 3px; }
.panel .bar i { display: block; height: 100%; border-radius: 2px; background: var(--spine); }
.panel .gen { color: var(--muted); font-size: 10.5px; }
.panel ul.facts { margin: 6px 0; padding: 0; list-style: none; }
.panel ul.facts li { display: flex; justify-content: space-between; gap: 10px; padding: 2px 0; border-bottom: 1px dotted var(--border); }
#spine .node .head-t { font-size: 30px; font-weight: 700; letter-spacing: 0.06em; }
#spine .node.cat-informal .shape { stroke-dasharray: 7 4; }
#spine .node.cat-published .shape { stroke-dasharray: 3 3; }
#spine .node.cat-lemma .shape { stroke-width: 2.4; }
#spine .node.cat-open .shape { stroke-width: 2.8; filter: drop-shadow(0 0 5px var(--n)); animation: pulse 2.6s ease-in-out infinite; }
#spine .node:hover .shape, #spine .node:focus-visible .shape, #spine .node.hl .shape { stroke-width: 3.2; }
#spine .node.sel .shape { stroke-width: 4; }
#spine .link.hl { opacity: 1; stroke-width: 4.4; }
#spine.tracing .node:not(.hl), #spine.tracing .link:not(.hl) { opacity: 0.32; }
#spine.hide-open [data-cat="open"], #spine.hide-informal [data-cat="informal"], #spine.hide-checked [data-cat="checked"],
#spine.hide-lemma [data-cat="lemma"], #spine.hide-published [data-cat="published"],
#spine.hide-num [data-cat="num"], #spine.hide-axiom [data-cat="axiom"] { opacity: 0.1; }
@keyframes pulse { 0%, 100% { stroke-opacity: 1; } 50% { stroke-opacity: 0.45; } }
@media (prefers-reduced-motion: reduce) { #spine .node.cat-open .shape { animation: none; } }
.progress-panel { display: none; padding: 22px 26px 40px; overflow: auto; min-height: 0; background: var(--bg); }
@media (max-width: 900px) {
  .wrap { height: auto; min-height: 100vh; }
  .content { grid-template-columns: 1fr; }
  .stage { height: 70vh; }
  .panel { border-left: 0; border-top: 1px solid var(--border); }
}
"""

SCRIPT = r"""
(function () {
  const data = JSON.parse(document.getElementById("spine-data").textContent);
  const svg = document.getElementById("spine");
  const stage = document.getElementById("stage");
  const panel = document.getElementById("panel");
  const searchEl = document.getElementById("search");
  const resultsEl = document.getElementById("results");
  const graphPanelEl = document.getElementById("graphPanel");
  const progressPanelEl = document.getElementById("progressPanel");
  const progressGraphicEl = document.getElementById("progressGraphic");
  const progressBtn = document.getElementById("progressBtn");
  const themeBtn = document.getElementById("themeBtn");
  const THEME_KEY = "mlc_graph_theme";
  const els = {};
  svg.querySelectorAll(".node").forEach((g) => { els[g.dataset.id] = g; });
  const linkOf = {};
  svg.querySelectorAll(".link").forEach((p) => { linkOf[p.dataset.to] = p; });
  const KIND_NAME = {
    head: "Statement", vertebra: "Milestone theorem", bud: "Supporting declarations",
    tip: "Branch tip", ground: "Kernel axiom",
  };
  const CAT_NAME = {
    checked: "Checked in Lean", num: "Kernel-checked computation", open: "Open problem (explicit hypothesis)",
    lemma: "Open statement of the programme (stated in Lean, proof open)", published: "Published theorem, not formalized",
    informal: "Not formalized", axiom: "Kernel axiom", spine: "Checked in Lean", head: "Conditional on RootInput",
  };
  let selected = null;

  function esc(text) {
    return String(text == null ? "" : text).replace(/[&<>"']/g, (c) => (
      { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  }

  // Zoom: the SVG is scaled by its CSS size and the stage scrolls.
  let zoom = 1;
  function applyZoom(anchorX, anchorY) {
    const before = { w: svg.clientWidth, h: svg.clientHeight };
    svg.style.width = Math.round(data.width * zoom) + "px";
    svg.style.height = Math.round(data.height * zoom) + "px";
    if (anchorX != null && before.w) {
      const k = svg.clientWidth / before.w;
      stage.scrollLeft = (stage.scrollLeft + anchorX) * k - anchorX;
      stage.scrollTop = (stage.scrollTop + anchorY) * k - anchorY;
    }
  }
  function setZoom(next, ax, ay) {
    zoom = Math.max(0.35, Math.min(2.4, next));
    applyZoom(ax, ay);
  }
  function fit() {
    zoom = Math.max(0.35, Math.min(1.6, (stage.clientWidth - 8) / data.width));
    applyZoom();
    stage.scrollTo(0, 0);
  }
  document.getElementById("zoomIn").addEventListener("click", () => setZoom(zoom * 1.2, stage.clientWidth / 2, stage.clientHeight / 2));
  document.getElementById("zoomOut").addEventListener("click", () => setZoom(zoom / 1.2, stage.clientWidth / 2, stage.clientHeight / 2));
  document.getElementById("fitBtn").addEventListener("click", fit);
  stage.addEventListener("wheel", (ev) => {
    if (!(ev.ctrlKey || ev.metaKey)) return;
    ev.preventDefault();
    const box = stage.getBoundingClientRect();
    setZoom(zoom * (ev.deltaY < 0 ? 1.1 : 1 / 1.1), ev.clientX - box.left, ev.clientY - box.top);
  }, { passive: false });
  let drag = null;
  stage.addEventListener("pointerdown", (ev) => {
    if (ev.target.closest(".node") || ev.button !== 0) return;
    drag = { x: ev.clientX, y: ev.clientY, sx: stage.scrollLeft, sy: stage.scrollTop };
    stage.classList.add("drag");
    stage.setPointerCapture(ev.pointerId);
  });
  stage.addEventListener("pointermove", (ev) => {
    if (!drag) return;
    stage.scrollLeft = drag.sx - (ev.clientX - drag.x);
    stage.scrollTop = drag.sy - (ev.clientY - drag.y);
  });
  const endDrag = () => { drag = null; stage.classList.remove("drag"); };
  stage.addEventListener("pointerup", endDrag);
  stage.addEventListener("pointercancel", endDrag);

  // Tracing: a node lights the way to the head.
  function trace(id) {
    clearTrace();
    const node = data.nodes[id];
    if (!node) return;
    svg.classList.add("tracing");
    node.path.forEach((step) => {
      if (els[step]) els[step].classList.add("hl");
      if (linkOf[step]) linkOf[step].classList.add("hl");
    });
  }
  function clearTrace() {
    svg.classList.remove("tracing");
    svg.querySelectorAll(".hl").forEach((e) => e.classList.remove("hl"));
  }
  svg.addEventListener("pointerover", (ev) => {
    const g = ev.target.closest(".node");
    if (g) trace(g.dataset.id);
  });
  svg.addEventListener("pointerout", (ev) => {
    if (!ev.target.closest(".node")) return;
    if (selected) trace(selected); else clearTrace();
  });
  svg.addEventListener("focusin", (ev) => {
    const g = ev.target.closest(".node");
    if (g) trace(g.dataset.id);
  });

  function sourceLink(node, file, line) {
    if (!data.base || !file || file.startsWith("[")) return "";
    return `${data.base}/blob/${data.commit}/${file}${line ? "#L" + line : ""}`;
  }

  function fmt(n) { return Number(n).toLocaleString("en-US"); }

  // Counts of declarations, by kind and by source, for the overview and for a node.
  function factsList(s) {
    const rows = [
      ["Theorems", s.thm], ["Definitions", s.def], ["Structures", s.str], ["Axioms", s.ax],
    ].filter((r) => r[1]).map((r) => `<li><span>${r[0]}</span><b>${fmt(r[1])}</b></li>`);
    if (s.lines) rows.push(`<li><span>Lines of Lean (hand-written)</span><b>${fmt(s.lines)}</b></li>`);
    if (s.gen) rows.push(`<li><span>Generated by a script</span><b>${fmt(s.gen)}</b></li>`);
    return `<ul class="facts">${rows.join("")}</ul>`;
  }

  function scaleSection() {
    const t = data.totals;
    const hand = t.n - t.gen;
    const rows = data.levels.map((lv) => {
      const s = lv.stats;
      return { id: lv.id, title: lv.title, hand: s.n - s.gen, thm: s.thm - s.gen_thm, lines: s.lines, gen: s.gen };
    });
    const peak = Math.max(1, ...rows.map((r) => r.hand));
    const body = rows.map((r) => `<tr data-go="${esc(r.id)}"><td>${esc(r.title)}
      <div class="bar"><i style="width:${(100 * r.hand / peak).toFixed(1)}%"></i></div></td>
      <td>${fmt(r.hand)}</td><td>${fmt(r.thm)}</td><td>${fmt(r.lines)}</td></tr>`).join("");
    return `
      <h3>Scale of the formalization</h3>
      <p><b>${fmt(t.n)}</b> declarations: ${fmt(t.thm)} theorems,
      ${fmt(t.def + t.str + t.ax)} definitions, structures and axioms.</p>
      <p><b>${fmt(hand)}</b> are written by hand (${fmt(t.thm - t.gen_thm)} theorems,
      ${fmt(t.lines)} lines of Lean). The other <b>${fmt(t.gen)}</b> are generated: ${fmt(data.modules)} modules
      (${data.generated_mb} MB) with the certificates of the kernel-checked grid, ${fmt(t.gen_thm)} theorems and
      ${fmt(t.gen_def)} definitions that the kernel evaluates.</p>
      <p class="hint">The bubble on a node counts the declarations that hang on it; its size grows
      with the logarithm of the count. A level is a vertebra with everything that first hangs on it.</p>
      <table class="scale"><thead><tr><th>Level (top to bottom)</th><th>By hand</th><th>Thm</th><th>Lines</th></tr></thead>
      <tbody>${body}</tbody></table>
      <p class="hint">The grid adds ${fmt(t.gen)} generated declarations to the level “Completion ⇔ coverage”.</p>`;
  }

  function overview(keepHash) {
    selected = null;
    if (!keepHash && window.history && history.replaceState) {
      history.replaceState(null, "", location.pathname + location.search);
    }
    svg.querySelectorAll(".sel").forEach((e) => e.classList.remove("sel"));
    clearTrace();
    panel.innerHTML = `
      <h2>How to read the figure</h2>
      <p>The spine climbs from the three kernel axioms at the bottom to the statement of MLC at the top.
      Each vertebra is a theorem of the Lean library, and each one builds on the vertebrae below it.</p>
      <p>Branches carry what a vertebra needs: checked theorems, the kernel-checked grid, and at the tips
      the <b style="color:var(--open)">open problems</b> of the root, the
      <b style="color:var(--lemma)">open statements of the programme</b> into which they are decomposed, the
      <b style="color:var(--published)">published cases</b> and the
      <b style="color:var(--informal)">targets of Dudko's programme</b> that are not formalized.</p>
      <p class="hint">Hover a node to light its way to the head. Click it for the statement, the Lean name
      and the declarations behind it. Search finds any declaration. Ctrl and the wheel zoom; drag moves.</p>
      ${scaleSection()}`;
    panel.querySelectorAll("tr[data-go]").forEach((tr) => tr.addEventListener("click", () => select(tr.dataset.go)));
  }

  function select(id, focusName) {
    const node = data.nodes[id];
    if (!node) return;
    selected = id;
    if (window.history && history.replaceState) history.replaceState(null, "", "#n=" + encodeURIComponent(id));
    svg.querySelectorAll(".sel").forEach((e) => e.classList.remove("sel"));
    if (els[id]) {
      els[id].classList.add("sel");
      const box = els[id].getBoundingClientRect();
      const view = stage.getBoundingClientRect();
      if (box.top < view.top + 40 || box.bottom > view.bottom - 40 || box.left < view.left || box.right > view.right) {
        const dy = box.top + box.height / 2 - (view.top + view.height / 2);
        const dx = box.left + box.width / 2 - (view.left + view.width / 2);
        stage.scrollBy({ top: dy, left: dx, behavior: "smooth" });
      }
    }
    trace(id);
    const link = sourceLink(node, node.file, node.line);
    const trail = node.path.slice(1).map((step) => data.nodes[step]).filter(Boolean);
    const where = node.file && !node.file.startsWith("[")
      ? `<p><code>${esc(node.file)}${node.line ? ":" + node.line : ""}</code>${link ? ` · <a href="${esc(link)}" target="_blank" rel="noopener">source</a>` : ""}</p>` : "";
    const lean = node.lean ? `<p>Lean: <code>${esc(node.lean)}</code></p>` : "";
    const count = node.count ? `<p class="hint">${node.count.toLocaleString()} declarations in this group.</p>` : "";
    const scale = node.level
      ? `<h3>This level with its branches</h3>${factsList(node.level)}`
      : (node.stats && node.stats.n > 1 ? `<h3>Declarations by kind</h3>${factsList(node.stats)}` : "");
    const rows = node.members.map((m) => {
      const hit = focusName && m.n === focusName ? " class=\"hit\"" : "";
      return `<li${hit}><span class="k">${esc(m.k)}</span>${esc(m.n)}<br><span class="hint">${esc(m.f)}:${m.l}</span></li>`;
    }).join("");
    const members = node.members.length > 1 || node.kind === "bud"
      ? `<h3>Declarations</h3><ul class="members">${rows}</ul>${node.more ? `<p class="hint">and ${node.more} more.</p>` : ""}` : "";
    const trailHtml = trail.length
      ? `<h3>Way to the head</h3><ol class="trail">${trail.map((t) => `<li data-go="${esc(t.id)}">${esc(t.title)}</li>`).join("")}</ol>` : "";
    panel.innerHTML = `
      <span class="badge cat-${esc(node.cat)}">${esc(CAT_NAME[node.cat] || node.cat)}</span>
      <h2>${esc(node.title)}</h2>
      <p class="hint">${esc(KIND_NAME[node.kind] || "")}${node.sub && node.kind !== "vertebra" ? " · " + esc(node.sub) : ""}</p>
      ${node.text ? `<p>${esc(node.text)}</p>` : ""}${lean}${where}${count}${scale}${members}${trailHtml}`;
    const hit = panel.querySelector("li.hit");
    if (hit) hit.scrollIntoView({ block: "center" });
    panel.querySelectorAll("[data-go]").forEach((li) => li.addEventListener("click", () => select(li.dataset.go)));
  }

  svg.addEventListener("click", (ev) => {
    const g = ev.target.closest(".node");
    if (g) select(g.dataset.id); else overview();
  });
  svg.addEventListener("keydown", (ev) => {
    const g = ev.target.closest(".node");
    if (g && (ev.key === "Enter" || ev.key === " ")) { ev.preventDefault(); select(g.dataset.id); }
    if (ev.key === "Escape") overview();
  });

  // Search over the declarations of the figure.
  let hits = [];
  let cursor = -1;
  function runSearch() {
    const q = searchEl.value.trim().toLowerCase();
    hits = [];
    if (q.length >= 2) {
      for (const row of data.search) {
        if (row.n.toLowerCase().includes(q)) hits.push(row);
        if (hits.length >= 14) break;
      }
    }
    cursor = -1;
    resultsEl.hidden = hits.length === 0;
    resultsEl.innerHTML = hits.map((row, i) => {
      const owner = data.nodes[row.o];
      return `<li data-i="${i}">${esc(row.n)}<span class="where">${esc(row.k)} · ${esc(owner ? owner.title : "")}</span></li>`;
    }).join("");
  }
  function pick(i) {
    const row = hits[i];
    if (!row) return;
    resultsEl.hidden = true;
    select(row.o, row.n);
  }
  searchEl.addEventListener("input", runSearch);
  searchEl.addEventListener("keydown", (ev) => {
    if (ev.key === "ArrowDown" || ev.key === "ArrowUp") {
      ev.preventDefault();
      cursor = Math.max(0, Math.min(hits.length - 1, cursor + (ev.key === "ArrowDown" ? 1 : -1)));
      resultsEl.querySelectorAll("li").forEach((li, i) => li.classList.toggle("on", i === cursor));
    } else if (ev.key === "Enter") {
      pick(cursor >= 0 ? cursor : 0);
    } else if (ev.key === "Escape") {
      resultsEl.hidden = true;
    }
  });
  resultsEl.addEventListener("click", (ev) => {
    const li = ev.target.closest("li");
    if (li) pick(Number(li.dataset.i));
  });
  document.addEventListener("click", (ev) => {
    if (!ev.target.closest(".search")) resultsEl.hidden = true;
  });

  // Legend chips hide a category of nodes.
  document.querySelectorAll(".legend button").forEach((btn) => {
    btn.addEventListener("click", () => {
      const on = btn.getAttribute("aria-pressed") !== "true";
      btn.setAttribute("aria-pressed", String(on));
      svg.classList.toggle("hide-" + btn.dataset.cat, !on);
    });
  });

  // Theme and the progress view.
  function applyTheme(theme) {
    document.documentElement.setAttribute("data-theme", theme);
    try { localStorage.setItem(THEME_KEY, theme); } catch (_err) {}
    themeBtn.textContent = theme === "dark" ? "Theme: Dark" : "Theme: Light";
  }
  let saved = null;
  try { saved = localStorage.getItem(THEME_KEY); } catch (_err) {}
  applyTheme(saved === "dark" || saved === "light" ? saved
    : (window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light"));
  themeBtn.addEventListener("click", () => {
    applyTheme(document.documentElement.getAttribute("data-theme") === "dark" ? "light" : "dark");
  });

  let progressLoaded = false;
  async function loadProgress() {
    if (progressLoaded) return;
    progressLoaded = true;
    try {
      const response = await fetch("progress_fragment.html", { cache: "no-store" });
      if (!response.ok) throw new Error("Failed to load progress_fragment.html");
      progressGraphicEl.innerHTML = await response.text();
    } catch (err) {
      progressLoaded = false;
      progressGraphicEl.textContent = String(err && err.message ? err.message : err);
    }
  }
  function setProgress(visible) {
    graphPanelEl.style.display = visible ? "none" : "grid";
    progressPanelEl.style.display = visible ? "block" : "none";
    document.body.classList.toggle("progress-mode", visible);
    progressBtn.textContent = visible ? "View: Spine" : "View: Progress";
    if (window.history && history.replaceState) {
      history.replaceState(null, "", visible ? "#progress" : location.pathname + location.search);
    }
    if (visible) loadProgress(); else fit();
  }
  progressBtn.addEventListener("click", () => setProgress(progressPanelEl.style.display !== "block"));

  fit();
  overview(true);
  window.addEventListener("resize", () => { if (progressPanelEl.style.display !== "block") fit(); });
  function followHash() {
    const hash = location.hash;
    const progressOn = progressPanelEl.style.display === "block";
    if (hash === "#progress") {
      if (!progressOn) setProgress(true);
      return;
    }
    if (progressOn) setProgress(false);
    if (hash.startsWith("#n=")) select(decodeURIComponent(hash.slice(3)));
  }
  window.addEventListener("hashchange", followHash);
  followHash();
})();
"""


def spine_page_html(title: str, model: dict[str, object], metrics: dict[str, object]) -> str:
    width, height = layout(model)
    svg = render_svg(model, width, height)
    data = model_json(model, width, height)
    percent = 100.0 - float(metrics.get("area_upper_percent", 100.0))
    totals = model["parameters"]["totals"]
    by_hand = totals["n"] - totals["gen"]
    other = totals["def"] + totals["str"] + totals["ax"]
    summary = (
        f"Resolved share {percent:.3f}% · {int(metrics.get('open_frontier', 0))} open problems · "
        f"{int(metrics.get('open_lemmas', 0))} open statements of the programme · "
        f"{totals['n']:,} declarations: {totals['thm']:,} theorems, "
        f"{other:,} definitions, structures and axioms · {by_hand:,} written by hand, "
        f"{totals['gen']:,} generated (the certificates of the grid)"
    )
    chips = "".join(
        f'<li><button type="button" data-cat="{cat}" aria-pressed="true">'
        f'<span class="dot{" dashed" if cat == "informal" else ""}" '
        f'style="--c:var(--{cat});--cb:var(--{cat}-bg)"></span>{html.escape(label)}</button></li>'
        for cat, label, _ in LEGEND
    )
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<link rel="icon" href="data:,">
<title>{html.escape(title)}</title>
<style>{STYLE}
{PROGRESS_CSS}</style>
</head>
<body>
<div class="wrap">
  <header class="toolbar">
    <h1>{html.escape(title)}</h1>
    <span class="meta" id="summary">{html.escape(summary)}</span>
    <label class="search spine-only">Search
      <input id="search" type="search" placeholder="declaration name" autocomplete="off">
      <ul id="results" hidden></ul>
    </label>
    <div class="btns">
      <span class="zoombox spine-only">
        <button id="zoomOut" type="button" title="Zoom out">−</button>
        <button id="zoomIn" type="button" title="Zoom in">+</button>
        <button id="fitBtn" type="button" title="Fit the figure to the width">Fit</button>
      </span>
      <button id="progressBtn" type="button">View: Progress</button>
      <button id="themeBtn" type="button">Theme</button>
    </div>
    <ul class="legend spine-only" id="legend">{chips}</ul>
  </header>
  <main class="content" id="graphPanel">
    <div class="stage" id="stage">{svg}</div>
    <aside class="panel" id="panel"></aside>
  </main>
  <section class="progress-panel" id="progressPanel"><div id="progressGraphic">Loading progress…</div></section>
</div>
<script id="spine-data" type="application/json">{data}</script>
<script>{SCRIPT}</script>
</body>
</html>
"""
