#!/usr/bin/env python3
"""Generate the rooted dependency figure of the Lean library.

The graph is declaration-level and cross-file (all `Mlc/*.lean`). Edges come
from the constants in elaborated Lean types and proof terms; generated
projection and constructor paths are collapsed to source declarations. The
graph is validated (rooted at `mlc_conjecture` and at the side results of the
programme such as the measure step of Route Z, acyclic, exactly the ground
axioms, exactly the operational forms of the two open problems of Dudko) and drawn as one 2D figure, the
spine of the proof (see `spine_graph.py`).

Output layout:
  site/
    index.html
    mlc_conjecture/
      index.html            the figure, its side panel and the search
      progress_fragment.html, progress.html, progress_*.tex, progress_map.svg
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import argparse
import html
import json
import re
import shutil
import subprocess
import sys
import tempfile
from collections import deque
from graphlib import CycleError, TopologicalSorter

from progress_report import progress_metrics_from_worktree, write_progress_assets
from spine_graph import SIDE_ROOTS, build_model, spine_page_html
from typology import object_usage


DECL_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected|unsafe|partial|mutual)\s+)*"
    r"(lemma|theorem|def|abbrev|axiom|structure|inductive|class|instance)\s+([^\s(:=\[{]+)"
)
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section\b")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z0-9_.']+)?\s*$")
EMBEDDED_AXIOMS = ("Quot.sound", "propext", "Classical.choice")
ROOT_SYMBOL = "MLC.mlc_conjecture"
OPEN_OBLIGATIONS = {
    "MLC.Problem43PseudoSiegelAPrioriBoundsData",
    "MLC.Problem44VirtualMoleculeData",
}
VIRTUAL_MOLECULE_PROGRAMME = {
    "MLC.Quadratic.filled_julia_set_compact",
    "MLC.Quadratic.filled_julia_set_connected_proved",
    "MLC.Quadratic.julia_subset_filled_julia",
    "MLC.Research.directed_intersection_continuum",
    "MLC.Research.exists_minimal_connected_hull",
    "MLC.Research.FirstReturnSchedule",
    "MLC.Research.CriticalOrbitWindow",
    "MLC.Research.VirtualJuliaNest",
    "MLC.Research.VirtualJuliaNest.carrier",
    "MLC.Research.VirtualJuliaNest.PartialInvariance",
    "MLC.Research.VirtualJuliaNest.SeparationEstimate",
    "MLC.Research.VirtualPhaseParameter",
    "MLC.Research.VirtualPhaseParameter.parameterSeparationEstimate",
    "MLC.Research.VirtualMoleculeAPrioriControl",
    "MLC.Quadratic.mandelbrot_subset_closedBall",
    "MLC.Quadratic.isCompact_mandelbrot",
    "MLC.Research.CandidateSystem.VirtualMoleculeResidual",
    "MLC.Research.CandidateSystem.residualOuterArea",
    "MLC.Research.CandidateSystem.residualOuterArea_le_four_pi",
    "MLC.Research.CandidateSystem.VirtualMoleculeCompletion",
    "MLC.Research.CandidateSystem.withVirtualMolecule_realization",
    "MLC.Research.CandidateSystem.withVirtualMolecule_coverage_iff_completion",
}


@dataclass(frozen=True)
class Decl:
    kind: str
    name: str
    fq_name: str
    file: str
    line: int
    end_line: int


def strip_comments(line: str, block_depth: int) -> tuple[str, int]:
    i = 0
    out: list[str] = []
    while i < len(line):
        if block_depth > 0:
            if line.startswith("/-", i):
                block_depth += 1
                i += 2
            elif line.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if line.startswith("--", i):
            break
        if line.startswith("/-", i):
            block_depth += 1
            i += 2
            continue
        out.append(line[i])
        i += 1
    return "".join(out), block_depth


def parse_decls_from_file(file_path: Path, repo_root: Path) -> tuple[list[Decl], list[str]]:
    text = file_path.read_text(encoding="utf-8")
    raw_lines = text.splitlines()

    stripped_lines: list[str] = []
    block_depth = 0
    for line in raw_lines:
        stripped, block_depth = strip_comments(line, block_depth)
        stripped_lines.append(stripped)

    rel_file = str(file_path.relative_to(repo_root))
    decl_meta: list[tuple[int, str, str, str]] = []  # line, kind, name, fq_name
    scope_stack: list[tuple[str, list[str] | None]] = []
    ns_parts: list[str] = []

    for line_no, line in enumerate(stripped_lines, start=1):
        ns_match = NS_RE.match(line)
        if ns_match:
            parts = ns_match.group(1).split(".")
            scope_stack.append(("namespace", parts))
            ns_parts.extend(parts)
            continue

        if SECTION_RE.match(line):
            scope_stack.append(("section", None))
            continue

        if END_RE.match(line):
            if scope_stack:
                kind, payload = scope_stack.pop()
                if kind == "namespace" and payload is not None:
                    del ns_parts[-len(payload) :]
            continue

        m = DECL_RE.match(line)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        if name.startswith(("(", ":", "{", "[")):
            continue
        fq_name = ".".join(ns_parts + [name]) if ns_parts else name
        decl_meta.append((line_no, kind, name, fq_name))

    decls: list[Decl] = []
    for i, (line_no, kind, name, fq_name) in enumerate(decl_meta):
        end_line = decl_meta[i + 1][0] - 1 if i + 1 < len(decl_meta) else len(raw_lines)
        decls.append(
            Decl(
                kind=kind,
                name=name,
                fq_name=fq_name,
                file=rel_file,
                line=line_no,
                end_line=end_line,
            )
        )
    return decls, stripped_lines


def build_full_graph(repo_root: Path) -> tuple[dict[str, Decl], dict[str, set[str]]]:
    """Kernel dependency export; comments and unresolved short names add no edges."""
    fq_index: dict[str, Decl] = {}
    for path in sorted((repo_root / "Mlc").rglob("*.lean")):
        decls, _ = parse_decls_from_file(path, repo_root)
        for decl in decls:
            fq_index.setdefault(decl.fq_name, decl)
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", "export_dependencies.lean"],
        cwd=repo_root, text=True, capture_output=True, check=False,
    )
    if proc.returncode:
        raise RuntimeError("Lean dependency export failed:\n" + proc.stdout + proc.stderr)
    rows = json.loads(proc.stdout)
    raw = {row["name"]: set(row["dependencies"]) for row in rows}
    # Retain only declarations actually present in the checked environment.
    fq_index = {name: decl for name, decl in fq_index.items() if name in raw}
    edges: dict[str, set[str]] = {name: set() for name in fq_index}
    for name in fq_index:
        pending = list(raw.get(name, ()))
        seen = {name}
        while pending:
            dep = pending.pop()
            if dep in seen:
                continue
            seen.add(dep)
            if dep in fq_index:
                edges[name].add(dep)
            elif dep in raw:
                # Autogenerated structure projections/constructors are not
                # theorem nodes; preserve their dependencies by contraction.
                pending.extend(raw[dep])
    for name in EMBEDDED_AXIOMS:
        fq_index[name] = Decl("axiom", name.split(".")[-1], name, "[Lean core]", 0, 0)
        edges[name] = set()
    return fq_index, edges


def rooted_closure(root: str, edges: dict[str, set[str]]) -> tuple[set[str], dict[str, int]]:
    reachable: set[str] = set()
    depth: dict[str, int] = {}
    q: deque[str] = deque([root])
    reachable.add(root)
    depth[root] = 0

    while q:
        u = q.popleft()
        for v in edges.get(u, set()):
            if v in reachable:
                continue
            reachable.add(v)
            depth[v] = depth[u] + 1
            q.append(v)
    return reachable, depth


def collect_axioms_from_check_axioms(repo_root: Path) -> set[str]:
    """Read the semantic axiom frontier emitted by `check_axioms.lean`.

    This complements the textual dependency graph by adding axioms that are
    introduced transitively through imported declarations (for example from
    upstream packages).
    """
    cmd = ["lake", "env", "lean", "--run", "check_axioms.lean"]
    try:
        proc = subprocess.run(
            cmd,
            cwd=repo_root,
            check=False,
            text=True,
            capture_output=True,
        )
    except FileNotFoundError:
        raise RuntimeError("Cannot collect semantic axiom frontier: `lake` was not found")
    if proc.returncode != 0:
        detail = (proc.stdout + "\n" + proc.stderr).strip()
        raise RuntimeError(
            "Cannot collect semantic axiom frontier: `check_axioms.lean` failed"
            + (f"\n{detail}" if detail else "")
        )

    axioms: set[str] = set()
    collecting = False
    for raw in proc.stdout.splitlines():
        line = raw.strip()
        if line == "All axioms used:":
            collecting = True
            continue
        if not collecting:
            continue
        if not line.startswith("- "):
            if line:
                break
            continue
        ax = line[2:].strip()
        if ax:
            axioms.add(ax)
    if not collecting:
        raise RuntimeError(
            "Cannot collect semantic axiom frontier: `All axioms used:` block was not found"
        )
    return axioms


def index_html(links: list[tuple[str, str]]) -> str:
    items = "\n".join(
        f'    <li><a href="{html.escape(href)}">{html.escape(label)}</a></li>'
        for label, href in links
    )
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>MLC Dependency Graph</title>
  <style>
    body {{
      margin: 24px;
      font-family: "IBM Plex Sans", "Segoe UI", sans-serif;
      background: #f8fafc;
      color: #0f172a;
    }}
    h1 {{ margin-top: 0; font-size: 22px; }}
    ul {{ line-height: 1.9; }}
    a {{ color: #1d4ed8; text-decoration: none; }}
    a:hover {{ text-decoration: underline; }}
  </style>
</head>
<body>
  <h1>MLC Dependency Graph</h1>
  <ul>
{items}
  </ul>
</body>
</html>
"""


def build_payload(
    fq_index: dict[str, Decl],
    edges: dict[str, set[str]],
    root: Decl,
    axiom_frontier: set[str],
) -> dict[str, object]:
    """The rooted graph: the declarations reachable from the root and from the side results,
    the dependency edges, and the kernel axioms."""
    reachable, _ = rooted_closure(root.fq_name, edges)
    for side in SIDE_ROOTS:
        if side not in fq_index:
            raise RuntimeError(f"Side result not found: {side}")
        reachable |= rooted_closure(side, edges)[0]
    reachable |= axiom_frontier
    nodes = [
        {
            "id": name,
            "kind": fq_index[name].kind,
            "proof_status": "open" if name in OPEN_OBLIGATIONS else "checked",
        }
        for name in sorted(reachable)
    ]
    edge_payload = [
        {"source": src, "target": dst}
        for src in sorted(reachable)
        for dst in sorted(edges.get(src, set()))
        if dst in reachable
    ]
    edge_payload.extend(
        {"source": root.fq_name, "target": name} for name in sorted(axiom_frontier)
    )
    return {
        "root": root.fq_name,
        "side_roots": list(SIDE_ROOTS),
        "nodes": nodes,
        "edges": edge_payload,
    }


def validate_research_graph(
    payload: dict[str, object], declarations: dict[str, Decl]
) -> None:
    nodes = {node["id"]: node for node in payload["nodes"]}
    adjacency = {name: set() for name in nodes}
    for edge in payload["edges"]:
        if edge["source"] not in nodes or edge["target"] not in nodes:
            raise RuntimeError("Graph edge has an unknown endpoint")
        adjacency[edge["source"]].add(edge["target"])
    reachable, _ = rooted_closure(payload["root"], adjacency)
    for side in payload.get("side_roots", []):
        reachable |= rooted_closure(side, adjacency)[0]
    if reachable != set(nodes):
        raise RuntimeError("The root graph contains disconnected declarations")
    local_declarations = set(declarations) - set(EMBEDDED_AXIOMS)
    disconnected_declarations = sorted(local_declarations - reachable)
    if disconnected_declarations:
        raise RuntimeError(
            "Disconnected Lean declarations: "
            + ", ".join(disconnected_declarations)
        )
    try:
        tuple(TopologicalSorter(adjacency).static_order())
    except CycleError as exc:
        raise RuntimeError("The declaration dependency graph has a cycle") from exc
    axioms = {name for name, node in nodes.items() if node["kind"] == "axiom"}
    if axioms != set(EMBEDDED_AXIOMS):
        raise RuntimeError("Unexpected ground axiom frontier")
    open_nodes = {
        name for name, node in nodes.items() if node["proof_status"] == "open"
    }
    if open_nodes != set(OPEN_OBLIGATIONS):
        raise RuntimeError(
            "The root must expose exactly Dudko Problems 4.3 and 4.4"
        )
    if not OPEN_OBLIGATIONS <= reachable:
        raise RuntimeError("A Dudko frontier problem is hidden from the graph")
    missing_programme = sorted(VIRTUAL_MOLECULE_PROGRAMME - reachable)
    if missing_programme:
        raise RuntimeError(
            "The virtual-Molecule programme is disconnected: "
            + ", ".join(missing_programme)
        )
    theorem_count = sum(node["kind"] in {"theorem", "lemma"} for node in nodes.values())
    if theorem_count < 40:
        raise RuntimeError("The research reduction has fewer than forty connected theorems")


def _generate_site(repo_root: Path, output_root: Path) -> None:
    fq_index, edges = build_full_graph(repo_root)
    output_root.mkdir(parents=True, exist_ok=True)

    root_decl = fq_index.get(ROOT_SYMBOL)
    if root_decl is None:
        raise RuntimeError(f"Root symbol not found: {ROOT_SYMBOL}")
    axiom_frontier = collect_axioms_from_check_axioms(repo_root)
    unexpected = axiom_frontier - set(EMBEDDED_AXIOMS)
    if unexpected:
        raise RuntimeError("Unexpected kernel axioms: " + ", ".join(sorted(unexpected)))
    for name in sorted(axiom_frontier):
        if name not in fq_index:
            fq_index[name] = Decl("axiom", name.split(".")[-1], name, "[Lean core]", 0, 0)
            edges.setdefault(name, set())

    payload = build_payload(fq_index, edges, root_decl, axiom_frontier)
    validate_research_graph(payload, fq_index)

    reachable = {node["id"] for node in payload["nodes"]}
    metrics = progress_metrics_from_worktree(repo_root)
    model = build_model(fq_index, edges, reachable, axiom_frontier, metrics, repo_root)
    graph_dir = output_root / "mlc_conjecture"
    graph_dir.mkdir(parents=True, exist_ok=True)
    (graph_dir / "index.html").write_text(
        spine_page_html("MLC proof spine", model, metrics),
        encoding="utf-8",
    )
    (output_root / "index.html").write_text(
        index_html([("The proof spine of MLC.mlc_conjecture", "mlc_conjecture/index.html")]),
        encoding="utf-8",
    )
    usage = object_usage(fq_index, edges)
    grid_users = sorted(key for key, objects in usage.items() if "grid" in objects)
    if grid_users:
        print(
            "warning: the certified grid is in the dependency cone of "
            + ", ".join(grid_users)
            + "; the ROADMAP argument for keeping the depth rests on no statement using it",
            file=sys.stderr,
        )
    write_progress_assets(repo_root, graph_dir, usage)


def generate_site(repo_root: Path, output_root: Path) -> None:
    output_root.parent.mkdir(parents=True, exist_ok=True)
    previous_root = output_root.with_name(f".{output_root.name}.previous")
    if previous_root.exists():
        if output_root.exists():
            shutil.rmtree(previous_root)
        else:
            previous_root.rename(output_root)

    with tempfile.TemporaryDirectory(
        prefix=f".{output_root.name}.staging-", dir=output_root.parent
    ) as staging:
        staging_root = Path(staging)
        _generate_site(repo_root, staging_root)
        if output_root.exists():
            output_root.rename(previous_root)
        try:
            staging_root.rename(output_root)
        except BaseException:
            if previous_root.exists() and not output_root.exists():
                previous_root.rename(output_root)
            raise

    if previous_root.exists():
        shutil.rmtree(previous_root)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate the proof-spine static site.")
    parser.add_argument("--output", default="site", help="Output directory (default: site)")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    output_root = (repo_root / args.output).resolve()
    generate_site(repo_root, output_root)
    print(f"Generated dependency graph site at: {output_root}/index.html")


if __name__ == "__main__":
    main()
