#!/usr/bin/env python3
"""Generate a single dependency graph rooted at `MLC.mlc_conjecture`.

The graph is declaration-level and cross-file (all `Mlc/*.lean`).
Edges are textual usage edges: source declaration body references target name.
Output layout:
  site/
    index.html
    mlc_conjecture/
      index.html
      graph.json
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import argparse
import html
import json
import re
import shutil
from collections import deque


DECL_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected|unsafe|partial|mutual)\s+)*"
    r"(lemma|theorem|def|abbrev|axiom|structure|class|instance)\s+([^\s(:=\[{]+)"
)
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section\b")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z0-9_.']+)?\s*$")
TOKEN_RE = re.compile(r"[A-Za-z0-9_.']+")
TOKEN_CHARS = r"A-Za-z0-9_.']"


@dataclass(frozen=True)
class Decl:
    kind: str
    name: str
    fq_name: str
    file: str
    line: int
    end_line: int

    @property
    def span(self) -> int:
        return max(1, self.end_line - self.line + 1)


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


def common_prefix_len(a: list[str], b: list[str]) -> int:
    n = min(len(a), len(b))
    i = 0
    while i < n and a[i] == b[i]:
        i += 1
    return i


def resolve_token(
    token: str,
    src: Decl,
    fq_index: dict[str, Decl],
    short_index: dict[str, list[Decl]],
    suffix_index: dict[str, list[Decl]],
) -> list[Decl]:
    if token in fq_index:
        return [fq_index[token]]

    if "." in token and token in suffix_index:
        cands = suffix_index[token]
        if len(cands) == 1:
            return cands

    short = token.split(".")[-1]
    cands = short_index.get(short, [])
    if not cands:
        return []
    if len(cands) == 1:
        return cands

    same_file = [d for d in cands if d.file == src.file]
    if len(same_file) == 1:
        return same_file

    src_parts = src.fq_name.split(".")[:-1]
    scored = sorted(
        cands,
        key=lambda d: common_prefix_len(src_parts, d.fq_name.split(".")[:-1]),
        reverse=True,
    )
    if scored:
        top_score = common_prefix_len(src_parts, scored[0].fq_name.split(".")[:-1])
        top = [d for d in scored if common_prefix_len(src_parts, d.fq_name.split(".")[:-1]) == top_score]
        if len(top) == 1 and top_score > 0:
            return top
    return []


def build_full_graph(repo_root: Path) -> tuple[dict[str, Decl], dict[str, set[str]]]:
    lean_files = sorted((repo_root / "Mlc").rglob("*.lean"))
    all_decls: list[Decl] = []
    stripped_by_file: dict[str, list[str]] = {}

    for f in lean_files:
        decls, stripped = parse_decls_from_file(f, repo_root)
        all_decls.extend(decls)
        stripped_by_file[str(f.relative_to(repo_root))] = stripped

    fq_index: dict[str, Decl] = {}
    for d in all_decls:
        if d.fq_name not in fq_index:
            fq_index[d.fq_name] = d

    short_index: dict[str, list[Decl]] = {}
    suffix_index: dict[str, list[Decl]] = {}
    for d in all_decls:
        short_index.setdefault(d.name, []).append(d)
        parts = d.fq_name.split(".")
        for i in range(len(parts)):
            suffix = ".".join(parts[i:])
            suffix_index.setdefault(suffix, []).append(d)

    edges: dict[str, set[str]] = {d.fq_name: set() for d in all_decls}
    for src in all_decls:
        lines = stripped_by_file[src.file]
        body = "\n".join(lines[src.line - 1 : src.end_line])
        tokens = set(TOKEN_RE.findall(body))
        for tok in tokens:
            cands = resolve_token(tok, src, fq_index, short_index, suffix_index)
            for dst in cands:
                if dst.fq_name == src.fq_name:
                    continue
                edges[src.fq_name].add(dst.fq_name)

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


def graph_page_html(title: str) -> str:
    esc_title = html.escape(title)
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>{esc_title}</title>
  <link rel="stylesheet" href="https://unpkg.com/vis-network@9.1.9/styles/vis-network.min.css">
  <style>
    :root {{
      --bg: #f5f7fb;
      --panel: #ffffff;
      --text: #0f172a;
      --muted: #475569;
      --border: #dbe2ea;
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      font-family: "IBM Plex Sans", "Segoe UI", sans-serif;
      background: var(--bg);
      color: var(--text);
    }}
    .wrap {{
      display: grid;
      grid-template-rows: auto 1fr;
      height: 100vh;
    }}
    .toolbar {{
      border-bottom: 1px solid var(--border);
      background: var(--panel);
      padding: 10px 14px;
      display: flex;
      align-items: center;
      gap: 14px;
      flex-wrap: wrap;
    }}
    .toolbar h1 {{
      margin: 0;
      font-size: 16px;
      font-weight: 600;
    }}
    .toolbar .meta {{
      color: var(--muted);
      font-size: 13px;
    }}
    .toolbar label {{
      font-size: 13px;
      color: var(--muted);
      display: flex;
      align-items: center;
      gap: 8px;
    }}
    #graph {{
      width: 100%;
      height: 100%;
    }}
    input[type="search"] {{
      border: 1px solid var(--border);
      border-radius: 8px;
      padding: 6px 8px;
      min-width: 220px;
      font-size: 13px;
    }}
    button {{
      border: 1px solid var(--border);
      background: #f8fafc;
      border-radius: 8px;
      padding: 6px 9px;
      cursor: pointer;
      font-size: 13px;
    }}
  </style>
</head>
<body>
<div class="wrap">
  <div class="toolbar">
    <h1>{esc_title}</h1>
    <span class="meta" id="summary"></span>
    <label>Search <input id="search" type="search" placeholder="declaration name"></label>
    <button id="fitBtn" type="button">Fit</button>
  </div>
  <div id="graph"></div>
</div>

<script src="https://unpkg.com/vis-network@9.1.9/standalone/umd/vis-network.min.js"></script>
<script>
const KIND_COLOR = {{
  theorem: "#ffb703",
  lemma: "#8ecae6",
  def: "#219ebc",
  abbrev: "#94d2bd",
  structure: "#ee9b00",
  class: "#ca6702",
  instance: "#bb3e03",
  axiom: "#9b2226"
}};

function nodeColor(kind) {{
  return KIND_COLOR[kind] || "#adb5bd";
}}

async function loadGraph() {{
  const response = await fetch("graph.json");
  if (!response.ok) throw new Error("Failed to load graph.json");
  return response.json();
}}

function makeNetwork(payload) {{
  const nodes = payload.nodes.map(n => ({{
    id: n.id,
    label: n.label,
    level: n.depth,
    shape: "dot",
    size: Math.min(34, 10 + Math.sqrt(Math.max(1, n.span)) * 3),
    color: {{
      background: nodeColor(n.kind),
      border: "#334155",
      highlight: {{
        background: nodeColor(n.kind),
        border: "#0f172a"
      }}
    }},
    font: {{
      face: "IBM Plex Sans, Segoe UI, sans-serif",
      size: 13,
      color: "#0f172a"
    }},
    title: `${{n.fq_name}}\\n${{n.kind}} line ${{n.line}}\\n${{n.file}}`
  }}));

  const edges = payload.edges.map(e => ({{
    from: e.source,
    to: e.target,
    arrows: "to",
    color: {{ color: "#64748b", highlight: "#0f172a" }},
    width: 1.1,
    smooth: {{
      enabled: true,
      type: "cubicBezier",
      roundness: 0.3
    }}
  }}));

  const network = new vis.Network(
    document.getElementById("graph"),
    {{ nodes: new vis.DataSet(nodes), edges: new vis.DataSet(edges) }},
    {{
      interaction: {{ hover: true, tooltipDelay: 120 }},
      physics: false,
      layout: {{
        hierarchical: {{
          enabled: true,
          direction: "UD",
          sortMethod: "directed",
          levelSeparation: 120,
          nodeSpacing: 180,
          treeSpacing: 220,
          blockShifting: true,
          edgeMinimization: true,
          parentCentralization: true
        }}
      }}
    }}
  );

  document.getElementById("summary").textContent =
    `${{payload.nodes.length}} declarations, ${{payload.edges.length}} edges`;

  const searchInput = document.getElementById("search");
  const fitBtn = document.getElementById("fitBtn");
  const allNodes = nodes;
  const ds = network.body.data.nodes;

  searchInput.addEventListener("input", () => {{
    const needle = searchInput.value.trim().toLowerCase();
    if (!needle) {{
      ds.update(allNodes.map(n => ({{
        id: n.id,
        hidden: false,
        font: {{ color: "#0f172a", size: 13 }}
      }})));
      return;
    }}
    ds.update(allNodes.map(n => {{
      const hit = n.label.toLowerCase().includes(needle) || n.id.toLowerCase().includes(needle);
      return {{
        id: n.id,
        hidden: false,
        font: {{ color: hit ? "#9b2226" : "#94a3b8", size: hit ? 15 : 12 }}
      }};
    }}));
  }});

  fitBtn.addEventListener("click", () => {{
    network.fit({{ animation: true }});
  }});

  network.fit({{ animation: false }});
}}

loadGraph().then(makeNetwork).catch((err) => {{
  document.getElementById("summary").textContent = err.message;
}});
</script>
</body>
</html>
"""


def redirect_html(target: str) -> str:
    esc_target = html.escape(target)
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta http-equiv="refresh" content="0; url={esc_target}">
  <title>MLC Graph</title>
</head>
<body>
  <p>Redirecting to <a href="{esc_target}">{esc_target}</a>...</p>
</body>
</html>
"""


def generate_site(repo_root: Path, output_root: Path, root_symbol: str) -> None:
    fq_index, edges = build_full_graph(repo_root)

    root_decl: Decl | None = fq_index.get(root_symbol)
    if root_decl is None:
        matches = [d for d in fq_index.values() if d.name == root_symbol.split(".")[-1]]
        if len(matches) == 1:
            root_decl = matches[0]
        elif matches:
            root_decl = sorted(matches, key=lambda d: d.fq_name == "MLC.mlc_conjecture", reverse=True)[0]
        else:
            raise RuntimeError(f"Root symbol not found: {root_symbol}")

    reachable, depth = rooted_closure(root_decl.fq_name, edges)
    nodes = []
    for node_id in sorted(reachable):
        d = fq_index[node_id]
        nodes.append(
            {
                "id": d.fq_name,
                "label": d.name,
                "fq_name": d.fq_name,
                "kind": d.kind,
                "file": d.file,
                "line": d.line,
                "span": d.span,
                "depth": depth.get(d.fq_name, 0),
            }
        )
    edge_payload = []
    for src in sorted(reachable):
        for dst in sorted(edges.get(src, set())):
            if dst in reachable:
                edge_payload.append({"source": src, "target": dst})

    payload = {
        "root": root_decl.fq_name,
        "nodes": nodes,
        "edges": edge_payload,
    }

    if output_root.exists():
        shutil.rmtree(output_root)
    graph_dir = output_root / "mlc_conjecture"
    graph_dir.mkdir(parents=True, exist_ok=True)

    (graph_dir / "graph.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    (graph_dir / "index.html").write_text(
        graph_page_html(f"Lean Dependency Graph: {root_decl.fq_name}"),
        encoding="utf-8",
    )
    (output_root / "index.html").write_text(
        redirect_html("mlc_conjecture/index.html"),
        encoding="utf-8",
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate root dependency-graph static site.")
    parser.add_argument("--output", default="site", help="Output directory (default: site)")
    parser.add_argument(
        "--root",
        default="MLC.mlc_conjecture",
        help="Root declaration name (default: MLC.mlc_conjecture)",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    output_root = (repo_root / args.output).resolve()
    generate_site(repo_root, output_root, args.root)
    print(f"Generated rooted dependency graph at: {output_root}/mlc_conjecture/index.html")


if __name__ == "__main__":
    main()

