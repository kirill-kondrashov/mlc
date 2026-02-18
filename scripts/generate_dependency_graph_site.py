#!/usr/bin/env python3
"""Generate a static dependency-graph site for Lean files in `Mlc/`.

The graph is declaration-level and intra-file:
- Nodes: top-level declarations (`lemma`, `theorem`, `def`, ...)
- Edges: textual references from one declaration body to another declaration
  name in the same file.

Output layout (default):
  site/
    index.html
    graphs/
      index.html
      Mlc/MainConjecture/index.html
      Mlc/MainConjecture/graph.json
      ...
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import argparse
import html
import json
import re
import shutil
from typing import Iterable


DECL_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected|unsafe|partial|mutual)\s+)*"
    r"(lemma|theorem|def|abbrev|axiom|structure|class|instance)\s+([^\s(:=\[{]+)"
)
TOKEN_CHARS = r"A-Za-z0-9_'."


@dataclass(frozen=True)
class Decl:
    kind: str
    name: str
    line: int
    end_line: int

    @property
    def span(self) -> int:
        return max(1, self.end_line - self.line + 1)


def strip_comments(line: str, block_depth: int) -> tuple[str, int]:
    """Remove Lean line/block comments from one line."""
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


def find_decls(lines: list[str]) -> list[Decl]:
    stripped: list[str] = []
    block_depth = 0
    for line in lines:
        s, block_depth = strip_comments(line, block_depth)
        stripped.append(s)

    raw_decls: list[tuple[str, str, int]] = []
    for i, line in enumerate(stripped, start=1):
        m = DECL_RE.match(line)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        if name.startswith(("(", ":", "{", "[")):
            continue
        raw_decls.append((kind, name, i))

    if not raw_decls:
        return []

    decls: list[Decl] = []
    for idx, (kind, name, line) in enumerate(raw_decls):
        if idx + 1 < len(raw_decls):
            end_line = raw_decls[idx + 1][2] - 1
        else:
            end_line = len(lines)
        decls.append(Decl(kind=kind, name=name, line=line, end_line=end_line))
    return decls


def symbol_regex(name: str) -> re.Pattern[str]:
    return re.compile(
        rf"(?<![{TOKEN_CHARS}]){re.escape(name)}(?![{TOKEN_CHARS}])"
    )


def build_graph_for_file(file_path: Path, root: Path) -> dict:
    text = file_path.read_text(encoding="utf-8")
    lines = text.splitlines()
    decls = find_decls(lines)

    rel_path = file_path.relative_to(root)
    module_name = ".".join(rel_path.with_suffix("").parts)

    node_payload = [
        {
            "id": d.name,
            "label": d.name,
            "kind": d.kind,
            "line": d.line,
            "span": d.span,
        }
        for d in decls
    ]

    compiled = {d.name: symbol_regex(d.name) for d in decls}
    edges: set[tuple[str, str]] = set()
    for src in decls:
        body = "\n".join(lines[src.line - 1 : src.end_line])
        for dst in decls:
            if src.name == dst.name:
                continue
            if compiled[dst.name].search(body):
                edges.add((src.name, dst.name))

    edge_payload = [
        {"source": s, "target": t}
        for (s, t) in sorted(edges)
    ]

    return {
        "module": module_name,
        "file": str(rel_path),
        "nodes": node_payload,
        "edges": edge_payload,
    }


def page_html(module: str, rel_to_graph_root: str) -> str:
    escaped_module = html.escape(module)
    back_href = rel_to_graph_root + "index.html"
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>{escaped_module} - Lean Dependency Graph</title>
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
    .toolbar a {{
      color: #0b57d0;
      text-decoration: none;
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
    input[type="range"] {{
      width: 160px;
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
    <h1>{escaped_module}</h1>
    <a href="{back_href}">Graph Index</a>
    <span class="meta" id="summary"></span>
    <label>Search <input id="search" type="search" placeholder="declaration name"></label>
    <label>Spacing <input id="spacing" type="range" min="60" max="320" value="170"></label>
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
    title: `${{n.kind}} ${{n.id}}\\nline ${{n.line}}, span ${{n.span}}`
  }}));

  const edges = payload.edges.map(e => ({{
    from: e.source,
    to: e.target,
    arrows: "to",
    color: {{ color: "#64748b", highlight: "#0f172a" }},
    width: 1.2
  }}));

  const network = new vis.Network(
    document.getElementById("graph"),
    {{ nodes: new vis.DataSet(nodes), edges: new vis.DataSet(edges) }},
    {{
      autoResize: true,
      interaction: {{ hover: true, tooltipDelay: 120 }},
      physics: {{
        enabled: true,
        solver: "forceAtlas2Based",
        forceAtlas2Based: {{
          gravitationalConstant: -68,
          centralGravity: 0.018,
          springLength: 170,
          springConstant: 0.09,
          damping: 0.52,
          avoidOverlap: 0.9
        }},
        stabilization: {{ iterations: 220 }}
      }},
      edges: {{
        smooth: {{
          enabled: true,
          type: "dynamic"
        }}
      }}
    }}
  );

  document.getElementById("summary").textContent =
    `${{payload.nodes.length}} declarations, ${{payload.edges.length}} edges`;

  const searchInput = document.getElementById("search");
  const spacing = document.getElementById("spacing");
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
      const hit = n.id.toLowerCase().includes(needle);
      return {{
        id: n.id,
        hidden: false,
        font: {{ color: hit ? "#9b2226" : "#94a3b8", size: hit ? 15 : 12 }}
      }};
    }}));
  }});

  spacing.addEventListener("input", () => {{
    const value = Number(spacing.value);
    network.setOptions({{
      physics: {{
        forceAtlas2Based: {{
          springLength: value
        }}
      }}
    }});
  }});

  fitBtn.addEventListener("click", () => {{
    network.fit({{ animation: true }});
  }});

  network.once("stabilizationIterationsDone", () => {{
    network.fit({{ animation: false }});
  }});
}}

loadGraph().then(makeNetwork).catch((err) => {{
  document.getElementById("summary").textContent = err.message;
}});
</script>
</body>
</html>
"""


def root_index_html() -> str:
    return """<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta http-equiv="refresh" content="0; url=graphs/index.html">
  <title>Lean Dependency Graphs</title>
</head>
<body>
  <p>Redirecting to <a href="graphs/index.html">graphs/index.html</a>...</p>
</body>
</html>
"""


def graph_index_html(entries: Iterable[dict]) -> str:
    rows = []
    for e in entries:
        module = html.escape(e["module"])
        href = html.escape(e["href"])
        file_ = html.escape(e["file"])
        nodes = e["nodes"]
        edges = e["edges"]
        rows.append(
            f'<tr><td><a href="{href}">{module}</a></td>'
            f"<td>{nodes}</td><td>{edges}</td><td><code>{file_}</code></td></tr>"
        )
    body_rows = "\n".join(rows)
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>Lean Dependency Graphs</title>
  <style>
    body {{
      margin: 24px;
      font-family: "IBM Plex Sans", "Segoe UI", sans-serif;
      color: #0f172a;
      background: #f5f7fb;
    }}
    h1 {{ margin: 0 0 8px; }}
    p {{ margin: 0 0 18px; color: #475569; }}
    table {{
      width: 100%;
      border-collapse: collapse;
      background: #fff;
      border: 1px solid #dbe2ea;
    }}
    th, td {{
      border-bottom: 1px solid #e2e8f0;
      padding: 10px 12px;
      text-align: left;
      font-size: 14px;
    }}
    th {{ background: #f8fafc; }}
    tr:hover td {{ background: #f8fbff; }}
    a {{ color: #0b57d0; text-decoration: none; }}
  </style>
</head>
<body>
  <h1>Lean Dependency Graphs</h1>
  <p>Declaration-level intra-file dependency graphs generated from <code>Mlc/*.lean</code>.</p>
  <table>
    <thead>
      <tr><th>Module</th><th>Nodes</th><th>Edges</th><th>Source File</th></tr>
    </thead>
    <tbody>
      {body_rows}
    </tbody>
  </table>
</body>
</html>
"""


def generate_site(repo_root: Path, output_root: Path) -> None:
    mlc_dir = repo_root / "Mlc"
    lean_files = sorted(mlc_dir.rglob("*.lean"))

    if output_root.exists():
        shutil.rmtree(output_root)
    graphs_root = output_root / "graphs"
    graphs_root.mkdir(parents=True, exist_ok=True)

    entries: list[dict] = []
    for lean_file in lean_files:
        graph = build_graph_for_file(lean_file, repo_root)
        rel = Path(graph["file"]).with_suffix("")
        page_dir = graphs_root / rel
        page_dir.mkdir(parents=True, exist_ok=True)

        (page_dir / "graph.json").write_text(
            json.dumps(graph, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )

        up = "../" * len(rel.parts)
        (page_dir / "index.html").write_text(
            page_html(graph["module"], up),
            encoding="utf-8",
        )

        entries.append(
            {
                "module": graph["module"],
                "file": graph["file"],
                "href": str((rel / "index.html").as_posix()),
                "nodes": len(graph["nodes"]),
                "edges": len(graph["edges"]),
            }
        )

    entries.sort(key=lambda x: x["module"])
    (graphs_root / "index.html").write_text(graph_index_html(entries), encoding="utf-8")
    (output_root / "index.html").write_text(root_index_html(), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate dependency-graph static site.")
    parser.add_argument(
        "--output",
        default="site",
        help="Output directory (default: site)",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    output_root = (repo_root / args.output).resolve()
    generate_site(repo_root, output_root)
    print(f"Generated dependency graph site at: {output_root}")


if __name__ == "__main__":
    main()

