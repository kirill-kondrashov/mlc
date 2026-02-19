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
EMBEDDED_AXIOMS = ("Quot.sound", "propext", "Classical.choice")


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


def is_external_candidate_token(token: str) -> bool:
    """Heuristic for unresolved qualified names that should remain visible."""
    if not token.startswith("MLC."):
        return False
    if token[0].isdigit():
        return False
    return "." in token


def build_full_graph(repo_root: Path) -> tuple[dict[str, Decl], dict[str, set[str]]]:
    lean_files = sorted((repo_root / "Mlc").rglob("*.lean"))
    all_decls: list[Decl] = []
    stripped_by_file: dict[str, list[str]] = {}

    for f in lean_files:
        decls, stripped = parse_decls_from_file(f, repo_root)
        all_decls.extend(decls)
        stripped_by_file[str(f.relative_to(repo_root))] = stripped

    # Add embedded/core axioms so they can appear as explicit nodes in the graph.
    existing = {d.fq_name for d in all_decls}
    for ax_name in EMBEDDED_AXIOMS:
        if ax_name in existing:
            continue
        short = ax_name.split(".")[-1]
        all_decls.append(
            Decl(
                kind="axiom",
                name=short,
                fq_name=ax_name,
                file="[embedded]",
                line=0,
                end_line=0,
            )
        )

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
    external_decls: dict[str, Decl] = {}
    for src in all_decls:
        if src.file not in stripped_by_file:
            continue
        lines = stripped_by_file[src.file]
        body = "\n".join(lines[src.line - 1 : src.end_line])
        tokens = set(TOKEN_RE.findall(body))
        for tok in tokens:
            cands = resolve_token(tok, src, fq_index, short_index, suffix_index)
            if cands:
                for dst in cands:
                    if dst.fq_name == src.fq_name:
                        continue
                    edges[src.fq_name].add(dst.fq_name)
                continue
            if not is_external_candidate_token(tok):
                continue
            if tok == src.fq_name:
                continue
            if tok not in external_decls and tok not in fq_index:
                external_decls[tok] = Decl(
                    kind="external",
                    name=tok.split(".")[-1],
                    fq_name=tok,
                    file="[external]",
                    line=0,
                    end_line=0,
                )
            if tok in external_decls or tok in fq_index:
                edges[src.fq_name].add(tok)

    for ext in external_decls.values():
        fq_index[ext.fq_name] = ext
        edges.setdefault(ext.fq_name, set())

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
  <style>
    :root {{
      --bg: #f5f7fb;
      --panel: #ffffff;
      --text: #0f172a;
      --muted: #475569;
      --border: #dbe2ea;
      --button-bg: #f8fafc;
      --canvas-bg: #f8fafc;
      --edge-color: #64748b;
      --edge-muted: rgba(148,163,184,0.25);
      --label-color: #0f172a;
      --label-muted: rgba(100,116,139,0.7);
      --cycle-ring: #ef4444;
      --cycle-edge: #f97316;
      --axiom-ring: #dc2626;
      --axiom-fill: rgba(220,38,38,0.26);
      --status-yes-bg: #fee2e2;
      --status-yes-fg: #991b1b;
      --status-no-bg: #dcfce7;
      --status-no-fg: #14532d;
    }}
    :root[data-theme="dark"] {{
      --bg: #0b1220;
      --panel: #101a2d;
      --text: #dbe7ff;
      --muted: #9db0cf;
      --border: #20304d;
      --button-bg: #13203a;
      --canvas-bg: #0a1428;
      --edge-color: #7f93b4;
      --edge-muted: rgba(93,118,156,0.28);
      --label-color: #e7efff;
      --label-muted: rgba(151,175,210,0.72);
      --cycle-ring: #fb7185;
      --cycle-edge: #f59e0b;
      --axiom-ring: #f87171;
      --axiom-fill: rgba(248,113,113,0.30);
      --status-yes-bg: rgba(251,113,133,0.22);
      --status-yes-fg: #fecdd3;
      --status-no-bg: rgba(34,197,94,0.2);
      --status-no-fg: #bbf7d0;
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
    .status-pill {{
      display: inline-flex;
      align-items: center;
      border-radius: 999px;
      padding: 3px 9px;
      font-size: 12px;
      font-weight: 600;
      border: 1px solid var(--border);
    }}
    .status-pill.detected {{
      background: var(--status-yes-bg);
      color: var(--status-yes-fg);
    }}
    .status-pill.none {{
      background: var(--status-no-bg);
      color: var(--status-no-fg);
    }}
    .toolbar label {{
      font-size: 13px;
      color: var(--muted);
      display: flex;
      align-items: center;
      gap: 8px;
    }}
    .legend {{
      margin-left: auto;
      display: flex;
      align-items: center;
      gap: 10px;
      font-size: 12px;
      color: var(--muted);
      white-space: nowrap;
    }}
    .legend-item {{
      display: inline-flex;
      align-items: center;
      gap: 6px;
    }}
    .legend-dot {{
      width: 12px;
      height: 12px;
      border-radius: 50%;
      border: 1px solid var(--border);
      display: inline-block;
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
      background: var(--button-bg);
      border-radius: 8px;
      padding: 6px 9px;
      cursor: pointer;
      font-size: 13px;
      color: var(--text);
    }}
    #graphCanvas {{
      width: 100%;
      height: 100%;
      display: block;
      background: var(--canvas-bg);
      cursor: grab;
    }}
  </style>
</head>
<body>
<div class="wrap">
  <div class="toolbar">
    <h1>{esc_title}</h1>
    <span class="meta" id="summary"></span>
    <span class="status-pill" id="cycleStatus"></span>
    <label>Search <input id="search" type="search" placeholder="declaration name"></label>
    <button id="fitBtn" type="button">Fit</button>
    <button id="themeBtn" type="button">Theme</button>
    <div id="legend" class="legend"></div>
  </div>
  <canvas id="graphCanvas"></canvas>
</div>

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

function degreeColor(d, minD, maxD) {{
  if (maxD <= minD) return "hsl(196, 70%, 62%)";
  const t = (d - minD) / (maxD - minD);
  const light = 82 - 40 * t;
  return `hsl(196, 74%, ${{light.toFixed(1)}}%)`;
}}

const state = {{
  nodes: [],
  edges: [],
  idToNode: new Map(),
  palette: {{
    edge: "#64748b",
    edgeMuted: "rgba(148,163,184,0.25)",
    label: "#0f172a",
    labelMuted: "rgba(100,116,139,0.7)",
    cycleRing: "#ef4444",
    cycleEdge: "#f97316",
    axiomRing: "#dc2626",
    axiomFill: "rgba(220,38,38,0.26)"
  }},
  minDegree: 0,
  maxDegree: 0,
  cycleNodeCount: 0,
  cycleEdgeCount: 0,
  cycleComponentCount: 0,
  axiomCount: 0,
  search: "",
  width: 0,
  height: 0,
  scale: 1,
  tx: 0,
  ty: 0,
  dragNode: null,
  panning: false,
  lastX: 0,
  lastY: 0,
  running: false
}};

const canvas = document.getElementById("graphCanvas");
const ctx = canvas.getContext("2d");
const THEME_KEY = "mlc_graph_theme";

function cssVar(name, fallback) {{
  const value = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  return value || fallback;
}}

function refreshPalette() {{
  state.palette.edge = cssVar("--edge-color", "#64748b");
  state.palette.edgeMuted = cssVar("--edge-muted", "rgba(148,163,184,0.25)");
  state.palette.label = cssVar("--label-color", "#0f172a");
  state.palette.labelMuted = cssVar("--label-muted", "rgba(100,116,139,0.7)");
  state.palette.cycleRing = cssVar("--cycle-ring", "#ef4444");
  state.palette.cycleEdge = cssVar("--cycle-edge", "#f97316");
  state.palette.axiomRing = cssVar("--axiom-ring", "#dc2626");
  state.palette.axiomFill = cssVar("--axiom-fill", "rgba(220,38,38,0.26)");
}}

function systemTheme() {{
  return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches
    ? "dark"
    : "light";
}}

function applyTheme(theme) {{
  const finalTheme = theme === "dark" ? "dark" : "light";
  document.documentElement.setAttribute("data-theme", finalTheme);
  try {{
    localStorage.setItem(THEME_KEY, finalTheme);
  }} catch (_err) {{}}
  const themeBtn = document.getElementById("themeBtn");
  if (themeBtn) {{
    themeBtn.textContent = finalTheme === "dark" ? "Theme: Dark" : "Theme: Light";
    themeBtn.title = "Toggle light/dark theme";
  }}
  refreshPalette();
  if (state.nodes.length > 0) {{
    renderLegend();
    draw();
  }}
}}

async function loadGraph() {{
  const response = await fetch("graph.json");
  if (!response.ok) throw new Error("Failed to load graph.json");
  return response.json();
}}

function resizeCanvas() {{
  const ratio = window.devicePixelRatio || 1;
  const w = Math.max(200, canvas.clientWidth);
  const h = Math.max(200, canvas.clientHeight);
  canvas.width = Math.floor(w * ratio);
  canvas.height = Math.floor(h * ratio);
  state.width = w;
  state.height = h;
  ctx.setTransform(ratio, 0, 0, ratio, 0, 0);
}}

function screenToWorld(sx, sy) {{
  return {{
    x: (sx - state.tx) / state.scale,
    y: (sy - state.ty) / state.scale
  }};
}}

function matchNode(n) {{
  if (!state.search) return true;
  return (
    n.label.toLowerCase().includes(state.search) ||
    n.id.toLowerCase().includes(state.search) ||
    n.fq_name.toLowerCase().includes(state.search) ||
    n.file.toLowerCase().includes(state.search)
  );
}}

function findNodeAt(wx, wy) {{
  for (let i = state.nodes.length - 1; i >= 0; i--) {{
    const n = state.nodes[i];
    const dx = wx - n.x;
    const dy = wy - n.y;
    if (dx * dx + dy * dy <= n.r * n.r) return n;
  }}
  return null;
}}

function fitToGraph() {{
  if (state.nodes.length === 0) return;
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const n of state.nodes) {{
    minX = Math.min(minX, n.x - n.r - 20);
    minY = Math.min(minY, n.y - n.r - 20);
    maxX = Math.max(maxX, n.x + n.r + 90);
    maxY = Math.max(maxY, n.y + n.r + 20);
  }}
  const gw = Math.max(1, maxX - minX);
  const gh = Math.max(1, maxY - minY);
  const pad = 30;
  state.scale = Math.max(0.08, Math.min(2.2, Math.min(
    (state.width - 2 * pad) / gw,
    (state.height - 2 * pad) / gh
  )));
  state.tx = (state.width - state.scale * (minX + maxX)) / 2;
  state.ty = (state.height - state.scale * (minY + maxY)) / 2;
}}

function detectCycles() {{
  const idx = new Map(state.nodes.map((n, i) => [n.id, i]));
  const adj = state.nodes.map(() => []);
  const selfLoop = state.nodes.map(() => false);
  for (const e of state.edges) {{
    const s = idx.get(e.source.id);
    const t = idx.get(e.target.id);
    if (s === undefined || t === undefined) continue;
    adj[s].push(t);
    if (s === t) selfLoop[s] = true;
  }}

  const n = state.nodes.length;
  const index = new Array(n).fill(-1);
  const low = new Array(n).fill(0);
  const onStack = new Array(n).fill(false);
  const stack = [];
  const comp = new Array(n).fill(-1);
  const compSize = [];
  let nextIndex = 0;

  function strongConnect(v) {{
    index[v] = nextIndex;
    low[v] = nextIndex;
    nextIndex += 1;
    stack.push(v);
    onStack[v] = true;

    for (const w of adj[v]) {{
      if (index[w] === -1) {{
        strongConnect(w);
        low[v] = Math.min(low[v], low[w]);
      }} else if (onStack[w]) {{
        low[v] = Math.min(low[v], index[w]);
      }}
    }}

    if (low[v] === index[v]) {{
      const cid = compSize.length;
      let size = 0;
      while (true) {{
        const w = stack.pop();
        onStack[w] = false;
        comp[w] = cid;
        size += 1;
        if (w === v) break;
      }}
      compSize.push(size);
    }}
  }}

  for (let v = 0; v < n; v++) {{
    if (index[v] === -1) strongConnect(v);
  }}

  const cycleComp = compSize.map(sz => sz > 1);
  for (let i = 0; i < n; i++) {{
    if (selfLoop[i]) cycleComp[comp[i]] = true;
  }}

  let cycleNodes = 0;
  for (let i = 0; i < n; i++) {{
    const cid = comp[i];
    const inCycle = Boolean(cycleComp[cid]);
    state.nodes[i].cycleId = cid;
    state.nodes[i].inCycle = inCycle;
    if (inCycle) cycleNodes += 1;
  }}

  let cycleEdges = 0;
  for (const e of state.edges) {{
    const sameCycle = e.source.inCycle && e.target.inCycle && e.source.cycleId === e.target.cycleId;
    e.inCycle = sameCycle;
    if (sameCycle) cycleEdges += 1;
  }}

  state.cycleNodeCount = cycleNodes;
  state.cycleEdgeCount = cycleEdges;
  state.cycleComponentCount = cycleComp.reduce((acc, x) => acc + (x ? 1 : 0), 0);
}}

function renderLegend() {{
  const legend = document.getElementById("legend");
  if (!legend) return;
  if (state.nodes.length === 0) {{
    legend.textContent = "";
    return;
  }}
  const midD = Math.round((state.minDegree + state.maxDegree) / 2);
  legend.innerHTML = `
    <span>Links</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{degreeColor(state.minDegree, state.minDegree, state.maxDegree)}}"></span>${{state.minDegree}}</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{degreeColor(midD, state.minDegree, state.maxDegree)}}"></span>${{midD}}</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{degreeColor(state.maxDegree, state.minDegree, state.maxDegree)}}"></span>${{state.maxDegree}}</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{state.palette.cycleEdge}}"></span>Cycle edge</span>
    <span class="legend-item"><span class="legend-dot" style="background:transparent;border-color:${{state.palette.cycleRing}}"></span>Cycle node</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{state.palette.axiomFill}};border-color:${{state.palette.axiomRing}}"></span>Axiom node</span>
  `;
}}

function renderCycleStatus() {{
  const status = document.getElementById("cycleStatus");
  if (!status) return;
  const directedDetected = state.cycleComponentCount > 0;
  const directedText = directedDetected
    ? `yes (${{state.cycleComponentCount}})`
    : "no";
  status.textContent = `Directed cycles: ${{directedText}}`;
  status.className = directedDetected
    ? "status-pill detected"
    : "status-pill none";
}}

function initGraph(payload) {{
  const byDepth = new Map();
  for (const n of payload.nodes) {{
    const d = Number(n.depth || 0);
    if (!byDepth.has(d)) byDepth.set(d, []);
    byDepth.get(d).push(n);
  }}
  const orderedDepths = Array.from(byDepth.keys()).sort((a, b) => a - b);
  const positioned = [];
  const dx = 320;
  const dy = 210;
  const maxDepth = Math.max(1, orderedDepths.length - 1);
  for (const d of orderedDepths) {{
    const layer = byDepth.get(d);
    layer.sort((a, b) => a.fq_name.localeCompare(b.fq_name));
    const mid = (layer.length - 1) / 2;
    const depthRatio = maxDepth === 0 ? 0 : d / maxDepth;
    const widthScale = 0.58 + 0.78 * Math.pow(depthRatio, 0.9);
    for (let i = 0; i < layer.length; i++) {{
      const n = layer[i];
      positioned.push({{
        ...n,
        x0: (i - mid) * dx * widthScale,
        y0: d * dy
      }});
    }}
  }}

  state.nodes = positioned.map((n, i) => ({{
    ...n,
    x: n.x0 + 18 * Math.cos(i * 1.618),
    y: n.y0 + 18 * Math.sin(i * 1.618),
    vx: 0,
    vy: 0,
    r: Math.min(19, 7 + Math.sqrt(Math.max(1, n.span)) * 1.9)
  }}));
  state.idToNode = new Map(state.nodes.map(n => [n.id, n]));
  state.edges = payload.edges
    .map(e => ({{
      source: state.idToNode.get(e.source),
      target: state.idToNode.get(e.target)
    }}))
    .filter(e => e.source && e.target);

  const degree = new Map(state.nodes.map(n => [n.id, 0]));
  for (const e of state.edges) {{
    degree.set(e.source.id, (degree.get(e.source.id) || 0) + 1);
    degree.set(e.target.id, (degree.get(e.target.id) || 0) + 1);
  }}
  let minD = Infinity;
  let maxD = -Infinity;
  for (const n of state.nodes) {{
    n.degree = degree.get(n.id) || 0;
    minD = Math.min(minD, n.degree);
    maxD = Math.max(maxD, n.degree);
  }}
  if (!Number.isFinite(minD)) minD = 0;
  if (!Number.isFinite(maxD)) maxD = 0;
  state.minDegree = minD;
  state.maxDegree = maxD;

  for (const n of state.nodes) {{
    n.r = Math.max(6, Math.min(24, 6 + Math.sqrt(n.degree + 1) * 2.9));
  }}
  state.axiomCount = state.nodes.filter(n => n.kind === "axiom").length;

  detectCycles();
  renderLegend();
  renderCycleStatus();

  document.getElementById("summary").textContent =
    `${{payload.nodes.length}} declarations, ${{payload.edges.length}} edges, ` +
    `${{state.cycleNodeCount}} directed-cycle nodes (${{state.cycleComponentCount}} components), ` +
    `${{state.cycleEdgeCount}} directed-cycle edges, ${{state.axiomCount}} axioms`;

  const searchInput = document.getElementById("search");
  const fitBtn = document.getElementById("fitBtn");
  const themeBtn = document.getElementById("themeBtn");

  searchInput.addEventListener("input", () => {{
    state.search = searchInput.value.trim().toLowerCase();
    draw();
  }});

  fitBtn.addEventListener("click", () => {{
    fitToGraph();
    draw();
  }});

  themeBtn.addEventListener("click", () => {{
    const nextTheme = document.documentElement.getAttribute("data-theme") === "dark"
      ? "light"
      : "dark";
    applyTheme(nextTheme);
  }});

  canvas.addEventListener("mousedown", (ev) => {{
    const p = screenToWorld(ev.offsetX, ev.offsetY);
    const hit = findNodeAt(p.x, p.y);
    state.lastX = ev.offsetX;
    state.lastY = ev.offsetY;
    if (hit) {{
      state.dragNode = hit;
      canvas.style.cursor = "grabbing";
    }} else {{
      state.panning = true;
      canvas.style.cursor = "grabbing";
    }}
    draw();
  }});

  canvas.addEventListener("mousemove", (ev) => {{
    const dx = ev.offsetX - state.lastX;
    const dy = ev.offsetY - state.lastY;
    state.lastX = ev.offsetX;
    state.lastY = ev.offsetY;
    if (state.dragNode) {{
      const p = screenToWorld(ev.offsetX, ev.offsetY);
      state.dragNode.x = p.x;
      state.dragNode.y = p.y;
      state.dragNode.vx = 0;
      state.dragNode.vy = 0;
    }} else if (state.panning) {{
      state.tx += dx;
      state.ty += dy;
    }}
    draw();
  }});

  function endPointer() {{
    state.dragNode = null;
    state.panning = false;
    canvas.style.cursor = "grab";
    draw();
  }}
  canvas.addEventListener("mouseup", endPointer);
  canvas.addEventListener("mouseleave", endPointer);

  canvas.addEventListener("wheel", (ev) => {{
    ev.preventDefault();
    const oldScale = state.scale;
    const factor = Math.exp(-ev.deltaY * 0.0012);
    const newScale = Math.max(0.04, Math.min(6, oldScale * factor));
    const wx = (ev.offsetX - state.tx) / oldScale;
    const wy = (ev.offsetY - state.ty) / oldScale;
    state.scale = newScale;
    state.tx = ev.offsetX - wx * newScale;
    state.ty = ev.offsetY - wy * newScale;
    draw();
  }}, {{ passive: false }});

  settleLayout();
  fitToGraph();
  draw();
}}

function stepForces() {{
  const nodes = state.nodes;
  const edges = state.edges;
  const n = nodes.length;
  const repulsion = 21000;
  const springK = 0.0014;
  const ideal = 190;
  const anchorK = 0.017;
  const damp = 0.84;

  function labelBox(node) {{
    const fontWorld = Math.max(8, 12 / state.scale);
    const width = Math.max(12, (node.label.length * 0.58 + 0.9) * fontWorld);
    const height = fontWorld + 4 / state.scale;
    const left = node.x + node.r + 5;
    const top = node.y - height / 2;
    return {{
      left,
      right: left + width,
      top,
      bottom: top + height,
      cx: left + width / 2,
      cy: node.y
    }};
  }}

  function repelLabelFromCircle(labelNode, box, circleNode, pad, strength) {{
    const cx = circleNode.x;
    const cy = circleNode.y;
    const nearX = Math.max(box.left, Math.min(cx, box.right));
    const nearY = Math.max(box.top, Math.min(cy, box.bottom));
    const dx = cx - nearX;
    const dy = cy - nearY;
    const d2 = dx * dx + dy * dy;
    const minDist = circleNode.r + pad;
    if (d2 >= minDist * minDist) return;
    const d = Math.sqrt(d2 + 1e-6);
    const push = (minDist - d) * strength * 0.9;
    const ux = d > 1e-4 ? (dx / d) : (box.cx <= cx ? 1 : -1);
    const uy = d > 1e-4 ? (dy / d) : 0;
    labelNode.vx -= ux * push;
    labelNode.vy -= uy * push;
    circleNode.vx += ux * push;
    circleNode.vy += uy * push;
  }}

  for (let i = 0; i < n; i++) {{
    const a = nodes[i];
    for (let j = i + 1; j < n; j++) {{
      const b = nodes[j];
      let dx = a.x - b.x;
      let dy = a.y - b.y;
      let d2 = dx * dx + dy * dy + 0.01;
      let d = Math.sqrt(d2);
      let f = repulsion / d2;
      let fx = (dx / d) * f;
      let fy = (dy / d) * f;
      a.vx += fx;
      a.vy += fy;
      b.vx -= fx;
      b.vy -= fy;
    }}
  }}

  for (const e of edges) {{
    const a = e.source;
    const b = e.target;
    let dx = b.x - a.x;
    let dy = b.y - a.y;
    let d = Math.sqrt(dx * dx + dy * dy) + 0.001;
    let f = (d - ideal) * springK;
    let fx = (dx / d) * f;
    let fy = (dy / d) * f;
    a.vx += fx;
    a.vy += fy;
    b.vx -= fx;
    b.vy -= fy;
  }}

  // Keep labels from overlapping each other and from colliding with nodes.
  const labelStrength = 0.28;
  const labelPad = 2.4 / state.scale;
  const circlePad = 3.2 / state.scale;
  for (let pass = 0; pass < 2; pass++) {{
    for (let i = 0; i < n; i++) {{
      const a = nodes[i];
      const boxA = labelBox(a);
      for (let j = i + 1; j < n; j++) {{
        const b = nodes[j];
        const boxB = labelBox(b);
        const ox = Math.min(boxA.right, boxB.right) - Math.max(boxA.left, boxB.left);
        const oy = Math.min(boxA.bottom, boxB.bottom) - Math.max(boxA.top, boxB.top);
        if (ox > 0 && oy > 0) {{
          if (ox < oy) {{
            const dir = boxA.cx <= boxB.cx ? -1 : 1;
            const push = (ox + labelPad) * labelStrength;
            a.vx += dir * push;
            b.vx -= dir * push;
          }} else {{
            const dir = boxA.cy <= boxB.cy ? -1 : 1;
            const push = (oy + labelPad) * labelStrength;
            a.vy += dir * push;
            b.vy -= dir * push;
          }}
        }}
        repelLabelFromCircle(a, boxA, b, circlePad, labelStrength);
        repelLabelFromCircle(b, boxB, a, circlePad, labelStrength);
      }}
    }}
  }}

  let kinetic = 0;
  for (const node of nodes) {{
    if (node !== state.dragNode) {{
      node.vx += (node.x0 - node.x) * anchorK;
      node.vy += (node.y0 - node.y) * anchorK;
      node.vx *= damp;
      node.vy *= damp;
      node.x += node.vx;
      node.y += node.vy;
    }}
    kinetic += node.vx * node.vx + node.vy * node.vy;
  }}
  if (kinetic < 0.02 && !state.dragNode && !state.panning) {{
    state.running = false;
  }}
}}

function settleLayout(maxSteps = 900) {{
  state.running = true;
  for (let i = 0; i < maxSteps; i++) {{
    stepForces();
    if (!state.running) break;
  }}
  for (const node of state.nodes) {{
    node.vx = 0;
    node.vy = 0;
  }}
  state.running = false;
}}

function draw() {{
  ctx.clearRect(0, 0, state.width, state.height);
  ctx.save();
  ctx.translate(state.tx, state.ty);
  ctx.scale(state.scale, state.scale);

  const lw = Math.max(0.45, 0.65 / state.scale);
  for (const e of state.edges) {{
    const a = e.source;
    const b = e.target;
    const hit = (!state.search) || matchNode(a) || matchNode(b);
    const edgeColor = e.inCycle ? state.palette.cycleEdge : state.palette.edge;
    const color = hit ? edgeColor : state.palette.edgeMuted;
    ctx.strokeStyle = color;
    ctx.lineWidth = lw;
    let dx = b.x - a.x;
    let dy = b.y - a.y;
    const d = Math.sqrt(dx * dx + dy * dy);
    if (d < 1e-6) continue;
    const ux = dx / d;
    const uy = dy / d;
    const startPad = a.r + 1.4;
    const endPad = b.r + 4.4;
    const sx = a.x + ux * startPad;
    const sy = a.y + uy * startPad;
    const tx = b.x - ux * endPad;
    const ty = b.y - uy * endPad;
    ctx.beginPath();
    ctx.moveTo(sx, sy);
    ctx.lineTo(tx, ty);
    ctx.stroke();

    const arrowLen = Math.max(3.0, 4.8 / state.scale);
    const arrowHalf = arrowLen * 0.42;
    const bx = tx - ux * arrowLen;
    const by = ty - uy * arrowLen;
    ctx.beginPath();
    ctx.moveTo(tx, ty);
    ctx.lineTo(bx - uy * arrowHalf, by + ux * arrowHalf);
    ctx.lineTo(bx + uy * arrowHalf, by - ux * arrowHalf);
    ctx.closePath();
    ctx.fillStyle = color;
    ctx.fill();
  }}

  for (const n of state.nodes) {{
    const hit = (!state.search) || matchNode(n);
    const isAxiom = n.kind === "axiom";
    ctx.beginPath();
    ctx.fillStyle = hit
      ? (isAxiom ? state.palette.axiomFill : degreeColor(n.degree, state.minDegree, state.maxDegree))
      : "rgba(148,163,184,0.25)";
    ctx.strokeStyle = isAxiom
      ? state.palette.axiomRing
      : (n.inCycle ? state.palette.cycleRing : nodeColor(n.kind));
    ctx.lineWidth = lw;
    ctx.arc(n.x, n.y, n.r, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();

    if (isAxiom) {{
      ctx.beginPath();
      ctx.strokeStyle = hit ? state.palette.axiomRing : state.palette.edgeMuted;
      ctx.lineWidth = Math.max(1.8, 2.2 / state.scale);
      ctx.arc(n.x, n.y, n.r + 2.6, 0, Math.PI * 2);
      ctx.stroke();
    }}
  }}

  for (const n of state.nodes) {{
    const hit = (!state.search) || matchNode(n);
    if (!hit && state.scale < 0.9) continue;
    if (state.scale < 0.35) continue;
    ctx.fillStyle = hit ? state.palette.label : state.palette.labelMuted;
    ctx.font = `${{Math.max(8, 12 / state.scale)}}px IBM Plex Sans, Segoe UI, sans-serif`;
    ctx.textBaseline = "middle";
    ctx.fillText(n.label, n.x + n.r + 5, n.y);
  }}
  ctx.restore();
}}

function start(payload) {{
  let initialTheme = systemTheme();
  try {{
    const saved = localStorage.getItem(THEME_KEY);
    if (saved === "light" || saved === "dark") initialTheme = saved;
  }} catch (_err) {{}}
  applyTheme(initialTheme);
  resizeCanvas();
  initGraph(payload);
  window.addEventListener("resize", () => {{
    resizeCanvas();
    draw();
  }});
  canvas.style.cursor = "grab";
}}

loadGraph().then(start).catch((err) => {{
  document.getElementById("summary").textContent = err.message;
  const status = document.getElementById("cycleStatus");
  if (status) {{
    status.textContent = "Directed cycle metrics: unavailable";
    status.className = "status-pill";
  }}
  ctx.clearRect(0, 0, state.width || 800, state.height || 300);
  ctx.fillStyle = "#9b2226";
  ctx.font = "14px IBM Plex Sans, Segoe UI, sans-serif";
  ctx.fillText(err.message, 16, 28);
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
    # The dependency extractor is textual over `Mlc/*.lean`, so kernel/core axioms
    # are not discoverable as regular declaration tokens. Include them explicitly
    # as first-level axiom dependencies of the root.
    edges.setdefault(root_decl.fq_name, set())
    for ax_name in EMBEDDED_AXIOMS:
        if ax_name in fq_index:
            reachable.add(ax_name)
            depth.setdefault(ax_name, 1)
            edges[root_decl.fq_name].add(ax_name)

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
