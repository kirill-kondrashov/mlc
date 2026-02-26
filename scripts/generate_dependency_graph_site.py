#!/usr/bin/env python3
"""Generate rooted dependency graph pages.

The graph is declaration-level and cross-file (all `Mlc/*.lean`).
Edges are textual usage edges: source declaration body references target name.
Output layout:
  site/
    index.html
    mlc_conjecture/
      index.html
      graph.json
    mlc_conjecture_injon_bridge/
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
MISSING_AXIOMS = ("MLC.Quadratic.external_ray_map_exists",)
INJON_BRIDGE_SYMBOL = "MLC.mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two"
CONSTRUCTION_SYMBOLS = (
    "MLC.mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two",
    "MLC.mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_two",
    "MLC.mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two",
    "MLC.mlc_conjecture_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis_two",
    "MLC.mlc_conjecture_of_analyticAt_of_preimageCompact_two",
    "MLC.mlc_conjecture_of_analyticAt_of_preimageClosed_two",
    "MLC.mlc_conjecture_of_analyticAt_of_boundaryExclusion_two",
    "MLC.mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo",
    "MLC.mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis_two",
    "MLC.mlc_conjecture_of_nonSlitQuotientConstConstructivePayloadTwo",
    "MLC.mlc_conjecture_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open_two",
    "MLC.mlc_conjecture_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse_two",
)


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
      --potential-edge: #7c3aed;
      --axiom-ring: #dc2626;
      --axiom-fill: rgba(220,38,38,0.26);
      --core-axiom-ring: #1d4ed8;
      --core-axiom-fill: rgba(29,78,216,0.22);
      --missing-axiom-ring: #dc2626;
      --missing-axiom-fill: rgba(220,38,38,0.32);
      --missing-axiom-edge: #ef4444;
      --sphere-fill: rgba(148,163,184,0.08);
      --sphere-stroke: rgba(100,116,139,0.55);
      --sphere-grid: rgba(100,116,139,0.35);
      --root-ring: #f59e0b;
      --root-fill: rgba(245,158,11,0.28);
      --missing-link: #ef4444;
      --construction-edge: #0ea5e9;
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
      --potential-edge: #a78bfa;
      --axiom-ring: #f87171;
      --axiom-fill: rgba(248,113,113,0.30);
      --core-axiom-ring: #60a5fa;
      --core-axiom-fill: rgba(96,165,250,0.28);
      --missing-axiom-ring: #f87171;
      --missing-axiom-fill: rgba(248,113,113,0.38);
      --missing-axiom-edge: #fb7185;
      --sphere-fill: rgba(37,99,235,0.08);
      --sphere-stroke: rgba(125,161,219,0.58);
      --sphere-grid: rgba(125,161,219,0.34);
      --root-ring: #fbbf24;
      --root-fill: rgba(251,191,36,0.28);
      --missing-link: #fb7185;
      --construction-edge: #38bdf8;
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

function stableHash(str) {{
  let h = 2166136261 >>> 0;
  for (let i = 0; i < str.length; i++) {{
    h ^= str.charCodeAt(i);
    h = Math.imul(h, 16777619);
  }}
  return h >>> 0;
}}

function boxesOverlap(a, b, pad = 0) {{
  return !(
    a.r + pad < b.l ||
    b.r + pad < a.l ||
    a.b + pad < b.t ||
    b.b + pad < a.t
  );
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
    potentialEdge: "#7c3aed",
    axiomRing: "#dc2626",
    axiomFill: "rgba(220,38,38,0.26)",
    coreAxiomRing: "#1d4ed8",
    coreAxiomFill: "rgba(29,78,216,0.22)",
    missingAxiomRing: "#dc2626",
    missingAxiomFill: "rgba(220,38,38,0.32)",
    missingAxiomEdge: "#ef4444",
    sphereFill: "rgba(148,163,184,0.08)",
    sphereStroke: "rgba(100,116,139,0.55)",
    sphereGrid: "rgba(100,116,139,0.35)",
    rootRing: "#f59e0b",
    rootFill: "rgba(245,158,11,0.28)",
    missingLink: "#ef4444",
    constructionEdge: "#0ea5e9"
  }},
  minDegree: 0,
  maxDegree: 0,
  cycleNodeCount: 0,
  cycleEdgeCount: 0,
  cycleComponentCount: 0,
  axiomCount: 0,
  coreAxiomCount: 0,
  missingAxiomCount: 0,
  search: "",
  width: 0,
  height: 0,
  scale: 1,
  tx: 0,
  ty: 0,
  panning: false,
  lastX: 0,
  lastY: 0,
  running: false,
  sphere: null
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
  state.palette.potentialEdge = cssVar("--potential-edge", "#7c3aed");
  state.palette.axiomRing = cssVar("--axiom-ring", "#dc2626");
  state.palette.axiomFill = cssVar("--axiom-fill", "rgba(220,38,38,0.26)");
  state.palette.coreAxiomRing = cssVar("--core-axiom-ring", "#1d4ed8");
  state.palette.coreAxiomFill = cssVar("--core-axiom-fill", "rgba(29,78,216,0.22)");
  state.palette.missingAxiomRing = cssVar("--missing-axiom-ring", "#dc2626");
  state.palette.missingAxiomFill = cssVar("--missing-axiom-fill", "rgba(220,38,38,0.32)");
  state.palette.missingAxiomEdge = cssVar("--missing-axiom-edge", "#ef4444");
  state.palette.sphereFill = cssVar("--sphere-fill", "rgba(148,163,184,0.08)");
  state.palette.sphereStroke = cssVar("--sphere-stroke", "rgba(100,116,139,0.55)");
  state.palette.sphereGrid = cssVar("--sphere-grid", "rgba(100,116,139,0.35)");
  state.palette.rootRing = cssVar("--root-ring", "#f59e0b");
  state.palette.rootFill = cssVar("--root-fill", "rgba(245,158,11,0.28)");
  state.palette.missingLink = cssVar("--missing-link", "#ef4444");
  state.palette.constructionEdge = cssVar("--construction-edge", "#0ea5e9");
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
  const depEdges = state.edges.filter(e => (e.kind || "dependency") !== "potential");
  for (const e of depEdges) {{
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
    if ((e.kind || "dependency") !== "dependency") {{
      e.inCycle = false;
      continue;
    }}
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
    <span class="legend-item"><span class="legend-dot" style="background:${{state.palette.constructionEdge}}"></span>Construction route</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{state.palette.coreAxiomFill}};border-color:${{state.palette.coreAxiomRing}}"></span>Core axiom</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{state.palette.axiomFill}};border-color:${{state.palette.axiomRing}}"></span>Project axiom</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{state.palette.missingAxiomFill}};border-color:${{state.palette.missingAxiomRing}}"></span>Missing axiom</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{state.palette.rootFill}};border-color:${{state.palette.rootRing}}"></span>Root: mlc_conjecture</span>
    <span class="legend-item"><span class="legend-dot" style="background:${{state.palette.missingLink}}"></span>Missing connection</span>
  `;
}}

function initGraph(payload) {{
  const allNodes = payload.nodes.slice();
  const rootId = payload.root;
  const rootNode = allNodes.find(n => n.id === rootId) || null;
  const regularNodes = allNodes.filter(n => n.id !== rootId);
  const byDepth = new Map();
  for (const n of regularNodes) {{
    const d = Number(n.depth || 0);
    if (!byDepth.has(d)) byDepth.set(d, []);
    byDepth.get(d).push(n);
  }}
  const orderedDepths = Array.from(byDepth.keys()).sort((a, b) => a - b);
  let maxDepth = 0;
  for (const n of allNodes) {{
    maxDepth = Math.max(maxDepth, Number(n.depth || 0));
  }}
  maxDepth = Math.max(1, maxDepth);

  const totalNodes = Math.max(1, payload.nodes.length);
  const sphereRx = Math.max(620, Math.min(1020, 560 + totalNodes * 3.2));
  const sphereRy = sphereRx * 0.63;
  state.sphere = {{
    cx: 0,
    cy: 0,
    rx: sphereRx,
    ry: sphereRy,
    azimuth: -0.78,
    elevation: 0.48,
    focal: 2.55
  }};

  function projectUnitPoint(xu, yu, zu) {{
    const s = state.sphere;
    const cosA = Math.cos(s.azimuth);
    const sinA = Math.sin(s.azimuth);
    const cosE = Math.cos(s.elevation);
    const sinE = Math.sin(s.elevation);

    const x1 = cosA * xu + sinA * zu;
    const z1 = -sinA * xu + cosA * zu;
    const y1 = cosE * yu - sinE * z1;
    const z2 = sinE * yu + cosE * z1;

    const depth = Math.max(0.2, s.focal - z2);
    const persp = s.focal / depth;
    return {{
      x0: s.cx + s.rx * x1 * persp,
      y0: s.cy - s.ry * y1 * persp,
      z0: z2,
      xu,
      yu,
      zu
    }};
  }}

  function projectOnSphere(lat, lon) {{
    const cosLat = Math.cos(lat);
    const x3 = cosLat * Math.cos(lon);
    const y3 = Math.sin(lat);
    const z3 = cosLat * Math.sin(lon);
    return projectUnitPoint(x3, y3, z3);
  }}

  const positioned = [];

  if (rootNode) {{
    const rootPos = projectOnSphere(0.08, Math.PI / 2);
    positioned.push({{ ...rootNode, ...rootPos }});
  }}

  for (const d of orderedDepths) {{
    const layer = byDepth.get(d);
    layer.sort((a, b) => a.fq_name.localeCompare(b.fq_name));
    const count = Math.max(1, layer.length);
    for (let i = 0; i < layer.length; i++) {{
      const n = layer[i];
      const depthRatio = Number(d) / maxDepth;
      const lat = 1.02 + (-2.04 * depthRatio);
      const baseLon = (2 * Math.PI * (i + 0.5)) / count;
      const h = stableHash(n.fq_name);
      const jitter = ((h % 1000) / 1000 - 0.5) * 0.24;
      const lon = baseLon + Number(d) * 0.47 + jitter;
      const p = projectOnSphere(lat, lon);
      positioned.push({{
        ...n,
        ...p
      }});
    }}
  }}

  state.nodes = positioned.map((n) => ({{
    ...n,
    x: n.x0,
    y: n.y0,
    isRoot: n.id === rootId,
    isConstructionNode: false,
    vx: 0,
    vy: 0,
    r: Math.min(19, 7 + Math.sqrt(Math.max(1, n.span)) * 1.9)
  }}));
  state.idToNode = new Map(state.nodes.map(n => [n.id, n]));
  state.edges = payload.edges
    .map(e => ({{
      source: state.idToNode.get(e.source),
      target: state.idToNode.get(e.target),
      kind: e.kind || "dependency"
    }}))
    .filter(e => e.source && e.target);

  const constructionTargets = new Set();
  for (const e of state.edges) {{
    e.isMissingConnection = e.source.id === rootId && e.target.axiom_tier === "missing";
    e.isConstruction = (e.kind || "dependency") === "construction";
    if (e.isConstruction && e.target.id === rootId) {{
      constructionTargets.add(e.source.id);
    }}
  }}
  for (const n of state.nodes) {{
    if (constructionTargets.has(n.id)) {{
      n.isConstructionNode = true;
    }}
  }}

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
    if (n.isRoot) n.r = Math.max(n.r, 14);
    if (n.axiom_tier === "core") n.r = Math.max(n.r, 11);
    if (n.axiom_tier === "missing") n.r = Math.max(n.r, 16);
  }}
  state.axiomCount = state.nodes.filter(n => n.kind === "axiom").length;
  state.coreAxiomCount = state.nodes.filter(n => n.axiom_tier === "core").length;
  state.missingAxiomCount = state.nodes.filter(n => n.axiom_tier === "missing").length;

  detectCycles();
  renderLegend();

  document.getElementById("summary").textContent =
    `${{payload.nodes.length}} declarations, ${{payload.edges.length}} edges, ` +
    `${{state.axiomCount}} axioms ` +
    `(${{state.coreAxiomCount}} core, ${{state.missingAxiomCount}} missing)`;

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
    state.lastX = ev.offsetX;
    state.lastY = ev.offsetY;
    state.panning = true;
    canvas.style.cursor = "grabbing";
    draw();
  }});

  canvas.addEventListener("mousemove", (ev) => {{
    const dx = ev.offsetX - state.lastX;
    const dy = ev.offsetY - state.lastY;
    state.lastX = ev.offsetX;
    state.lastY = ev.offsetY;
    if (state.panning) {{
      state.tx += dx;
      state.ty += dy;
    }}
    draw();
  }});

  function endPointer() {{
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
  // Deliberately no free-force drifting: nodes are locked to the projected
  // 3D sphere coordinates.
  state.running = false;
}}

function settleLayout(maxSteps = 900) {{
  for (const node of state.nodes) {{
    node.x = node.x0;
    node.y = node.y0;
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
  if (state.sphere) {{
    const s = state.sphere;
    ctx.beginPath();
    ctx.fillStyle = state.palette.sphereFill;
    ctx.strokeStyle = state.palette.sphereStroke;
    ctx.lineWidth = Math.max(0.75, 1.0 / state.scale);
    ctx.ellipse(s.cx, s.cy, s.rx, s.ry, 0, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();

    ctx.strokeStyle = state.palette.sphereGrid;
    ctx.lineWidth = Math.max(0.45, 0.7 / state.scale);
    ctx.setLineDash([Math.max(2.0, 2.8 / state.scale), Math.max(1.8, 2.4 / state.scale)]);
    const bands = [-0.68, -0.35, 0, 0.35, 0.68];
    for (const t of bands) {{
      const y = s.cy - s.ry * t;
      const rx = s.rx * Math.sqrt(Math.max(0.01, 1 - t * t));
      const ry = Math.max(1.8, s.ry * 0.062 * Math.sqrt(Math.max(0.02, 1 - t * t)));
      ctx.beginPath();
      ctx.ellipse(s.cx, y, rx, ry, 0, 0, Math.PI * 2);
      ctx.stroke();
    }}
    for (const m of [0.26, 0.5, 0.74]) {{
      ctx.beginPath();
      ctx.ellipse(s.cx, s.cy, s.rx * m, s.ry, 0, 0, Math.PI * 2);
      ctx.stroke();
    }}
    ctx.setLineDash([]);

  }}

  const drawNodes = [...state.nodes].sort((a, b) => (a.z0 || 0) - (b.z0 || 0));
  for (const e of state.edges) {{
    const a = e.source;
    const b = e.target;
    const kind = e.kind || "dependency";
    const isConstruction = kind === "construction";
    const isPotential = kind === "potential";
    const isMissingConnection = Boolean(e.isMissingConnection);
    const hasMissingAxiom = a.axiom_tier === "missing" || b.axiom_tier === "missing";
    const hasCoreAxiom = a.axiom_tier === "core" || b.axiom_tier === "core";
    const hit = (!state.search) || matchNode(a) || matchNode(b);
    const edgeColor = isMissingConnection
      ? state.palette.missingLink
      : isConstruction
      ? state.palette.constructionEdge
      : isPotential
      ? state.palette.potentialEdge
      : hasMissingAxiom
      ? state.palette.missingAxiomEdge
      : (hasCoreAxiom
          ? state.palette.coreAxiomRing
          : (e.inCycle ? state.palette.cycleEdge : state.palette.edge));
    const color = hit ? edgeColor : state.palette.edgeMuted;
    const dash = isMissingConnection
      ? []
      : isConstruction
      ? [Math.max(2.2, 3.0 / state.scale), Math.max(1.5, 2.2 / state.scale)]
      : isPotential
      ? [Math.max(2.6, 3.4 / state.scale), Math.max(1.8, 2.4 / state.scale)]
      : hasMissingAxiom
      ? [Math.max(1.8, 2.2 / state.scale), Math.max(1.4, 1.8 / state.scale)]
      : [];
    ctx.setLineDash(dash);
    ctx.strokeStyle = color;
    ctx.lineWidth = isMissingConnection
      ? Math.max(1.35, lw * 2.1)
      : (isConstruction ? lw * 1.45 : (isPotential ? lw * 1.2 : (hasMissingAxiom ? lw * 1.35 : lw)));
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
    if (dash.length > 0) ctx.setLineDash([]);
  }}

  for (const n of drawNodes) {{
    const hit = (!state.search) || matchNode(n);
    const axiomTier = n.axiom_tier || "none";
    const isAxiom = axiomTier !== "none";
    const isCoreAxiom = axiomTier === "core";
    const isMissingAxiom = axiomTier === "missing";
    const isRoot = Boolean(n.isRoot);
    const isConstructionNode = Boolean(n.isConstructionNode);
    let fillColor;
    if (isRoot && hit) {{
      fillColor = state.palette.rootFill;
    }} else if (!hit) {{
      fillColor = "rgba(148,163,184,0.25)";
    }} else if (isMissingAxiom) {{
      fillColor = state.palette.missingAxiomFill;
    }} else if (isCoreAxiom) {{
      fillColor = state.palette.coreAxiomFill;
    }} else if (isAxiom) {{
      fillColor = state.palette.axiomFill;
    }} else {{
      fillColor = degreeColor(n.degree, state.minDegree, state.maxDegree);
    }}
    let strokeColor;
    if (isMissingAxiom) {{
      strokeColor = state.palette.missingAxiomRing;
    }} else if (isRoot) {{
      strokeColor = state.palette.rootRing;
    }} else if (isCoreAxiom) {{
      strokeColor = state.palette.coreAxiomRing;
    }} else if (isConstructionNode) {{
      strokeColor = state.palette.constructionEdge;
    }} else if (isAxiom) {{
      strokeColor = state.palette.axiomRing;
    }} else {{
      strokeColor = n.inCycle ? state.palette.cycleRing : nodeColor(n.kind);
    }}
    ctx.beginPath();
    ctx.fillStyle = fillColor;
    ctx.strokeStyle = strokeColor;
    ctx.lineWidth = lw;
    ctx.arc(n.x, n.y, n.r, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();

    if (isRoot) {{
      ctx.beginPath();
      ctx.strokeStyle = hit ? state.palette.rootRing : state.palette.edgeMuted;
      ctx.lineWidth = Math.max(1.9, 2.6 / state.scale);
      ctx.arc(n.x, n.y, n.r + 4.8, 0, Math.PI * 2);
      ctx.stroke();
    }}

    if (isAxiom) {{
      ctx.beginPath();
      const ringColor = isMissingAxiom
        ? state.palette.missingAxiomRing
        : (isCoreAxiom ? state.palette.coreAxiomRing : state.palette.axiomRing);
      ctx.strokeStyle = hit ? ringColor : state.palette.edgeMuted;
      ctx.lineWidth = Math.max(1.8, 2.2 / state.scale) * (isMissingAxiom ? 1.15 : 1.0);
      ctx.arc(n.x, n.y, n.r + (isMissingAxiom ? 3.4 : 2.6), 0, Math.PI * 2);
      ctx.stroke();
      if (isMissingAxiom) {{
        ctx.beginPath();
        ctx.strokeStyle = hit ? state.palette.missingAxiomEdge : state.palette.edgeMuted;
        ctx.lineWidth = Math.max(1.1, 1.5 / state.scale);
        ctx.arc(n.x, n.y, n.r + 6.2, 0, Math.PI * 2);
        ctx.stroke();
      }}
    }}
  }}

  ctx.restore();

  if (state.scale < 0.28) return;

  const nodeRects = drawNodes.map(n => {{
    const sx = n.x * state.scale + state.tx;
    const sy = n.y * state.scale + state.ty;
    const sr = n.r * state.scale;
    return {{
      n,
      l: sx - sr,
      r: sx + sr,
      t: sy - sr,
      b: sy + sr
    }};
  }});

  const labelCandidates = [...drawNodes].sort((a, b) => {{
    const tierScore = (n) => n.isRoot ? 6200
      : (n.isConstructionNode ? 5600
      : (n.axiom_tier === "missing" ? 5000
      : (n.axiom_tier === "core" ? 4200
      : (n.axiom_tier === "project" ? 3300 : 0))));
    const searchScore = (n) => matchNode(n) ? 1200 : 0;
    const zScore = (n) => ((n.z0 || 0) + 1.2) * 180;
    return (tierScore(b) + searchScore(b) + b.degree * 10 + zScore(b)) -
      (tierScore(a) + searchScore(a) + a.degree * 10 + zScore(a));
  }});

  ctx.save();
  ctx.font = "12px IBM Plex Sans, Segoe UI, sans-serif";
  ctx.textBaseline = "middle";
  const occupied = [];
  const labelPad = 2.0;
  for (const n of labelCandidates) {{
    const hit = (!state.search) || matchNode(n);
    if (!hit && state.scale < 0.85) continue;
    if ((n.z0 || 0) < -0.65 && state.scale < 1.45 && n.axiom_tier === "none") continue;
    const sx = n.x * state.scale + state.tx;
    const sy = n.y * state.scale + state.ty;
    const sr = n.r * state.scale;
    const text = n.label;
    const width = ctx.measureText(text).width;
    const box = {{
      l: sx + sr + 7,
      r: sx + sr + 7 + width + 2,
      t: sy - 6.5,
      b: sy + 6.5
    }};
    let blocked = false;
    for (const occ of occupied) {{
      if (boxesOverlap(box, occ, labelPad)) {{
        blocked = true;
        break;
      }}
    }}
    if (blocked) continue;
    for (const nr of nodeRects) {{
      if (nr.n.id === n.id) continue;
      if (boxesOverlap(box, nr, 1.0)) {{
        blocked = true;
        break;
      }}
    }}
    if (blocked) continue;
    occupied.push(box);
    ctx.fillStyle = hit ? state.palette.label : state.palette.labelMuted;
    ctx.fillText(text, box.l, sy);
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
  ctx.clearRect(0, 0, state.width || 800, state.height || 300);
  ctx.fillStyle = "#9b2226";
  ctx.font = "14px IBM Plex Sans, Segoe UI, sans-serif";
  ctx.fillText(err.message, 16, 28);
}});
</script>
</body>
</html>
"""


def graph_page_html_v2(title: str) -> str:
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
      --canvas-bg: #0b1220;
      --legend-dot-border: #1f2937;
    }}
    :root[data-theme="dark"] {{
      --bg: #0b1220;
      --panel: #101a2d;
      --text: #dbe7ff;
      --muted: #9db0cf;
      --border: #20304d;
      --button-bg: #13203a;
      --canvas-bg: #050b18;
      --legend-dot-border: #dbe7ff;
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
    .legend {{
      margin-left: auto;
      display: flex;
      align-items: center;
      gap: 10px;
      font-size: 12px;
      color: var(--muted);
      white-space: nowrap;
      flex-wrap: wrap;
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
      border: 1px solid var(--legend-dot-border);
      display: inline-block;
    }}
    input[type="search"] {{
      border: 1px solid var(--border);
      border-radius: 8px;
      padding: 6px 8px;
      min-width: 220px;
      font-size: 13px;
      color: var(--text);
      background: var(--panel);
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
    #scene {{
      width: 100%;
      height: 100%;
      position: relative;
      background: var(--canvas-bg);
    }}
    #hover {{
      position: absolute;
      pointer-events: none;
      transform: translate(10px, -8px);
      padding: 6px 8px;
      border-radius: 6px;
      font-size: 12px;
      line-height: 1.35;
      background: rgba(15, 23, 42, 0.9);
      color: #e2e8f0;
      border: 1px solid rgba(148, 163, 184, 0.55);
      display: none;
      max-width: 420px;
      white-space: normal;
      z-index: 10;
    }}
  </style>
</head>
<body>
<div class="wrap">
  <div class="toolbar">
    <h1>{esc_title}</h1>
    <span class="meta" id="summary"></span>
    <label>Search <input id="search" type="search" placeholder="declaration name"></label>
    <button id="fitBtn" type="button">Fit Camera</button>
    <button id="modeBtn" type="button">Mode: 2D</button>
    <button id="themeBtn" type="button">Theme</button>
    <div id="legend" class="legend"></div>
  </div>
  <div id="scene"><div id="hover"></div></div>
</div>
<script src="graph.js"></script>
</body>
</html>
"""


def graph_page_js() -> str:
    return """(function () {
  const sceneEl = document.getElementById("scene");
  const summaryEl = document.getElementById("summary");
  const legendEl = document.getElementById("legend");
  const searchEl = document.getElementById("search");
  const fitBtn = document.getElementById("fitBtn");
  const modeBtn = document.getElementById("modeBtn");
  const themeBtn = document.getElementById("themeBtn");
  const hoverEl = document.getElementById("hover");
  const THEME_KEY = "mlc_graph_theme";

  const KIND_COLOR = {
    theorem: 0xffb703,
    def: 0x06b6d4,
    lemma: 0x8ecae6,
    abbrev: 0x94d2bd,
    structure: 0xee9b00,
    class: 0xca6702,
    instance: 0xbb3e03,
    axiom: 0xdc2626
  };

  const COLORS = {
    root: 0x22c55e,
    coreAxiom: 0x3b82f6,
    missingAxiom: 0xef4444,
    edge: 0x64748b,
    construction: 0x0ea5e9,
    potential: 0x7c3aed,
    missingConnection: 0xef4444,
    sphereWire: 0x64748b
  };

  function kindColor(kind) {
    return KIND_COLOR[kind] || 0x9ca3af;
  }

  function hexToRgb01(hex) {
    return [
      ((hex >> 16) & 255) / 255,
      ((hex >> 8) & 255) / 255,
      (hex & 255) / 255
    ];
  }

  function rgb01ToCss(rgb, a = 1) {
    const r = Math.max(0, Math.min(255, Math.round((rgb[0] || 0) * 255)));
    const g = Math.max(0, Math.min(255, Math.round((rgb[1] || 0) * 255)));
    const b = Math.max(0, Math.min(255, Math.round((rgb[2] || 0) * 255)));
    const alpha = Math.max(0, Math.min(1, a));
    return `rgba(${r}, ${g}, ${b}, ${alpha})`;
  }

  function parseHexColorToRgb01(hexText) {
    const t = String(hexText || "").trim();
    const m = /^#([0-9a-fA-F]{6})$/.exec(t);
    if (!m) return [0.04, 0.08, 0.14];
    const v = parseInt(m[1], 16);
    return hexToRgb01(v);
  }

  const V3 = {
    add: (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]],
    sub: (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]],
    scale: (a, s) => [a[0] * s, a[1] * s, a[2] * s],
    dot: (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2],
    cross: (a, b) => [
      a[1] * b[2] - a[2] * b[1],
      a[2] * b[0] - a[0] * b[2],
      a[0] * b[1] - a[1] * b[0]
    ],
    len: (a) => Math.sqrt(a[0] * a[0] + a[1] * a[1] + a[2] * a[2]),
    norm: (a) => {
      const d = Math.sqrt(a[0] * a[0] + a[1] * a[1] + a[2] * a[2]) || 1;
      return [a[0] / d, a[1] / d, a[2] / d];
    }
  };

  function mat4Identity() {
    return new Float32Array([
      1, 0, 0, 0,
      0, 1, 0, 0,
      0, 0, 1, 0,
      0, 0, 0, 1
    ]);
  }

  function mat4Perspective(fovy, aspect, near, far) {
    const f = 1 / Math.tan(fovy / 2);
    const nf = 1 / (near - far);
    const out = mat4Identity();
    out[0] = f / Math.max(0.1, aspect);
    out[5] = f;
    out[10] = (far + near) * nf;
    out[11] = -1;
    out[14] = (2 * far * near) * nf;
    out[15] = 0;
    return out;
  }

  function mat4LookAt(eye, center, up) {
    const z = V3.norm(V3.sub(eye, center));
    let x = V3.cross(up, z);
    if (V3.len(x) < 1e-6) x = [1, 0, 0];
    x = V3.norm(x);
    const y = V3.cross(z, x);
    const out = mat4Identity();
    out[0] = x[0]; out[1] = y[0]; out[2] = z[0];
    out[4] = x[1]; out[5] = y[1]; out[6] = z[1];
    out[8] = x[2]; out[9] = y[2]; out[10] = z[2];
    out[12] = -V3.dot(x, eye);
    out[13] = -V3.dot(y, eye);
    out[14] = -V3.dot(z, eye);
    return out;
  }

  function mat4Multiply(a, b) {
    const out = new Float32Array(16);
    for (let c = 0; c < 4; c += 1) {
      for (let r = 0; r < 4; r += 1) {
        out[c * 4 + r] =
          a[0 * 4 + r] * b[c * 4 + 0] +
          a[1 * 4 + r] * b[c * 4 + 1] +
          a[2 * 4 + r] * b[c * 4 + 2] +
          a[3 * 4 + r] * b[c * 4 + 3];
      }
    }
    return out;
  }

  function systemTheme() {
    return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches
      ? "dark"
      : "light";
  }

  function applyTheme(theme) {
    const finalTheme = theme === "dark" ? "dark" : "light";
    document.documentElement.setAttribute("data-theme", finalTheme);
    try { localStorage.setItem(THEME_KEY, finalTheme); } catch (_err) {}
    if (themeBtn) {
      themeBtn.textContent = finalTheme === "dark" ? "Theme: Dark" : "Theme: Light";
    }
  }

  function renderLegend() {
    if (!legendEl) return;
    legendEl.innerHTML = `
      <span class="legend-item"><span class="legend-dot" style="background:#ffb703"></span>Theorem</span>
      <span class="legend-item"><span class="legend-dot" style="background:#06b6d4"></span>Definition</span>
      <span class="legend-item"><span class="legend-dot" style="background:#8ecae6"></span>Lemma</span>
      <span class="legend-item"><span class="legend-dot" style="background:#22c55e"></span>Root</span>
      <span class="legend-item"><span class="legend-dot" style="background:#ef4444"></span>Missing axiom</span>
      <span class="legend-item"><span class="legend-dot" style="background:#3b82f6"></span>Core axiom</span>
      <span class="legend-item"><span class="legend-dot" style="background:#0ea5e9"></span>Construction route</span>
      <span class="legend-item"><span class="legend-dot" style="background:#ef4444"></span>Missing connection</span>
      <span class="legend-item">→ Directed dependency</span>
    `;
  }

  async function loadPayload() {
    const resp = await fetch("graph.json");
    if (!resp.ok) throw new Error("Failed to load graph.json");
    return await resp.json();
  }

  function fibonacciPoint(i, n) {
    if (n <= 1) return [0, 0, 1];
    const phi = Math.PI * (3 - Math.sqrt(5));
    const y = 1 - (2 * i) / (n - 1);
    const r = Math.sqrt(Math.max(0, 1 - y * y));
    const theta = phi * i;
    return [Math.cos(theta) * r, y, Math.sin(theta) * r];
  }

  function init(payload) {
    const rootId = payload.root;
    const nodes = payload.nodes.slice();
    nodes.sort((a, b) => {
      if (a.id === rootId) return -1;
      if (b.id === rootId) return 1;
      const da = Number(a.depth || 0);
      const db = Number(b.depth || 0);
      if (da !== db) return da - db;
      return String(a.fq_name || a.id).localeCompare(String(b.fq_name || b.id));
    });

    const missingAxiomIds = new Set(
      payload.nodes.filter(n => n.axiom_tier === "missing").map(n => n.id)
    );

    const canvas = document.createElement("canvas");
    canvas.style.width = "100%";
    canvas.style.height = "100%";
    canvas.style.display = "block";
    canvas.style.position = "absolute";
    canvas.style.inset = "0";
    sceneEl.prepend(canvas);
    const canvas2d = document.createElement("canvas");
    canvas2d.style.width = "100%";
    canvas2d.style.height = "100%";
    canvas2d.style.display = "none";
    canvas2d.style.position = "absolute";
    canvas2d.style.inset = "0";
    sceneEl.prepend(canvas2d);
    const ctx2d = canvas2d.getContext("2d");
    const gl = canvas.getContext("webgl", { antialias: true, alpha: false });
    if (!gl) {
      if (summaryEl) summaryEl.textContent = "WebGL is unavailable in this browser.";
      return;
    }

    function compileShader(type, source) {
      const sh = gl.createShader(type);
      gl.shaderSource(sh, source);
      gl.compileShader(sh);
      if (!gl.getShaderParameter(sh, gl.COMPILE_STATUS)) {
        throw new Error(gl.getShaderInfoLog(sh) || "Shader compile failed");
      }
      return sh;
    }

    function createProgram(vsSource, fsSource) {
      const vs = compileShader(gl.VERTEX_SHADER, vsSource);
      const fs = compileShader(gl.FRAGMENT_SHADER, fsSource);
      const p = gl.createProgram();
      gl.attachShader(p, vs);
      gl.attachShader(p, fs);
      gl.linkProgram(p);
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      if (!gl.getProgramParameter(p, gl.LINK_STATUS)) {
        throw new Error(gl.getProgramInfoLog(p) || "Program link failed");
      }
      return p;
    }

    const lineProgram = createProgram(
      `
      attribute vec3 aPosition;
      attribute vec4 aColor;
      uniform mat4 uViewProj;
      varying vec4 vColor;
      void main() {
        gl_Position = uViewProj * vec4(aPosition, 1.0);
        vColor = aColor;
      }
      `,
      `
      precision mediump float;
      varying vec4 vColor;
      void main() {
        gl_FragColor = vColor;
      }
      `
    );

    const pointProgram = createProgram(
      `
      attribute vec3 aPosition;
      attribute vec4 aColor;
      attribute float aSize;
      uniform mat4 uView;
      uniform mat4 uProj;
      uniform float uPointScale;
      varying vec4 vColor;
      void main() {
        vec4 viewPos = uView * vec4(aPosition, 1.0);
        gl_Position = uProj * viewPos;
        gl_PointSize = max(2.0, aSize * uPointScale / max(1.0, -viewPos.z));
        vColor = aColor;
      }
      `,
      `
      precision mediump float;
      varying vec4 vColor;
      void main() {
        vec2 p = gl_PointCoord * 2.0 - 1.0;
        float d = dot(p, p);
        if (d > 1.0) discard;
        float border = smoothstep(0.72, 1.0, d);
        vec3 col = mix(vColor.rgb, vec3(0.03, 0.04, 0.08), border * 0.55);
        gl_FragColor = vec4(col, vColor.a);
      }
      `
    );

    const linePosBuf = gl.createBuffer();
    const lineColBuf = gl.createBuffer();
    const pointPosBuf = gl.createBuffer();
    const pointColBuf = gl.createBuffer();
    const pointSizeBuf = gl.createBuffer();
    const spherePosBuf = gl.createBuffer();
    const sphereColBuf = gl.createBuffer();
    let edgeVertexCount = 0;
    let sphereVertexCount = 0;

    const sphereRadius = Math.max(140, Math.min(260, 120 + nodes.length * 0.55));
    const nodeData = [];
    const idToIndex = new Map();
    for (let i = 0; i < nodes.length; i += 1) {
      const n = nodes[i];
      const p = fibonacciPoint(i, nodes.length);
      const world = n.id === rootId ? [0, 0, sphereRadius] : V3.scale(p, sphereRadius);
      const isRoot = n.id === rootId;
      const isMissing = n.axiom_tier === "missing";
      const isCore = n.axiom_tier === "core";
      let c = kindColor(n.kind);
      if (isRoot) c = COLORS.root;
      else if (isMissing) c = COLORS.missingAxiom;
      else if (isCore) c = COLORS.coreAxiom;
      nodeData.push({
        id: n.id,
        label: n.label,
        fq_name: n.fq_name,
        kind: n.kind,
        file: n.file,
        pos: world,
        color: hexToRgb01(c),
        baseSize: isRoot ? 13 : 8,
        sizeScale: 1,
        alpha: 0.96
      });
      idToIndex.set(n.id, i);
    }

    const edgeData = [];
    for (const e of payload.edges) {
      const aIdx = idToIndex.get(e.source);
      const bIdx = idToIndex.get(e.target);
      if (aIdx === undefined || bIdx === undefined) continue;
      const kind = e.kind || "dependency";
      const isMissingConnection = e.source === rootId && missingAxiomIds.has(e.target);
      let color = COLORS.edge;
      if (isMissingConnection) color = COLORS.missingConnection;
      else if (kind === "construction") color = COLORS.construction;
      else if (kind === "potential") color = COLORS.potential;
      edgeData.push({
        sourceIndex: aIdx,
        targetIndex: bIdx,
        sourceId: e.source,
        targetId: e.target,
        color: hexToRgb01(color),
        alpha: isMissingConnection ? 1.0 : 0.72,
        visible: true
      });
    }

    const renderMode = { value: "2d" };
    const layout2d = {
      nodes: [],
      panX: 0,
      panY: 0,
      scale: 1,
      draggingIndex: -1,
      panning: false,
      lastX: 0,
      lastY: 0
    };
    function modeButtonText() {
      return renderMode.value === "3d" ? "Mode: 3D" : "Mode: 2D";
    }

    function buildSphereBuffers() {
      const latSteps = 24;
      const lonSteps = 36;
      const positions = [];
      const colors = [];
      const col = hexToRgb01(COLORS.sphereWire);
      function pushSeg(a, b) {
        positions.push(a[0], a[1], a[2], b[0], b[1], b[2]);
        colors.push(col[0], col[1], col[2], 0.36, col[0], col[1], col[2], 0.36);
      }
      for (let i = 1; i < latSteps; i += 1) {
        const phi = -Math.PI / 2 + (i * Math.PI) / latSteps;
        const cp = Math.cos(phi);
        const sp = Math.sin(phi);
        for (let j = 0; j < lonSteps; j += 1) {
          const t0 = (j * 2 * Math.PI) / lonSteps;
          const t1 = ((j + 1) * 2 * Math.PI) / lonSteps;
          const a = [sphereRadius * cp * Math.cos(t0), sphereRadius * sp, sphereRadius * cp * Math.sin(t0)];
          const b = [sphereRadius * cp * Math.cos(t1), sphereRadius * sp, sphereRadius * cp * Math.sin(t1)];
          pushSeg(a, b);
        }
      }
      for (let j = 0; j < lonSteps; j += 1) {
        const t = (j * 2 * Math.PI) / lonSteps;
        for (let i = 0; i < latSteps; i += 1) {
          const p0 = -Math.PI / 2 + (i * Math.PI) / latSteps;
          const p1 = -Math.PI / 2 + ((i + 1) * Math.PI) / latSteps;
          const a = [sphereRadius * Math.cos(p0) * Math.cos(t), sphereRadius * Math.sin(p0), sphereRadius * Math.cos(p0) * Math.sin(t)];
          const b = [sphereRadius * Math.cos(p1) * Math.cos(t), sphereRadius * Math.sin(p1), sphereRadius * Math.cos(p1) * Math.sin(t)];
          pushSeg(a, b);
        }
      }
      gl.bindBuffer(gl.ARRAY_BUFFER, spherePosBuf);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(positions), gl.STATIC_DRAW);
      gl.bindBuffer(gl.ARRAY_BUFFER, sphereColBuf);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(colors), gl.STATIC_DRAW);
      sphereVertexCount = positions.length / 3;
    }

    function build2DLayout() {
      const byDepth = new Map();
      for (let i = 0; i < nodes.length; i += 1) {
        const d = Number(nodes[i].depth || 0);
        if (!byDepth.has(d)) byDepth.set(d, []);
        byDepth.get(d).push(i);
      }
      const depthKeys = Array.from(byDepth.keys()).sort((a, b) => a - b);
      const layout = new Array(nodes.length);
      for (const depth of depthKeys) {
        const ids = byDepth.get(depth) || [];
        const ring = depth === 0 ? 0 : 70 + depth * 62;
        const offset = (depth * 0.63) % (2 * Math.PI);
        for (let j = 0; j < ids.length; j += 1) {
          const idx = ids[j];
          const angle = offset + (j * 2 * Math.PI) / Math.max(1, ids.length);
          const x = depth === 0 ? 0 : Math.cos(angle) * ring;
          const y = depth === 0 ? 0 : Math.sin(angle) * ring;
          const isRoot = nodeData[idx].id === rootId;
          layout[idx] = { x, y, r: isRoot ? 11 : 7 };
        }
      }
      layout2d.nodes = layout;
      fit2DLayout();
    }

    function fit2DLayout() {
      if (!layout2d.nodes.length) return;
      let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
      for (let i = 0; i < layout2d.nodes.length; i += 1) {
        const p = layout2d.nodes[i];
        if (!p) continue;
        minX = Math.min(minX, p.x - p.r - 20);
        minY = Math.min(minY, p.y - p.r - 20);
        maxX = Math.max(maxX, p.x + p.r + 120);
        maxY = Math.max(maxY, p.y + p.r + 20);
      }
      const w = Math.max(1, maxX - minX);
      const h = Math.max(1, maxY - minY);
      const pad = 26;
      layout2d.scale = Math.max(0.2, Math.min(4.0, Math.min(
        (canvasCssW - 2 * pad) / w,
        (canvasCssH - 2 * pad) / h
      )));
      layout2d.panX = (canvasCssW - layout2d.scale * (minX + maxX)) / 2;
      layout2d.panY = (canvasCssH - layout2d.scale * (minY + maxY)) / 2;
    }

    function worldFromScreen2D(clientX, clientY) {
      const rect = canvas2d.getBoundingClientRect();
      const sx = clientX - rect.left;
      const sy = clientY - rect.top;
      return {
        x: (sx - layout2d.panX) / layout2d.scale,
        y: (sy - layout2d.panY) / layout2d.scale
      };
    }

    function pickNode2D(clientX, clientY) {
      const p = worldFromScreen2D(clientX, clientY);
      let best = -1;
      let bestD2 = Infinity;
      for (let i = layout2d.nodes.length - 1; i >= 0; i -= 1) {
        const n = layout2d.nodes[i];
        if (!n) continue;
        const scale = nodeData[i].sizeScale || 1;
        const r = n.r * scale + 3 / Math.max(0.35, layout2d.scale);
        const dx = p.x - n.x;
        const dy = p.y - n.y;
        const d2 = dx * dx + dy * dy;
        if (d2 <= r * r && d2 < bestD2) {
          best = i;
          bestD2 = d2;
        }
      }
      return best;
    }

    function draw2D() {
      if (!ctx2d) return;
      const bgCss = getComputedStyle(document.documentElement).getPropertyValue("--canvas-bg") || "#0b1220";
      const dpr = canvasPxW / Math.max(1, canvasCssW);
      ctx2d.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx2d.clearRect(0, 0, canvasCssW, canvasCssH);
      ctx2d.fillStyle = bgCss.trim();
      ctx2d.fillRect(0, 0, canvasCssW, canvasCssH);
      ctx2d.save();
      ctx2d.translate(layout2d.panX, layout2d.panY);
      ctx2d.scale(layout2d.scale, layout2d.scale);
      for (const e of edgeData) {
        if (!e.visible) continue;
        const a = layout2d.nodes[e.sourceIndex];
        const b = layout2d.nodes[e.targetIndex];
        if (!a || !b) continue;
        const dx = b.x - a.x;
        const dy = b.y - a.y;
        const len = Math.hypot(dx, dy);
        if (len <= 1e-4) continue;
        const ux = dx / len;
        const uy = dy / len;
        const aScale = nodeData[e.sourceIndex].sizeScale || 1;
        const bScale = nodeData[e.targetIndex].sizeScale || 1;
        const sx = a.x + ux * (a.r * aScale + 1.2 / Math.max(0.35, layout2d.scale));
        const sy = a.y + uy * (a.r * aScale + 1.2 / Math.max(0.35, layout2d.scale));
        const tx = b.x - ux * (b.r * bScale + 1.2 / Math.max(0.35, layout2d.scale));
        const ty = b.y - uy * (b.r * bScale + 1.2 / Math.max(0.35, layout2d.scale));
        const segLen = Math.hypot(tx - sx, ty - sy);
        if (segLen <= 1e-4) continue;

        const lineColor = rgb01ToCss(e.color, e.alpha);
        ctx2d.strokeStyle = lineColor;
        ctx2d.lineWidth = Math.max(1 / Math.max(0.35, layout2d.scale), 1.1 / Math.max(0.35, layout2d.scale));
        ctx2d.beginPath();
        ctx2d.moveTo(sx, sy);
        ctx2d.lineTo(tx, ty);
        ctx2d.stroke();

        const headLen = Math.min(segLen * 0.55, Math.max(8 / Math.max(0.35, layout2d.scale), 11 / layout2d.scale));
        const headHalf = headLen * 0.44;
        const bx = tx - ux * headLen;
        const by = ty - uy * headLen;
        ctx2d.fillStyle = lineColor;
        ctx2d.beginPath();
        ctx2d.moveTo(tx, ty);
        ctx2d.lineTo(bx - uy * headHalf, by + ux * headHalf);
        ctx2d.lineTo(bx + uy * headHalf, by - ux * headHalf);
        ctx2d.closePath();
        ctx2d.fill();
      }
      const q = String(searchEl?.value || "").trim().toLowerCase();
      for (let i = 0; i < layout2d.nodes.length; i += 1) {
        const p = layout2d.nodes[i];
        if (!p) continue;
        const n = nodeData[i];
        const r = p.r * (n.sizeScale || 1);
        const fill = rgb01ToCss(n.color, Math.max(0.16, n.alpha));
        ctx2d.fillStyle = fill;
        ctx2d.beginPath();
        ctx2d.arc(p.x, p.y, r, 0, Math.PI * 2);
        ctx2d.fill();
        if (n.id === rootId) {
          ctx2d.strokeStyle = "#22c55e";
          ctx2d.lineWidth = Math.max(1 / Math.max(0.35, layout2d.scale), 1.8 / Math.max(0.35, layout2d.scale));
          ctx2d.beginPath();
          ctx2d.arc(p.x, p.y, r + 1.6 / Math.max(0.35, layout2d.scale), 0, Math.PI * 2);
          ctx2d.stroke();
        }
        const showLabel =
          n.id === rootId ||
          (q && (
            String(n.id).toLowerCase().includes(q) ||
            String(n.label).toLowerCase().includes(q) ||
            String(n.fq_name).toLowerCase().includes(q)
          ));
        if (showLabel) {
          ctx2d.fillStyle = rgb01ToCss([0.90, 0.94, 1.0], Math.min(1, Math.max(0.5, n.alpha + 0.1)));
          ctx2d.font = `${Math.max(10 / Math.max(0.35, layout2d.scale), 8)}px "IBM Plex Sans", "Segoe UI", sans-serif`;
          ctx2d.fillText(n.label, p.x + r + 2 / Math.max(0.35, layout2d.scale), p.y - 2 / Math.max(0.35, layout2d.scale));
        }
      }
      ctx2d.restore();
    }

    let pointsDirty = true;
    let edgesDirty = true;
    function syncPointBuffers() {
      const pos = new Float32Array(nodeData.length * 3);
      const col = new Float32Array(nodeData.length * 4);
      const siz = new Float32Array(nodeData.length);
      for (let i = 0; i < nodeData.length; i += 1) {
        const n = nodeData[i];
        pos[i * 3 + 0] = n.pos[0];
        pos[i * 3 + 1] = n.pos[1];
        pos[i * 3 + 2] = n.pos[2];
        col[i * 4 + 0] = n.color[0];
        col[i * 4 + 1] = n.color[1];
        col[i * 4 + 2] = n.color[2];
        col[i * 4 + 3] = n.alpha;
        siz[i] = n.baseSize * n.sizeScale;
      }
      gl.bindBuffer(gl.ARRAY_BUFFER, pointPosBuf);
      gl.bufferData(gl.ARRAY_BUFFER, pos, gl.DYNAMIC_DRAW);
      gl.bindBuffer(gl.ARRAY_BUFFER, pointColBuf);
      gl.bufferData(gl.ARRAY_BUFFER, col, gl.DYNAMIC_DRAW);
      gl.bindBuffer(gl.ARRAY_BUFFER, pointSizeBuf);
      gl.bufferData(gl.ARRAY_BUFFER, siz, gl.DYNAMIC_DRAW);
      pointsDirty = false;
    }

    function syncEdgeBuffers() {
      const positions = [];
      const colors = [];
      const shaftInset = Math.max(7, sphereRadius * 0.018);
      const minEdgeLength = Math.max(4, sphereRadius * 0.012);
      function pushSeg(a, b, color, alpha) {
        positions.push(a[0], a[1], a[2], b[0], b[1], b[2]);
        colors.push(
          color[0], color[1], color[2], alpha,
          color[0], color[1], color[2], alpha
        );
      }
      function sideVector(dir, target) {
        let s = V3.cross(dir, target);
        if (V3.len(s) < 1e-5) s = V3.cross(dir, [0, 1, 0]);
        if (V3.len(s) < 1e-5) s = V3.cross(dir, [1, 0, 0]);
        return V3.norm(s);
      }
      for (const e of edgeData) {
        if (!e.visible) continue;
        const a = nodeData[e.sourceIndex].pos;
        const b = nodeData[e.targetIndex].pos;
        const ab = V3.sub(b, a);
        const abLen = V3.len(ab);
        if (abLen <= minEdgeLength) continue;
        const dir = V3.scale(ab, 1 / abLen);
        const inset = Math.min(shaftInset, abLen * 0.18);
        const start = V3.add(a, V3.scale(dir, inset));
        const tip = V3.sub(b, V3.scale(dir, inset));
        const shaft = V3.sub(tip, start);
        const shaftLen = V3.len(shaft);
        if (shaftLen <= minEdgeLength) continue;

        pushSeg(start, tip, e.color, e.alpha);

        const headLen = Math.min(Math.max(9, sphereRadius * 0.03), shaftLen * 0.65);
        if (headLen <= 1e-3) continue;
        const headHalf = headLen * 0.45;
        const base = V3.sub(tip, V3.scale(dir, headLen));
        const targetUnit = V3.norm(b);
        const side = sideVector(dir, targetUnit);
        const wingA = V3.add(base, V3.scale(side, headHalf));
        const wingB = V3.sub(base, V3.scale(side, headHalf));
        pushSeg(wingA, tip, e.color, e.alpha);
        pushSeg(wingB, tip, e.color, e.alpha);
      }
      gl.bindBuffer(gl.ARRAY_BUFFER, linePosBuf);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(positions), gl.DYNAMIC_DRAW);
      gl.bindBuffer(gl.ARRAY_BUFFER, lineColBuf);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(colors), gl.DYNAMIC_DRAW);
      edgeVertexCount = positions.length / 3;
      edgesDirty = false;
    }

    const camera = {
      yaw: 0,
      pitch: 0,
      distance: Math.max(360, sphereRadius * 2.6),
      target: [0, 0, 0],
      fov: 50 * Math.PI / 180,
      near: 0.1,
      far: 4000,
      eye: [0, 0, 1],
      right: [1, 0, 0],
      up: [0, 1, 0],
      forward: [0, 0, -1],
      view: mat4Identity(),
      proj: mat4Identity(),
      viewProj: mat4Identity(),
      pointScale: 1
    };

    function fitCamera() {
      camera.yaw = 0;
      camera.pitch = 0;
      camera.distance = Math.max(360, sphereRadius * 2.6);
      cameraDirty = true;
    }

    let canvasCssW = 1;
    let canvasCssH = 1;
    let canvasPxW = 1;
    let canvasPxH = 1;
    let cameraDirty = true;
    function resize() {
      const dpr = Math.min(window.devicePixelRatio || 1, 2);
      canvasCssW = Math.max(1, sceneEl.clientWidth);
      canvasCssH = Math.max(1, sceneEl.clientHeight);
      canvasPxW = Math.max(2, Math.floor(canvasCssW * dpr));
      canvasPxH = Math.max(2, Math.floor(canvasCssH * dpr));
      canvas.width = canvasPxW;
      canvas.height = canvasPxH;
      canvas2d.width = canvasPxW;
      canvas2d.height = canvasPxH;
      if (ctx2d) ctx2d.setTransform(dpr, 0, 0, dpr, 0, 0);
      gl.viewport(0, 0, canvasPxW, canvasPxH);
      cameraDirty = true;
      fit2DLayout();
    }
    window.addEventListener("resize", resize);
    resize();

    function updateCameraMatrices() {
      const cp = Math.cos(camera.pitch);
      const sp = Math.sin(camera.pitch);
      const cy = Math.cos(camera.yaw);
      const sy = Math.sin(camera.yaw);
      camera.eye = [
        camera.target[0] + sy * cp * camera.distance,
        camera.target[1] + sp * camera.distance,
        camera.target[2] + cy * cp * camera.distance
      ];
      camera.forward = V3.norm(V3.sub(camera.target, camera.eye));
      camera.right = V3.norm(V3.cross(camera.forward, [0, 1, 0]));
      if (V3.len(camera.right) < 1e-6) camera.right = [1, 0, 0];
      camera.up = V3.norm(V3.cross(camera.right, camera.forward));
      camera.view = mat4LookAt(camera.eye, camera.target, camera.up);
      camera.proj = mat4Perspective(
        camera.fov,
        canvasCssW / Math.max(1, canvasCssH),
        camera.near,
        camera.far
      );
      camera.viewProj = mat4Multiply(camera.proj, camera.view);
      camera.pointScale = canvasPxH / (2 * Math.tan(camera.fov / 2));
      cameraDirty = false;
    }

    function projectToScreen(pos) {
      const rel = V3.sub(pos, camera.eye);
      const x = V3.dot(rel, camera.right);
      const y = V3.dot(rel, camera.up);
      const z = V3.dot(rel, camera.forward);
      if (z <= 1e-3) return null;
      const tanHalf = Math.tan(camera.fov / 2);
      const ndcX = x / (z * tanHalf * (canvasCssW / Math.max(1, canvasCssH)));
      const ndcY = y / (z * tanHalf);
      return {
        x: (ndcX * 0.5 + 0.5) * canvasCssW,
        y: (1 - (ndcY * 0.5 + 0.5)) * canvasCssH,
        depth: z
      };
    }

    function pickNode(clientX, clientY) {
      const rect = canvas.getBoundingClientRect();
      const x = clientX - rect.left;
      const y = clientY - rect.top;
      let bestIndex = -1;
      let bestDepth = Infinity;
      let bestDist2 = Infinity;
      for (let i = 0; i < nodeData.length; i += 1) {
        const n = nodeData[i];
        const p = projectToScreen(n.pos);
        if (!p) continue;
        const dx = p.x - x;
        const dy = p.y - y;
        const r = n.baseSize * n.sizeScale + 6;
        const d2 = dx * dx + dy * dy;
        if (d2 > r * r) continue;
        if (p.depth < bestDepth || (Math.abs(p.depth - bestDepth) < 1e-3 && d2 < bestDist2)) {
          bestDepth = p.depth;
          bestDist2 = d2;
          bestIndex = i;
        }
      }
      return bestIndex;
    }

    function screenRay(clientX, clientY) {
      const rect = canvas.getBoundingClientRect();
      const x = clientX - rect.left;
      const y = clientY - rect.top;
      const ndcX = (x / canvasCssW) * 2 - 1;
      const ndcY = 1 - (y / canvasCssH) * 2;
      const tanHalf = Math.tan(camera.fov / 2);
      const vx = ndcX * tanHalf * (canvasCssW / Math.max(1, canvasCssH));
      const vy = ndcY * tanHalf;
      const dir = V3.norm(
        V3.add(
          V3.add(V3.scale(camera.right, vx), V3.scale(camera.up, vy)),
          camera.forward
        )
      );
      return { origin: camera.eye, dir };
    }

    function intersectSphere(rayOrigin, rayDir, radius) {
      const b = V3.dot(rayOrigin, rayDir);
      const c = V3.dot(rayOrigin, rayOrigin) - radius * radius;
      const disc = b * b - c;
      if (disc < 0) return null;
      const s = Math.sqrt(disc);
      let t = -b - s;
      if (t < 0) t = -b + s;
      if (t < 0) return null;
      return V3.add(rayOrigin, V3.scale(rayDir, t));
    }

    function applySearch() {
      const q = String(searchEl?.value || "").trim().toLowerCase();
      const visibleNodes = new Set();
      for (const n of nodeData) {
        const hit = !q ||
          String(n.id).toLowerCase().includes(q) ||
          String(n.label).toLowerCase().includes(q) ||
          String(n.fq_name).toLowerCase().includes(q) ||
          String(n.file).toLowerCase().includes(q);
        n.alpha = hit ? 0.98 : 0.2;
        n.sizeScale = hit ? 1.0 : 0.85;
        if (hit) visibleNodes.add(n.id);
      }
      for (const e of edgeData) {
        e.visible = !q || visibleNodes.has(e.sourceId) || visibleNodes.has(e.targetId);
      }
      pointsDirty = true;
      edgesDirty = true;
    }

    let draggingNodeIndex = -1;
    let orbiting = false;
    let lastX = 0;
    let lastY = 0;

    function onPointerDown(ev) {
      if (renderMode.value !== "3d") return;
      if (cameraDirty) updateCameraMatrices();
      const pick = pickNode(ev.clientX, ev.clientY);
      if (pick >= 0) {
        draggingNodeIndex = pick;
      } else {
        orbiting = true;
      }
      lastX = ev.clientX;
      lastY = ev.clientY;
      canvas.setPointerCapture(ev.pointerId);
    }

    function onPointerMove(ev) {
      if (renderMode.value !== "3d") return;
      if (cameraDirty) updateCameraMatrices();
      if (draggingNodeIndex >= 0) {
        const ray = screenRay(ev.clientX, ev.clientY);
        const hit = intersectSphere(ray.origin, ray.dir, sphereRadius);
        if (hit) {
          nodeData[draggingNodeIndex].pos = V3.scale(V3.norm(hit), sphereRadius);
          pointsDirty = true;
          edgesDirty = true;
        }
        hoverEl.style.display = "none";
        return;
      }
      if (orbiting) {
        const dx = ev.clientX - lastX;
        const dy = ev.clientY - lastY;
        lastX = ev.clientX;
        lastY = ev.clientY;
        camera.yaw += dx * 0.007;
        camera.pitch = Math.max(-1.45, Math.min(1.45, camera.pitch + dy * 0.007));
        cameraDirty = true;
        hoverEl.style.display = "none";
        return;
      }
      const pick = pickNode(ev.clientX, ev.clientY);
      if (pick >= 0) {
        const n = nodeData[pick];
        hoverEl.style.display = "block";
        hoverEl.style.left = `${ev.clientX}px`;
        hoverEl.style.top = `${ev.clientY}px`;
        hoverEl.textContent = `${n.fq_name} (${n.kind})`;
      } else {
        hoverEl.style.display = "none";
      }
    }

    function onPointerUp(ev) {
      draggingNodeIndex = -1;
      orbiting = false;
      try { canvas.releasePointerCapture(ev.pointerId); } catch (_err) {}
    }

    function onWheel(ev) {
      if (renderMode.value !== "3d") return;
      ev.preventDefault();
      const scale = Math.exp(ev.deltaY * 0.001);
      camera.distance = Math.max(180, Math.min(900, camera.distance * scale));
      cameraDirty = true;
    }

    function onPointerDown2D(ev) {
      if (renderMode.value !== "2d") return;
      const pick = pickNode2D(ev.clientX, ev.clientY);
      if (pick >= 0) {
        layout2d.draggingIndex = pick;
      } else {
        layout2d.panning = true;
      }
      layout2d.lastX = ev.clientX;
      layout2d.lastY = ev.clientY;
      canvas2d.setPointerCapture(ev.pointerId);
    }

    function onPointerMove2D(ev) {
      if (renderMode.value !== "2d") return;
      if (layout2d.draggingIndex >= 0) {
        const p = worldFromScreen2D(ev.clientX, ev.clientY);
        const n = layout2d.nodes[layout2d.draggingIndex];
        n.x = p.x;
        n.y = p.y;
        hoverEl.style.display = "none";
        return;
      }
      if (layout2d.panning) {
        const dx = ev.clientX - layout2d.lastX;
        const dy = ev.clientY - layout2d.lastY;
        layout2d.lastX = ev.clientX;
        layout2d.lastY = ev.clientY;
        layout2d.panX += dx;
        layout2d.panY += dy;
        hoverEl.style.display = "none";
        return;
      }
      const pick = pickNode2D(ev.clientX, ev.clientY);
      if (pick >= 0) {
        const n = nodeData[pick];
        hoverEl.style.display = "block";
        hoverEl.style.left = `${ev.clientX}px`;
        hoverEl.style.top = `${ev.clientY}px`;
        hoverEl.textContent = `${n.fq_name} (${n.kind})`;
      } else {
        hoverEl.style.display = "none";
      }
    }

    function onPointerUp2D(ev) {
      layout2d.draggingIndex = -1;
      layout2d.panning = false;
      try { canvas2d.releasePointerCapture(ev.pointerId); } catch (_err) {}
    }

    function onWheel2D(ev) {
      if (renderMode.value !== "2d") return;
      ev.preventDefault();
      const rect = canvas2d.getBoundingClientRect();
      const sx = ev.clientX - rect.left;
      const sy = ev.clientY - rect.top;
      const wx = (sx - layout2d.panX) / layout2d.scale;
      const wy = (sy - layout2d.panY) / layout2d.scale;
      const factor = Math.exp(-ev.deltaY * 0.001);
      layout2d.scale = Math.max(0.2, Math.min(6.0, layout2d.scale * factor));
      layout2d.panX = sx - wx * layout2d.scale;
      layout2d.panY = sy - wy * layout2d.scale;
    }

    function setRenderMode(mode) {
      renderMode.value = mode === "2d" ? "2d" : "3d";
      canvas.style.display = renderMode.value === "3d" ? "block" : "none";
      canvas2d.style.display = renderMode.value === "2d" ? "block" : "none";
      hoverEl.style.display = "none";
      if (modeBtn) modeBtn.textContent = modeButtonText();
    }

    canvas.addEventListener("pointerdown", onPointerDown);
    canvas.addEventListener("pointermove", onPointerMove);
    window.addEventListener("pointerup", onPointerUp);
    canvas.addEventListener("wheel", onWheel, { passive: false });
    canvas2d.addEventListener("pointerdown", onPointerDown2D);
    canvas2d.addEventListener("pointermove", onPointerMove2D);
    window.addEventListener("pointerup", onPointerUp2D);
    canvas2d.addEventListener("wheel", onWheel2D, { passive: false });

    if (searchEl) searchEl.addEventListener("input", applySearch);
    if (fitBtn) fitBtn.addEventListener("click", () => {
      if (renderMode.value === "2d") fit2DLayout();
      else fitCamera();
    });
    if (modeBtn) {
      modeBtn.addEventListener("click", () => {
        setRenderMode(renderMode.value === "3d" ? "2d" : "3d");
      });
      modeBtn.textContent = modeButtonText();
    }
    if (themeBtn) {
      themeBtn.addEventListener("click", () => {
        const cur = document.documentElement.getAttribute("data-theme") === "dark" ? "dark" : "light";
        applyTheme(cur === "dark" ? "light" : "dark");
      });
    }

    const declCount = payload.nodes.length;
    const edgeCount = payload.edges.length;
    const theoremCount = payload.nodes.filter(n => n.kind === "theorem").length;
    const defCount = payload.nodes.filter(n => n.kind === "def").length;
    if (summaryEl) {
      summaryEl.textContent =
        `${declCount} declarations, ${edgeCount} edges, ` +
        `${theoremCount} theorems, ${defCount} definitions`;
    }

    function drawLines(posBuf, colBuf, vertexCount) {
      if (vertexCount <= 0) return;
      gl.useProgram(lineProgram);
      const posLoc = gl.getAttribLocation(lineProgram, "aPosition");
      const colLoc = gl.getAttribLocation(lineProgram, "aColor");
      const vpLoc = gl.getUniformLocation(lineProgram, "uViewProj");
      gl.uniformMatrix4fv(vpLoc, false, camera.viewProj);
      gl.bindBuffer(gl.ARRAY_BUFFER, posBuf);
      gl.enableVertexAttribArray(posLoc);
      gl.vertexAttribPointer(posLoc, 3, gl.FLOAT, false, 0, 0);
      gl.bindBuffer(gl.ARRAY_BUFFER, colBuf);
      gl.enableVertexAttribArray(colLoc);
      gl.vertexAttribPointer(colLoc, 4, gl.FLOAT, false, 0, 0);
      gl.drawArrays(gl.LINES, 0, vertexCount);
    }

    function drawPoints() {
      gl.useProgram(pointProgram);
      const posLoc = gl.getAttribLocation(pointProgram, "aPosition");
      const colLoc = gl.getAttribLocation(pointProgram, "aColor");
      const sizeLoc = gl.getAttribLocation(pointProgram, "aSize");
      gl.uniformMatrix4fv(gl.getUniformLocation(pointProgram, "uView"), false, camera.view);
      gl.uniformMatrix4fv(gl.getUniformLocation(pointProgram, "uProj"), false, camera.proj);
      gl.uniform1f(gl.getUniformLocation(pointProgram, "uPointScale"), camera.pointScale);
      gl.bindBuffer(gl.ARRAY_BUFFER, pointPosBuf);
      gl.enableVertexAttribArray(posLoc);
      gl.vertexAttribPointer(posLoc, 3, gl.FLOAT, false, 0, 0);
      gl.bindBuffer(gl.ARRAY_BUFFER, pointColBuf);
      gl.enableVertexAttribArray(colLoc);
      gl.vertexAttribPointer(colLoc, 4, gl.FLOAT, false, 0, 0);
      gl.bindBuffer(gl.ARRAY_BUFFER, pointSizeBuf);
      gl.enableVertexAttribArray(sizeLoc);
      gl.vertexAttribPointer(sizeLoc, 1, gl.FLOAT, false, 0, 0);
      gl.drawArrays(gl.POINTS, 0, nodeData.length);
    }

    function currentCanvasBgColor() {
      const css = getComputedStyle(document.documentElement).getPropertyValue("--canvas-bg");
      return parseHexColorToRgb01(css);
    }

    function render() {
      requestAnimationFrame(render);
      if (renderMode.value === "2d") {
        draw2D();
        return;
      }
      if (cameraDirty) updateCameraMatrices();
      if (pointsDirty) syncPointBuffers();
      if (edgesDirty) syncEdgeBuffers();

      const bg = currentCanvasBgColor();
      gl.clearColor(bg[0], bg[1], bg[2], 1);
      gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
      gl.enable(gl.DEPTH_TEST);
      gl.depthFunc(gl.LEQUAL);
      gl.enable(gl.BLEND);
      gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);

      drawLines(spherePosBuf, sphereColBuf, sphereVertexCount);
      drawLines(linePosBuf, lineColBuf, edgeVertexCount);
      drawPoints();
    }

    renderLegend();
    fitCamera();
    buildSphereBuffers();
    build2DLayout();
    setRenderMode("2d");
    applySearch();
    render();
  }

  (async function bootstrap() {
    let initialTheme = systemTheme();
    try {
      const saved = localStorage.getItem(THEME_KEY);
      if (saved === "light" || saved === "dark") initialTheme = saved;
    } catch (_err) {}
    applyTheme(initialTheme);
    try {
      const payload = await loadPayload();
      init(payload);
    } catch (err) {
      if (summaryEl) summaryEl.textContent = String(err && err.message ? err.message : err);
    }
  })();
})();"""


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
  <title>MLC Dependency Graphs</title>
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
  <h1>MLC Dependency Graphs</h1>
  <ul>
{items}
  </ul>
</body>
</html>
"""


def resolve_root_decl(root_symbol: str, fq_index: dict[str, Decl]) -> Decl:
    root_decl = fq_index.get(root_symbol)
    if root_decl is not None:
        return root_decl
    matches = [d for d in fq_index.values() if d.name == root_symbol.split(".")[-1]]
    if len(matches) == 1:
        return matches[0]
    if matches:
        return sorted(matches, key=lambda d: d.fq_name == "MLC.mlc_conjecture", reverse=True)[0]
    raise RuntimeError(f"Root symbol not found: {root_symbol}")


def build_payload(
    fq_index: dict[str, Decl],
    edges: dict[str, set[str]],
    root_decl: Decl,
    *,
    extra_nodes: set[str] | None = None,
    extra_edges: list[dict[str, str]] | None = None,
) -> dict[str, object]:
    reachable, depth = rooted_closure(root_decl.fq_name, edges)
    edges.setdefault(root_decl.fq_name, set())
    for ax_name in EMBEDDED_AXIOMS:
        if ax_name in fq_index:
            reachable.add(ax_name)
            depth.setdefault(ax_name, 1)
            edges[root_decl.fq_name].add(ax_name)

    if extra_nodes:
        extra_depth = max(depth.values(), default=0) + 1
        for node_id in sorted(extra_nodes):
            if node_id in fq_index:
                reachable.add(node_id)
                depth.setdefault(node_id, extra_depth)

    nodes = []
    for node_id in sorted(reachable):
        d = fq_index[node_id]
        axiom_tier = "none"
        if d.kind == "axiom":
            if d.fq_name in EMBEDDED_AXIOMS:
                axiom_tier = "core"
            elif d.fq_name in MISSING_AXIOMS:
                axiom_tier = "missing"
            else:
                axiom_tier = "project"
        nodes.append(
            {
                "id": d.fq_name,
                "label": d.name,
                "fq_name": d.fq_name,
                "kind": d.kind,
                "axiom_tier": axiom_tier,
                "file": d.file,
                "line": d.line,
                "span": d.span,
                "depth": depth.get(d.fq_name, 0),
            }
        )

    edge_payload: list[dict[str, str]] = []
    seen_edges: set[tuple[str, str, str]] = set()
    for src in sorted(reachable):
        for dst in sorted(edges.get(src, set())):
            if dst in reachable:
                edge = {"source": src, "target": dst, "kind": "dependency"}
                edge_payload.append(edge)
                seen_edges.add((src, dst, "dependency"))

    if extra_edges:
        for e in extra_edges:
            src = e["source"]
            dst = e["target"]
            kind = e.get("kind", "potential")
            key = (src, dst, kind)
            if src in reachable and dst in reachable and key not in seen_edges:
                edge_payload.append({"source": src, "target": dst, "kind": kind})
                seen_edges.add(key)

    return {
        "root": root_decl.fq_name,
        "nodes": nodes,
        "edges": edge_payload,
    }


def write_graph(output_root: Path, slug: str, title: str, payload: dict[str, object]) -> str:
    graph_dir = output_root / slug
    graph_dir.mkdir(parents=True, exist_ok=True)
    (graph_dir / "graph.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    (graph_dir / "graph.js").write_text(
        graph_page_js(),
        encoding="utf-8",
    )
    (graph_dir / "index.html").write_text(
        graph_page_html_v2(title),
        encoding="utf-8",
    )
    return f"{slug}/index.html"


def generate_site(repo_root: Path, output_root: Path, root_symbol: str) -> None:
    fq_index, edges = build_full_graph(repo_root)

    if output_root.exists():
        shutil.rmtree(output_root)
    output_root.mkdir(parents=True, exist_ok=True)

    root_decl = resolve_root_decl(root_symbol, fq_index)
    root_extra_nodes: set[str] = set()
    root_extra_edges: list[dict[str, str]] = []
    if root_decl.fq_name == "MLC.mlc_conjecture":
        for sym in CONSTRUCTION_SYMBOLS:
            decl = fq_index.get(sym)
            if decl is None:
                continue
            if decl.fq_name == root_decl.fq_name:
                continue
            root_extra_nodes.add(decl.fq_name)
            root_extra_edges.append(
                {
                    "source": decl.fq_name,
                    "target": root_decl.fq_name,
                    "kind": "construction",
                }
            )
    root_payload = build_payload(
        fq_index,
        edges,
        root_decl,
        extra_nodes=root_extra_nodes,
        extra_edges=root_extra_edges,
    )
    root_href = write_graph(
        output_root,
        "mlc_conjecture",
        f"Lean Dependency Graph: {root_decl.fq_name}",
        root_payload,
    )

    links: list[tuple[str, str]] = [
        (f"Rooted graph: {root_decl.fq_name}", root_href),
    ]
    bridge_decl = fq_index.get(INJON_BRIDGE_SYMBOL)
    mlc_decl = fq_index.get("MLC.mlc_conjecture")
    if bridge_decl is not None:
        extra_nodes: set[str] = set()
        extra_edges: list[dict[str, str]] = []
        if mlc_decl is not None:
            extra_nodes.add(mlc_decl.fq_name)
            extra_edges.append(
                {
                    "source": mlc_decl.fq_name,
                    "target": bridge_decl.fq_name,
                    "kind": "potential",
                }
            )
        bridge_payload = build_payload(
            fq_index,
            edges,
            bridge_decl,
            extra_nodes=extra_nodes,
            extra_edges=extra_edges,
        )
        bridge_href = write_graph(
            output_root,
            "mlc_conjecture_injon_bridge",
            f"Lean Dependency Graph: {bridge_decl.fq_name}",
            bridge_payload,
        )
        links.append((f"Alternative graph: {bridge_decl.fq_name}", bridge_href))

    (output_root / "index.html").write_text(
        index_html(links),
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
    print(f"Generated dependency graph site at: {output_root}/index.html")


if __name__ == "__main__":
    main()
