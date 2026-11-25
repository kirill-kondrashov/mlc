#!/usr/bin/env python3
"""Progress metrics and reports for the MLC dependency-graph site.

The unresolved set R is the set of parameters c in the Mandelbrot set M at
which no local-connectivity certificate has been proved. The dashboard reports
the resolved share 100% - mu*(R)/(4 pi) of the envelope: 0% means nothing is
resolved, 100% means mu*(R) = 0. MLC means R is empty, which gives 100%. The
converse fails: a measure-zero R may be nonempty, so the share is always read
together with the number of open root obligations. The commit gate works on
the equivalent upper bound mu*(R)/(4 pi).

Lean sources are read from Git history. The module renders

* the commit table relative to ``origin/main``,
* the route-planning table,
* a vector map of M showing the parameters certified by each commit,
* LaTeX fragments used by the status report.
"""

from __future__ import annotations

from datetime import datetime
from pathlib import Path
import argparse
import hashlib
import html
import math
import re
import subprocess
import time

PROGRESS_MILESTONES = (
    ("Conditional root", "MLC.mlc_conjecture", 1),
    ("Harmonic budget", "UnboundedBudget", 1),
    ("Connected parameter nest", "ConnectedNest", 1),
    ("Virtual-Molecule bridge", "VirtualMoleculeAPrioriControl", 2),
    ("Filled-Julia topology", "filled_julia_set_connected_proved", 2),
    ("Minimal connected hull", "exists_minimal_connected_hull", 2),
    ("Mandelbrot compactness", "isCompact_mandelbrot", 1),
    ("Residual-area envelope", "residualOuterArea_le_four_pi", 1),
    ("Certified interior parameter ball", "ball_quarter_subset_interior_mandelbrot", 1),
    ("Kernel-checked grid bound", "unresolved_volume_le_grid", 2),
    ("Unconditional MLC", "mlc_conjecture_unconditional", 8),
)

# Each step lowers the certified bound on mu*(R) / (4 pi). A step is achieved
# when its Lean symbol occurs in the commit's sources. The regions describe
# the parameters that the step certifies and are drawn on the map of M:
#   interior: points of int M (local connectivity is automatic there),
#   exterior: points outside M (removed from the envelope),
#   envelope: the bounding region of the unresolved set.
AREA_STEPS = (
    {
        "symbol": "residualOuterArea_le_four_pi",
        "percent": 100.0,
        "exact": "4π",
        "color": "#94a3b8",
        "title": "Disk envelope",
        "reason": (
            "Proved M ⊆ {|c| ≤ 2}, so the unresolved set lies in the disk "
            "of area 4π (the normalization; the resolved share stays 0%)."
        ),
        "regions": [
            {"kind": "disk", "cx": 0.0, "cy": 0.0, "r": 2.0, "role": "envelope"}
        ],
    },
    {
        "symbol": "ball_quarter_subset_interior_mandelbrot",
        "percent": 100.0 * 63.0 / 64.0,
        "exact": "63π/16",
        "color": "#22c55e",
        "title": "Interior disk |c| < 1/4",
        "reason": (
            "Proved B(0,1/4) ⊆ int M. Local connectivity is automatic at "
            "interior points, so this disk is resolved: unresolved area "
            "4π → 63π/16."
        ),
        "regions": [
            {"kind": "disk", "cx": 0.0, "cy": 0.0, "r": 0.25, "role": "interior"}
        ],
    },
    {
        "symbol": "unresolved_volume_le_grid",
        "percent": None,
        "exact": None,
        "color": "#38bdf8",
        "title": "Kernel-checked grid",
        "reason": (
            "A kernel-checked dyadic grid removes the squares proved outside M "
            "(ball-arithmetic escape test) or inside M (periodic trapping "
            "disk). The remaining cells cover M ∖ int M."
        ),
        "regions": [],
    },
    {
        "symbol": "mlc_conjecture_unconditional",
        "percent": 0.0,
        "exact": "0",
        "color": "#f43f5e",
        "title": "Unconditional MLC",
        "reason": "The unresolved set is empty.",
        "regions": [],
    },
)

PROGRESS_ROUTES = (
    {
        "id": "1",
        "name": "Problem 4.3: unbounded satellite pseudo-Siegel control",
        "range": (0.10, 0.30),
        "probability": 0.12,
        "color": "#38bdf8",
        "next": "Build the remaining pseudo-Siegel a priori realization.",
    },
    {
        "id": "2",
        "name": "Problem 4.4: virtual bounded-period satellite interpolation",
        "range": (0.24, 0.46),
        "probability": 0.20,
        "color": "#a78bfa",
        "next": "Prove collars, hulls in J, and a divergent transfer budget.",
    },
    {
        "id": "3",
        "name": "Problem 4.4: virtual near-neutral interpolation",
        "range": (0.18, 0.42),
        "probability": 0.12,
        "color": "#f59e0b",
        "next": "Formalize finite-return regularization and near-neutral charts.",
    },
    {
        "id": "4",
        "name": "Unified phase-parameter transfer, conditional on genuine geometry",
        "range": (0.38, 0.72),
        "probability": 0.45,
        "color": "#22c55e",
        "next": "Build a global winding/holonomy theorem for all residual classes.",
    },
)

OPEN_ROOT_SYMBOLS = (
    "Problem43PseudoSiegelAPrioriBoundsData",
    "Problem44VirtualMoleculeData",
)
TARGET_PERCENT = 1.0
MAP_WINDOW = (-2.3, 0.8, -1.4, 1.4)
MAP_GRID = (620, 560)
MAP_ITERATIONS = 120
EPS = 1e-12


GRID_SYMBOL = "unresolved_volume_le_grid"
ROOT_LEVEL = 3  # the root squares have side 2^-3


def grid_bound(lean_text: str) -> dict[str, object] | None:
    """Area bound proved by the kernel-checked grid, read from the Lean source."""
    if GRID_SYMBOL not in lean_text:
        return None
    cells = re.search(r"def gridCells\s*:\s*(?:ℕ|Nat)\s*:=\s*(\d+)", lean_text)
    fuel = re.search(r"def gridFuel\s*:\s*(?:ℕ|Nat)\s*:=\s*(\d+)", lean_text)
    if not (cells and fuel):
        return None
    depth = int(fuel.group(1)) + ROOT_LEVEL
    n, d = int(cells.group(1)), depth
    area = 2.0 * n / 4**d
    return {
        "cells": n,
        "depth": d,
        "area": area,
        "percent": 100.0 * area / (4.0 * math.pi),
        "exact": f"2·{n}/4^{d}",
    }


def progress_metrics_from_text(lean_text: str) -> dict[str, object]:
    achieved = [
        {"label": label, "weight": weight}
        for label, symbol, weight in PROGRESS_MILESTONES
        if symbol in lean_text
    ]
    achieved_weight = sum(item["weight"] for item in achieved)
    open_roots = (
        len(OPEN_ROOT_SYMBOLS)
        if all(symbol in lean_text for symbol in OPEN_ROOT_SYMBOLS)
        else 0
    )
    debt = 100.0 * open_roots / max(1.0, 1.0 + achieved_weight)
    area_symbols = [
        step["symbol"] for step in AREA_STEPS if step["symbol"] in lean_text
    ]
    area_percent = 100.0
    area_exact = "4π"
    for step in AREA_STEPS:
        if step["symbol"] in area_symbols and step["percent"] is not None:
            if float(step["percent"]) < area_percent:
                area_percent = float(step["percent"])
                area_exact = str(step["exact"])
    grid = grid_bound(lean_text)
    if grid is not None and float(grid["percent"]) < area_percent:
        area_percent = float(grid["percent"])
        area_exact = str(grid["exact"])
    return {
        "grid": grid,
        "area_exact": area_exact,
        "debt_percent": debt,
        "area_upper_percent": area_percent,
        "area_symbols": area_symbols,
        "open_frontier": open_roots,
        "milestone_weight": achieved_weight,
        "milestones": [item["label"] for item in achieved],
    }


def progress_metrics_from_ref(repo_root: Path, ref: str) -> dict[str, object]:
    proc = subprocess.run(
        ["git", "grep", "-h", "", ref, "--", "Mlc/**/*.lean", "Mlc/*.lean"],
        cwd=repo_root,
        check=False,
        text=True,
        capture_output=True,
    )
    if proc.returncode not in (0, 1):
        raise RuntimeError(f"Cannot read Lean progress from git ref {ref}")
    return progress_metrics_from_text(proc.stdout)


def progress_metrics_from_worktree(repo_root: Path) -> dict[str, object]:
    text = "\n".join(
        path.read_text(encoding="utf-8")
        for path in sorted((repo_root / "Mlc").rglob("*.lean"))
    )
    return progress_metrics_from_text(text)


def staged_progress_metrics(repo_root: Path) -> dict[str, object]:
    proc = subprocess.run(
        ["git", "write-tree"],
        cwd=repo_root,
        check=False,
        text=True,
        capture_output=True,
    )
    if proc.returncode != 0:
        raise RuntimeError("Cannot inspect the staged tree")
    return progress_metrics_from_ref(repo_root, proc.stdout.strip())


def _git(repo_root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        text=True,
        capture_output=True,
    ).stdout.strip()


def baseline_reference(repo_root: Path) -> tuple[str, str]:
    """Return the merge base with origin/main (falling back to main)."""
    for name in ("origin/main", "main"):
        found = subprocess.run(
            ["git", "rev-parse", "--verify", "--quiet", f"{name}^{{commit}}"],
            cwd=repo_root,
            check=False,
            capture_output=True,
        )
        if found.returncode == 0:
            return _git(repo_root, "merge-base", "HEAD", name), name
    raise RuntimeError("Neither origin/main nor main is available")


def _step_by_symbol(symbol: str) -> dict[str, object]:
    return next(step for step in AREA_STEPS if step["symbol"] == symbol)


def commit_progress_history(repo_root: Path) -> list[dict[str, object]]:
    try:
        base, base_name = baseline_reference(repo_root)
        chain = _git(
            repo_root, "rev-list", "--reverse", "--first-parent", f"{base}..HEAD"
        ).splitlines()
        refs = [base] + [line for line in chain if line]
    except (RuntimeError, subprocess.CalledProcessError):
        refs = _git(
            repo_root, "rev-list", "--reverse", "--first-parent", "-12", "HEAD"
        ).splitlines()
        base_name = "HEAD~12"
    rows: list[dict[str, object]] = []
    for index, ref in enumerate(refs):
        short, stamp, subject = _git(
            repo_root, "show", "-s", "--format=%h%x09%ct%x09%s", ref
        ).split("\t", 2)
        rows.append(
            {
                "sha": short,
                "timestamp": int(stamp),
                "subject": subject,
                "baseline": index == 0,
                "baseline_name": base_name,
                **progress_metrics_from_ref(repo_root, ref),
            }
        )
    head = rows[-1]
    working = progress_metrics_from_worktree(repo_root)
    if (
        abs(float(working["debt_percent"]) - float(head["debt_percent"])) > EPS
        or abs(
            float(working["area_upper_percent"])
            - float(head["area_upper_percent"])
        )
        > EPS
    ):
        rows.append(
            {
                "sha": "worktree",
                "timestamp": int(time.time()),
                "subject": "Uncommitted working tree",
                "baseline": False,
                "baseline_name": base_name,
                **working,
            }
        )
    annotate_rows(rows)
    return rows


def annotate_rows(rows: list[dict[str, object]]) -> None:
    previous: dict[str, object] | None = None
    previous_date = None
    for row in rows:
        moment = datetime.fromtimestamp(int(row["timestamp"]))
        date = moment.strftime("%Y-%m-%d")
        row["date"] = date if date != previous_date else ""
        row["time"] = moment.strftime("%H:%M")
        previous_date = date
        if previous is None:
            row["delta"] = None
            row["steps"] = []
            row["note"] = (
                f"Baseline ({row['baseline_name']}): nothing is resolved yet. "
                "The unresolved set is only known to lie in the disk |c| ≤ 2 "
                "of area 4π."
            )
        else:
            new_symbols = [
                symbol
                for symbol in row["area_symbols"]
                if symbol not in previous["area_symbols"]
            ]
            steps = [_step_by_symbol(symbol) for symbol in new_symbols]
            row["steps"] = steps
            delta = float(row["area_upper_percent"]) - float(
                previous["area_upper_percent"]
            )
            row["delta"] = delta
            reasons = " ".join(str(step["reason"]) for step in steps)
            grid = row.get("grid")
            if grid is not None and delta < -EPS:
                reasons = (
                    (reasons + " " if steps else "Finer certified grid. ")
                    + f"Depth {grid['depth']}: {grid['cells']} unresolved cells of "
                    f"side 2^-{grid['depth']} in the upper half-plane (the lower half "
                    f"is the mirror image), unresolved area ≤ {grid['exact']} ≈ "
                    f"{grid['area']:.3f}."
                )
            if delta < -EPS:
                row["note"] = reasons
            elif steps:
                row["note"] = f"No numeric change. {reasons}"
            else:
                row["note"] = "No change in the resolved share."
        previous = row


def format_percent(value: float) -> str:
    if value == 0:
        return "0%"
    return f"{value:.3f}%" if value >= 10.0 else f"{value:.4f}%"


def resolved_percent(area_percent: float) -> float:
    return 100.0 - area_percent


def format_factor(value: float) -> str:
    if value <= 0:
        return "∞"
    factor = 100.0 / value
    return f"×{factor:.3f}" if factor < 10 else f"×{factor:.1f}"


def area_value(percent: float) -> float:
    return percent / 100.0 * 4.0 * math.pi


def exact_area_text(row: dict[str, object]) -> str:
    return str(row["area_exact"])


def format_delta(delta: float | None) -> str:
    if delta is None or abs(delta) < EPS:
        return ""
    sign = "+" if delta < 0 else "−"
    return f"{sign}{abs(delta):.4f} pp"


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def swatch_color(row: dict[str, object]) -> str | None:
    for step in row["steps"]:
        if step["regions"]:
            return str(step["color"])
    return None


def row_kind(row: dict[str, object]) -> str:
    if row["baseline"]:
        return "baseline"
    if row["sha"] == "worktree":
        return "worktree"
    if row["delta"] is not None and row["delta"] < -EPS:
        return "drop"
    return "step" if row["steps"] else "idle"


def commit_table_html(rows: list[dict[str, object]]) -> str:
    out = [
        '<table class="ctable">',
        "<thead><tr>"
        '<th class="c-time">Time</th><th class="c-sha">Commit</th>'
        "<th>Description</th>"
        '<th class="c-area">Resolved share</th>'
        "<th>What it resolved</th></tr></thead><tbody>",
    ]
    for row in rows:
        if row["date"]:
            out.append(
                f'<tr class="date-row"><th colspan="5">{esc(row["date"])}</th></tr>'
            )
        kind = row_kind(row)
        color = swatch_color(row)
        dot = (
            f'<span class="swatch" style="background:{esc(color)}"></span>'
            if color
            else ""
        )
        tag = ' <span class="chip">baseline</span>' if kind == "baseline" else ""
        area = float(row["area_upper_percent"])
        delta = format_delta(row["delta"])
        chip = (
            f'<span class="chip down">{esc(delta)}</span>'
            if kind == "drop" and delta
            else ""
        )
        note = "—" if kind == "idle" else esc(row["note"])
        out.append(
            f'<tr class="{kind}">'
            f'<td class="c-time">{esc(row["time"])}</td>'
            f'<td class="c-sha">{dot}<code>{esc(row["sha"])}</code>{tag}</td>'
            f'<td class="c-desc">{esc(row["subject"])}</td>'
            f'<td class="c-area"><b>{esc(format_percent(resolved_percent(area)))}</b>'
            f'<span class="sub">unresolved ≤ {esc(exact_area_text(row))} ≈ '
            f"{area_value(area):.3f}</span>{chip}</td>"
            f'<td class="c-note">{note}</td></tr>'
        )
    out.append("</tbody></table>")
    return "\n".join(out)


def routes_html() -> str:
    cards = []
    for route in PROGRESS_ROUTES:
        low, high = route["range"]
        cards.append(
            f'<div class="route" style="--route:{esc(route["color"])}">'
            f'<div class="route-name"><span class="route-id">{esc(route["id"])}'
            f"</span>{esc(route['name'])}</div>"
            '<dl class="route-facts">'
            f"<div><dt>Planned reduction</dt><dd>{low * 100:.0f}–{high * 100:.0f}%</dd></div>"
            f"<div><dt>Planning prior</dt><dd>{route['probability'] * 100:.0f}%</dd></div>"
            "</dl>"
            f'<p class="route-next"><span>Next theorem</span>{esc(route["next"])}</p>'
            "</div>"
        )
    return f'<div class="routes">{"".join(cards)}</div>'


def mandelbrot_path(repo_root: Path) -> str:
    """Vector path of a numerical rendering of M (illustration only)."""
    nx, ny = MAP_GRID
    cache_dir = repo_root / ".lake" / "progress-cache"
    cache = cache_dir / f"mandelbrot_{nx}x{ny}_{MAP_ITERATIONS}.txt"
    if cache.exists():
        return cache.read_text(encoding="utf-8")
    x0, x1, y0, y1 = MAP_WINDOW
    dx = (x1 - x0) / nx
    dy = (y1 - y0) / ny
    rows: list[list[tuple[int, int]]] = []
    for t in range(ny // 2):
        ci = y1 - (t + 0.5) * dy
        runs: list[tuple[int, int]] = []
        start = -1
        for i in range(nx):
            cr = x0 + (i + 0.5) * dx
            q = (cr - 0.25) ** 2 + ci * ci
            inside = q * (q + (cr - 0.25)) <= 0.25 * ci * ci or (
                (cr + 1.0) ** 2 + ci * ci <= 0.0625
            )
            if not inside:
                zr = zi = 0.0
                inside = True
                for _ in range(MAP_ITERATIONS):
                    zr, zi = zr * zr - zi * zi + cr, 2.0 * zr * zi + ci
                    if zr * zr + zi * zi > 4.0:
                        inside = False
                        break
            if inside and start < 0:
                start = i
            elif not inside and start >= 0:
                runs.append((start, i - start))
                start = -1
        if start >= 0:
            runs.append((start, nx - start))
        rows.append(runs)
    parts = []
    for t, runs in enumerate(rows):
        for start, width in runs:
            parts.append(f"M{start} {t}h{width}v1h-{width}z")
            parts.append(f"M{start} {ny - 1 - t}h{width}v1h-{width}z")
    data = "".join(parts)
    cache_dir.mkdir(parents=True, exist_ok=True)
    cache.write_text(data, encoding="utf-8")
    return data


def grid_regions(repo_root: Path) -> list[dict[str, object]]:
    """Squares of the kernel-checked grid, exported by the Lean checker itself."""
    sources = [
        repo_root / "Mlc" / "GridCertificate.lean",
        repo_root / "Mlc" / "GridCertified.lean",
        repo_root / "export_grid_regions.lean",
    ]
    if not all(path.exists() for path in sources):
        return []
    digest = hashlib.sha256(
        b"".join(path.read_bytes() for path in sources)
    ).hexdigest()[:16]
    cache_dir = repo_root / ".lake" / "progress-cache"
    cache = cache_dir / f"grid_regions_{digest}.txt"
    if cache.exists():
        text = cache.read_text(encoding="utf-8")
    else:
        proc = subprocess.run(
            ["lake", "env", "lean", "--run", "export_grid_regions.lean"],
            cwd=repo_root,
            check=False,
            text=True,
            capture_output=True,
        )
        if proc.returncode != 0:
            return []
        text = proc.stdout
        cache_dir.mkdir(parents=True, exist_ok=True)
        cache.write_text(text, encoding="utf-8")
    inner: list[tuple[float, float, float, float]] = []
    unresolved: list[tuple[float, float, float, float]] = []
    for line in text.splitlines():
        tag, x, y, k = line.split()
        scale = 2.0 ** int(k)
        rect = (
            int(x) / scale,
            int(y) / scale,
            (int(x) + 1) / scale,
            (int(y) + 1) / scale,
        )
        target = inner if tag == "I" else unresolved
        target.append(rect)
        target.append((rect[0], -rect[3], rect[2], -rect[1]))
    return [
        {"kind": "rects", "role": "interior", "rects": inner},
        {"kind": "rects", "role": "unresolved", "rects": unresolved},
    ]


def grid_point(x: float, y: float) -> tuple[float, float]:
    x0, x1, y0, y1 = MAP_WINDOW
    nx, ny = MAP_GRID
    return (x - x0) / (x1 - x0) * nx, (y1 - y) / (y1 - y0) * ny


def region_svg(region: dict[str, object], color: str) -> str:
    role = region["role"]
    if role == "envelope":
        style = f'fill="none" stroke="{color}" stroke-width="2.2" stroke-dasharray="9 6"'
    elif role == "exterior":
        style = f'fill="{color}" fill-opacity="0.22" stroke="none"'
    elif role == "unresolved":
        style = 'fill="#f59e0b" fill-opacity="0.5" stroke="none"'
    else:
        style = f'fill="{color}" fill-opacity="0.9" stroke="none"'
    if region["kind"] == "disk":
        x0, x1, _, _ = MAP_WINDOW
        scale = MAP_GRID[0] / (x1 - x0)
        cx, cy = grid_point(float(region["cx"]), float(region["cy"]))
        return (
            f'<circle cx="{cx:.2f}" cy="{cy:.2f}" '
            f'r="{float(region["r"]) * scale:.2f}" {style}/>'
        )
    if region["kind"] == "rects":
        path = []
        for rx0, ry0, rx1, ry1 in region["rects"]:
            ax, ay = grid_point(rx0, ry1)
            bx, by = grid_point(rx1, ry0)
            path.append(f"M{ax:.1f} {ay:.1f}H{bx:.1f}V{by:.1f}H{ax:.1f}z")
        return f'<path d="{"".join(path)}" {style}/>'
    raise ValueError(f"Unknown region kind {region['kind']}")


def parameter_map_svg(repo_root: Path, rows: list[dict[str, object]]) -> str:
    """Map of M; every colour marks the parameters certified by one commit."""
    nx, ny = MAP_GRID
    x0, x1, y0, y1 = MAP_WINDOW
    margin_left, margin_bottom, margin_top, margin_right = 46, 44, 10, 10
    total_w = nx + margin_left + margin_right
    total_h = ny + margin_top + margin_bottom
    achieved: list[dict[str, object]] = []
    for row in rows:
        achieved.extend(step for step in row["steps"] if step["regions"])
    layers = []
    for step in achieved:
        for region in step["regions"]:
            layers.append(region_svg(region, str(step["color"])))
    grid_step = next(
        (
            step
            for row in rows
            for step in row["steps"]
            if step["symbol"] == GRID_SYMBOL
        ),
        None,
    )
    if grid_step is not None:
        for region in grid_regions(repo_root):
            layers.append(region_svg(region, str(grid_step["color"])))
    grid = []
    labels = []
    for value in (-2, -1, 0):
        gx, _ = grid_point(float(value), 0.0)
        grid.append(
            f'<line x1="{gx:.1f}" y1="0" x2="{gx:.1f}" y2="{ny}" '
            f'stroke="#23324b" stroke-width="1"/>'
        )
        labels.append(
            f'<text x="{gx:.1f}" y="{ny + 28}" fill="#94a3b8" font-size="18" '
            f'text-anchor="middle">{value}</text>'
        )
    for value in (-1, 0, 1):
        _, gy = grid_point(0.0, float(value))
        grid.append(
            f'<line x1="0" y1="{gy:.1f}" x2="{nx}" y2="{gy:.1f}" '
            f'stroke="#23324b" stroke-width="1"/>'
        )
        labels.append(
            f'<text x="-10" y="{gy + 6:.1f}" fill="#94a3b8" font-size="18" '
            f'text-anchor="end">{value}</text>'
        )
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" '
        f'viewBox="{-margin_left} {-margin_top} {total_w} {total_h}" '
        f'role="img" aria-label="Parameter plane with the certified regions" '
        f'font-family="IBM Plex Sans, Segoe UI, sans-serif">'
        f'<rect x="{-margin_left}" y="{-margin_top}" width="{total_w}" '
        f'height="{total_h}" fill="#07111f"/>'
        f'<defs><clipPath id="mapFrame"><rect width="{nx}" height="{ny}"/>'
        f"</clipPath></defs>"
        f'<g clip-path="url(#mapFrame)">{"".join(grid)}'
        f'<path d="{mandelbrot_path(repo_root)}" fill="#9fb3d1" '
        f'fill-opacity="0.5" shape-rendering="crispEdges"/>'
        f'{"".join(layers)}</g>'
        f'<rect width="{nx}" height="{ny}" fill="none" stroke="#475569" '
        f'stroke-width="1.5"/>{"".join(labels)}</svg>'
    )


def map_legend_html(rows: list[dict[str, object]]) -> str:
    meaning = {
        "envelope": "bounding envelope (dashed)",
        "interior": "certified inside M",
        "exterior": "certified outside M",
    }
    items = []
    for row in rows:
        for step in row["steps"]:
            if step["symbol"] == GRID_SYMBOL:
                items.append(
                    f'<li><span class="swatch" style="background:{esc(step["color"])}">'
                    f'</span><code>{esc(row["sha"])}</code>'
                    f"<span>{esc(step['title'])} · certified inside M</span></li>"
                )
                items.append(
                    '<li><span class="swatch" style="background:#f59e0b"></span>'
                    "<span>unresolved cells of the current grid</span></li>"
                )
                continue
            if not step["regions"]:
                continue
            roles = sorted({region["role"] for region in step["regions"]})
            text = ", ".join(meaning[role] for role in roles)
            items.append(
                f'<li><span class="swatch" style="background:{esc(step["color"])}">'
                f'</span><code>{esc(row["sha"])}</code>'
                f'<span>{esc(step["title"])} · {esc(text)}</span></li>'
            )
    return f'<ul class="map-legend">{"".join(items)}</ul>'


def stats_html(rows: list[dict[str, object]]) -> str:
    current = rows[-1]
    base = rows[0]
    area = float(current["area_upper_percent"])
    open_roots = int(current["open_frontier"])
    tiles = (
        (
            "primary",
            "Certified resolved share of the 4π envelope",
            format_percent(resolved_percent(area)),
            f"unresolved area ≤ {format_percent(area)} of 4π "
            f"({exact_area_text(current)} ≈ {area_value(area):.3f})",
        ),
        (
            "",
            "Unresolved-area reduction",
            format_factor(area),
            f"baseline {base['sha']} on {base['baseline_name']}",
        ),
        (
            "",
            "Target",
            f"≥ {100.0 - TARGET_PERCENT:.0f}%",
            "a ×100 reduction of the unresolved area",
        ),
        (
            "",
            "Open root problems",
            str(open_roots),
            "Problems 4.3 and 4.4" if open_roots else "none",
        ),
    )
    cells = "".join(
        f'<div class="stat {kind}"><div class="stat-label">{esc(label)}</div>'
        f'<div class="stat-value">{esc(value)}</div>'
        f'<div class="stat-sub">{esc(sub)}</div></div>'
        for kind, label, value, sub in tiles
    )
    return f'<div class="stats">{cells}</div>'


def profile_html(rows: list[dict[str, object]]) -> str:
    """Coverage-Uncertainty Profile, shown as certified shares (1 - component)."""
    area = float(rows[-1]["area_upper_percent"]) / 100.0
    components = (
        ("Area", 1.0 - area, "resolved share of the 4π envelope"),
        ("Classes", 0.0, "weight of parameter classes with a Lean certificate"),
        ("Complexity", 0.0, "return depth and relative period retired"),
        ("Budgets", 0.0, "quantitative separation budgets secured"),
    )
    overall = sum(value for _, value, _ in components) / len(components)
    cells = "".join(
        f'<div class="profile-cell" title="{esc(hint)}"><div class="v">'
        f"{esc(format_percent(100.0 * value))}</div>"
        f'<div class="k">{esc(name)}</div></div>'
        for name, value, hint in components
    )
    cells += (
        '<div class="profile-cell total"><div class="v">'
        f"{esc(format_percent(100.0 * overall))}</div>"
        '<div class="k">Overall</div></div>'
    )
    return (
        '<section class="p-card"><h2>Coverage-Uncertainty Profile · certified '
        f'shares</h2><div class="profile-grid">{cells}</div>'
        '<p class="p-foot">Each share is 100% minus the corresponding component. '
        "Only the area component has moved; the class, complexity and budget "
        "components stay at the conservative value 0% until a class "
        "certificate exists. The profile is a planning dashboard, not an "
        "entropy.</p></section>"
    )


def callout_html() -> str:
    return (
        '<aside class="callout"><b>How to read the number.</b> The resolved '
        "share is 100% − μ*(R) / 4π: the part of the envelope certified to be "
        "outside M or at interior points of M, where local connectivity is "
        "automatic. R is the unresolved set. MLC means R = ∅, which gives "
        "100%. The converse fails: a nonempty R of measure zero also gives "
        "100%, and the area of ∂M is itself unknown. Read the share together "
        "with the open problems.</aside>"
    )


def progress_fragment_html(repo_root: Path, rows: list[dict[str, object]]) -> str:
    svg = parameter_map_svg(repo_root, rows)
    origin = esc(rows[0]["baseline_name"])
    return f"""<div class="progress-section">
<div class="p-hero">
<div class="p-hero-left">
{stats_html(rows)}
{profile_html(rows)}
{callout_html()}
</div>
<figure class="p-card p-map">
<h2>Certified region on M</h2>
{svg}
{map_legend_html(rows)}
<figcaption>Parameter plane c = x + iy. Grey: numerical rendering of M
(illustration only, not part of the proof). A colour marks the parameters
certified by the commit with the same colour in the table.</figcaption>
</figure>
</div>
<section class="p-card">
<h2>Commits after the merge base with <code>{origin}</code></h2>
<div class="table-wrap">
{commit_table_html(rows)}
</div>
</section>
<section class="p-card">
<h2>Next routes <span class="chip">planning priors, not theorems</span></h2>
{routes_html()}
<p class="p-foot">The commit hook requires the resolved share to increase,
together with a decrease of the formalization-debt proxy ({float(rows[-1]['debt_percent']):.3f}% now).</p>
</section>
</div>"""


PROGRESS_CSS = """
.progress-section {
  --p-accent: #0369a1; --p-good: #15803d; --p-good-bg: rgba(21, 128, 61, 0.09);
  --p-soft: rgba(100, 116, 139, 0.08);
  display: grid; gap: 20px; max-width: 1480px; margin: 0 auto;
  color: var(--text); font-size: 14px; line-height: 1.5;
}
:root[data-theme="dark"] .progress-section {
  --p-accent: #38bdf8; --p-good: #4ade80; --p-good-bg: rgba(74, 222, 128, 0.09);
  --p-soft: rgba(148, 163, 184, 0.08);
}
.progress-section code {
  font-family: "IBM Plex Mono", "SFMono-Regular", monospace; font-size: 12.5px;
}
.p-card, .stat {
  background: var(--panel); border: 1px solid var(--border);
  border-radius: 12px; padding: 18px 20px; margin: 0;
}
.p-card > h2 {
  margin: 0 0 14px; font-size: 12px; font-weight: 600;
  letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted);
}
.p-card > h2 code { text-transform: none; letter-spacing: 0; }
.p-hero {
  display: grid; gap: 20px; align-items: start;
  grid-template-columns: minmax(0, 1fr) minmax(320px, 440px);
}
@media (max-width: 1000px) { .p-hero { grid-template-columns: 1fr; } }
.stats { display: grid; gap: 14px; grid-template-columns: repeat(3, minmax(0, 1fr)); }
@media (max-width: 700px) { .stats { grid-template-columns: 1fr; } }
.stat.primary { grid-column: 1 / -1; border-color: var(--p-accent); }
.stat-label {
  font-size: 12px; font-weight: 600; letter-spacing: 0.06em;
  text-transform: uppercase; color: var(--muted);
}
.stat-value {
  font-size: 38px; font-weight: 700; line-height: 1.15; margin: 6px 0 2px;
  font-variant-numeric: tabular-nums;
}
.stat.primary .stat-value { font-size: 58px; color: var(--p-accent); }
.stat-sub { font-size: 13px; color: var(--muted); }
.callout {
  margin-top: 14px; padding: 14px 18px; background: var(--panel);
  border: 1px solid var(--border); border-left: 3px solid var(--p-accent);
  border-radius: 10px; color: var(--text);
}
.profile-grid { display: grid; gap: 10px; grid-template-columns: repeat(5, minmax(0, 1fr)); }
@media (max-width: 700px) { .profile-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
.profile-cell { padding: 8px 10px; border: 1px solid var(--border); border-radius: 10px; }
.profile-cell.total { border-color: var(--p-accent); }
.profile-cell .v { font-size: 22px; font-weight: 700; font-variant-numeric: tabular-nums; }
.profile-cell .k { font-size: 12px; color: var(--muted); letter-spacing: 0.04em; text-transform: uppercase; }
.chip {
  display: inline-block; padding: 1px 8px; border-radius: 999px;
  font-size: 11.5px; font-weight: 500; letter-spacing: 0; text-transform: none;
  border: 1px solid var(--border); color: var(--muted); white-space: nowrap;
}
.chip.down { color: var(--p-good); border-color: var(--p-good); }
.table-wrap { overflow-x: auto; }
.ctable { width: 100%; border-collapse: separate; border-spacing: 0; font-size: 13.5px; }
.ctable th {
  text-align: left; font-size: 12px; font-weight: 600; letter-spacing: 0.06em;
  text-transform: uppercase; color: var(--muted); padding: 8px 12px;
  border-bottom: 1px solid var(--border); white-space: nowrap;
}
.ctable td { padding: 10px 12px; vertical-align: top; border-bottom: 1px solid var(--border); }
.ctable tr.date-row th {
  padding: 16px 12px 6px; border-bottom: 0; letter-spacing: 0.02em;
  text-transform: none; font-size: 12.5px; color: var(--p-accent);
}
.ctable tr.date-row:first-child th, .ctable thead + tbody tr.date-row:first-child th { padding-top: 8px; }
.ctable th.c-area, .ctable td.c-area { text-align: right; }
.ctable td.c-time { color: var(--muted); white-space: nowrap; width: 64px; font-variant-numeric: tabular-nums; }
.ctable td.c-sha { white-space: nowrap; width: 150px; }
.ctable td.c-desc { min-width: 220px; }
.ctable td.c-area { white-space: nowrap; width: 150px; font-variant-numeric: tabular-nums; }
.ctable td.c-note { min-width: 260px; }
.ctable .sub { display: block; font-size: 12px; color: var(--muted); font-weight: 400; }
.ctable .chip { margin-top: 3px; }
.ctable tr.idle td { color: var(--muted); }
.ctable tr.idle td.c-area b { font-weight: 500; }
.ctable tr.drop td { background: var(--p-good-bg); }
.ctable tr.drop td:first-child { box-shadow: inset 3px 0 0 var(--p-good); }
.ctable tr.drop td.c-area b { color: var(--p-good); }
.ctable tr.baseline td { background: var(--p-soft); }
.ctable tr.worktree td { font-style: italic; }
.swatch {
  display: inline-block; width: 11px; height: 11px; margin-right: 7px;
  border-radius: 3px; vertical-align: -1px;
}
.p-map svg { display: block; width: 100%; height: auto; border-radius: 8px; }
.p-map figcaption { margin-top: 10px; font-size: 12.5px; color: var(--muted); }
.map-legend { list-style: none; margin: 12px 0 0; padding: 0; font-size: 13px; }
.map-legend li { display: flex; align-items: baseline; gap: 6px; margin: 4px 0; }
.map-legend li span:last-child { color: var(--text); }
.map-legend .swatch { flex: none; }
.routes { display: grid; gap: 14px; grid-template-columns: repeat(auto-fit, minmax(260px, 1fr)); }
.route {
  border: 1px solid var(--border); border-top: 3px solid var(--route);
  border-radius: 10px; padding: 14px 16px; background: var(--p-soft);
}
.route-name { font-weight: 600; margin-bottom: 10px; }
.route-id {
  display: inline-block; min-width: 20px; margin-right: 8px; text-align: center;
  border-radius: 999px; background: var(--route); color: #07111f; font-size: 12px;
}
.route-facts { display: flex; gap: 22px; margin: 0 0 10px; }
.route-facts dt { font-size: 11.5px; color: var(--muted); }
.route-facts dd { margin: 0; font-size: 18px; font-weight: 600; font-variant-numeric: tabular-nums; }
.route-next { margin: 0; font-size: 13px; color: var(--muted); }
.route-next span {
  display: block; font-size: 11.5px; letter-spacing: 0.06em;
  text-transform: uppercase; margin-bottom: 2px;
}
.p-foot { margin: 14px 0 0; font-size: 12.5px; color: var(--muted); }
"""

STANDALONE_CSS = """
:root { --bg: #f5f7fb; --panel: #ffffff; --text: #0f172a; --muted: #475569;
  --border: #dbe2ea; }
:root[data-theme="dark"] { --bg: #0b1220; --panel: #101a2d; --text: #dbe7ff;
  --muted: #9db0cf; --border: #20304d; }
body { margin: 0; padding: 26px; background: var(--bg); color: var(--text);
  font-family: "IBM Plex Sans", "Segoe UI", sans-serif; }
"""


def standalone_html(fragment: str) -> str:
    return (
        '<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        "<title>MLC proof progress</title>"
        "<script>document.documentElement.dataset.theme = "
        "matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';"
        "</script>"
        f"<style>{STANDALONE_CSS}{PROGRESS_CSS}</style></head>"
        f"<body>{fragment}</body></html>\n"
    )


TEX_SPECIAL = {
    "\\": r"\textbackslash{}",
    "&": r"\&",
    "%": r"\%",
    "$": r"\$",
    "#": r"\#",
    "_": r"\_",
    "{": r"\{",
    "}": r"\}",
    "~": r"\textasciitilde{}",
    "^": r"\textasciicircum{}",
    "|": r"\textbar{}",
    "⊆": r"$\subseteq$",
    "π": r"$\pi$",
    "≤": r"$\leq$",
    "≥": r"$\geq$",
    "→": r"$\to$",
    "∈": r"$\in$",
    "∂": r"$\partial$",
    "μ": r"$\mu$",
    "×": r"$\times$",
    "−": r"$-$",
    "—": "---",
    "–": "--",
    "∅": r"$\emptyset$",
    "∞": r"$\infty$",
    "≈": r"$\approx$",
}


def tex_escape(value: object) -> str:
    return "".join(TEX_SPECIAL.get(char, char) for char in str(value))


def tex_swatch(color: str | None) -> str:
    if not color:
        return ""
    return rf"\textcolor[HTML]{{{color.lstrip('#')}}}{{\rule{{1.1ex}}{{1.1ex}}}}\,"


def commits_tex(rows: list[dict[str, object]]) -> str:
    lines = [
        r"\begin{tabularx}{\linewidth}"
        r"{@{}>{\raggedright\arraybackslash}p{19mm}l>{\raggedright\arraybackslash}X"
        r">{\raggedleft\arraybackslash}p{23mm}>{\raggedright\arraybackslash}X@{}}",
        r"\toprule",
        r"When & Commit & Description & Resolved share & What it resolved \\",
        r"\midrule",
    ]
    for row in rows:
        when = tex_escape(row["time"])
        if row["date"]:
            when = tex_escape(row["date"]) + r"\newline " + when
        area = float(row["area_upper_percent"])
        delta = format_delta(row["delta"])
        area_cell = tex_escape(format_percent(resolved_percent(area)))
        if delta:
            area_cell += r"\newline{\scriptsize " + tex_escape(delta) + "}"
        lines.append(
            " & ".join(
                [
                    when,
                    tex_swatch(swatch_color(row))
                    + r"\texttt{"
                    + tex_escape(row["sha"])
                    + "}",
                    tex_escape(row["subject"]),
                    area_cell,
                    tex_escape(row["note"]),
                ]
            )
            + r" \\"
        )
    lines += [r"\bottomrule", r"\end{tabularx}"]
    return "\n".join(lines) + "\n"


def routes_tex() -> str:
    lines = [
        r"\begin{tabularx}{\linewidth}"
        r"{@{}c>{\raggedright\arraybackslash}Xcc>{\raggedright\arraybackslash}X@{}}",
        r"\toprule",
        r"\# & Route & Planned reduction & Prior & Next theorem \\",
        r"\midrule",
    ]
    for route in PROGRESS_ROUTES:
        low, high = route["range"]
        lines.append(
            " & ".join(
                [
                    tex_swatch(str(route["color"])) + tex_escape(route["id"]),
                    tex_escape(route["name"]),
                    f"{low * 100:.0f}--{high * 100:.0f}" + r"\%",
                    f"{route['probability'] * 100:.0f}" + r"\%",
                    tex_escape(route["next"]),
                ]
            )
            + r" \\"
        )
    lines += [r"\bottomrule", r"\end{tabularx}"]
    return "\n".join(lines) + "\n"


def write_progress_assets(repo_root: Path, output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    rows = commit_progress_history(repo_root)
    fragment = progress_fragment_html(repo_root, rows)
    (output_dir / "progress_fragment.html").write_text(fragment, encoding="utf-8")
    (output_dir / "progress.html").write_text(
        standalone_html(fragment), encoding="utf-8"
    )
    (output_dir / "progress_map.svg").write_text(
        parameter_map_svg(repo_root, rows), encoding="utf-8"
    )
    (output_dir / "progress_commits.tex").write_text(
        commits_tex(rows), encoding="utf-8"
    )
    (output_dir / "progress_routes.tex").write_text(routes_tex(), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    write_progress_assets(args.repo, args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
