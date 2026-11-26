#!/usr/bin/env python3
"""Progress metrics and reports for the MLC dependency-graph site.

The unresolved set R is the set of parameters c in the Mandelbrot set M at
which no local-connectivity certificate has been proved. The dashboard reports
the resolved share 100% - mu*(R)/(4 pi) of the envelope; 100% means
mu*(R) = 0. MLC means R is empty, which gives 100%. The converse fails: a
measure-zero R may be nonempty, so the share is always read together with the
number of open root obligations. The commit gate works on the equivalent upper
bound mu*(R)/(4 pi).

The baseline is the state of the literature: the first commit of the history
whose formal root (``RootInput``) is exactly Dudko's Problems 4.3 and 4.4. Its
row lists the two open problems; later rows show what each commit resolved.

Lean sources are read from Git history. The module renders

* the commit table after the literature baseline,
* the route-planning table,
* a vector map of M showing the parameters certified by each commit,
* LaTeX fragments used by the status report.
"""

from __future__ import annotations

from datetime import datetime
from pathlib import Path
import argparse
import functools
import hashlib
import html
import math
import re
import subprocess
import sys
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
        "exact": r"4\pi",
        "color": "#94a3b8",
        "title": "Disk envelope",
        "reason": (
            r"Proved $M\subseteq\{|c|\le 2\}$, so the unresolved set lies in "
            r"the disk of area $4\pi$ (the normalization of the area scale)."
        ),
        "regions": [
            {"kind": "disk", "cx": 0.0, "cy": 0.0, "r": 2.0, "role": "envelope"}
        ],
    },
    {
        "symbol": "ball_quarter_subset_interior_mandelbrot",
        "percent": 100.0 * 63.0 / 64.0,
        "exact": r"63\pi/16",
        "color": "#22c55e",
        "title": r"Interior disk $|c|<1/4$",
        "reason": (
            r"Proved $B(0,1/4)\subseteq\operatorname{int}M$. Local "
            r"connectivity is automatic at interior points, so this disk is "
            r"resolved: unresolved area $4\pi\to 63\pi/16$."
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
            "A kernel-checked dyadic grid removes the squares proved outside $M$ "
            "(ball-arithmetic escape test) or inside $M$ (periodic trapping "
            r"disk). The remaining cells cover $M\setminus\operatorname{int}M$."
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
        "next": r"Prove collars, hulls in $J$, and a divergent transfer budget.",
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
# Colours of the successive grid commits; the first is the colour of the
# "Kernel-checked grid" step. Orange is reserved for the unresolved cells.
GRID_PALETTE = (
    "#38bdf8",
    "#a78bfa",
    "#f472b6",
    "#2dd4bf",
    "#e879f9",
    "#a3e635",
    "#f87171",
    "#6366f1",
)
TARGET_PERCENT = 1.0  # second gate: a hundredfold reduction of the unresolved area
MIN_TARGET_PERCENT = 5.0  # first gate: a twentyfold reduction, i.e. a 95% resolved share
MAP_WINDOW = (-2.3, 0.8, -1.4, 1.4)
MAP_GRID = (620, 560)
MAP_ITERATIONS = 120
EPS = 1e-12


GRID_SYMBOL = "unresolved_volume_le_grid"
ROOT_LEVEL = 3  # the root squares have side 2^-3


def _lean_nat(name: str, lean_text: str) -> int | None:
    found = re.search(rf"def {name}\s*:\s*(?:ℕ|Nat)\s*:=\s*(\d+)", lean_text)
    return int(found.group(1)) if found else None


def grid_bound(lean_text: str) -> dict[str, object] | None:
    """Area bound proved by the kernel-checked grid, read from the Lean source."""
    if GRID_SYMBOL not in lean_text:
        return None
    if "def gridModules" in lean_text:
        # Modules of tiles with their own depths; the cells are weighed to the
        # common side 2^-scale.
        weight, scale = (_lean_nat(name, lean_text) for name in ("gridCells", "gridDepth"))
        depths = [int(v) for v in re.findall(r"\((\d+), tiles_\d+_\d+\)", lean_text)]
        if weight is None or scale is None or not depths:
            return None
        n, d = weight, scale
        while n % 4 == 0 and d > max(depths):
            n, d = n // 4, d - 1
        area = 2.0 * weight / 4**scale
        return {
            "format": "blocks",
            "cells": n,
            "depth": d,
            "weight": weight,
            "scale": scale,
            "finest": max(depths),
            "coarsest": min(depths),
            "area": area,
            "percent": 100.0 * area / (4.0 * math.pi),
            "exact": rf"2\cdot {n}/4^{{{d}}}",
        }
    cells, fuel, pmax, steps = (
        _lean_nat(name, lean_text)
        for name in ("gridCells", "gridFuel", "gridPmax", "gridJ")
    )
    hints = "def gridTiles" in lean_text
    # Only the classifier of the first grids has search parameters in the source.
    if cells is None or fuel is None or (not hints and None in (pmax, steps)):
        return None
    depth = fuel + ROOT_LEVEL
    n, d = cells, depth
    area = 2.0 * n / 4**d
    return {
        "format": "hints" if hints else "classifier",
        "cells": n,
        "depth": d,
        "weight": n,
        "scale": d,
        "fuel": fuel,
        "pmax": pmax,
        "J": steps,
        "area": area,
        "percent": 100.0 * area / (4.0 * math.pi),
        "exact": rf"2\cdot {n}/4^{{{d}}}",
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
    area_exact = r"4\pi"
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


def has_literature_root(repo_root: Path, ref: str) -> bool:
    """The formal root of ``ref`` has exactly Dudko's two open problems as fields."""
    proc = subprocess.run(
        ["git", "grep", "-h", "-A4", "-E", r"^structure RootInput\b", ref, "--", "Mlc"],
        cwd=repo_root,
        check=False,
        text=True,
        capture_output=True,
    )
    if proc.returncode != 0:
        return False
    fields: list[str] = []
    inside = False
    for line in proc.stdout.splitlines():
        if line.startswith("structure RootInput"):
            inside = True
            continue
        field = re.match(r"[ \t]+\w+\s*:\s*(\w+)", line)
        if inside and field:
            fields.append(field.group(1))
        elif inside:
            break
    return fields == list(OPEN_ROOT_SYMBOLS)


def literature_baseline(repo_root: Path) -> str:
    """The first commit of the history whose formal root is exactly Dudko's
    Problems 4.3 and 4.4: the state of the literature (MLC follows from them).

    The test is monotone along the first-parent history, so a binary search
    finds the commit.
    """
    history = _git(repo_root, "rev-list", "--reverse", "--first-parent", "HEAD").splitlines()
    if not history or not has_literature_root(repo_root, history[-1]):
        raise RuntimeError("The root of HEAD is not Dudko's Problems 4.3 and 4.4")
    low, high = 0, len(history) - 1
    while low < high:
        mid = (low + high) // 2
        if has_literature_root(repo_root, history[mid]):
            high = mid
        else:
            low = mid + 1
    return history[low]


def _step_by_symbol(symbol: str) -> dict[str, object]:
    return next(step for step in AREA_STEPS if step["symbol"] == symbol)


LITERATURE_NAME = "the literature baseline"


def commit_progress_history(repo_root: Path) -> list[dict[str, object]]:
    try:
        base = literature_baseline(repo_root)
        base_name = LITERATURE_NAME
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
        message = _git(repo_root, "show", "-s", "--format=%B", ref)
        noted = re.search(r"(?m)^Area-note:\s*(.+)$", message)
        rows.append(
            {
                "sha": short,
                "timestamp": int(stamp),
                "subject": subject,
                "area_note": noted.group(1).strip() if noted else "",
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
    grid_commits = 0
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
                "State of the literature: MLC follows from Dudko's Problems 4.3 "
                "and 4.4, which remain open. The unresolved set $R$ is only "
                r"known to lie in the disk $|c|\le 2$ of area $4\pi$."
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
                row["layer"] = {
                    "color": GRID_PALETTE[grid_commits % len(GRID_PALETTE)],
                    "grid": grid,
                    "sha": row["sha"],
                }
                grid_commits += 1
                before = previous.get("grid")
                modern = ("hints", "blocks")
                if grid.get("format") in modern and (
                    before is None or before.get("format") not in modern
                ):
                    lead = (
                        "First-order Taylor models of the critical orbit replace the "
                        "disk enclosures: a square is outside $M$ when the model "
                        "leaves the disk $|z|\\le 2$, and inside $M$ when a moving "
                        "disk around the model returns into itself. The unresolved "
                        "layer at a hyperbolic component is then as thin as the "
                        "cells, while the disk enclosures needed a layer of "
                        "thickness $\\sqrt{s}$ for cells of side $s$. A search "
                        "program writes the certificates as hints that the kernel "
                        "verifies. "
                    )
                else:
                    lead = (
                        f"{row['area_note']} " if row.get("area_note") else "Finer certified grid. "
                    )
                weights = (
                    f" Cells of the blocks of depth {grid['coarsest']} count with "
                    "their weights."
                    if grid.get("format") == "blocks"
                    and grid["coarsest"] != grid["finest"]
                    else ""
                )
                reasons = (
                    (reasons + " " if steps else lead)
                    + f"Depth {grid['depth']}: {grid['cells']} unresolved cells of "
                    f"side $2^{{-{grid['depth']}}}$ in the upper half-plane (the "
                    "lower half is the mirror image), unresolved area "
                    rf"$\le {grid['exact']}\approx {grid['area']:.3f}$." + weights
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


# Text with TeX math. Math is written between dollar signs in TeX syntax and
# rendered once as TeX (``tex_rich``) and once as MathML (``html_rich``), so both
# outputs typeset the same formulas.
MATH_TOKEN = re.compile(r"\\[A-Za-z]+|\\.|.", re.S)
MATH_OPERATORS = {
    "le": "≤",
    "leq": "≤",
    "ge": "≥",
    "geq": "≥",
    "approx": "≈",
    "subseteq": "⊆",
    "setminus": "∖",
    "to": "→",
    "cdot": "⋅",
    "times": "×",
    "in": "∈",
}
MATH_IDENTIFIERS = {
    "pi": "π",
    "mu": "μ",
    "partial": "∂",
    "varnothing": "∅",
    "infty": "∞",
}
MATH_SPACES = {",": "0.1667em", " ": "0.2778em"}
DIGITS = "0123456789"


def _ml_argument(tokens: list[str], pos: int) -> tuple[str, int]:
    """A script or radicand: a braced group or a single token."""
    while pos < len(tokens) and tokens[pos] == " ":
        pos += 1
    if pos >= len(tokens):
        raise ValueError("Missing argument in TeX math")
    if tokens[pos] == "{":
        items, pos = _ml_sequence(tokens, pos + 1, True)
        return "<mrow>" + "".join(items) + "</mrow>", pos
    items, _ = _ml_sequence([tokens[pos]], 0, False)
    return "".join(items), pos + 1


def _ml_sequence(
    tokens: list[str], pos: int = 0, nested: bool = False
) -> tuple[list[str], int]:
    """MathML elements of a TeX math token list (a subset of TeX)."""
    items: list[str] = []
    while pos < len(tokens):
        token = tokens[pos]
        pos += 1
        if token == "}":
            if not nested:
                raise ValueError("Unbalanced } in TeX math")
            return items, pos
        if token == "{":
            inner, pos = _ml_sequence(tokens, pos, True)
            items.append("<mrow>" + "".join(inner) + "</mrow>")
        elif token in ("^", "_"):
            base = items.pop() if items else "<mrow></mrow>"
            first, pos = _ml_argument(tokens, pos)
            other = "_" if token == "^" else "^"
            second = None
            if pos < len(tokens) and tokens[pos] == other:
                second, pos = _ml_argument(tokens, pos + 1)
            sup, sub = (first, second) if token == "^" else (second, first)
            if sup is not None and sub is not None:
                items.append(f"<msubsup>{base}{sub}{sup}</msubsup>")
            elif sup is not None:
                items.append(f"<msup>{base}{sup}</msup>")
            else:
                items.append(f"<msub>{base}{sub}</msub>")
        elif token == " ":
            continue
        elif token in (r"\operatorname", r"\mathrm", r"\text"):
            if pos >= len(tokens) or tokens[pos] != "{" or "}" not in tokens[pos:]:
                raise ValueError(f"{token} needs a braced argument")
            end = tokens.index("}", pos)
            text = html.escape("".join(tokens[pos + 1 : end]))
            pos = end + 1
            if token == r"\text":
                items.append(f"<mtext>{text}</mtext>")
            else:
                items.append(f'<mi mathvariant="normal">{text}</mi>')
                if token == r"\operatorname":
                    items.append('<mspace width="0.1667em"></mspace>')
        elif token == r"\sqrt":
            radicand, pos = _ml_argument(tokens, pos)
            items.append(f"<msqrt>{radicand}</msqrt>")
        elif len(token) > 1 and token[0] == "\\" and token[1].isalpha():
            name = token[1:]
            if name in MATH_OPERATORS:
                items.append(f"<mo>{MATH_OPERATORS[name]}</mo>")
            elif name in MATH_IDENTIFIERS:
                items.append(f"<mi>{MATH_IDENTIFIERS[name]}</mi>")
            else:
                raise ValueError(f"Unsupported TeX command {token}")
        elif token[0] == "\\":
            name = token[1:]
            if name in MATH_SPACES:
                items.append(f'<mspace width="{MATH_SPACES[name]}"></mspace>')
            elif name in ("{", "}"):
                items.append(f'<mo stretchy="false">{name}</mo>')
            elif name == "%":
                items.append('<mi mathvariant="normal">%</mi>')
            else:
                raise ValueError(f"Unsupported TeX escape {token}")
        elif token in DIGITS:
            number = token
            while pos < len(tokens) and (
                tokens[pos] in DIGITS
                or (tokens[pos] == "." and pos + 1 < len(tokens) and tokens[pos + 1] in DIGITS)
            ):
                number += tokens[pos]
                pos += 1
            items.append(f"<mn>{number}</mn>")
        elif token in ("+", "-"):
            symbol = "−" if token == "-" else "+"
            form = "" if _binary_operator(tokens, pos - 1) else ' form="prefix"'
            items.append(f"<mo{form}>{symbol}</mo>")
        elif token in ("=", "<", ">", ","):
            items.append(f"<mo>{html.escape(token)}</mo>")
        elif token in ("(", ")", "[", "]"):
            items.append(f'<mo stretchy="false">{token}</mo>')
        elif token == "|":
            items.append('<mo stretchy="false" lspace="0" rspace="0">|</mo>')
        elif token == "/":
            items.append('<mo lspace="0" rspace="0">/</mo>')
        elif token == "*":
            items.append("<mo>∗</mo>")
        elif token.isalpha():
            items.append(f"<mi>{token}</mi>")
        else:
            raise ValueError(f"Unsupported TeX token {token!r}")
    if nested:
        raise ValueError("Unbalanced { in TeX math")
    return items, pos


def _binary_operator(tokens: list[str], index: int) -> bool:
    """A + or - after an operand is binary; elsewhere it is a sign."""
    j = index - 1
    while j >= 0 and tokens[j] == " ":
        j -= 1
    if j < 0:
        return False
    before = tokens[j]
    if before in ("(", "[", "{", "^", "_", ",", "=", "<", ">", "+", "-"):
        return False
    return not (before.startswith("\\") and before[1:] in MATH_OPERATORS)


def _split_math(text: str) -> list[str]:
    parts = re.split(r"(?<!\\)\$", text)
    if len(parts) % 2 == 0:
        raise ValueError(f"Unbalanced $ in {text!r}")
    return parts


def html_rich(text: object) -> str:
    """HTML for a text whose ``$...$`` parts are TeX math, typeset as MathML."""
    out = []
    for index, part in enumerate(_split_math(str(text))):
        if index % 2:
            items, _ = _ml_sequence(MATH_TOKEN.findall(part))
            out.append(f'<math class="tex">{"".join(items)}</math>')
        else:
            out.append(esc(part))
    return "".join(out)


def tex_rich(text: object) -> str:
    """LaTeX for a text whose ``$...$`` parts are TeX math."""
    return "".join(
        f"${part}$" if index % 2 else tex_escape(part)
        for index, part in enumerate(_split_math(str(text)))
    )


def swatch_color(row: dict[str, object]) -> str | None:
    layer = row.get("layer")
    if layer is not None:
        return str(layer["color"])
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


def share_label(row: dict[str, object]) -> tuple[str, str]:
    """Headline and detail (rich text) of the resolved-share cell.

    The baseline is the literature state, where Dudko's two problems are open;
    a commit that resolves nothing beyond it shows a dash instead of 0%.
    """
    if row["baseline"]:
        return "Open", "Dudko 4.3 and 4.4"
    area = float(row["area_upper_percent"])
    resolved = resolved_percent(area)
    if resolved <= EPS:
        return "—", ""
    detail = rf"unresolved $\le {exact_area_text(row)}\approx {area_value(area):.3f}$"
    return format_percent(resolved), detail


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
        headline, detail = share_label(row)
        delta = format_delta(row["delta"])
        chip = (
            f'<span class="chip down">{esc(delta)}</span>'
            if kind == "drop" and delta
            else ""
        )
        sub = f'<span class="sub">{html_rich(detail)}</span>' if detail else ""
        note = "—" if kind == "idle" else html_rich(row["note"])
        out.append(
            f'<tr class="{kind}">'
            f'<td class="c-time">{esc(row["time"])}</td>'
            f'<td class="c-sha">{dot}<code>{esc(row["sha"])}</code>{tag}</td>'
            f'<td class="c-desc">{esc(row["subject"])}</td>'
            f'<td class="c-area"><b>{esc(headline)}</b>{sub}{chip}</td>'
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
            f"</span>{html_rich(route['name'])}</div>"
            '<dl class="route-facts">'
            f"<div><dt>Planned reduction</dt><dd>{low * 100:.0f}–{high * 100:.0f}%</dd></div>"
            f"<div><dt>Planning prior</dt><dd>{route['probability'] * 100:.0f}%</dd></div>"
            "</dl>"
            f'<p class="route-next"><span>Next theorem</span>{html_rich(route["next"])}</p>'
            "</div>"
        )
    return f'<div class="routes">{"".join(cards)}</div>'


def _contour_path(mask: list[list[bool]]) -> str:
    """Border of a pixel mask by marching squares.

    The vertices are the midpoints between neighbouring pixel centres; the
    result is a set of closed polylines in pixel units.
    """
    ny, nx = len(mask), len(mask[0])

    def inside(i: int, t: int) -> bool:
        return 0 <= t < ny and 0 <= i < nx and mask[t][i]

    neighbours: dict[tuple[int, int], list[tuple[int, int]]] = {}

    def link(p: tuple[int, int], q: tuple[int, int]) -> None:
        neighbours.setdefault(p, []).append(q)
        neighbours.setdefault(q, []).append(p)

    for t in range(-1, ny):
        for i in range(-1, nx):
            case = (
                inside(i, t)
                + 2 * inside(i + 1, t)
                + 4 * inside(i + 1, t + 1)
                + 8 * inside(i, t + 1)
            )
            if case in (0, 15):
                continue
            top = (2 * i + 2, 2 * t + 1)
            right = (2 * i + 3, 2 * t + 2)
            bottom = (2 * i + 2, 2 * t + 3)
            left = (2 * i + 1, 2 * t + 2)
            if case in (1, 14):
                link(left, top)
            elif case in (2, 13):
                link(top, right)
            elif case in (4, 11):
                link(right, bottom)
            elif case in (8, 7):
                link(bottom, left)
            elif case in (3, 12):
                link(left, right)
            elif case in (6, 9):
                link(top, bottom)
            elif case == 5:
                link(left, top)
                link(right, bottom)
            else:
                link(top, right)
                link(bottom, left)

    visited: set[tuple[int, int]] = set()
    loops = []
    for start in neighbours:
        if start in visited:
            continue
        loop = []
        previous, current = None, start
        while True:
            visited.add(current)
            loop.append(current)
            first, second = neighbours[current]
            following = first if first != previous else second
            previous, current = current, following
            if current == start:
                break
        corners = [
            loop[k]
            for k in range(len(loop))
            if (loop[k][0] - loop[k - 1][0]) * (loop[(k + 1) % len(loop)][1] - loop[k][1])
            != (loop[k][1] - loop[k - 1][1]) * (loop[(k + 1) % len(loop)][0] - loop[k][0])
        ]
        if len(corners) >= 3:
            loops.append(corners)
    parts = []
    for corners in loops:
        points = " ".join(f"{x / 2:g} {y / 2:g}" for x, y in corners[1:])
        parts.append(f"M{corners[0][0] / 2:g} {corners[0][1] / 2:g}L{points}Z")
    return "".join(parts)


def mandelbrot_border(repo_root: Path) -> str:
    """Vector path of the border of a numerical rendering of M (illustration only)."""
    nx, ny = MAP_GRID
    cache_dir = repo_root / ".lake" / "progress-cache"
    cache = cache_dir / f"mandelbrot_border_{nx}x{ny}_{MAP_ITERATIONS}.txt"
    if cache.exists():
        return cache.read_text(encoding="utf-8")
    x0, x1, y0, y1 = MAP_WINDOW
    dx = (x1 - x0) / nx
    dy = (y1 - y0) / ny
    upper: list[list[bool]] = []
    for t in range(ny // 2):
        ci = y1 - (t + 0.5) * dy
        row: list[bool] = []
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
            row.append(inside)
        upper.append(row)
    data = _contour_path(upper + upper[::-1])
    cache_dir.mkdir(parents=True, exist_ok=True)
    cache.write_text(data, encoding="utf-8")
    return data


def merge_rects(
    rects: list[tuple[float, float, float, float]]
) -> list[tuple[float, float, float, float]]:
    """Merge horizontally adjacent rectangles with the same vertical extent."""
    rows: dict[tuple[float, float], list[tuple[float, float]]] = {}
    for x0, y0, x1, y1 in rects:
        rows.setdefault((y0, y1), []).append((x0, x1))
    merged = []
    for (y0, y1), spans in rows.items():
        spans.sort()
        start, end = spans[0]
        for x0, x1 in spans[1:]:
            if abs(x0 - end) < 1e-12:
                end = x1
            else:
                merged.append((start, y0, end, y1))
                start, end = x0, x1
        merged.append((start, y0, end, y1))
    return merged


@functools.lru_cache(maxsize=None)
def _grid_regions(
    repo_root: Path, pmax: int, steps: int, fuel: int, cells: int
) -> tuple[dict[str, object], ...]:
    sources = [repo_root / "export_grid_regions.lean"]
    if not all(path.exists() for path in sources):
        return ()
    params = [str(pmax), str(steps), str(fuel)]
    digest = hashlib.sha256(
        b"".join(path.read_bytes() for path in sources) + "/".join(params).encode()
    ).hexdigest()[:16]
    cache_dir = repo_root / ".lake" / "progress-cache"
    cache = cache_dir / f"grid_regions_{digest}.txt"
    if cache.exists():
        text = cache.read_text(encoding="utf-8")
    else:
        proc = subprocess.run(
            ["lake", "env", "lean", "--run", "export_grid_regions.lean", *params],
            cwd=repo_root,
            check=False,
            text=True,
            capture_output=True,
        )
        if proc.returncode != 0:
            return ()
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
    count = len(unresolved) // 2
    if count != cells:
        print(
            f"warning: the grid with parameters {params} leaves {count} unresolved "
            f"cells; its commit proved {cells}, so its regions are omitted",
            file=sys.stderr,
        )
        return ()
    return (
        {"kind": "rects", "role": "interior", "rects": merge_rects(inner)},
        {"kind": "rects", "role": "unresolved", "rects": merge_rects(unresolved)},
    )


TILE_ENTRY = re.compile(r"\(⟨(-?\d+), (-?\d+), (\d+)⟩,\s*\[([^\]]*)\]\)")
MODULE_DEPTH = re.compile(r"cellsH \((\d+) - p\.1\.k\)")


def _module_order(name: str) -> tuple[int, ...]:
    """Order of the tile modules: ``G<block>_<part>`` by block and part, the earlier
    ``Part<index>`` by index."""
    stem = Path(name).stem
    return tuple(int(v) for v in re.findall(r"\d+", stem))


def tile_texts(repo_root: Path, sha: str) -> list[str]:
    """The tile modules of a commit (or of the working tree), in order."""
    if sha == "worktree":
        paths = sorted(
            (repo_root / "Mlc" / "GridTiles").glob("*.lean"),
            key=lambda path: _module_order(path.name),
        )
        return [path.read_text(encoding="utf-8") for path in paths]
    names = sorted(
        _git(
            repo_root, "ls-tree", "-r", "--name-only", sha, "--", "Mlc/GridTiles"
        ).splitlines(),
        key=_module_order,
    )
    return [
        subprocess.run(
            ["git", "show", f"{sha}:{name}"],
            cwd=repo_root,
            check=True,
            text=True,
            capture_output=True,
        ).stdout
        for name in names
    ]


def hint_squares(
    texts: list[str], depth: int, scale: int | None = None
) -> tuple[list[tuple[int, int, int]], list[tuple[int, int, int]], int]:
    """Replay the hint streams of the tile modules (``verifyTree``): the squares
    certified inside M, the unresolved squares and the number of unresolved
    finest cells, weighed to cells of side ``2^-scale`` (a module states its own
    depth; ``depth`` is used for modules that do not)."""
    scale = depth if scale is None else scale
    inside: list[tuple[int, int, int]] = []
    unresolved: list[tuple[int, int, int]] = []
    cells = 0
    for text in texts:
        stated = MODULE_DEPTH.search(text)
        module_depth = int(stated.group(1)) if stated else depth
        for entry in TILE_ENTRY.finditer(text):
            x, y, k = int(entry[1]), int(entry[2]), int(entry[3])
            hints = [int(v) for v in entry[4].split(",") if v.strip()]
            position = [0]

            def walk(x: int, y: int, k: int) -> None:
                nonlocal cells
                fuel = module_depth - k
                index = position[0]
                position[0] += 1
                hint = hints[index] if index < len(hints) else 0
                if hint == 0 or (hint == 1 and fuel == 0):
                    unresolved.append((x, y, k))
                    cells += 4**fuel * 4 ** (scale - module_depth)
                elif hint == 1:
                    for dx, dy in ((0, 0), (1, 0), (0, 1), (1, 1)):
                        walk(2 * x + dx, 2 * y + dy, k + 1)
                elif hint % 2 == 1:
                    inside.append((x, y, k))

            walk(x, y, k)
    return inside, unresolved, cells


def squares_to_regions(
    inside: list[tuple[int, int, int]], unresolved: list[tuple[int, int, int]]
) -> tuple[dict[str, object], ...]:
    """Map regions (upper half and its mirror image) of lists of squares."""
    inner: list[tuple[float, float, float, float]] = []
    outer: list[tuple[float, float, float, float]] = []
    for squares, target in ((inside, inner), (unresolved, outer)):
        for x, y, k in squares:
            scale = 2.0**k
            rect = (x / scale, y / scale, (x + 1) / scale, (y + 1) / scale)
            target.append(rect)
            target.append((rect[0], -rect[3], rect[2], -rect[1]))
    return (
        {"kind": "rects", "role": "interior", "rects": merge_rects(inner)},
        {"kind": "rects", "role": "unresolved", "rects": merge_rects(outer)},
    )


@functools.lru_cache(maxsize=None)
def _hint_regions(
    repo_root: Path, sha: str, depth: int, weight: int, scale: int
) -> tuple[dict[str, object], ...]:
    inside, unresolved, found = hint_squares(tile_texts(repo_root, sha), depth, scale)
    if found != weight:
        print(
            f"warning: the tiles of {sha} leave {found} unresolved cells; the commit "
            f"proved {weight}, so its regions are omitted",
            file=sys.stderr,
        )
        return ()
    return squares_to_regions(inside, unresolved)


def grid_regions(
    repo_root: Path, grid: dict[str, object], sha: str
) -> list[dict[str, object]]:
    """Squares of the grid of one commit.

    A grid of hints is replayed from the tile modules of the commit. An older
    grid, found by the classifier of the first commits, is reproduced by the
    Lean exporter (a copy of that classifier) with the parameters of the commit.
    In both cases the number of unresolved cells must equal the count that the
    commit proved; otherwise no regions are returned.
    """
    if grid.get("format") in ("hints", "blocks"):
        return list(
            _hint_regions(
                repo_root,
                sha,
                int(grid["depth"]),
                int(grid["weight"]),
                int(grid["scale"]),
            )
        )
    return list(
        _grid_regions(
            repo_root,
            int(grid["pmax"]),
            int(grid["J"]),
            int(grid["fuel"]),
            int(grid["cells"]),
        )
    )


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


MAP_MEANING = {
    "envelope": "bounding envelope (dashed)",
    "interior": "certified inside $M$",
    "exterior": "certified outside $M$",
}


def map_layers(
    repo_root: Path, rows: list[dict[str, object]]
) -> list[dict[str, object]]:
    """One layer per commit that certifies a region, oldest first.

    A commit contributes the regions of its step or, for a grid commit, the
    interior squares of its own grid, each in the colour of its table row. The
    unresolved cells of the latest grid join that layer.
    """
    layers: list[dict[str, object]] = []
    for row in rows:
        for step in row["steps"]:
            if step["regions"]:
                roles = sorted({str(region["role"]) for region in step["regions"]})
                meaning = ", ".join(MAP_MEANING[role] for role in roles)
                layers.append(
                    {
                        "sha": row["sha"],
                        "color": str(step["color"]),
                        "title": f"{step['title']} · {meaning}",
                        "regions": list(step["regions"]),
                    }
                )
        layer = row.get("layer")
        if layer is not None:
            grid = layer["grid"]
            regions = grid_regions(repo_root, grid, str(layer["sha"]))
            if regions:
                how = (
                    "Taylor-model certificates"
                    if grid.get("format") in ("hints", "blocks")
                    else f"periods up to {grid['pmax']}, {grid['J']} orbit steps"
                )
                depth_text = (
                    f"{grid['finest']}" if grid.get("format") == "blocks" else f"{grid['depth']}"
                )
                staged = re.match(r"Depth \d+ for (.+?)\.(?:\s|$)", str(row.get("area_note", "")))
                region_text = f" for {staged.group(1)}" if staged else ""
                layers.append(
                    {
                        "sha": row["sha"],
                        "color": str(layer["color"]),
                        "title": (
                            f"Kernel-checked grid of depth {depth_text}{region_text}: {how} · "
                            + MAP_MEANING["interior"]
                        ),
                        "regions": regions[:1],
                        "unresolved": regions[1],
                    }
                )
    grid_layers = [layer for layer in layers if "unresolved" in layer]
    for layer in grid_layers[:-1]:
        del layer["unresolved"]
    if grid_layers:
        latest = grid_layers[-1]
        latest["regions"] = [latest.pop("unresolved"), *latest["regions"]]
        latest["has_unresolved"] = True
    return layers


def parameter_map_svg(repo_root: Path, rows: list[dict[str, object]]) -> str:
    """Map of M; every colour marks the parameters certified by one commit."""
    nx, ny = MAP_GRID
    x0, x1, y0, y1 = MAP_WINDOW
    margin_left, margin_bottom, margin_top, margin_right = 46, 44, 10, 10
    total_w = nx + margin_left + margin_right
    total_h = ny + margin_top + margin_bottom
    # A newer commit certifies a larger area, so its layer is painted first;
    # every older, smaller layer is painted over it and stays visible.
    layers = [
        region_svg(region, str(layer["color"]))
        for layer in reversed(map_layers(repo_root, rows))
        for region in layer["regions"]
    ]
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
        f'xmlns:xlink="http://www.w3.org/1999/xlink" '
        f'viewBox="{-margin_left} {-margin_top} {total_w} {total_h}" '
        f'role="img" aria-label="Parameter plane with the certified regions" '
        f'font-family="IBM Plex Sans, Segoe UI, sans-serif">'
        f'<rect x="{-margin_left}" y="{-margin_top}" width="{total_w}" '
        f'height="{total_h}" fill="#07111f"/>'
        f'<defs><clipPath id="mapFrame"><rect width="{nx}" height="{ny}"/>'
        f'</clipPath><path id="mapBorder" fill="none" stroke-linejoin="round" '
        f'd="{mandelbrot_border(repo_root)}"/></defs>'
        f'<g clip-path="url(#mapFrame)">{"".join(grid)}'
        f'{"".join(layers)}'
        f'<use href="#mapBorder" xlink:href="#mapBorder" stroke="#07111f" '
        f'stroke-opacity="0.6" stroke-width="3.8"/>'
        f'<use href="#mapBorder" xlink:href="#mapBorder" stroke="#f8fafc" '
        f'stroke-width="1.8"/></g>'
        f'<rect width="{nx}" height="{ny}" fill="none" stroke="#475569" '
        f'stroke-width="1.5"/>{"".join(labels)}</svg>'
    )


def map_legend_html(repo_root: Path, rows: list[dict[str, object]]) -> str:
    items = []
    layers = map_layers(repo_root, rows)
    for layer in layers:
        items.append(
            f'<li><span class="swatch" style="background:{esc(layer["color"])}">'
            f'</span><code>{esc(layer["sha"])}</code>'
            f'<span>{html_rich(layer["title"])}</span></li>'
        )
    if any(layer.get("has_unresolved") for layer in layers):
        items.append(
            '<li><span class="swatch" style="background:#f59e0b"></span>'
            "<span>unresolved cells of the current grid</span></li>"
        )
    items.append(
        '<li><span class="swatch outline"></span>'
        f'<span>{html_rich("numerical outline of the border of $M$ (illustration)")}'
        "</span></li>"
    )
    return f'<ul class="map-legend">{"".join(items)}</ul>'


def stats_html(rows: list[dict[str, object]]) -> str:
    current = rows[-1]
    base = rows[0]
    area = float(current["area_upper_percent"])
    open_roots = int(current["open_frontier"])
    gates = tuple(
        (100.0 - percent, 100.0 / percent)
        for percent in (MIN_TARGET_PERCENT, TARGET_PERCENT)
    )
    reached = [gate for gate in gates if resolved_percent(area) >= gate[0]]
    ahead = [gate for gate in gates if resolved_percent(area) < gate[0]]
    gate_text = ", ".join(
        [f"{share:.0f}% (×{factor:.0f}) reached" for share, factor in reached]
        + [f"{share:.0f}% (×{factor:.0f}) next" for share, factor in ahead[:1]]
    )
    tiles = (
        (
            "primary",
            r"Certified resolved share of the $4\pi$ envelope",
            format_percent(resolved_percent(area)),
            rf"unresolved area $\le$ {format_percent(area)} of $4\pi$ "
            rf"(${exact_area_text(current)}\approx {area_value(area):.3f}$)",
        ),
        (
            "",
            "Unresolved-area reduction",
            format_factor(area),
            f"baseline {base['sha']}: Dudko's Problems 4.3 and 4.4 open",
        ),
        (
            "",
            "Target",
            "100%",
            f"unresolved area $0$. Gates: {gate_text}",
        ),
        (
            "",
            "Open root problems",
            str(open_roots),
            "Problems 4.3 and 4.4" if open_roots else "none",
        ),
    )
    cells = "".join(
        f'<div class="stat {kind}"><div class="stat-label">{html_rich(label)}</div>'
        f'<div class="stat-value">{esc(value)}</div>'
        f'<div class="stat-sub">{html_rich(sub)}</div></div>'
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
        "certificate exists. Overall is the mean of the four shares.</p></section>"
    )


def callout_html() -> str:
    text = (
        r"The resolved share is $100\%-\mu^*(R)/4\pi$: the part of the envelope "
        r"certified to be outside $M$ or at interior points of $M$, where local "
        r"connectivity is automatic. $R$ is the unresolved set. MLC means "
        r"$R=\varnothing$, which gives $100\%$. The converse fails: a nonempty "
        r"$R$ of measure zero also gives $100\%$, and the area of $\partial M$ "
        r"is itself unknown. Read the share together with the open problems. "
        r"The baseline is the state of the literature, where Dudko's Problems "
        r"4.3 and 4.4 are open."
    )
    return f'<aside class="callout"><b>How to read the number.</b> {html_rich(text)}</aside>'


def progress_fragment_html(repo_root: Path, rows: list[dict[str, object]]) -> str:
    svg = parameter_map_svg(repo_root, rows)
    baseline = esc(rows[0]["sha"])
    caption = html_rich(
        "Parameter plane $c=x+iy$. White outline: numerical rendering of the "
        "border of $M$ (an illustration that the Lean proof does not use). A "
        "colour marks the parameters certified by the commit with the same "
        "colour in the table. The layers are stacked from the newest, largest "
        "region at the bottom to the oldest on top."
    )
    return f"""<div class="progress-section">
<div class="p-hero">
<div class="p-hero-left">
{stats_html(rows)}
{profile_html(rows)}
{callout_html()}
</div>
<figure class="p-card p-map">
<h2>{html_rich("Certified region on $M$")}</h2>
{svg}
{map_legend_html(repo_root, rows)}
<figcaption>{caption}</figcaption>
</figure>
</div>
<section class="p-card">
<h2>Commits after the literature baseline <code>{baseline}</code></h2>
<div class="table-wrap">
{commit_table_html(rows)}
</div>
</section>
<section class="p-card">
<h2>Next routes <span class="chip">planning priors</span></h2>
{routes_html()}
<p class="p-foot">The commit hook requires the resolved share to increase,
while the formalization-debt proxy must not increase ({float(rows[-1]['debt_percent']):.3f}% now).</p>
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
.swatch.outline { background: #07111f; box-shadow: inset 0 0 0 2px #f8fafc; }
math.tex {
  white-space: nowrap; text-transform: none; letter-spacing: normal;
  font-family: "STIX Two Math", "Latin Modern Math", "Cambria Math", "DejaVu Math TeX Gyre", math;
  font-size: 1.1em;
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
.route-next > span:first-child {
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
    """Rows of the commits table. The environment (``xltabular``, which breaks
    across pages) with its header and footer is in ``docs/mlc_progress.tex``."""
    lines = []
    for row in rows:
        when = tex_escape(row["time"])
        if row["date"]:
            when = tex_escape(row["date"]) + r"\newline " + when
        headline, _ = share_label(row)
        delta = format_delta(row["delta"])
        share_cell = tex_escape(headline)
        if row["baseline"]:
            share_cell += r"\newline{\scriptsize Dudko 4.3, 4.4}"
        elif delta:
            share_cell += r"\newline{\scriptsize " + tex_escape(delta) + "}"
        note = "---" if row_kind(row) == "idle" else tex_rich(row["note"])
        lines.append(
            " & ".join(
                [
                    when,
                    tex_swatch(swatch_color(row))
                    + r"\texttt{"
                    + tex_escape(row["sha"])
                    + "}",
                    tex_escape(row["subject"]),
                    share_cell,
                    note,
                ]
            )
            + r" \\"
        )
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
                    tex_rich(route["name"]),
                    f"{low * 100:.0f}--{high * 100:.0f}" + r"\%",
                    f"{route['probability'] * 100:.0f}" + r"\%",
                    tex_rich(route["next"]),
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
