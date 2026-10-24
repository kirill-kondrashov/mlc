#!/usr/bin/env python3
"""Render a high-resolution Mandelbrot status figure for the review."""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LinearSegmentedColormap, Normalize
from matplotlib.lines import Line2D
from matplotlib.patches import Patch, Rectangle


FEIGENBAUM = -1.401155189092 + 0.0j
PARABOLIC_ROOT = 0.25 + 0.0j
MISUREWICZ = -2.0 + 0.0j


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("docs/figures/mlc_status_render.pdf"),
        help="output PDF path",
    )
    return parser.parse_args()


def escape_render(
    bounds: tuple[float, float, float, float],
    width: int,
    height: int,
    max_iter: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    x_min, x_max, y_min, y_max = bounds
    x = np.linspace(x_min, x_max, width)
    y = np.linspace(y_min, y_max, height)
    parameters = x[None, :] + 1j * y[:, None]
    orbit = np.zeros_like(parameters)
    escape_time = np.full(parameters.shape, float(max_iter + 1))
    escaped = np.zeros(parameters.shape, dtype=bool)

    for iteration in range(max_iter):
        active = ~escaped
        orbit[active] = orbit[active] * orbit[active] + parameters[active]
        newly_escaped = active & (np.abs(orbit) > 2.0)
        if np.any(newly_escaped):
            modulus = np.abs(orbit[newly_escaped])
            escape_time[newly_escaped] = (
                iteration
                + 1
                - np.log(np.log(modulus)) / np.log(2.0)
            )
        escaped |= newly_escaped

    inside = ~escaped
    return x, y, escape_time, inside


def escape_cmap() -> LinearSegmentedColormap:
    return LinearSegmentedColormap.from_list(
        "mlc_escape",
        [
            "#fff7bc",
            "#fec44f",
            "#fe9929",
            "#ec7014",
            "#cc4c02",
            "#993404",
            "#54278f",
            "#2b1b47",
        ],
    )


def plot_render(
    ax: plt.Axes,
    bounds: tuple[float, float, float, float],
    width: int,
    height: int,
    max_iter: int,
    *,
    title: str,
    boundary_color: str = "#f2f2f2",
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    x, y, escape_time, inside = escape_render(
        bounds, width, height, max_iter
    )
    image = np.ma.masked_where(
        inside, np.clip(escape_time, 0.0, float(max_iter))
    )
    cmap = escape_cmap()
    cmap.set_bad("#10131a")
    ax.imshow(
        image,
        extent=bounds,
        origin="lower",
        interpolation="none",
        cmap=cmap,
        norm=Normalize(0.0, float(max_iter)),
        aspect="equal",
    )
    ax.contour(
        x,
        y,
        inside.astype(float),
        levels=[0.5],
        colors=[boundary_color],
        linewidths=0.45,
        alpha=0.95,
    )
    ax.set_xlim(bounds[0], bounds[1])
    ax.set_ylim(bounds[2], bounds[3])
    ax.set_aspect("equal", adjustable="box")
    ax.set_title(title, fontsize=11, pad=7)
    ax.set_xlabel(r"$\operatorname{Re} c$", fontsize=8)
    ax.set_ylabel(r"$\operatorname{Im} c$", fontsize=8)
    ax.tick_params(labelsize=7, length=2, pad=2)
    return x, y, inside


def cardioid_mask(
    x: np.ndarray, y: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    parameters = x[None, :] + 1j * y[:, None]
    multiplier = 1.0 - np.sqrt(1.0 - 4.0 * parameters)
    cardioid = np.abs(multiplier) <= 1.0
    period_two_bulb = np.abs(parameters + 1.0) <= 0.25
    return cardioid, period_two_bulb


def overlay_main_components(
    ax: plt.Axes, x: np.ndarray, y: np.ndarray
) -> None:
    cardioid, period_two_bulb = cardioid_mask(x, y)
    ax.contour(
        x,
        y,
        cardioid.astype(float),
        levels=[0.5],
        colors=["#5abf72"],
        linewidths=1.1,
    )
    ax.contour(
        x,
        y,
        period_two_bulb.astype(float),
        levels=[0.5],
        colors=["#5abf72"],
        linewidths=1.1,
    )
    ax.text(
        -0.32,
        -0.03,
        "main cardioid\n(attracting fixed point)",
        color="#d9ffe1",
        fontsize=7,
        ha="center",
        va="center",
        bbox={"facecolor": "#15291b", "edgecolor": "#5abf72", "alpha": 0.9},
    )
    ax.text(
        -1.0,
        -0.02,
        "period 2",
        color="#d9ffe1",
        fontsize=7,
        ha="center",
        va="center",
        bbox={"facecolor": "#15291b", "edgecolor": "#5abf72", "alpha": 0.9},
    )


def annotate_known_points(ax: plt.Axes) -> None:
    points = [
        (
            MISUREWICZ,
            "Misiurewicz\n(DH/Yoccoz)",
            "#62c5ff",
            (0.13, 0.28),
        ),
        (
            PARABOLIC_ROOT,
            "parabolic root\n(DH/Yoccoz)",
            "#62c5ff",
            (-0.52, 0.24),
        ),
    ]
    for point, label, color, offset in points:
        ax.scatter(
            [point.real],
            [point.imag],
            s=25,
            color=color,
            edgecolor="#11151d",
            linewidth=0.55,
            zorder=8,
        )
        ax.annotate(
            label,
            xy=(point.real, point.imag),
            xytext=(point.real + offset[0], point.imag + offset[1]),
            fontsize=7,
            color=color,
            ha="center",
            va="center",
            arrowprops={"arrowstyle": "-", "color": color, "lw": 0.7},
            bbox={
                "facecolor": "#10131a",
                "edgecolor": color,
                "alpha": 0.9,
                "pad": 2,
            },
            zorder=9,
        )


def add_main_legend(ax: plt.Axes) -> None:
    ax.legend(
        handles=[
            Patch(
                facecolor="#10131a",
                edgecolor="#f2f2f2",
                label="numerically bounded orbit",
            ),
            Line2D(
                [0],
                [0],
                color="#f2f2f2",
                lw=1,
                label="rendered boundary of $M$",
            ),
        ],
        loc="lower left",
        fontsize=7,
        framealpha=0.9,
        facecolor="#10131a",
        edgecolor="#667085",
        labelcolor="white",
    )


def add_status_table(ax: plt.Axes) -> None:
    ax.axis("off")
    ax.set_title(
        "Components and theorem coverage",
        fontsize=10,
        loc="left",
        pad=8,
    )
    rows = [
        ["Interior", "open subset of C", "proved"],
        ["Hyperbolic / subhyp.", "DH external rays", "partial"],
        ["Misiurewicz / parabolic", "DH--Yoccoz puzzles", "interface"],
        ["Finitely renorm.", "Yoccoz moduli", "interface"],
        ["Bounded satellite", "Dudko--Lyubich", "interface"],
        ["Feigenbaum", "Dudko--Lyubich", "interface"],
        ["Parabolic primitive", "Kahn--Kapiamba--Lyubich", "interface"],
        ["Neutral renorm.", "Dudko--Lim--Lyubich", "interface"],
        ["Unbounded IR frontier", "not covered", "open"],
    ]
    table = ax.table(
        cellText=rows,
        colLabels=["component / class", "mathematical input", "Lean"],
        colWidths=[0.24, 0.55, 0.15],
        cellLoc="left",
        colLoc="left",
        loc="upper left",
        bbox=[0.0, 0.05, 1.0, 0.82],
    )
    table.auto_set_font_size(False)
    table.set_fontsize(8.2)
    table.scale(1.0, 1.65)
    for (row, column), cell in table.get_celld().items():
        cell.set_edgecolor("#596273")
        cell.set_linewidth(0.45)
        cell.PAD = 0.045
        if row == 0:
            cell.set_facecolor("#263244")
            cell.get_text().set_color("white")
            cell.get_text().set_weight("bold")
        else:
            cell.set_facecolor("#171c27" if row % 2 else "#202735")
            cell.get_text().set_color("#e8edf5")
            if column == 2:
                status = rows[row - 1][2]
                cell.get_text().set_color(
                    "#8ee39b"
                    if status == "proved"
                    else "#f5c542"
                    if status == "interface"
                    else "#ff8b7b"
                )
    ax.text(
        0.0,
        0.0,
        "The overlay records the proof inventory, not a decidable "
        "characteristic function of the unresolved set.",
        transform=ax.transAxes,
        fontsize=7,
        color="#4e5969",
        va="top",
    )


def make_figure(output: Path) -> None:
    plt.rcParams.update(
        {
            "font.family": "DejaVu Serif",
            "mathtext.fontset": "dejavuserif",
            "axes.edgecolor": "#697386",
            "axes.labelcolor": "#313a4d",
            "xtick.color": "#313a4d",
            "ytick.color": "#313a4d",
        }
    )
    figure = plt.figure(figsize=(13.0, 8.25), facecolor="white")
    grid = figure.add_gridspec(
        2,
        2,
        width_ratios=[1.03, 0.97],
        height_ratios=[1.0, 1.0],
        wspace=0.27,
        hspace=0.38,
        left=0.045,
        right=0.98,
        top=0.90,
        bottom=0.08,
    )

    main = figure.add_subplot(grid[0, 0])
    x, y, _ = plot_render(
        main,
        (-2.08, 0.78, -1.24, 1.24),
        1400,
        900,
        850,
        title="A. Classical and finite-combinatorial coverage",
    )
    overlay_main_components(main, x, y)
    annotate_known_points(main)
    add_main_legend(main)
    main.text(
        0.02,
        0.015,
        "Green: interior / hyperbolic geometry.  Blue: selected "
        "postcritically finite and parabolic classes.\n"
        "Lean: escape-radius and finite-orbit theorems; parameter-plane "
        "landing remains a separate contract.",
        transform=main.transAxes,
        fontsize=6.5,
        color="#e4e7ec",
        va="bottom",
        bbox={"facecolor": "#10131a", "alpha": 0.86, "pad": 3},
    )

    yoccoz = figure.add_subplot(grid[0, 1])
    yoccoz.set_xlim(0, 1)
    yoccoz.set_ylim(0, 1)
    yoccoz.set_aspect("equal")
    yoccoz.axis("off")
    yoccoz.set_title(
        "B. Yoccoz: nested parapuzzles and the missing bridge",
        fontsize=10,
        pad=8,
    )
    for left, bottom, width, height, color, label in [
        (0.06, 0.16, 0.45, 0.66, "#62c5ff", r"$\mathcal{P}_n(c)$"),
        (0.16, 0.26, 0.25, 0.46, "#f5c542", r"$\mathcal{P}_{n+1}(c)$"),
        (0.25, 0.35, 0.08, 0.28, "#ff8b7b", r"$\mathcal{P}_{n+2}(c)$"),
    ]:
        yoccoz.add_patch(
            Rectangle(
                (left, bottom),
                width,
                height,
                fill=False,
                edgecolor=color,
                linewidth=2.0,
                linestyle="--",
            )
        )
        yoccoz.text(
            left + width / 2,
            bottom + height + 0.025,
            label,
            color=color,
            fontsize=9,
            ha="center",
        )
    yoccoz.scatter([0.29], [0.49], s=24, color="#62c5ff", zorder=4)
    yoccoz.annotate(
        "",
        xy=(0.88, 0.49),
        xytext=(0.62, 0.49),
        arrowprops={"arrowstyle": "->", "lw": 1.6, "color": "#313a4d"},
    )
    yoccoz.text(
        0.69,
        0.60,
        "modulus divergence",
        fontsize=7.4,
        ha="center",
        color="#313a4d",
    )
    yoccoz.text(
        0.69,
        0.39,
        r"$\bigcap_n\overline{\mathcal{P}_n(c)}=\{c\}$",
        fontsize=8,
        ha="center",
        color="#313a4d",
    )
    yoccoz.text(
        0.02,
        0.02,
        "Proved dynamical endpoint: `yoccoz_puzzle_shrinkage`.\n"
        "Open parameter endpoint: connected shrinking parapuzzles.",
        fontsize=6.7,
        color="#313a4d",
        ha="left",
        va="bottom",
        bbox={"facecolor": "#f5f7fa", "edgecolor": "#9aa4b2", "pad": 3},
    )

    cases = figure.add_subplot(grid[1, 0])
    cases.axis("off")
    cases.text(
        0.0,
        1.08,
        "C. Infinite-renormalization cases with published estimates",
        transform=cases.transAxes,
        fontsize=10,
        ha="left",
        va="bottom",
    )
    case_grid = cases.get_subplotspec().subgridspec(
        1, 2, wspace=0.22
    )
    feigenbaum = figure.add_subplot(case_grid[0])
    plot_render(
        feigenbaum,
        (-1.47, -1.34, -0.115, 0.115),
        900,
        620,
        1400,
        title="Feigenbaum case",
        boundary_color="#f5c542",
    )
    feigenbaum.scatter(
        [FEIGENBAUM.real],
        [FEIGENBAUM.imag],
        s=24,
        color="#f5c542",
        edgecolor="#11151d",
        linewidth=0.5,
        zorder=5,
    )
    feigenbaum.text(
        0.02,
        0.04,
        "Dudko--Lyubich\n`FeigenbaumCertificate`",
        transform=feigenbaum.transAxes,
        fontsize=6.3,
        color="#f7f8fa",
        bbox={"facecolor": "#10131a", "alpha": 0.86, "pad": 2},
    )
    satellite = figure.add_subplot(case_grid[1])
    plot_render(
        satellite,
        (-0.20, 0.02, 0.62, 0.84),
        900,
        620,
        1400,
        title="Bounded satellite / cusp",
        boundary_color="#62c5ff",
    )
    satellite.text(
        0.02,
        0.04,
        "Dudko--Lyubich and KKL\n"
        "`BoundedTypeSatelliteCertificate`",
        transform=satellite.transAxes,
        fontsize=6.3,
        color="#f7f8fa",
        bbox={"facecolor": "#10131a", "alpha": 0.86, "pad": 2},
    )

    frontier = figure.add_subplot(grid[1, 1])
    plot_render(
        frontier,
        (-0.748, -0.739, 0.127, 0.137),
        1100,
        720,
        1900,
        title="D. Neutral / unbounded frontier",
        boundary_color="#ff8b7b",
    )
    frontier.text(
        0.02,
        0.04,
        "Neutral bubble and rigidity papers provide machinery;\n"
        "unbounded combinatorics and the parameter bridge remain open.\n"
        "The frozen full-Green categorical datum is refuted at $(i,16)$.",
        transform=frontier.transAxes,
        fontsize=6.2,
        color="#f7f8fa",
        bbox={"facecolor": "#10131a", "alpha": 0.88, "pad": 2},
    )
    frontier.add_patch(
        Rectangle(
            (0.03, 0.84),
            0.035,
            0.10,
            transform=frontier.transAxes,
            facecolor="none",
            edgecolor="#ff8b7b",
            hatch="///",
            linewidth=0.8,
        )
    )
    frontier.text(
        0.08,
        0.89,
        "hatched = unresolved theorem coverage\n"
        "(schematic; not a certified subset of $M$)",
        transform=frontier.transAxes,
        fontsize=6.2,
        color="#7f1d1d",
        va="center",
        bbox={"facecolor": "white", "edgecolor": "#ff8b7b", "pad": 2},
    )

    figure.suptitle(
        "Figure 1.1. Four coverage layers for the MLC program",
        fontsize=16,
        fontweight="bold",
        color="#182133",
    )
    figure.text(
        0.045,
        0.025,
        "All renders are finite-resolution illustrations.  Each panel names "
        "the theorem family and Lean endpoint; a visual boundary point is "
        "never itself a proof of local connectivity.",
        fontsize=8,
        color="#4e5969",
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    figure.savefig(
        output,
        format="pdf",
        dpi=400,
        metadata={
            "Title": "Mandelbrot components versus the MLC proof frontier",
            "Subject": "Numerical Mandelbrot render with literature coverage",
        },
    )
    plt.close(figure)


if __name__ == "__main__":
    make_figure(parse_args().output)
