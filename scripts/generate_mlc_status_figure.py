#!/usr/bin/env python3
"""Render a six-page theorem-coverage atlas for the MLC book."""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.backends.backend_pdf import PdfPages
from matplotlib.colors import LinearSegmentedColormap, Normalize
from matplotlib.lines import Line2D
from matplotlib.patches import Patch, Rectangle
from matplotlib.ticker import MaxNLocator


FEIGENBAUM = -1.401155189092 + 0.0j
PARABOLIC_ROOT = 0.25 + 0.0j
MISUREWICZ = -2.0 + 0.0j


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("docs/figures/mlc_status_render.pdf"),
        help="output multipage PDF path",
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
    ax.set_title(title, fontsize=12, pad=8)
    ax.set_xlabel(r"$\operatorname{Re} c$", fontsize=10)
    ax.set_ylabel(r"$\operatorname{Im} c$", fontsize=10)
    ax.tick_params(labelsize=9, length=2, pad=3)
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
        fontsize=9,
        ha="center",
        va="center",
        bbox={"facecolor": "#15291b", "edgecolor": "#5abf72", "alpha": 0.9},
    )
    ax.text(
        -1.0,
        -0.02,
        "period 2",
        color="#d9ffe1",
        fontsize=9,
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
            fontsize=9,
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
        fontsize=8.5,
        framealpha=0.9,
        facecolor="#10131a",
        edgecolor="#667085",
        labelcolor="white",
    )


def rendered_page(
    title: str,
    bounds: tuple[float, float, float, float],
    width: int,
    height: int,
    max_iter: int,
) -> tuple[plt.Figure, plt.Axes, plt.Axes, np.ndarray, np.ndarray]:
    figure = plt.figure(figsize=(11.5, 6.2), facecolor="white")
    ax = figure.add_axes((0.07, 0.13, 0.56, 0.73))
    x, y, _ = plot_render(
        ax, bounds, width, height, max_iter, title=""
    )
    notes = figure.add_axes((0.69, 0.15, 0.29, 0.70))
    notes.axis("off")
    figure.suptitle(title, fontsize=16, color="#182133", y=0.97)
    figure.text(
        0.07,
        0.025,
        f"Finite-time orbit render: {width} x {height} samples; "
        f"{max_iter} iterates.  Pixel colours do not classify theorem coverage.",
        fontsize=9,
        color="#4e5969",
    )
    return figure, ax, notes, x, y


def note(ax: plt.Axes, y: float, heading: str, body: str) -> None:
    ax.text(
        0, y, heading, fontsize=12, fontweight="bold",
        va="top", color="#182133",
    )
    ax.text(
        0, y - 0.09, body, fontsize=10, linespacing=1.5,
        va="top", color="#313a4d",
    )


def puzzle_diagram(ax: plt.Axes, *, parameter: bool) -> None:
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect("equal")
    ax.axis("off")
    labels = (
        [r"$Q_n(c)$", r"$Q_{n+1}(c)$", r"$Q_{n+2}(c)$"]
        if parameter
        else [r"$P_n(c,0)$", r"$P_{n+1}(c,0)$", r"$P_{n+2}(c,0)$"]
    )
    for (left, bottom, width, height), color, label in zip(
        [(0.04, 0.04, 0.92, 0.90), (0.18, 0.16, 0.64, 0.63),
         (0.35, 0.29, 0.30, 0.34)],
        ["#2878b5", "#bf8b00", "#a64131"],
        labels,
    ):
        ax.add_patch(
            Rectangle((left, bottom), width, height, fill=False,
                      edgecolor=color, linewidth=1.8)
        )
        ax.text(
            left + 0.025, bottom + height - 0.035, label,
            fontsize=12, color=color, va="top",
        )
    ax.scatter([0.50], [0.40], s=22, color="#182133")
    ax.text(0.55, 0.38, r"$c$" if parameter else r"$0$", fontsize=12)


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
    output.parent.mkdir(parents=True, exist_ok=True)
    with PdfPages(
        output,
        metadata={"Title": "MLC theorem-coverage atlas",
                  "Subject": "Separate numerical contexts and proof obligations"},
    ) as pdf:
        figure, ax, notes, x, y = rendered_page(
            "Classical coverage: the global context",
            (-2.08, 0.78, -1.24, 1.24), 1500, 1300, 1000,
        )
        overlay_main_components(ax, x, y)
        annotate_known_points(ax)
        add_main_legend(ax)
        note(notes, 0.98, "Interior and named points",
             "Green contours locate the main\n"
             "cardioid and period-two component.\n"
             "Blue markers locate two classical\n"
             "boundary parameters.")
        note(notes, 0.59, "Source and proof layer",
             "Douady--Hubbard: external geometry.\n"
             "Yoccoz: marked puzzle machinery.\n"
             "Lean: orbit bounds and compact\n"
             "outer stages are proved.")
        note(notes, 0.20, "Boundary coverage",
             "The theorem classes are specified\n"
             "by hypotheses, not filled pixel masks.")
        pdf.savefig(figure, dpi=350)
        plt.close(figure)

        figure = plt.figure(figsize=(11.5, 6.2), facecolor="white")
        figure.suptitle(
            "The Yoccoz route: two planes and a separate analytic bridge",
            fontsize=16, color="#182133", y=0.97,
        )
        dynamical = figure.add_axes((0.07, 0.30, 0.30, 0.53))
        parameter = figure.add_axes((0.63, 0.30, 0.30, 0.53))
        puzzle_diagram(dynamical, parameter=False)
        puzzle_diagram(parameter, parameter=True)
        figure.text(0.22, 0.86, "Dynamical graph-cut pieces",
                    ha="center", fontsize=12)
        figure.text(0.78, 0.86, "Parameter graph-cut pieces",
                    ha="center", fontsize=12)
        figure.text(0.50, 0.67, "phase--parameter\nconstruction",
                    ha="center", fontsize=12, linespacing=1.6)
        figure.text(0.50, 0.52, r"$\Longrightarrow$",
                    ha="center", fontsize=32, color="#bf8b00")
        figure.text(0.50, 0.41, "formalization pending",
                    ha="center", fontsize=11, color="#8c6200")
        figure.text(
            0.22, 0.24,
            "Conformal-modulus divergence\n"
            "is a classical analytic input.",
            ha="center", fontsize=11, linespacing=1.5,
        )
        figure.text(
            0.78, 0.24,
            "Connected intersections with M;\n"
            "compact closures shrink to c.",
            ha="center", fontsize=11, linespacing=1.5,
        )
        figure.text(
            0.50, 0.07,
            r"Kernel-checked endpoint: these parameter hypotheses "
            r"$\Longrightarrow$ MLC at $c$.",
            ha="center", fontsize=12, color="#236638",
        )
        pdf.savefig(figure)
        plt.close(figure)

        figure, ax, notes, _, _ = rendered_page(
            "Bounded satellite results: a limb context, not a coverage mask",
            (-0.20, 0.02, 0.62, 0.84), 1200, 1200, 1600,
        )
        root = -0.125 + 3j * np.sqrt(3) / 8
        ax.scatter([root.real], [root.imag], s=35, color="#62c5ff", zorder=5)
        ax.annotate(
            "1/3 attachment", (root.real, root.imag),
            xytext=(-0.18, 0.632), fontsize=10, color="white",
            arrowprops={"arrowstyle": "-", "color": "#62c5ff"},
            bbox={"facecolor": "#10131a", "alpha": 0.9, "pad": 3},
        )
        note(notes, 0.98, "What the theorem selects",
             "Infinite marked satellite towers\n"
             "with the source's bounded-type\n"
             "and additional hypotheses.\n"
             "A whole limb is not selected.")
        note(notes, 0.59, "Published result",
             "Dudko--Lyubich, arXiv:1808.10425:\n"
             "some bounded-type satellite classes.\n"
             "The attachment marker is classical;\n"
             "it is only a location reference.")
        note(notes, 0.20, "Lean boundary",
             "A generic certificate endpoint exists.\n"
             "The source construction is pending.")
        pdf.savefig(figure, dpi=350)
        plt.close(figure)

        figure, ax, notes, _, _ = rendered_page(
            "Feigenbaum points: bounded combinatorics, including period doubling",
            (-1.47, -1.34, -0.115, 0.115), 1000, 1500, 1800,
        )
        ax.scatter(
            [FEIGENBAUM.real], [FEIGENBAUM.imag],
            s=45, color="#f5c542", edgecolor="#11151d", zorder=5,
        )
        ax.annotate(
            "period-doubling limit", (FEIGENBAUM.real, 0),
            xytext=(-1.46, 0.075), fontsize=10, color="white",
            arrowprops={"arrowstyle": "-", "color": "#f5c542"},
            bbox={"facecolor": "#10131a", "alpha": 0.9, "pad": 3},
        )
        note(notes, 0.98, "The marked example",
             "c is approximately -1.401155189092.\n"
             "Successive relative periods are 2;\n"
             "original return periods are 2^n.\n"
             "Period doubling is satellite.")
        note(notes, 0.59, "Published coverage",
             "Dudko--Lyubich, arXiv:2309.02107:\n"
             "MLC at all infinitely renormalizable\n"
             "parameters of bounded type,\n"
             "including mixed combinatorics.")
        note(notes, 0.20, "Lean boundary",
             "The period product is proved.\n"
             "Analytic beau bounds are pending.")
        pdf.savefig(figure, dpi=350)
        plt.close(figure)

        figure, ax, notes, _, _ = rendered_page(
            "Primitive parabolic tails: the cusp context",
            (0.18, 0.285, -0.0525, 0.0525), 1200, 1200, 1800,
        )
        ax.scatter([0.25], [0], s=35, color="#62c5ff", zorder=5)
        ax.annotate(
            "main cusp", (0.25, 0), xytext=(0.19, 0.036),
            fontsize=10, color="white",
            arrowprops={"arrowstyle": "-", "color": "#62c5ff"},
            bbox={"facecolor": "#10131a", "alpha": 0.9, "pad": 3},
        )
        note(notes, 0.98, "Parabolically bounded",
             "A finite union of individual types\n"
             "and source-defined parabolic tails,\n"
             "restricted to prime primitive types.\n"
             "Nearness to the cusp is insufficient.")
        note(notes, 0.59, "Kahn--Kapiamba--Lyubich",
             "arXiv:2606.27272, Theorems A--C:\n"
             "beau bounds + bounded puzzle\n"
             "Teichmueller diameter -> rigidity\n"
             "and pointwise MLC.")
        note(notes, 0.20, "Lean boundary",
             "The source-class certificate is an\n"
             "interface, not the analytic proof.")
        pdf.savefig(figure, dpi=350)
        plt.close(figure)

        figure, ax, notes, _, _ = rendered_page(
            "The unresolved frontier: a deep numerical context",
            (-0.743646, -0.743640, 0.131822, 0.131828), 1300, 1300, 2600,
        )
        ax.ticklabel_format(axis="both", style="plain", useOffset=False)
        ax.xaxis.set_major_locator(MaxNLocator(4))
        ax.yaxis.set_major_locator(MaxNLocator(4))
        note(notes, 0.98, "Open coverage questions",
             "General unbounded satellite cases;\n"
             "interpolation between regimes;\n"
             "parameter realization from the\n"
             "appropriate neutral estimates.")
        note(notes, 0.59, "What this window means",
             "Its width is 0.000006 in parameter space.\n"
             "The image illustrates fine geometry.\n"
             "No pixel here is certified as outside\n"
             "all known theorem classes.")
        note(notes, 0.20, "No known failure locus",
             "Unresolved coverage means a missing\n"
             "applicable proof, not a failure of MLC.")
        pdf.savefig(figure, dpi=350)
        plt.close(figure)


if __name__ == "__main__":
    make_figure(parse_args().output)
