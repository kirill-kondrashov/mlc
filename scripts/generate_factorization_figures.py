#!/usr/bin/env python3
"""Render separate numerical figures for the factorization theorem example."""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, Ellipse, Patch


C0 = 0.25 + 0.0j
N = 2
L = 20
RADIUS = 0.4
DELTA = 0.2
LOCAL_HALF_WIDTH = 0.48

SLICE_C0 = C0
SLICE_N = N
SLICE_L = L
SLICE_RADIUS = RADIUS
SLICE_DELTA = DELTA
SLICE_HALF_WIDTH = LOCAL_HALF_WIDTH

OUTER_COLOR = "#b7d9e8"
LEVEL_L_COLOR = "#83b4a6"
LEVEL_L_EDGE = "#3d786d"
ANNOTATION_COLOR = "#193b59"
SOURCE_COLOR = "#ed9b40"
TARGET_COLOR = "#477d9e"
TARGET_SLICE_COLOR = "#c9e1eb"
MARKER_COLOR = "#b23a48"


def finite_outer_levels(
    parameters: np.ndarray, requested_levels: tuple[int, ...]
) -> dict[int, np.ndarray]:
    """Sample O_n = K intersected with the first n+1 orbit constraints."""
    requested = set(requested_levels)
    max_level = max(requested)
    orbit = np.zeros(parameters.shape, dtype=np.complex128)
    survives = np.abs(parameters) <= 2.0
    result: dict[int, np.ndarray] = {}

    for level in range(max_level + 1):
        survives &= np.abs(orbit) <= 2.0
        if level in requested:
            result[level] = survives.copy()
        if level < max_level:
            orbit = np.where(survives, orbit * orbit + parameters, 3.0 + 0.0j)

    return result


def draw_mask(
    ax: plt.Axes,
    x: np.ndarray,
    y: np.ndarray,
    mask: np.ndarray,
    color: str,
    *,
    zorder: int = 1,
) -> None:
    cmap = ListedColormap(["white", color])
    ax.imshow(
        mask.astype(np.uint8),
        extent=(float(x[0]), float(x[-1]), float(y[0]), float(y[-1])),
        origin="lower",
        interpolation="nearest",
        cmap=cmap,
        vmin=0,
        vmax=1,
        aspect="equal",
        zorder=zorder,
    )


def style_parameter_axis(
    ax: plt.Axes, bounds: tuple[float, float, float, float]
) -> None:
    x_min, x_max, y_min, y_max = bounds
    ax.set_xlim(x_min, x_max)
    ax.set_ylim(y_min, y_max)
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlabel(r"$\operatorname{Re} c$", fontsize=10)
    ax.set_ylabel(r"$\operatorname{Im} c$", fontsize=10)
    ax.tick_params(labelsize=9, length=3, pad=3)
    ax.set_facecolor("white")


def save_pdf(fig: plt.Figure, output: Path, title: str, subject: str) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(
        output,
        format="pdf",
        dpi=400,
        bbox_inches="tight",
        metadata={"Title": title, "Subject": subject},
    )
    plt.close(fig)


def make_global_figure(
    output_dir: Path,
    global_bounds: tuple[float, float, float, float],
    global_x: np.ndarray,
    global_y: np.ndarray,
    o_n: np.ndarray,
    o_l: np.ndarray,
) -> None:
    fig, ax = plt.subplots(figsize=(6.0, 5.0))
    classes = np.zeros(o_n.shape, dtype=np.uint8)
    classes[o_n] = 1
    classes[o_l] = 2
    ax.imshow(
        classes,
        extent=global_bounds,
        origin="lower",
        interpolation="nearest",
        cmap=ListedColormap(["white", OUTER_COLOR, LEVEL_L_COLOR]),
        vmin=0,
        vmax=2,
        aspect="equal",
    )
    parameters = global_x[None, :] + 1j * global_y[:, None]
    distance = np.abs(parameters - C0)
    target = o_n & (distance <= RADIUS)
    source = o_l & (distance <= DELTA)
    if np.any(source & ~target):
        raise RuntimeError("The sampled nested slice escaped the outer slice.")
    ax.imshow(
        target.astype(np.uint8),
        extent=global_bounds,
        origin="lower",
        interpolation="nearest",
        cmap=ListedColormap(["none", TARGET_COLOR]),
        vmin=0,
        vmax=1,
        aspect="equal",
        alpha=0.36,
        zorder=2,
    )
    ax.imshow(
        source.astype(np.uint8),
        extent=global_bounds,
        origin="lower",
        interpolation="nearest",
        cmap=ListedColormap(["none", SOURCE_COLOR]),
        vmin=0,
        vmax=1,
        aspect="equal",
        alpha=0.4,
        zorder=3,
    )
    ax.contour(
        global_x,
        global_y,
        source.astype(np.uint8),
        levels=[0.5],
        colors=[SOURCE_COLOR],
        linewidths=0.9,
        zorder=4,
    )
    ax.contour(
        global_x,
        global_y,
        o_l.astype(np.uint8),
        levels=[0.5],
        colors=[LEVEL_L_EDGE],
        linewidths=0.75,
        linestyles="--",
        zorder=4,
    )
    ax.add_patch(
        Circle(
            (C0.real, C0.imag),
            RADIUS,
            fill=False,
            edgecolor=MARKER_COLOR,
            linewidth=1.6,
            linestyle="--",
            zorder=4,
        )
    )
    ax.add_patch(
        Circle(
            (C0.real, C0.imag),
            DELTA,
            fill=False,
            edgecolor=SOURCE_COLOR,
            linewidth=1.4,
            linestyle=":",
            zorder=4,
        )
    )
    ax.scatter(
        [C0.real],
        [C0.imag],
        marker="*",
        s=90,
        color=MARKER_COLOR,
        edgecolor="white",
        linewidth=0.6,
        zorder=5,
    )
    ax.text(
        C0.real + 0.62 * RADIUS,
        C0.imag + 0.62 * RADIUS,
        r"$F_2$",
        fontsize=15,
        color=TARGET_COLOR,
        ha="center",
        va="center",
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 1},
        zorder=6,
    )
    ax.text(
        C0.real - 0.62 * DELTA,
        C0.imag + 0.38 * DELTA,
        rf"$X_{{{L}}}$",
        fontsize=15,
        color="#8c4c10",
        ha="center",
        va="center",
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 1},
        zorder=6,
    )
    ax.annotate(
        r"$c_0=\frac{1}{4}$",
        xy=(C0.real, C0.imag),
        xytext=(C0.real + 0.1, C0.imag - 0.12),
        fontsize=9,
        color=MARKER_COLOR,
        arrowprops={"arrowstyle": "-", "color": MARKER_COLOR, "lw": 0.8},
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 1},
        zorder=6,
    )
    style_parameter_axis(ax, global_bounds)
    ax.set_xlabel(r"$\operatorname{Re} c$", fontsize=12)
    ax.set_ylabel(r"$\operatorname{Im} c$", fontsize=12)
    ax.tick_params(labelsize=11, length=3, pad=3)
    ax.set_title(
        rf"Окрестность граничной точки $c_0=\frac{{1}}{{4}}$ ($N={N}$, $L={L}$)",
        fontsize=14,
        pad=9,
    )
    ax.legend(
        handles=[
            Patch(
                facecolor=OUTER_COLOR,
                edgecolor="none",
                label=rf"$O_{{{N}}}\setminus O_{{{L}}}$",
            ),
            Patch(
                facecolor=LEVEL_L_COLOR,
                edgecolor="none",
                label=rf"$O_{{{L}}}$",
            ),
            Line2D(
                [0],
                [0],
                color=LEVEL_L_EDGE,
                linestyle="--",
                linewidth=1.1,
                label=rf"граница выборки $O_{{{L}}}$",
            ),
            Patch(
                facecolor=TARGET_COLOR,
                edgecolor="none",
                label=rf"часть среза $F_{{{N}}}\setminus X_{{{L}}}$",
            ),
            Patch(
                facecolor=SOURCE_COLOR,
                edgecolor="none",
                label=rf"вложенный срез $X_{{{L}}}$",
            ),
        ],
        loc="upper right",
        framealpha=0.96,
        fontsize=10,
        borderpad=0.5,
        handlelength=1.7,
        labelspacing=0.35,
    )
    save_pdf(
        fig,
        output_dir / "factorization-global-levels.pdf",
        "Конечные уровни и локальные окна факторизации",
        "Global parameter-plane context for the finite-level example",
    )


def make_slices_figure(output_dir: Path) -> None:
    local_x = np.linspace(
        SLICE_C0.real - SLICE_HALF_WIDTH,
        SLICE_C0.real + SLICE_HALF_WIDTH,
        1501,
    )
    local_y = np.linspace(
        SLICE_C0.imag - SLICE_HALF_WIDTH,
        SLICE_C0.imag + SLICE_HALF_WIDTH,
        1501,
    )
    parameters = local_x[None, :] + 1j * local_y[:, None]
    levels = finite_outer_levels(parameters, (SLICE_N, SLICE_L))
    distance = np.abs(parameters - SLICE_C0)
    source = levels[SLICE_L] & (distance <= SLICE_DELTA)
    target = levels[SLICE_N] & (distance <= SLICE_RADIUS)
    if np.any(source & ~target):
        raise RuntimeError("The sampled nested slice escaped the outer slice.")

    bounds = (
        float(local_x[0]),
        float(local_x[-1]),
        float(local_y[0]),
        float(local_y[-1]),
    )
    fig, ax = plt.subplots(figsize=(6.0, 5.5))
    draw_mask(ax, local_x, local_y, target, OUTER_COLOR)
    ax.imshow(
        source.astype(np.uint8),
        extent=bounds,
        origin="lower",
        interpolation="nearest",
        cmap=ListedColormap(["none", SOURCE_COLOR]),
        vmin=0,
        vmax=1,
        aspect="equal",
        zorder=2,
    )
    ax.add_patch(
        Circle(
            (SLICE_C0.real, SLICE_C0.imag),
            SLICE_RADIUS,
            fill=False,
            edgecolor=MARKER_COLOR,
            linewidth=1.35,
            linestyle="--",
            zorder=3,
        )
    )
    ax.add_patch(
        Circle(
            (SLICE_C0.real, SLICE_C0.imag),
            SLICE_DELTA,
            fill=False,
            edgecolor="#6b4c2a",
            linewidth=1.1,
            linestyle=":",
            zorder=3,
        )
    )
    ax.scatter(
        [SLICE_C0.real],
        [SLICE_C0.imag],
        marker="*",
        s=105,
        color=MARKER_COLOR,
        edgecolor="white",
        linewidth=0.7,
        zorder=5,
    )
    style_parameter_axis(ax, bounds)
    ax.set_xlabel(r"$\operatorname{Re} c$", fontsize=13)
    ax.set_ylabel(r"$\operatorname{Im} c$", fontsize=13)
    ax.tick_params(labelsize=12, length=3, pad=3)
    ax.set_xticks(np.linspace(local_x[0], local_x[-1], 5))
    ax.set_yticks(np.linspace(local_y[0], local_y[-1], 5))
    ax.set_title(
        rf"Срезы $X_{{{SLICE_L}}}\subset F_{{{SLICE_N}}}$ при $c_0=\frac{{1}}{{4}}$",
        fontsize=16,
        pad=9,
    )
    ax.legend(
        handles=[
            Patch(
                facecolor=OUTER_COLOR,
                edgecolor="none",
                label=rf"$F_{{{SLICE_N}}}\setminus X_{{{SLICE_L}}}$",
            ),
            Patch(
                facecolor=SOURCE_COLOR,
                edgecolor="none",
                label=rf"вложенный срез $X_{{{SLICE_L}}}$",
            ),
            Line2D(
                [0],
                [0],
                color=MARKER_COLOR,
                linestyle="--",
                linewidth=1.35,
                label=rf"$\partial\overline{{B}}(c_0,r)$, $r={SLICE_RADIUS:g}$",
            ),
            Line2D(
                [0],
                [0],
                color="#6b4c2a",
                linestyle=":",
                linewidth=1.1,
                label=rf"$\partial\overline{{B}}(c_0,\delta)$, $\delta={SLICE_DELTA:g}$",
            ),
        ],
        loc="lower left",
        framealpha=0.96,
        fontsize=12,
        borderpad=0.5,
        labelspacing=0.4,
    )
    save_pdf(
        fig,
        output_dir / "factorization-slices.pdf",
        "Локальные срезы у граничной точки c0=1/4",
        "Grid samples of nested parameter slices near the main cardioid cusp",
    )


def make_orbit_figure(output_dir: Path) -> None:
    orbit = [0.0]
    for _ in range(18):
        orbit.append(orbit[-1] ** 2 + C0.real)
    steps = np.arange(len(orbit))
    fig, ax = plt.subplots(figsize=(6.2, 3.8))
    ax.axhspan(0, 0.5, facecolor="#f4f6f8", zorder=0)
    ax.axhline(
        0.5,
        color=MARKER_COLOR,
        linewidth=1.0,
        linestyle="--",
        label=r"параболическая неподвижная точка $\frac{1}{2}$",
        zorder=1,
    )
    ax.plot(
        steps,
        orbit,
        color=TARGET_COLOR,
        linewidth=1.3,
        marker="o",
        markersize=3.5,
        zorder=2,
    )
    ax.scatter(
        [steps[0]],
        [orbit[0]],
        marker="*",
        s=115,
        color=MARKER_COLOR,
        edgecolor="white",
        linewidth=0.7,
        zorder=4,
    )
    ax.annotate(
        r"$p_0=0$",
        xy=(steps[0], orbit[0]),
        xytext=(1.0, 0.06),
        fontsize=11,
        arrowprops={"arrowstyle": "-", "color": MARKER_COLOR, "lw": 0.8},
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.92, "pad": 1.5},
    )
    ax.annotate(
        r"$p_1=\frac{1}{4}$",
        xy=(steps[1], orbit[1]),
        xytext=(2.3, 0.16),
        fontsize=11,
        arrowprops={"arrowstyle": "-", "color": ANNOTATION_COLOR, "lw": 0.8},
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.92, "pad": 1.5},
    )
    ax.text(
        0.98,
        0.96,
        r"$p_{n+1}=p_n^2+\frac{1}{4},\quad 0\leq p_n<\frac{1}{2}<2$",
        transform=ax.transAxes,
        ha="right",
        va="top",
        fontsize=10,
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 1.5},
    )
    ax.set_xlim(-0.5, 18.5)
    ax.set_ylim(-0.02, 0.58)
    ax.set_xticks([0, 4, 8, 12, 16])
    ax.set_xlabel(r"номер итерации $n$", fontsize=10)
    ax.set_ylabel(r"$p_n(c_0)$", fontsize=10)
    ax.tick_params(labelsize=9, length=3, pad=3)
    ax.set_title(
        r"Орбита при граничном параметре $c_0=\frac{1}{4}$",
        fontsize=11,
        pad=9,
    )
    ax.legend(loc="lower right", fontsize=8.5, framealpha=0.95)
    save_pdf(
        fig,
        output_dir / "factorization-critical-orbit.pdf",
        "Критическая орбита при граничном c0=1/4",
        "The critical orbit converges to the parabolic fixed point 1/2",
    )


def make_target_figure(
    output_dir: Path,
    local_x: np.ndarray,
    local_y: np.ndarray,
    source: np.ndarray,
    target: np.ndarray,
    o_l: np.ndarray,
    local_bounds: tuple[float, float, float, float],
) -> None:
    fig, ax = plt.subplots(figsize=(4.8, 4.5))
    draw_mask(ax, local_x, local_y, target, TARGET_SLICE_COLOR)
    ax.imshow(
        source.astype(np.uint8),
        extent=(
            float(local_x[0]),
            float(local_x[-1]),
            float(local_y[0]),
            float(local_y[-1]),
        ),
        origin="lower",
        interpolation="nearest",
        cmap=ListedColormap(["none", SOURCE_COLOR]),
        vmin=0,
        vmax=1,
        aspect="equal",
        alpha=0.55,
        zorder=2,
    )
    ax.contour(
        local_x,
        local_y,
        source.astype(np.uint8),
        levels=[0.5],
        colors=[SOURCE_COLOR],
        linewidths=1.4,
        zorder=4,
    )
    parameters = local_x[None, :] + 1j * local_y[:, None]
    o_l_boundary = np.ma.masked_where(
        np.abs(parameters - C0) > RADIUS, o_l.astype(float)
    )
    ax.contour(
        local_x,
        local_y,
        o_l_boundary,
        levels=[0.5],
        colors=[LEVEL_L_EDGE],
        linewidths=0.9,
        linestyles="dashdot",
        zorder=5,
    )
    ax.add_patch(
        Circle(
            (C0.real, C0.imag),
            RADIUS,
            fill=False,
            edgecolor=MARKER_COLOR,
            linewidth=1.2,
            linestyle="--",
            zorder=3,
        )
    )
    ax.add_patch(
        Circle(
            (C0.real, C0.imag),
            DELTA,
            fill=False,
            edgecolor=SOURCE_COLOR,
            linewidth=1.0,
            linestyle=":",
            zorder=3,
        )
    )
    ax.scatter(
        [C0.real],
        [C0.imag],
        marker="*",
        s=90,
        color=MARKER_COLOR,
        edgecolor="white",
        linewidth=0.6,
        zorder=5,
    )
    ax.annotate(
        rf"$C_{{{N}}}(c_0,r)=F_{{{N}}}=\overline{{B}}(c_0,r)$",
        xy=(C0.real + 0.24, C0.imag + 0.16),
        xytext=(C0.real - 0.08, C0.imag + 0.4),
        fontsize=11,
        color=ANNOTATION_COLOR,
        arrowprops={"arrowstyle": "->", "color": ANNOTATION_COLOR, "lw": 1.0},
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 1.5},
    )
    ax.annotate(
        rf"$A\subset X_{{{L}}}$",
        xy=(C0.real - 0.06, C0.imag + 0.03),
        xytext=(C0.real - 0.25, C0.imag - 0.18),
        fontsize=9.5,
        color="#8c4c10",
        arrowprops={"arrowstyle": "->", "color": SOURCE_COLOR, "lw": 0.9},
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 1.5},
    )
    ax.text(
        C0.real + 0.015,
        C0.imag + 0.012,
        r"$c_0$",
        fontsize=9,
        color=MARKER_COLOR,
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 0.5},
        zorder=6,
    )
    style_parameter_axis(ax, local_bounds)
    ax.set_xlabel(r"$\operatorname{Re} c$", fontsize=12)
    ax.set_ylabel(r"$\operatorname{Im} c$", fontsize=12)
    ax.tick_params(labelsize=11, length=3, pad=3)
    ax.set_xticks(np.linspace(local_bounds[0], local_bounds[1], 5))
    ax.set_yticks(np.linspace(local_bounds[2], local_bounds[3], 5))
    ax.set_title(
        rf"Внешний срез $F_{{{N}}}$ у точки $c_0=\frac{{1}}{{4}}$",
        fontsize=13,
        pad=8,
    )
    save_pdf(
        fig,
        output_dir / "factorization-target.pdf",
        "Срезы около граничной точки c0=1/4",
        "The finite local slices near the cusp parameter 1/4",
    )


def make_component_geometry_figure(output_dir: Path) -> None:
    fig, axes = plt.subplots(
        1, 2, figsize=(8.0, 3.2), gridspec_kw={"wspace": 0.08}
    )
    target_fill = "#e7f1f6"
    neutral_fill = "#f1f3f5"
    shallow_components = (
        ((1.97, 2.85), r"$A_0$", 1.1, 0.72),
        ((4.05, 3.7), r"$A_1$", 1.15, 0.72),
        ((8.25, 2.95), r"$B$", 1.0, 0.72),
    )

    def add_region(
        ax: plt.Axes,
        center: tuple[float, float],
        width: float,
        height: float,
        facecolor: str,
        edgecolor: str,
        *,
        linewidth: float = 1.2,
        linestyle: str = "-",
        alpha: float = 1.0,
        zorder: int = 1,
    ) -> None:
        ax.add_patch(
            Ellipse(
                center,
                width,
                height,
                facecolor=facecolor,
                edgecolor=edgecolor,
                linewidth=linewidth,
                linestyle=linestyle,
                alpha=alpha,
                zorder=zorder,
            )
        )

    def add_component(
        ax: plt.Axes,
        center: tuple[float, float],
        label: str,
        width: float,
        height: float,
        *,
        facecolor: str = SOURCE_COLOR,
        linestyle: str = "-",
        alpha: float = 1.0,
        textcolor: str = "#704111",
    ) -> None:
        add_region(
            ax,
            center,
            width,
            height,
            facecolor,
            "#8c4c10",
            linewidth=1.0,
            linestyle=linestyle,
            alpha=alpha,
            zorder=3,
        )
        if label:
            ax.text(
                *center,
                label,
                fontsize=9,
                color=textcolor,
                ha="center",
                va="center",
                zorder=5,
            )

    def draw_outer_components(ax: plt.Axes, *, emphasize: bool) -> None:
        ax.text(
            3.95,
            4.52,
            r"$C_N(c,r)$",
            fontsize=10.5,
            color="#285b78" if emphasize else TARGET_COLOR,
            ha="center",
            bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 1},
            zorder=4,
        )
        ax.text(
            8.25,
            3.82,
            r"$D$",
            fontsize=9.5,
            color="#59636d",
            ha="center",
            bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 0.8},
            zorder=4,
        )

    def draw_base(ax: plt.Axes, *, emphasize: bool) -> None:
        add_region(
            ax,
            (3.95, 2.95),
            5.2,
            4.1,
            "#d7e9f2" if emphasize else target_fill,
            "#285b78" if emphasize else TARGET_COLOR,
            linewidth=2.0 if emphasize else 1.35,
            zorder=1,
        )
        add_region(
            ax,
            (8.25, 2.95),
            1.7,
            1.4,
            neutral_fill,
            "#89939b",
            linewidth=1.0,
            zorder=1,
        )
        draw_outer_components(ax, emphasize=emphasize)

    def mark_c(ax: plt.Axes) -> None:
        ax.scatter(
            [1.62],
            [2.85],
            marker="*",
            s=55,
            color=MARKER_COLOR,
            edgecolor="white",
            linewidth=0.45,
            zorder=6,
        )
        ax.text(
            1.62,
            3.08,
            r"$c$",
            fontsize=8.5,
            color=MARKER_COLOR,
            ha="center",
            bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 0.5},
            zorder=4,
        )

    for ax in axes:
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 6)
        ax.set_aspect("equal", adjustable="box")
        ax.axis("off")

    left = axes[0]
    left.text(
        5, 5.68, r"а) Промежуточная глубина $\ell$", fontsize=11.5,
        ha="center",
        va="center",
    )
    left.text(
        5,
        5.28,
        r"$\operatorname{im}\varphi_{\ell,N}=\{C_N,D\}$",
        fontsize=9.2,
        ha="center",
        va="center",
    )
    draw_base(left, emphasize=False)
    for center, label, width, height in shallow_components:
        add_component(left, center, label, width, height)
    mark_c(left)
    left.text(
        3.95,
        1.2,
        r"$X_\ell=A_0\cup A_1\cup B$",
        fontsize=9,
        color="#8c4c10",
        ha="center",
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.88, "pad": 1},
        zorder=4,
    )

    right = axes[1]
    right.text(
        5,
        5.68,
        r"б) Достаточная глубина $L>\ell$",
        fontsize=11.5,
        ha="center",
        va="center",
    )
    right.text(
        5,
        5.28,
        r"$\pi_0(X_L)/{\sim}=\{[A]\}$",
        fontsize=9.2,
        ha="center",
        va="center",
    )
    draw_base(right, emphasize=True)
    for center, label, width, height in shallow_components:
        add_component(
            right,
            center,
            label if label == r"$B$" else "",
            width,
            height,
            facecolor="none",
            linestyle="--",
            alpha=0.65,
            textcolor="#8c4c10",
        )
    for center, label, width, height in shallow_components[:2]:
        add_component(
            right,
            center,
            rf"${label[1:-1]}'$",
            width * 0.68,
            height * 0.68,
        )
    mark_c(right)
    right.text(
        3.95,
        1.2,
        r"$A_0'\sim A_1'$",
        fontsize=9,
        color="#8c4c10",
        ha="center",
        bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.88, "pad": 1},
        zorder=4,
    )

    save_pdf(
        fig,
        output_dir / "factorization-component-geometry.pdf",
        "Геометрическое ограничение на компоненты при увеличении глубины",
        "Shallow and deep slices with component images before and after the theorem bound",
    )


def make_figures(output_dir: Path) -> None:
    matplotlib.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "mathtext.fontset": "dejavusans",
            "pdf.fonttype": 42,
            "axes.unicode_minus": False,
        }
    )
    global_bounds = (-2.4, 0.85, -1.4, 1.4)
    global_x = np.linspace(global_bounds[0], global_bounds[1], 1301)
    global_y = np.linspace(global_bounds[2], global_bounds[3], 1101)
    global_parameters = global_x[None, :] + 1j * global_y[:, None]
    global_levels = finite_outer_levels(global_parameters, (N, L))
    o_n = global_levels[N]
    o_l = global_levels[L]
    if np.any(o_l & ~o_n):
        raise RuntimeError("Finite outer stages lost their nesting.")

    local_x = np.linspace(
        C0.real - LOCAL_HALF_WIDTH, C0.real + LOCAL_HALF_WIDTH, 1601
    )
    local_y = np.linspace(
        C0.imag - LOCAL_HALF_WIDTH, C0.imag + LOCAL_HALF_WIDTH, 1601
    )
    local_parameters = local_x[None, :] + 1j * local_y[:, None]
    local_levels = finite_outer_levels(local_parameters, (N, L))
    distance = np.abs(local_parameters - C0)
    source = local_levels[L] & (distance <= DELTA)
    target = local_levels[N] & (distance <= RADIUS)
    if np.any(source & ~target):
        raise RuntimeError("The sampled nested slice escaped the outer slice.")

    local_bounds = (
        float(local_x[0]),
        float(local_x[-1]),
        float(local_y[0]),
        float(local_y[-1]),
    )
    make_global_figure(
        output_dir, global_bounds, global_x, global_y, o_n, o_l
    )
    make_slices_figure(output_dir)
    make_orbit_figure(output_dir)
    make_target_figure(
        output_dir,
        local_x,
        local_y,
        source,
        target,
        local_levels[L],
        local_bounds,
    )
    make_component_geometry_figure(output_dir)


def main() -> None:
    default_output_dir = (
        Path(__file__).resolve().parents[1] / "docs" / "figures"
    )
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=default_output_dir,
        help="directory in which to write the separate factorization PDF figures",
    )
    args = parser.parse_args()
    make_figures(args.output_dir)
    print(f"Wrote factorization figures to {args.output_dir}")


if __name__ == "__main__":
    main()
