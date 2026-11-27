#!/usr/bin/env python3
"""Checks of the progress ledger: recording, the lag check, squash merges, masks, numbering
and the pre-commit hook, on temporary Git repositories."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path
from unittest import mock

import numpy as np

import map_raster
import progress_ledger as ledger
import progress_report as report

SCRIPTS = Path(__file__).resolve().parent
ENV = {
    **os.environ,
    "GIT_AUTHOR_NAME": "t",
    "GIT_AUTHOR_EMAIL": "t@example.org",
    "GIT_COMMITTER_NAME": "t",
    "GIT_COMMITTER_EMAIL": "t@example.org",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_SYSTEM": os.devnull,
}

# A tiny Lean library: the root with the two open problems (the baseline), then a milestone.
ROOT = (
    "structure RootInput where\n"
    "  one : Problem43PseudoSiegelAPrioriBoundsData\n"
    "  two : Problem44VirtualMoleculeData\n"
    "theorem mlc_conjecture : True := trivial\n"
)
MILESTONE = "def UnboundedBudget : Nat := 0\n"


def grid_modules(hints: list[int], weight: int) -> tuple[str, str]:
    """A tile module and the aggregator that proves its weight (gridDepth 4, module depth 2).

    The tile ``(0, 0, 1)`` splits once and the four hints are those of its squares of level 2:
    0 is unresolved (weight 16), an odd hint is inside M, an even one outside M. A second tile
    lies inside M.
    """
    tile = (
        "def tiles_0_0 : List (Sq × List ℕ) :=\n"
        f"  [(⟨0, 0, 1⟩, [1, {', '.join(map(str, hints))}]), (⟨1, 0, 1⟩, [3])]\n"
        "theorem tiles_0_0_ok : ∀ p ∈ tiles_0_0, cellsH (2 - p.1.k) = 1 := sorry\n"
    )
    aggregator = (
        f"def gridDepth : ℕ := 4\ndef gridCells : ℕ := {weight}\n"
        "def gridModules : List TileModule := [(2, tiles_0_0)]\n"
        "theorem unresolved_volume_le_grid : True := trivial\n"
    )
    return tile, aggregator


GRID_TWO = grid_modules([0, 2, 0, 3], 32)  # two unresolved cells
GRID_ONE = grid_modules([3, 2, 0, 3], 16)  # one unresolved cell


def git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-c", "commit.gpgsign=false", *args],
        cwd=repo, env=ENV, check=True, text=True, capture_output=True,
    ).stdout.strip()


def write(repo: Path, name: str, text: str) -> None:
    path = repo / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def set_grid(repo: Path, modules: tuple[str, str]) -> None:
    write(repo, "Mlc/GridTiles/G0_0.lean", modules[0])
    write(repo, "Mlc/GridCertified.lean", modules[1])


def commit_all(repo: Path, message: str) -> None:
    git(repo, "add", "-A")
    git(repo, "commit", "-m", message)


def new_repo(tmp: str) -> Path:
    """A repository on `main` with the Lean root and a ledger that holds the baseline."""
    repo = Path(tmp)
    git(repo, "init", "-b", "main")
    write(repo, "Mlc/Root.lean", ROOT)
    metrics = report.progress_metrics_from_worktree(repo)
    baseline = {
        "id": "2026-01-01-baseline",
        "timestamp": "2026-01-01T09:00:00+01:00",
        "subject": "Baseline",
        "area_note": "",
        "baseline": True,
        **{key: metrics[key] for key in ledger.METRIC_KEYS},
    }
    ledger.write_ledger(repo, [baseline])
    commit_all(repo, "baseline")
    return repo


@contextmanager
def small_raster():
    """Masks of 57 x 57 pixels, so that these tests need not draw the full map."""
    with mock.patch.multiple(
        report, MAP_WINDOW=(-2.0, 2.0, -2.0, 2.0), MAP_GRID=(19, 19), MAP_SCALE=3
    ):
        yield


def mask_of(repo: Path, name: str) -> np.ndarray:
    return map_raster.decode_png_gray((repo / report.LAYER_DIR / name).read_bytes())


def test_mask_round_trip() -> None:
    rects = np.array([[0.2, 0.3, 4.6, 5.9], [8.0, 8.0, 12.5, 11.1], [20.0, 1.0, 30.0, 2.5]])
    exact = map_raster.coverage(rects, 32, 16)
    mask = map_raster.mask_from_rects(rects, 32, 16)
    assert mask.dtype == np.uint8 and mask.shape == (16, 32)
    assert np.abs(mask / 255.0 - exact).max() <= 0.5 / 255 + 1e-9
    assert 0 < mask[0, 0] < 255 and mask[2, 2] == 255 and mask[15, 31] == 0
    assert np.array_equal(map_raster.decode_png_gray(map_raster.encode_png_gray(mask)), mask)
    # Painting the masks gives the painting of the rectangles up to the 8-bit quantization.
    layers = [(rects[:2], (1.0, 0.5, 0.0), 0.9), (rects[1:], (0.0, 0.2, 1.0), 0.5)]
    direct = map_raster.composite(layers, 32, 16)
    quantized = map_raster.composite_masks(
        [(map_raster.mask_from_rects(r, 32, 16), rgb, a) for r, rgb, a in layers], 32, 16
    )
    assert np.abs(direct - quantized).max() < 2.0 / 255


def test_numbers_dates_and_dots() -> None:
    with tempfile.TemporaryDirectory() as tmp, small_raster():
        repo = new_repo(tmp)
        write(repo, "Mlc/Root.lean", ROOT + MILESTONE)
        ledger.record(
            repo, "Prove the budget", note="The budget is proved.", when="2026-01-02T10:00:00+01:00"
        )
        set_grid(repo, GRID_TWO)
        ledger.record(
            repo, "Add a grid", note="Depth 2 for Re c < 1.", when="2026-01-02T18:30:00+01:00"
        )
        rows = ledger.ledger_rows(repo)
        assert [row["number"] for row in rows] == [0, 1, 2]
        assert [row["date"] for row in rows] == ["2026-01-01", "2026-01-02", "2026-01-02"]
        assert [report.row_kind(row) for row in rows] == ["baseline", "idle", "drop"]
        assert report.swatch_color(rows[1]) is None
        assert report.swatch_color(rows[2]) == report.GRID_PALETTE[0]
        table = report.commit_table_html(rows)
        assert '<th class="c-no">№</th><th class="c-date">Date</th>' in table
        assert "<code>" not in table and table.count("<tr class=") == 3
        assert table.count('<td class="c-date"><time datetime="2026-01-02T') == 2
        # An update that changes no share shows its note, or a dash without one.
        assert '<td class="c-note">The budget is proved.</td>' in table
        assert report.shown_note(rows[1]) == "The budget is proved."
        legend = report.map_legend_html(rows)
        assert '<b class="no">2</b>' in legend and "depth 2 for" in legend
        tex = report.commits_tex(rows).splitlines()
        assert len(tex) == 3 and "2026-01-02" in tex[2]
        assert tex[2].startswith(r"\textcolor[HTML]{38bdf8}{\rule{1.1ex}{1.1ex}}\,2 &")


def test_recording_a_milestone_and_a_grid() -> None:
    with tempfile.TemporaryDirectory() as tmp, small_raster():
        repo = new_repo(tmp)
        write(repo, "Mlc/Root.lean", ROOT + MILESTONE)
        first = ledger.record(repo, "Prove the budget", note="A note.")
        assert "layer" not in first and first["area_note"] == "A note."
        assert first["milestones"] == ["Conditional root", "Harmonic budget"]
        set_grid(repo, GRID_TWO)
        second = ledger.record(repo, "Add a grid")
        assert second["layer"]["color"] == report.GRID_PALETTE[0]
        names = second["layer"]["masks"]
        assert set(names) == {"interior", "unresolved"}
        interior, unresolved = mask_of(repo, names["interior"]), mask_of(repo, names["unresolved"])
        assert interior.shape == (57, 57) and interior.sum() > 0 and unresolved.sum() > 0
        assert ((interior > 0) & (interior < 255)).any()  # partial pixel coverage survives
        set_grid(repo, GRID_ONE)
        third = ledger.record(repo, "Refine the grid")
        assert third["layer"]["color"] == report.GRID_PALETTE[1]
        entries = ledger.read_ledger(repo)
        # Only the latest grid update keeps the mask of the unresolved cells.
        assert "unresolved" not in entries[2]["layer"]["masks"]
        assert not (repo / report.LAYER_DIR / names["unresolved"]).exists()
        assert (repo / report.LAYER_DIR / names["interior"]).exists()
        assert set(entries[3]["layer"]["masks"]) == {"interior", "unresolved"}
        assert len({entry["id"] for entry in entries}) == 4
        assert ledger.check_problems(repo) == []
        try:
            ledger.record(repo, "Nothing new")
        except ledger.LedgerError as exc:
            assert "nothing to add" in str(exc)
        else:
            raise AssertionError("an update without a change was accepted")


def test_the_check_reports_a_lagging_ledger() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        repo = new_repo(tmp)
        command = [sys.executable, str(SCRIPTS / "progress_ledger.py"), "--repo", str(repo), "check"]
        assert subprocess.run(command, capture_output=True).returncode == 0
        write(repo, "Mlc/Root.lean", ROOT + MILESTONE)
        problems = ledger.check_problems(repo)
        assert len(problems) == 1 and "lags the tree" in problems[0] and "milestones" in problems[0]
        proc = subprocess.run(command, capture_output=True, text=True)
        assert proc.returncode == 1 and "progress_ledger.py add" in proc.stderr
        ledger.record(repo, "Prove the budget")
        assert subprocess.run(command, capture_output=True).returncode == 0


def test_a_malformed_ledger_is_rejected() -> None:
    with tempfile.TemporaryDirectory() as tmp, small_raster():
        repo = new_repo(tmp)
        set_grid(repo, GRID_TWO)
        ledger.record(repo, "Add a grid")
        entries = ledger.read_ledger(repo)
        name = entries[1]["layer"]["masks"]["interior"]
        (repo / report.LAYER_DIR / name).unlink()
        assert any("lacks the mask file" in p for p in ledger.check_problems(repo))
        wrong = map_raster.encode_png_gray(np.zeros((5, 5), np.uint8))
        (repo / report.LAYER_DIR / name).write_bytes(wrong)
        assert any("8-bit grayscale PNG of 57x57" in p for p in ledger.check_problems(repo))
        entries[1]["baseline"] = True
        assert any("first entry is the baseline" in p for p in ledger.structure_problems(repo, entries))
        entries[1]["baseline"] = False
        entries.append(dict(entries[0], baseline=False))
        assert any("repeats an id" in p for p in ledger.structure_problems(repo, entries))
        entries.pop()
        entries[1]["area_note"] = "costs $5"
        assert any("fails to typeset" in p for p in ledger.structure_problems(repo, entries))
        try:
            ledger.record(repo, "A title", note="costs $5")
        except ledger.LedgerError as exc:
            assert "fails to typeset" in str(exc)
        else:
            raise AssertionError("a note with an unbalanced $ was accepted")


def test_titles_and_ids() -> None:
    first = {"milestones": ["Conditional root"], "grid": None, "open_lemmas": 3}
    achieved = dict(first, milestones=["Conditional root", "Harmonic budget"])
    assert ledger.derive_title(first, achieved) == "Milestone: Harmonic budget"
    grid = {"format": "blocks", "depth": 12, "finest": 13, "cells": 5}
    assert ledger.derive_title(first, dict(first, grid=grid)) == (
        "Refine the kernel-checked grid to depth 13"
    )
    assert ledger.derive_title(first, dict(first, open_lemmas=2)) == (
        "Prove 1 open statement of the programme"
    )
    taken = {"2026-03-04-a-title"}
    assert ledger.make_id("2026-03-04T10:00:00+01:00", "A title!", taken) == "2026-03-04-a-title-2"
    assert ledger.make_id("2026-03-04T10:00:00+01:00", "Another", taken) == "2026-03-04-another"


def test_a_squash_merge_keeps_every_update_and_mask() -> None:
    with tempfile.TemporaryDirectory() as tmp, small_raster():
        repo = new_repo(tmp)
        git(repo, "checkout", "-b", "feature")
        write(repo, "Mlc/Root.lean", ROOT + MILESTONE)
        ledger.record(repo, "Prove the budget")
        commit_all(repo, "milestone")
        set_grid(repo, GRID_TWO)
        ledger.record(repo, "Add a grid")
        commit_all(repo, "grid")
        set_grid(repo, GRID_ONE)
        ledger.record(repo, "Refine the grid")
        commit_all(repo, "finer grid")
        before = [row["subject"] for row in ledger.ledger_rows(repo)]
        git(repo, "checkout", "main")
        git(repo, "merge", "--squash", "feature")
        git(repo, "commit", "-m", "squash of feature")
        git(repo, "branch", "-D", "feature")
        assert git(repo, "tag", "--list") == "" and len(git(repo, "log", "--format=%h").split()) == 2
        rows = ledger.ledger_rows(repo)
        assert [row["subject"] for row in rows] == before
        assert before == ["Baseline", "Prove the budget", "Add a grid", "Refine the grid"]
        assert [row["number"] for row in rows] == [0, 1, 2, 3]
        masks = [row["layer"]["masks"] for row in rows if row.get("layer")]
        assert len(masks) == 2
        assert all((repo / report.LAYER_DIR / name).is_file() for m in masks for name in m.values())
        assert ledger.check_problems(repo) == []
        svg = report.parameter_map_svg(repo, rows)
        assert svg.count("<image ") == 1 and "data:image/png;base64," in svg


def hook_repo(tmp: str) -> Path:
    """A repository with the scripts, to run the pre-commit policy in a subprocess."""
    repo = new_repo(tmp)
    shutil.copytree(SCRIPTS, repo / "scripts", ignore=shutil.ignore_patterns("__pycache__", "test_*"))
    commit_all(repo, "scripts")
    return repo


def run_hook(repo: Path, **variables: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "scripts/check_progress.py"],
        cwd=repo, env={**ENV, **variables}, text=True, capture_output=True,
    )


def test_the_hook_records_the_update_of_a_staged_lean_commit() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        repo = hook_repo(tmp)
        # A commit without Lean sources passes unchecked and records nothing.
        write(repo, "notes.txt", "x")
        git(repo, "add", "notes.txt")
        proc = run_hook(repo)
        assert proc.returncode == 0 and "No staged Lean sources" in proc.stdout
        assert len(ledger.read_ledger(repo)) == 1
        # A Lean commit that improves a metric appends its update and stages the ledger.
        write(repo, "Mlc/Root.lean", ROOT + MILESTONE)
        git(repo, "add", "Mlc/Root.lean")
        proc = run_hook(repo, PROGRESS_NOTE="Budget.")
        assert proc.returncode == 0, proc.stderr
        entries = ledger.read_ledger(repo)
        assert [e["subject"] for e in entries] == ["Baseline", "Milestone: Harmonic budget"]
        assert entries[1]["area_note"] == "Budget."
        assert "docs/progress/ledger.json" in git(repo, "diff", "--cached", "--name-only").split()
        # The same tree needs no second update.
        assert run_hook(repo).returncode == 0 and len(ledger.read_ledger(repo)) == 2
        # A commit that worsens a metric is refused, and the ledger stays as it is.
        git(repo, "commit", "-m", "budget")
        write(repo, "Mlc/Root.lean", ROOT)
        git(repo, "add", "Mlc/Root.lean")
        proc = run_hook(repo)
        assert proc.returncode == 1 and "Refusing commit" in proc.stderr
        assert len(ledger.read_ledger(repo)) == 2


def test_the_hook_stages_a_grid_update_with_its_masks() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        repo = hook_repo(tmp)
        set_grid(repo, GRID_TWO)
        git(repo, "add", "Mlc")
        proc = run_hook(repo, PROGRESS_TITLE="Add a grid")
        assert proc.returncode == 0, proc.stderr
        entry = ledger.read_ledger(repo)[1]
        assert entry["subject"] == "Add a grid"
        staged = git(repo, "diff", "--cached", "--name-only").split()
        for name in entry["layer"]["masks"].values():
            assert f"docs/progress/layers/{name}" in staged
        assert mask_of(repo, entry["layer"]["masks"]["interior"]).shape == (2000, 2080)


def test_the_hook_needs_numpy_only_for_a_grid_update() -> None:
    with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as blocker:
        write(Path(blocker), "numpy/__init__.py", "raise ImportError('numpy is blocked')\n")
        repo = hook_repo(tmp)
        write(repo, "Mlc/Root.lean", ROOT + MILESTONE)
        git(repo, "add", "Mlc/Root.lean")
        assert run_hook(repo, PYTHONPATH=blocker).returncode == 0
        git(repo, "commit", "-m", "budget")
        set_grid(repo, GRID_TWO)
        git(repo, "add", "Mlc")
        proc = run_hook(repo, PYTHONPATH=blocker)
        assert proc.returncode == 1 and "pip install -r scripts/requirements.txt" in proc.stderr
        assert len(ledger.read_ledger(repo)) == 2


if __name__ == "__main__":
    for name, function in sorted(globals().items()):
        if name.startswith("test_"):
            function()
            print(f"ok {name}")
