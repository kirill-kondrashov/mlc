#!/usr/bin/env python3
"""The progress ledger: the updates of the proof, stored in the repository tree.

The Progress page and the status report show a numbered table of updates and a map whose
colours mark the parameters that each update certified. Both are rendered from the ledger
alone, so they survive squash merges, rebases and deleted branches: the ledger is part of
the tree and needs no Git history.

    docs/progress/ledger.json        an array of entries, oldest first
    docs/progress/layers/<id>*.png   coverage masks of the certified regions of an entry

An entry is an object with the fields

    id           a stable name; the number of the update is computed when the page is
                 rendered (the baseline is 0, then 1, 2, ...)
    timestamp    date and time of the decision (ISO 8601 with the UTC offset)
    subject      the title of the update
    area_note    a sentence that the table shows for a grid update ("" if none)
    baseline     true for the first entry, the state of the literature
    grid, area_exact, debt_percent, area_upper_percent, area_symbols, open_frontier,
    open_lemmas, classes_share, milestone_weight, milestones
                 the metrics of the tree at the update (``progress_metrics_from_text``)
    layer        optional, for an update that certifies grid cells:
                 {"color": "#rrggbb", "masks": {"interior": file, "unresolved": file}}.
                 A mask is an 8-bit grayscale PNG of MAP_GRID * MAP_SCALE pixels whose
                 sample v stands for the coverage v / 255: "interior" marks the cells that
                 the update certified inside M; "unresolved" marks the cells that the grid
                 leaves open and belongs to the latest grid update only
    source       optional, the short hash of the commit that the entry was migrated from
                 (provenance only, never displayed)

Commands (``python3 scripts/progress_ledger.py --help``):

    add --title T [--note N] [--staged] [--date D]
                 append an update for the metrics of the working tree (or of the staged
                 tree); a grid update also writes its masks, which needs numpy
    check [--staged]
                 exit 1 when the ledger is malformed or lags the tree
    list         print the numbered updates

The pre-commit hook (``scripts/check_progress.py``) appends the update of a staged Lean
commit by itself.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import struct
import subprocess
import sys
from datetime import datetime
from pathlib import Path

import progress_report as report
from progress_report import (
    EPS,
    GRID_PALETTE,
    LAYER_DIR,
    LEDGER_FILE,
    annotate_rows,
    grid_depth,
    progress_metrics_from_ref,
    progress_metrics_from_worktree,
)

METRIC_KEYS = (
    "grid",
    "area_exact",
    "debt_percent",
    "area_upper_percent",
    "area_symbols",
    "open_frontier",
    "open_lemmas",
    "classes_share",
    "milestone_weight",
    "milestones",
)
REQUIRED_KEYS = ("id", "timestamp", "subject", "area_note", "baseline", *METRIC_KEYS)
ID_PATTERN = re.compile(r"[a-z0-9][a-z0-9-]*$")
COLOR_PATTERN = re.compile(r"#[0-9a-f]{6}$")
MASK_ROLES = ("interior", "unresolved")


class LedgerError(RuntimeError):
    """The ledger is malformed, lags the tree, or an update cannot be recorded."""


# ---------------------------------------------------------------------------------------
# Reading and writing


def png_header(path: Path) -> tuple[int, int, int, int] | None:
    """Width, height, bit depth and color type of a PNG file (standard library only), or
    None when the file lacks a PNG header."""
    with path.open("rb") as handle:
        head = handle.read(26)
    if head[:8] != b"\x89PNG\r\n\x1a\n" or head[12:16] != b"IHDR" or len(head) < 26:
        return None
    width, height, depth, color = struct.unpack(">IIBB", head[16:26])
    return width, height, depth, color


def raster_size() -> tuple[int, int]:
    """The size in pixels of a mask: MAP_GRID * MAP_SCALE."""
    return report.MAP_GRID[0] * report.MAP_SCALE, report.MAP_GRID[1] * report.MAP_SCALE


def note_problem(note: str) -> str:
    """Why the note of an entry fails to typeset (formulas go between ``$...$``, in the
    subset of TeX that ``progress_report`` renders), or an empty string."""
    try:
        report.html_rich(note)
        report.tex_rich(note)
    except ValueError as exc:
        return str(exc)
    return ""


def structure_problems(repo_root: Path, entries: object) -> list[str]:
    """What is wrong with the shape of the ledger (not with its freshness)."""
    if not isinstance(entries, list) or not entries:
        return ["the ledger must be a non-empty array of entries"]
    problems: list[str] = []
    seen: set[str] = set()
    referenced: set[str] = set()
    with_unresolved: list[int] = []
    with_layer: list[int] = []
    for index, entry in enumerate(entries):
        where = f"entry {index}"
        if not isinstance(entry, dict):
            problems.append(f"{where} must be an object")
            continue
        missing = [key for key in REQUIRED_KEYS if key not in entry]
        if missing:
            problems.append(f"{where} lacks the fields {', '.join(missing)}")
            continue
        identifier = str(entry["id"])
        where = f"entry {index} ({identifier})"
        if not ID_PATTERN.match(identifier):
            problems.append(f"{where} has an id outside [a-z0-9-]")
        if identifier in seen:
            problems.append(f"{where} repeats an id")
        seen.add(identifier)
        if bool(entry["baseline"]) != (index == 0):
            problems.append(f"{where}: exactly the first entry is the baseline")
        try:
            datetime.fromisoformat(str(entry["timestamp"]))
        except ValueError:
            problems.append(f"{where} has a timestamp that is no ISO 8601 date-time")
        problem = note_problem(str(entry["area_note"]))
        if problem:
            problems.append(f"{where} has a note that fails to typeset: {problem}")
        layer = entry.get("layer")
        if layer is None:
            continue
        with_layer.append(index)
        if not isinstance(entry["grid"], dict):
            problems.append(f"{where} has a layer but no grid")
        if not isinstance(layer, dict) or not COLOR_PATTERN.match(str(layer.get("color", ""))):
            problems.append(f"{where} needs a layer color #rrggbb")
            continue
        masks = layer.get("masks")
        if not isinstance(masks, dict) or "interior" not in masks or set(masks) - set(MASK_ROLES):
            problems.append(f"{where} needs the masks interior and, at most, unresolved")
            continue
        if "unresolved" in masks:
            with_unresolved.append(index)
        for role, name in masks.items():
            name = str(name)
            referenced.add(name)
            path = repo_root / LAYER_DIR / name
            if Path(name).name != name or not name.startswith(identifier) or not name.endswith(".png"):
                problems.append(f"{where} has the mask file {name!r}; expected <id>*.png")
            elif not path.is_file():
                problems.append(f"{where} lacks the mask file {LAYER_DIR / name}")
            elif png_header(path) != (*raster_size(), 8, 0):
                problems.append(
                    f"{LAYER_DIR / name} must be an 8-bit grayscale PNG of "
                    f"{raster_size()[0]}x{raster_size()[1]} pixels"
                )
    if with_unresolved and (len(with_unresolved) > 1 or with_unresolved[0] != with_layer[-1]):
        problems.append("only the latest grid update keeps the mask of the unresolved cells")
    directory = repo_root / LAYER_DIR
    if directory.is_dir():
        stray = sorted(path.name for path in directory.glob("*.png") if path.name not in referenced)
        if stray:
            problems.append(f"{LAYER_DIR} has masks that no entry uses: {', '.join(stray)}")
    return problems


def read_ledger(repo_root: Path) -> list[dict[str, object]]:
    """The validated entries of the ledger, oldest first."""
    path = repo_root / LEDGER_FILE
    if not path.is_file():
        raise LedgerError(
            f"{LEDGER_FILE} is missing: the progress ledger is part of the repository tree"
        )
    try:
        entries = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise LedgerError(f"{LEDGER_FILE} is no valid JSON: {exc}") from exc
    problems = structure_problems(repo_root, entries)
    if problems:
        raise LedgerError(f"{LEDGER_FILE} is malformed:\n  " + "\n  ".join(problems))
    return entries


def write_ledger(repo_root: Path, entries: list[dict[str, object]]) -> None:
    path = repo_root / LEDGER_FILE
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(entries, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def ledger_rows(repo_root: Path) -> list[dict[str, object]]:
    """The rows of the progress table: the entries with their number, date, change of the
    share, area steps and note."""
    rows = [dict(entry) for entry in read_ledger(repo_root)]
    annotate_rows(rows)
    return rows


# ---------------------------------------------------------------------------------------
# Freshness


def _same(a: object, b: object) -> bool:
    if isinstance(a, dict) and isinstance(b, dict):
        return a.keys() == b.keys() and all(_same(a[key], b[key]) for key in a)
    if isinstance(a, (list, tuple)) and isinstance(b, (list, tuple)):
        return len(a) == len(b) and all(_same(x, y) for x, y in zip(a, b))
    numbers = (int, float)
    if isinstance(a, numbers) and isinstance(b, numbers) and not isinstance(a, bool):
        return abs(a - b) <= EPS
    return a == b


def differing_metrics(entry: dict[str, object], metrics: dict[str, object]) -> list[str]:
    """The metrics of the tree that the entry does not record."""
    return [key for key in METRIC_KEYS if not _same(entry.get(key), metrics.get(key))]


def check_problems(
    repo_root: Path, metrics: dict[str, object] | None = None
) -> list[str]:
    """Why the ledger fails to describe the tree (the working tree unless ``metrics`` of
    another tree are given); an empty list when it describes it."""
    try:
        entries = read_ledger(repo_root)
    except LedgerError as exc:
        return [str(exc)]
    if metrics is None:
        metrics = progress_metrics_from_worktree(repo_root)
    differing = differing_metrics(entries[-1], metrics)
    if not differing:
        return []
    last = entries[-1]
    return [
        f"the progress ledger lags the tree: its last update (number {len(entries) - 1}, "
        f"{last['subject']!r}) differs from the tree in {', '.join(differing)}. Record the "
        'update with `python3 scripts/progress_ledger.py add --title "..."`; the commit '
        "hook does it for staged Lean changes."
    ]


# ---------------------------------------------------------------------------------------
# Replay of the tiles of the grid: the masks of a grid update

TILE_ENTRY = re.compile(r"\(⟨(-?\d+), (-?\d+), (\d+)⟩,\s*\[([^\]]*)\]\)")
MODULE_DEPTH = re.compile(r"cellsH \((\d+) - p\.1\.k\)")


def _module_order(name: str) -> tuple[int, ...]:
    """Order of the tile modules: ``G<block>_<part>`` by block and part, the earlier
    ``Part<index>`` by index."""
    return tuple(int(v) for v in re.findall(r"\d+", Path(name).stem))


def tile_texts(repo_root: Path, ref: str = "worktree") -> list[str]:
    """The tile modules of the working tree (``"worktree"``) or of a tree-ish, in order."""
    if ref == "worktree":
        paths = sorted(
            (repo_root / "Mlc" / "GridTiles").glob("*.lean"),
            key=lambda path: _module_order(path.name),
        )
        return [path.read_text(encoding="utf-8") for path in paths]
    listing = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref, "--", "Mlc/GridTiles"],
        cwd=repo_root, check=True, text=True, capture_output=True,
    ).stdout
    names = sorted(listing.splitlines(), key=_module_order)
    answer = subprocess.run(
        ["git", "cat-file", "--batch"],
        cwd=repo_root, check=True, capture_output=True,
        input="".join(f"{ref}:{name}\n" for name in names).encode(),
    ).stdout
    texts, position = [], 0
    for _ in names:
        end = answer.index(b"\n", position)
        size = int(answer[position:end].split()[2])
        texts.append(answer[end + 1 : end + 1 + size].decode("utf-8"))
        position = end + 2 + size
    return texts


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


def raster_module():
    """``map_raster`` (it needs numpy), with the instruction to install numpy when missing."""
    try:
        import map_raster
    except ImportError as exc:
        raise LedgerError(
            "numpy is needed to record a change of the grid, because its layer is stored as "
            "coverage masks: run `pip install -r scripts/requirements.txt`, then repeat"
        ) from exc
    return map_raster


def grid_masks(
    repo_root: Path, grid: dict[str, object], ref: str = "worktree"
) -> dict[str, object]:
    """The coverage masks ``{"interior": ..., "unresolved": ...}`` of the tiles of ``ref``."""
    raster = raster_module()
    if grid.get("format") not in ("hints", "blocks"):
        raise LedgerError(
            f"the layer of a grid of the format {grid.get('format')!r} cannot be replayed"
        )
    inside, unresolved, found = hint_squares(
        tile_texts(repo_root, ref), int(grid["depth"]), int(grid["scale"])
    )
    if found != int(grid["weight"]):
        raise LedgerError(
            f"the tile modules leave {found} unresolved cells, but the grid bound proves "
            f"{grid['weight']}: stage or commit all tile modules first"
        )
    width, height = raster_size()
    return {
        region["role"]: raster.mask_from_rects(
            raster.rect_pixels(region["rects"], report.MAP_WINDOW, report.MAP_GRID, report.MAP_SCALE),
            width,
            height,
        )
        for region in squares_to_regions(inside, unresolved)
    }


# ---------------------------------------------------------------------------------------
# Recording


def slug(text: str, limit: int = 48) -> str:
    words = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    if len(words) > limit:
        cut = words[:limit]
        words = cut.rsplit("-", 1)[0] if "-" in cut and words[limit] != "-" else cut
    return words.strip("-")


def make_id(stamp: str, title: str, taken: set[str]) -> str:
    """A readable id from the date and the title; a numeric suffix keeps it unique."""
    base = f"{stamp[:10]}-{slug(title) or 'update'}"
    identifier, counter = base, 1
    while identifier in taken:
        counter += 1
        identifier = f"{base}-{counter}"
    return identifier


def now_stamp() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def parse_when(text: str) -> str:
    """``YYYY-MM-DD`` or an ISO 8601 date-time, as a time stamp with the UTC offset."""
    try:
        moment = datetime.fromisoformat(text)
    except ValueError as exc:
        raise LedgerError(f"{text!r} is no ISO 8601 date (YYYY-MM-DD) or date-time") from exc
    if moment.tzinfo is None:
        moment = moment.astimezone()  # the local time zone
    return moment.isoformat(timespec="seconds")


def derive_title(previous: dict[str, object], metrics: dict[str, object]) -> str:
    """A title for an update that nobody named: from its new milestones, else from the grid."""
    achieved = [name for name in metrics["milestones"] if name not in previous["milestones"]]
    if achieved:
        return "Milestone: " + "; ".join(achieved)
    grid = metrics.get("grid")
    if grid is not None and not _same(grid, previous.get("grid")):
        return f"Refine the kernel-checked grid to depth {grid_depth(grid)}"
    closed = int(previous["open_lemmas"]) - int(metrics["open_lemmas"])
    if closed > 0:
        return f"Prove {closed} open statement{'s' if closed != 1 else ''} of the programme"
    return "Update the progress metrics"


def write_tree(repo_root: Path) -> str:
    proc = subprocess.run(
        ["git", "write-tree"], cwd=repo_root, check=False, text=True, capture_output=True
    )
    if proc.returncode != 0:
        raise LedgerError("cannot inspect the staged tree: " + proc.stderr.strip())
    return proc.stdout.strip()


def record(
    repo_root: Path,
    title: str,
    note: str = "",
    staged: bool = False,
    when: str | None = None,
    metrics: dict[str, object] | None = None,
) -> dict[str, object]:
    """Append the update for the metrics of the working tree (or of the staged tree) and write
    the ledger and, for an update that certifies grid cells, its masks."""
    problem = note_problem(note)
    if problem:
        raise LedgerError(f"the note fails to typeset: {problem}")
    entries = read_ledger(repo_root)
    ref = write_tree(repo_root) if staged else "worktree"
    if metrics is None:
        metrics = (
            progress_metrics_from_ref(repo_root, ref)
            if staged
            else progress_metrics_from_worktree(repo_root)
        )
    previous = entries[-1]
    if not differing_metrics(previous, metrics):
        raise LedgerError("the last update already records this tree; there is nothing to add")
    stamp = parse_when(when) if when else now_stamp()
    identifier = make_id(stamp, title, {str(entry["id"]) for entry in entries})
    entry: dict[str, object] = {
        "id": identifier,
        "timestamp": stamp,
        "subject": title,
        "area_note": note,
        "baseline": False,
        **{key: metrics[key] for key in METRIC_KEYS},
    }
    grid = metrics.get("grid")
    gained = float(previous["area_upper_percent"]) - float(metrics["area_upper_percent"])
    written: list[Path] = []
    superseded: Path | None = None
    if grid is not None and gained > EPS:
        masks = grid_masks(repo_root, grid, ref)
        raster = raster_module()
        directory = repo_root / LAYER_DIR
        directory.mkdir(parents=True, exist_ok=True)
        files = {"interior": f"{identifier}.png", "unresolved": f"{identifier}.open.png"}
        for role, name in files.items():
            written.append(directory / name)
            written[-1].write_bytes(raster.encode_png_gray(masks[role]))
        colors = sum(1 for other in entries if other.get("layer") is not None)
        entry["layer"] = {"color": GRID_PALETTE[colors % len(GRID_PALETTE)], "masks": files}
        for other in reversed(entries):
            held = (other.get("layer") or {}).get("masks", {})
            if "unresolved" in held:
                superseded = directory / held.pop("unresolved")
                break
    try:
        write_ledger(repo_root, [*entries, entry])
    except BaseException:
        for path in written:
            path.unlink(missing_ok=True)
        raise
    if superseded is not None:
        superseded.unlink(missing_ok=True)
    return entry


# ---------------------------------------------------------------------------------------
# Command line


def command_add(args: argparse.Namespace) -> int:
    entry = record(args.repo, args.title, args.note, staged=args.staged, when=args.date)
    count = len(read_ledger(args.repo)) - 1
    layer = entry.get("layer")
    print(f"Recorded update {count}: {entry['subject']} ({entry['id']})")
    if layer is not None:
        print(f"  layer {layer['color']}: " + ", ".join(sorted(layer["masks"].values())))
    return 0


def command_check(args: argparse.Namespace) -> int:
    metrics = None
    if args.staged:
        metrics = progress_metrics_from_ref(args.repo, write_tree(args.repo))
    problems = check_problems(args.repo, metrics)
    for problem in problems:
        print(problem, file=sys.stderr)
    if not problems:
        print("The progress ledger matches the tree.")
    return 1 if problems else 0


def command_list(args: argparse.Namespace) -> int:
    for row in ledger_rows(args.repo):
        share = report.share_label(row)[0]
        print(f"{row['number']:>3}  {row['date']}  {share:>9}  {row['subject']}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="The progress ledger.")
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="the repository root (default: the repository of this script)",
    )
    commands = parser.add_subparsers(dest="command", required=True)
    add = commands.add_parser("add", help="record an update")
    add.add_argument("--title", required=True, help="the title of the update")
    add.add_argument("--note", default="", help="a sentence for the column 'What it resolved'")
    add.add_argument("--staged", action="store_true", help="read the staged tree")
    add.add_argument("--date", help="decision date (YYYY-MM-DD or ISO 8601); default: now")
    add.set_defaults(run=command_add)
    check = commands.add_parser("check", help="fail when the ledger lags the tree")
    check.add_argument("--staged", action="store_true", help="compare with the staged tree")
    check.set_defaults(run=command_check)
    commands.add_parser("list", help="list the updates").set_defaults(run=command_list)
    args = parser.parse_args(argv)
    try:
        return args.run(args)
    except LedgerError as exc:
        print(f"progress ledger: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
