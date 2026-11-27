#!/usr/bin/env python3
"""The pre-commit policy of the proof progress and the check of the progress ledger.

    check_progress.py            the hook: a commit that stages Lean sources must improve
                                 at least one progress metric and worsen none; the hook
                                 then records the update in the ledger when the ledger lags
                                 the staged tree, and stages docs/progress
    check_progress.py --ledger   the consistency check that CI runs: the ledger is
                                 well-formed and its last update matches the tree (no Git
                                 history is read)

The title and the note of an update that the hook records come from the environment
variables PROGRESS_TITLE and PROGRESS_NOTE; without a title it is derived from the new
milestones or from the depth of the grid.
"""

from __future__ import annotations

from pathlib import Path
import argparse
import os
import subprocess
import sys

from progress_report import (
    progress_metrics_from_ref,
    staged_progress_metrics,
)


def staged_lean_sources(repo_root: Path) -> list[str]:
    """Staged paths of the Lean proof (``Mlc.lean`` and ``Mlc/**/*.lean``)."""
    proc = subprocess.run(
        ["git", "diff", "--cached", "--name-only", "--no-renames"],
        cwd=repo_root,
        check=True,
        text=True,
        capture_output=True,
    )
    return [
        path
        for path in proc.stdout.splitlines()
        if path.endswith(".lean") and (path.startswith("Mlc/") or path == "Mlc.lean")
    ]


def check_ledger(repo_root: Path) -> int:
    """Fail when the ledger is malformed or lags the working tree."""
    from progress_ledger import check_problems  # numpy is needed to record, not to check

    problems = check_problems(repo_root)
    for problem in problems:
        print(problem, file=sys.stderr)
    if not problems:
        print("The progress ledger matches the tree.")
    return 1 if problems else 0


def record_update(repo_root: Path, staged: dict[str, object]) -> int:
    """Append the update of the staged tree to the ledger when the ledger lags it, and stage
    docs/progress with the new entry, the masks of a grid update included."""
    from progress_ledger import (
        LedgerError,
        derive_title,
        differing_metrics,
        read_ledger,
        record,
    )

    try:
        entries = read_ledger(repo_root)
        if differing_metrics(entries[-1], staged):
            title = os.environ.get("PROGRESS_TITLE", "").strip() or derive_title(
                entries[-1], staged
            )
            entry = record(
                repo_root,
                title,
                os.environ.get("PROGRESS_NOTE", "").strip(),
                staged=True,
                metrics=staged,
            )
            print(f"Progress ledger: recorded update {len(entries)}: {entry['subject']}")
        subprocess.run(["git", "add", "--", "docs/progress"], cwd=repo_root, check=True)
    except LedgerError as exc:
        print(f"Refusing commit: {exc}", file=sys.stderr)
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument(
        "--ledger",
        action="store_true",
        help="only check that the progress ledger matches the tree",
    )
    repo_root = Path(__file__).resolve().parents[1]
    if parser.parse_args().ledger:
        return check_ledger(repo_root)
    if not staged_lean_sources(repo_root):
        print("No staged Lean sources: the progress check applies to proof changes.")
        return 0
    head = progress_metrics_from_ref(repo_root, "HEAD")
    staged = staged_progress_metrics(repo_root)
    head_debt = float(head["debt_percent"])
    staged_debt = float(staged["debt_percent"])
    head_area = float(head["area_upper_percent"])
    staged_area = float(staged["area_upper_percent"])
    head_classes = float(head.get("classes_share", 0.0))
    staged_classes = float(staged.get("classes_share", 0.0))
    print(f"Formalization frontier debt: {head_debt:.3f}% -> {staged_debt:.3f}%")
    print(
        "Certified resolved share: "
        f"{100.0 - head_area:.4f}% -> {100.0 - staged_area:.4f}% "
        f"(unresolved area bound {head_area:.4f}% -> {staged_area:.4f}%)"
    )
    print(f"Classes with a Lean certificate: {head_classes:.3%} -> {staged_classes:.3%}")
    eps = 1e-12
    worse = (
        staged_debt > head_debt + eps
        or staged_area > head_area + eps
        or staged_classes < head_classes - eps
    )
    better = (
        staged_debt < head_debt - eps
        or staged_area < head_area - eps
        or staged_classes > head_classes + eps
    )
    if worse or not better:
        print(
            "Refusing commit: staged Lean changes must improve at least one of "
            "the formalization-debt proxy (lower), the certified resolved share "
            "(higher) and the share of classes with a Lean certificate (higher), "
            "and must worsen none of them.",
            file=sys.stderr,
        )
        return 1
    return record_update(repo_root, staged)


if __name__ == "__main__":
    raise SystemExit(main())
