#!/usr/bin/env python3
"""Reject staged commits that do not improve both progress metrics."""

from __future__ import annotations

from pathlib import Path
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


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
