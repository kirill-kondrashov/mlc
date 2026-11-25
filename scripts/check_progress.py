#!/usr/bin/env python3
"""Reject staged commits that do not reduce the formalization-debt proxy."""

from __future__ import annotations

from pathlib import Path
import sys

from generate_dependency_graph_site import (
    progress_metrics_from_ref,
    staged_progress_metrics,
)


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
    head = progress_metrics_from_ref(repo_root, "HEAD")
    staged = staged_progress_metrics(repo_root)
    head_debt = float(head["debt_percent"])
    staged_debt = float(staged["debt_percent"])
    head_area = float(head["area_upper_percent"])
    staged_area = float(staged["area_upper_percent"])
    print(f"Formalization frontier debt: {head_debt:.3f}% -> {staged_debt:.3f}%")
    print(f"Certified residual-area envelope: {head_area:.3f}% -> {staged_area:.3f}%")
    if staged_debt >= head_debt or staged_area >= head_area:
        print(
            "Refusing commit: staged Lean changes must strictly decrease both "
            "the formalization-debt proxy and the certified residual-area "
            "envelope.",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
