#!/usr/bin/env python3
"""Checks of the history that the progress table replays (squash merges and archive tags)."""

from __future__ import annotations

import os
import subprocess
import tempfile
from pathlib import Path

from progress_report import progress_history

ENV = {
    **os.environ,
    "GIT_AUTHOR_NAME": "t",
    "GIT_AUTHOR_EMAIL": "t@example.org",
    "GIT_COMMITTER_NAME": "t",
    "GIT_COMMITTER_EMAIL": "t@example.org",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_SYSTEM": os.devnull,
}


def git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false", *args],
        cwd=repo,
        env=ENV,
        check=True,
        text=True,
        capture_output=True,
    ).stdout.strip()


def commit(repo: Path, name: str, text: str) -> str:
    (repo / name).write_text(text, encoding="utf-8")
    git(repo, "add", name)
    git(repo, "commit", "-m", f"{name}: {text}")
    return git(repo, "rev-parse", "HEAD")


def squash(repo: Path, branch: str) -> str:
    git(repo, "merge", "--squash", branch)
    git(repo, "commit", "-m", f"squash of {branch}")
    return git(repo, "rev-parse", "HEAD")


def new_repo(tmp: str) -> Path:
    repo = Path(tmp)
    git(repo, "init", "-b", "main")
    return repo


def test_squash_without_tag_is_one_commit() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        repo = new_repo(tmp)
        base = commit(repo, "a", "1")
        git(repo, "checkout", "-b", "feature")
        commit(repo, "b", "1")
        commit(repo, "b", "2")
        git(repo, "checkout", "main")
        merged = squash(repo, "feature")
        assert progress_history(repo) == [base, merged]


def test_archive_tag_restores_the_squashed_commits() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        repo = new_repo(tmp)
        base = commit(repo, "a", "1")
        git(repo, "checkout", "-b", "feature")
        steps = [commit(repo, "b", "1"), commit(repo, "b", "2"), commit(repo, "c", "1")]
        git(repo, "checkout", "main")
        squash(repo, "feature")
        after = commit(repo, "d", "1")
        git(repo, "tag", "-a", "progress-archive/1", "feature", "-m", "archive")
        git(repo, "branch", "-D", "feature")
        assert progress_history(repo) == [base, *steps, after]


def test_two_squashed_branches() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        repo = new_repo(tmp)
        base = commit(repo, "a", "1")
        git(repo, "checkout", "-b", "one")
        first = [commit(repo, "b", "1"), commit(repo, "b", "2")]
        git(repo, "checkout", "main")
        squash(repo, "one")
        git(repo, "tag", "progress-archive/1", "one")
        git(repo, "checkout", "-b", "two")
        second = [commit(repo, "c", "1"), commit(repo, "c", "2")]
        git(repo, "checkout", "main")
        squash(repo, "two")
        git(repo, "tag", "progress-archive/2", "two")
        last = commit(repo, "d", "1")
        assert progress_history(repo) == [base, *first, *second, last]


def test_fast_forward_ignores_the_tag() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        repo = new_repo(tmp)
        base = commit(repo, "a", "1")
        git(repo, "checkout", "-b", "feature")
        steps = [commit(repo, "b", "1"), commit(repo, "b", "2")]
        git(repo, "tag", "progress-archive/1", "feature")
        git(repo, "checkout", "main")
        git(repo, "merge", "--ff-only", "feature")
        assert progress_history(repo) == [base, *steps]


def test_moved_base_keeps_the_squash_commit() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        repo = new_repo(tmp)
        base = commit(repo, "a", "1")
        git(repo, "checkout", "-b", "feature")
        commit(repo, "b", "1")
        git(repo, "tag", "progress-archive/1", "feature")
        git(repo, "checkout", "main")
        moved = commit(repo, "m", "1")
        merged = squash(repo, "feature")
        assert progress_history(repo) == [base, moved, merged]


if __name__ == "__main__":
    for name, function in sorted(globals().items()):
        if name.startswith("test_"):
            function()
            print(f"ok {name}")
