"""Tests of scripts/ci_grid.py: shards, the key, archives and the seed in a git ref.

The Lake-dependent parts (`check`, `build-shard`) need a Lean workspace and are exercised by CI.
"""

from __future__ import annotations

import os
import random
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import ci_grid  # noqa: E402


def make_repo(root: Path, tiles: dict[str, str]) -> None:
    """A miniature working tree: tile modules, GridDefs and the files of the key."""
    (root / "Mlc" / "GridTiles").mkdir(parents=True)
    for name, text in tiles.items():
        (root / "Mlc" / "GridTiles" / f"{name}.lean").write_text(text, encoding="utf-8")
    (root / "Mlc" / "GridDefs.lean").write_text("defs", encoding="utf-8")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.28.0\n", encoding="utf-8")
    (root / "lake-manifest.json").write_text("{}", encoding="utf-8")


def git(cwd: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=cwd, check=True, text=True, capture_output=True
    ).stdout.strip()


class Shards(unittest.TestCase):
    NAMES = [f"G{block}_{part}" for block in range(12) for part in range(40)]

    def setUp(self) -> None:
        self.dir = tempfile.TemporaryDirectory()
        self.root = Path(self.dir.name)
        make_repo(self.root, {name: name for name in self.NAMES})

    def tearDown(self) -> None:
        self.dir.cleanup()

    def test_order_is_numeric(self) -> None:
        modules = ci_grid.tile_modules(self.root)
        self.assertEqual(modules[0], "Mlc.GridTiles.G0_0")
        self.assertLess(modules.index("Mlc.GridTiles.G0_9"), modules.index("Mlc.GridTiles.G0_10"))
        self.assertLess(modules.index("Mlc.GridTiles.G2_39"), modules.index("Mlc.GridTiles.G10_0"))

    def test_shards_partition_the_tiles(self) -> None:
        pieces = [ci_grid.shard_modules(i, 7, self.root) for i in range(7)]
        flat = [m for piece in pieces for m in piece]
        self.assertEqual(sorted(flat), sorted(ci_grid.tile_modules(self.root)))
        self.assertEqual(len(flat), len(set(flat)))
        self.assertTrue(all(pieces))

    def test_a_new_tile_moves_no_other_tile(self) -> None:
        before = {m: ci_grid.shard_of(m, 20) for m in ci_grid.tile_modules(self.root)}
        (self.root / "Mlc" / "GridTiles" / "G99_0.lean").write_text("new", encoding="utf-8")
        after = {m: ci_grid.shard_of(m, 20) for m in ci_grid.tile_modules(self.root)}
        self.assertEqual({m: s for m, s in after.items() if m in before}, before)

    def test_key_follows_the_inputs(self) -> None:
        key = ci_grid.grid_key(self.root)
        self.assertEqual(key, ci_grid.grid_key(self.root))
        tile = self.root / "Mlc" / "GridTiles" / "G3_3.lean"
        tile.write_text("changed", encoding="utf-8")
        self.assertNotEqual(key, ci_grid.grid_key(self.root))
        tile.write_text("G3_3", encoding="utf-8")
        self.assertEqual(key, ci_grid.grid_key(self.root))
        for name in ci_grid.KEY_FILES:
            path = self.root / name
            path.write_text(path.read_text(encoding="utf-8") + " ", encoding="utf-8")
            self.assertNotEqual(key, ci_grid.grid_key(self.root), name)
            path.write_text(path.read_text(encoding="utf-8")[:-1], encoding="utf-8")


class Archives(unittest.TestCase):
    def setUp(self) -> None:
        self.dir = tempfile.TemporaryDirectory()
        self.root = Path(self.dir.name)
        make_repo(self.root, {"G0_0": "a", "G0_1": "b", "G1_0": "c"})
        self.build = self.root / ".lake" / "build"
        for module in [ci_grid.DEFS, *ci_grid.tile_modules(self.root)]:
            for rel in ci_grid.artifact_paths(module):
                path = self.build / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(os.urandom(64) + rel.encode())
        patches = [
            mock.patch.object(ci_grid, "ROOT", self.root),
            mock.patch.object(ci_grid, "BUILD", self.build),
        ]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    def tearDown(self) -> None:
        self.dir.cleanup()

    def run_cli(self, *argv: str) -> int:
        args = ci_grid.parser().parse_args(list(argv))
        return int(args.func(args))

    def snapshot(self) -> dict[str, bytes]:
        return {
            str(path.relative_to(self.build)): path.read_bytes()
            for path in self.build.rglob("*")
            if path.is_file()
        }

    def test_round_trip(self) -> None:
        archive = self.root / "all.tar.zst"
        self.assertEqual(self.run_cli("pack", "--with-defs", "--out", str(archive)), 0)
        expected = self.snapshot()
        for path in list(self.build.rglob("*")):
            if path.is_file():
                path.unlink()
        self.assertEqual(self.run_cli("unpack", str(archive)), 0)
        self.assertEqual(self.snapshot(), expected)

    def test_shards_and_defs_make_the_whole(self) -> None:
        parts = []
        self.assertEqual(
            self.run_cli("pack", "--defs-only", "--out", str(self.root / "defs.tar.zst")), 0
        )
        parts.append(self.root / "defs.tar.zst")
        for shard in range(3):
            out = self.root / f"shard-{shard}.tar.zst"
            self.assertEqual(
                self.run_cli("pack", "--shard", str(shard), "--shards", "3", "--out", str(out)), 0
            )
            parts.append(out)
        expected = self.snapshot()
        for path in list(self.build.rglob("*")):
            if path.is_file():
                path.unlink()
        self.assertEqual(self.run_cli("unpack", *map(str, parts)), 0)
        self.assertEqual(self.snapshot(), expected)

    def test_missing_outputs_are_an_error(self) -> None:
        (self.build / "lib/lean/Mlc/GridTiles/G0_1.trace").unlink()
        with self.assertRaises(SystemExit):
            self.run_cli("pack", "--out", str(self.root / "x.tar.zst"))


class Seed(unittest.TestCase):
    def setUp(self) -> None:
        self.dir = tempfile.TemporaryDirectory()
        base = Path(self.dir.name)
        self.root = base / "work"
        self.root.mkdir()
        make_repo(self.root, {"G0_0": "a", "G0_1": "b"})
        git(self.root, "init", "-q")
        git(self.root, "config", "user.email", "t@example.org")
        git(self.root, "config", "user.name", "t")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "init")
        self.remote = base / "remote.git"
        git(base, "init", "-q", "--bare", str(self.remote))
        git(self.root, "remote", "add", "origin", str(self.remote))
        for patch in (
            mock.patch.object(ci_grid, "ROOT", self.root),
            mock.patch.object(ci_grid, "CHUNK_BYTES", 10_000),
        ):
            patch.start()
            self.addCleanup(patch.stop)

    def tearDown(self) -> None:
        self.dir.cleanup()

    def run_cli(self, *argv: str) -> int:
        args = ci_grid.parser().parse_args(list(argv))
        return int(args.func(args))

    def test_push_probe_fetch(self) -> None:
        self.assertEqual(self.run_cli("seed-probe"), 1)
        payload = random.Random(7).randbytes(35_000)
        archive = self.root / "tiles.tar.zst"
        archive.write_bytes(payload)
        self.assertEqual(self.run_cli("seed-push", "--archive", str(archive)), 0)
        self.assertEqual(self.run_cli("seed-probe"), 0)
        refs = subprocess.run(
            ["git", f"--git-dir={self.remote}", "for-each-ref", "--format=%(refname)"],
            check=True,
            text=True,
            capture_output=True,
        ).stdout.strip()
        self.assertEqual(refs, f"{ci_grid.SEED_NAMESPACE}/tiles-{ci_grid.grid_key(self.root)}")
        # A clone does not see the seed: it lives outside refs/heads and refs/tags.
        clone = Path(self.dir.name) / "clone"
        git(Path(self.dir.name), "clone", "-q", str(self.remote), str(clone))
        self.assertEqual(git(clone, "for-each-ref", "--format=%(refname)").count("ci-cache"), 0)
        out = self.root / "fetched.tar.zst"
        self.assertEqual(self.run_cli("seed-fetch", "--out", str(out)), 0)
        self.assertEqual(out.read_bytes(), payload)

    def test_another_key_has_no_seed(self) -> None:
        archive = self.root / "tiles.tar.zst"
        archive.write_bytes(b"x" * 100)
        self.assertEqual(self.run_cli("seed-push", "--archive", str(archive)), 0)
        (self.root / "Mlc" / "GridTiles" / "G0_0.lean").write_text("other", encoding="utf-8")
        self.assertEqual(self.run_cli("seed-probe"), 1)
        out = self.root / "fetched.tar.zst"
        self.assertEqual(self.run_cli("seed-fetch", "--out", str(out)), 1)
        self.assertFalse(out.exists())


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=1, stream=sys.stdout).run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
