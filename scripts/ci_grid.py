#!/usr/bin/env python3
"""Helpers of the CI pipeline for the kernel-checked grid (see docs/ci.md).

The grid is 14 000 independent modules `Mlc/GridTiles/G<block>_<part>.lean`, whose kernel
checks cost tens of CPU hours. The pipeline builds them in parallel shards, moves the build
outputs between jobs as zstd archives, and lets Lake confirm that they are up to date, so
that no job but the shards ever runs the kernel on a tile. Everything here uses the standard
library only.

    plan          key of the grid and the list of shards (GitHub step outputs)
    targets       Lake targets of a shard (or of all tiles)
    build-shard   build the modules of a shard
    pack          archive the build outputs of a shard (or of everything)
    unpack        extract archives into .lake/build
    check         `lake build --no-build` over all tiles: fail if any would be rebuilt
    seed-push     publish a local archive as a git ref (a seed for CI)
    seed-fetch    download such an archive
    seed-probe    exit 0 when the seed of the current key exists on the remote
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TILES = ROOT / "Mlc" / "GridTiles"
BUILD = ROOT / ".lake" / "build"
DEFS = "Mlc.GridDefs"
DEFAULT_SHARDS = 20
SEED_NAMESPACE = "refs/ci-cache"
CHUNK_BYTES = 48 * 1024 * 1024  # GitHub rejects blobs above 100 MB
CHECK_BATCH = 3000
# Inputs that change the build outputs of the tiles besides the tile sources themselves.
KEY_FILES = ("Mlc/GridDefs.lean", "lean-toolchain", "lake-manifest.json")


def order(name: str) -> tuple[int, ...]:
    """Numeric order of `G<block>_<part>`."""
    return tuple(int(v) for v in re.findall(r"\d+", name))


def tile_modules(root: Path | None = None) -> list[str]:
    """The tile modules, in order of block and part."""
    base = root or ROOT
    stems = [path.stem for path in (base / "Mlc" / "GridTiles").glob("G*.lean")]
    return [f"Mlc.GridTiles.{stem}" for stem in sorted(stems, key=order)]


def shard_of(module: str, shards: int) -> int:
    """A stable assignment: a change of one tile never moves another tile to a different shard."""
    return zlib.crc32(module.encode()) % shards


def shard_modules(shard: int, shards: int, root: Path | None = None) -> list[str]:
    return [m for m in tile_modules(root) if shard_of(m, shards) == shard]


def grid_key(root: Path | None = None) -> str:
    """A digest of everything that determines the build outputs of the tiles."""
    base = root or ROOT
    digest = hashlib.sha256()
    for module in tile_modules(base):
        path = base / (module.replace(".", "/") + ".lean")
        digest.update(module.encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    for name in KEY_FILES:
        digest.update(name.encode() + b"\0")
        digest.update(hashlib.sha256((base / name).read_bytes()).digest())
    return digest.hexdigest()[:20]


def artifact_paths(module: str) -> list[str]:
    """Build outputs of a module, relative to `.lake/build` (what Lake checks and replays)."""
    base = module.replace(".", "/")
    lib, ir = f"lib/lean/{base}", f"ir/{base}"
    return [
        f"{lib}.olean",
        f"{lib}.olean.hash",
        f"{lib}.ilean",
        f"{lib}.ilean.hash",
        f"{lib}.trace",
        f"{ir}.c",
        f"{ir}.c.hash",
    ]


def targets(modules: list[str]) -> list[str]:
    return [f"+{module}" for module in modules]


def run(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, check=True, text=True, **kwargs)  # type: ignore[call-overload]


def github_output(**values: str) -> None:
    """Print `name=value` lines, and append them to $GITHUB_OUTPUT when it is set."""
    lines = [f"{name}={value}" for name, value in values.items()]
    print("\n".join(lines))
    path = os.environ.get("GITHUB_OUTPUT")
    if path:
        with open(path, "a", encoding="utf-8") as handle:
            handle.write("\n".join(lines) + "\n")


def modules_for(args: argparse.Namespace) -> list[str]:
    modules = tile_modules() if args.shard is None else shard_modules(args.shard, args.shards)
    return modules[: args.limit] if args.limit else modules


# ---------------------------------------------------------------- plan, build, check


def cmd_plan(args: argparse.Namespace) -> int:
    modules = tile_modules()
    sizes = [len(shard_modules(i, args.shards)) for i in range(args.shards)]
    github_output(
        key=grid_key(),
        shards=json.dumps(list(range(args.shards))),
        modules=str(len(modules)),
    )
    print(f"shard sizes: min {min(sizes)}, max {max(sizes)}", file=sys.stderr)
    return 0


def cmd_targets(args: argparse.Namespace) -> int:
    print("\n".join(targets(modules_for(args))))
    return 0


def cmd_build_shard(args: argparse.Namespace) -> int:
    modules = modules_for(args)
    print(f"building {len(modules)} modules", flush=True)
    return subprocess.run(["lake", "build", *targets(modules)], cwd=ROOT, check=False).returncode


def cmd_check(args: argparse.Namespace) -> int:
    """Fail when Lake would rebuild a tile (the outputs of another job did not match)."""
    modules = modules_for(args)
    for start in range(0, len(modules), CHECK_BATCH):
        batch = modules[start : start + CHECK_BATCH]
        proc = subprocess.run(
            ["lake", "build", "--no-build", *targets(batch)],
            cwd=ROOT,
            check=False,
            text=True,
            capture_output=True,
        )
        if proc.returncode != 0:
            tail = (proc.stdout + proc.stderr).strip().splitlines()[-25:]
            print("\n".join(tail), file=sys.stderr)
            print(
                f"error: tiles {start}..{start + len(batch)} are not up to date; "
                "the unpacked outputs do not match the sources or the toolchain",
                file=sys.stderr,
            )
            return 1
    print(f"all {len(modules)} tile modules are up to date")
    return 0


# ---------------------------------------------------------------- archives


def archive_files(modules: list[str], with_defs: bool) -> list[str]:
    names = ([DEFS] if with_defs else []) + modules
    files: list[str] = []
    missing: list[str] = []
    for module in names:
        for rel in artifact_paths(module):
            (files if (BUILD / rel).is_file() else missing).append(rel)
    if missing:
        raise SystemExit(f"error: {len(missing)} outputs are missing, for example {missing[0]}")
    return files


def cmd_pack(args: argparse.Namespace) -> int:
    modules = [] if args.defs_only else modules_for(args)
    files = archive_files(modules, args.with_defs or args.defs_only)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as listing:
        listing.write("\n".join(files) + "\n")
    try:
        run(
            ["tar", "-I", f"zstd -T0 -{args.level}", "-cf", str(out), "-C", str(BUILD), "-T", listing.name]
        )
    finally:
        os.unlink(listing.name)
    print(f"{out}: {len(files)} files, {out.stat().st_size / 1e6:.1f} MB")
    return 0


def cmd_unpack(args: argparse.Namespace) -> int:
    BUILD.mkdir(parents=True, exist_ok=True)
    for name in args.archives:
        run(["tar", "-I", "zstd -T0", "-xf", name, "-C", str(BUILD)])
        print(f"unpacked {name}")
    return 0


# ---------------------------------------------------------------- seed: an archive in a git ref


def remote_url(args: argparse.Namespace) -> str:
    if args.remote:
        return args.remote
    return run(["git", "remote", "get-url", "origin"], cwd=ROOT, capture_output=True).stdout.strip()


def seed_ref(key: str) -> str:
    return f"{SEED_NAMESPACE}/tiles-{key}"


def cmd_seed_probe(args: argparse.Namespace) -> int:
    key = args.key or grid_key()
    out = run(
        ["git", "ls-remote", remote_url(args), seed_ref(key)], cwd=ROOT, capture_output=True
    ).stdout.strip()
    print("present" if out else "absent")
    return 0 if out else 1


def cmd_seed_push(args: argparse.Namespace) -> int:
    """Publish an archive of all tile outputs (and `Mlc.GridDefs`) as chunks of a git commit.

    The commit has no parent and lives only under `refs/ci-cache/`, which clones and
    `actions/checkout` never fetch, so the repository history stays as small as before.
    """
    key = grid_key()
    archive = Path(args.archive)
    if not archive.is_file():
        raise SystemExit(f"error: {archive} does not exist; run `pack --all --with-defs` first")
    work = Path(tempfile.mkdtemp(prefix="ci-seed-"))
    try:
        git_dir = work / "seed.git"
        run(["git", "init", "-q", "--bare", str(git_dir)])
        env = {**os.environ, "GIT_DIR": str(git_dir), "GIT_INDEX_FILE": str(work / "index")}
        digest = hashlib.sha256()
        entries: list[tuple[str, str]] = []
        with archive.open("rb") as stream:
            index = 0
            while chunk := stream.read(CHUNK_BYTES):
                digest.update(chunk)
                part = work / f"part-{index:04d}"
                part.write_bytes(chunk)
                blob = run(
                    ["git", "-c", "core.looseCompression=0", "hash-object", "-w", "--no-filters", str(part)],
                    env=env,
                    capture_output=True,
                ).stdout.strip()
                part.unlink()
                entries.append((f"chunk-{index:04d}", blob))
                index += 1
        manifest = {
            "key": key,
            "chunks": len(entries),
            "bytes": archive.stat().st_size,
            "sha256": digest.hexdigest(),
            "modules": len(tile_modules()),
        }
        text = json.dumps(manifest, indent=1) + "\n"
        blob = run(
            ["git", "hash-object", "-w", "--stdin"], env=env, input=text, capture_output=True
        ).stdout.strip()
        entries.append(("MANIFEST.json", blob))
        for name, sha in entries:
            run(["git", "update-index", "--add", "--cacheinfo", f"100644,{sha},{name}"], env=env)
        tree = run(["git", "write-tree"], env=env, capture_output=True).stdout.strip()
        commit_env = {
            **env,
            "GIT_AUTHOR_NAME": "ci-cache",
            "GIT_AUTHOR_EMAIL": "ci-cache@users.noreply.github.com",
            "GIT_COMMITTER_NAME": "ci-cache",
            "GIT_COMMITTER_EMAIL": "ci-cache@users.noreply.github.com",
        }
        commit = run(
            ["git", "commit-tree", tree, "-m", f"Build outputs of the grid tiles, key {key}"],
            env=commit_env,
            capture_output=True,
        ).stdout.strip()
        ref = seed_ref(key)
        print(f"pushing {len(entries) - 1} chunks ({manifest['bytes'] / 1e6:.0f} MB) to {ref}")
        run(
            ["git", "-c", "pack.compression=0", "push", remote_url(args), f"{commit}:{ref}"],
            env=env,
        )
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return 0


def cmd_seed_fetch(args: argparse.Namespace) -> int:
    """Download the seed of the current key and write it to one archive."""
    key = args.key or grid_key()
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    ref = seed_ref(key)
    fetched = subprocess.run(
        [
            "git",
            "-c",
            "transfer.unpackLimit=1",  # keep the pack as received instead of inflating 17 blobs
            "fetch",
            "--depth=1",
            "--no-tags",
            "--quiet",
            remote_url(args),
            f"+{ref}:{ref}",
        ],
        cwd=ROOT,
        check=False,
    )
    if fetched.returncode != 0:
        print(f"no seed under {ref}", file=sys.stderr)
        return 1
    tree = run(["git", "ls-tree", "-r", "--name-only", ref], cwd=ROOT, capture_output=True).stdout.split()
    manifest = json.loads(
        run(["git", "show", f"{ref}:MANIFEST.json"], cwd=ROOT, capture_output=True).stdout
    )
    chunks = sorted(name for name in tree if name.startswith("chunk-"))
    if len(chunks) != manifest["chunks"]:
        print("error: the seed is incomplete", file=sys.stderr)
        return 1
    digest = hashlib.sha256()
    with out.open("wb") as sink:
        for name in chunks:
            data = subprocess.run(
                ["git", "cat-file", "blob", f"{ref}:{name}"], cwd=ROOT, check=True, capture_output=True
            ).stdout
            digest.update(data)
            sink.write(data)
    if digest.hexdigest() != manifest["sha256"]:
        out.unlink()
        print("error: the checksum of the seed does not match", file=sys.stderr)
        return 1
    print(f"{out}: {out.stat().st_size / 1e6:.1f} MB from {ref}")
    return 0


# ---------------------------------------------------------------- command line


def parser() -> argparse.ArgumentParser:
    top = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = top.add_subparsers(dest="command", required=True)

    def add(name: str, func: object, *, scope: bool = False) -> argparse.ArgumentParser:
        p = sub.add_parser(name)
        p.set_defaults(func=func)
        p.add_argument("--shards", type=int, default=DEFAULT_SHARDS)
        if scope:
            p.add_argument("--shard", type=int, default=None, help="only this shard (default: all tiles)")
            p.add_argument("--limit", type=int, default=0, help="only the first N modules (tests)")
        return p

    add("plan", cmd_plan)
    add("targets", cmd_targets, scope=True)
    add("build-shard", cmd_build_shard, scope=True)
    add("check", cmd_check, scope=True)
    pack = add("pack", cmd_pack, scope=True)
    pack.add_argument("--out", required=True)
    pack.add_argument("--with-defs", action="store_true", help=f"include {DEFS}")
    pack.add_argument("--defs-only", action="store_true", help=f"archive {DEFS} alone")
    pack.add_argument("--level", type=int, default=3)
    unpack = add("unpack", cmd_unpack)
    unpack.add_argument("archives", nargs="+")
    for name, func in (("seed-push", cmd_seed_push), ("seed-fetch", cmd_seed_fetch), ("seed-probe", cmd_seed_probe)):
        p = add(name, func)
        p.add_argument("--remote", default="")
        p.add_argument("--key", default="")
        if name == "seed-push":
            p.add_argument("--archive", required=True)
        if name == "seed-fetch":
            p.add_argument("--out", required=True)
    return top


def main() -> int:
    args = parser().parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    sys.exit(main())
