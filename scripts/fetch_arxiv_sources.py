#!/usr/bin/env python3
"""Fetch arXiv metadata and source archives listed in refs/mlc_sources.json.

The script uses only the Python standard library.  It keeps the compressed
source archive and extracts a safe, inspectable TeX tree under refs/.
"""

from __future__ import annotations

import argparse
import gzip
import io
import json
import re
import tarfile
import time
import urllib.request
from urllib.error import HTTPError, URLError
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "refs" / "mlc_sources.json"
USER_AGENT = "mlc-reference-fetcher/1.0 (+https://github.com/kirill-kondrashov/mlc)"


def slug(arxiv_id: str) -> str:
    return arxiv_id.replace("/", "-")


def download(urls: str | list[str], attempts: int = 4) -> bytes:
    candidates = [urls] if isinstance(urls, str) else urls
    last_error: Exception | None = None
    for url in candidates:
        for attempt in range(attempts):
            request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            try:
                with urllib.request.urlopen(request, timeout=120) as response:
                    return response.read()
            except HTTPError as error:
                last_error = error
                if error.code not in {429, 500, 502, 503, 504}:
                    break
                retry_after = error.headers.get("Retry-After")
                delay = int(retry_after) if retry_after and retry_after.isdigit() else 2 ** attempt
                print(f"retrying {url} after HTTP {error.code} in {delay}s")
                time.sleep(delay)
            except URLError as error:
                last_error = error
                if attempt + 1 < attempts:
                    time.sleep(2 ** attempt)
    if last_error is not None:
        raise last_error
    raise RuntimeError("no download URL supplied")


def is_tar(data: bytes) -> bool:
    try:
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:*"):
            return True
    except tarfile.TarError:
        return False


def safe_extract(archive: bytes, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:*") as tar:
        for member in tar.getmembers():
            target = (destination / member.name).resolve()
            if destination.resolve() not in target.parents and target != destination.resolve():
                raise RuntimeError(f"unsafe archive member: {member.name}")
        tar.extractall(destination)


def find_main_tex(destination: Path) -> Path | None:
    candidates = sorted(destination.rglob("*.tex"))

    def score(path: Path) -> tuple[int, int, str]:
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            return (-1, 0, str(path))
        document = int("\\documentclass" in text) + int("\\begin{document}" in text)
        title = int("Mandelbrot" in text or "MLC" in text or "Geometry of quadratic" in text)
        plain_tex_entry = int("\\centerline" in text and "\\input" in text)
        return (
            100 * document + 20 * title + 10 * plain_tex_entry,
            -len(path.parts),
            str(path),
        )

    scored = sorted(((score(path), path) for path in candidates), reverse=True)
    return scored[0][1] if scored and scored[0][0][0] > 0 else None


def arxiv_version(metadata: bytes) -> str | None:
    match = re.search(rb"/abs/[^<\s]+v(\d+)", metadata)
    return match.group(1).decode("ascii") if match else None


def extract_source(data: bytes, destination: Path) -> tuple[Path | None, str]:
    if is_tar(data):
        archive_name = destination.parent / f"{destination.name}-source.tar.gz"
        archive_name.write_bytes(data)
        safe_extract(data, destination)
        return find_main_tex(destination), archive_name.name

    if data[:2] == b"\x1f\x8b":
        tex = gzip.decompress(data)
        archive_name = destination.parent / f"{destination.name}-source.tex.gz"
        archive_name.write_bytes(data)
        destination.mkdir(parents=True, exist_ok=True)
        main = destination / f"{destination.name}.tex"
        main.write_bytes(tex)
        return main, archive_name.name

    archive_name = destination.parent / f"{destination.name}-source.bin"
    archive_name.write_bytes(data)
    destination.mkdir(parents=True, exist_ok=True)
    main = destination / f"{destination.name}.tex"
    main.write_bytes(data)
    return main, archive_name.name


def fetch_entry(entry: dict[str, Any], force: bool) -> None:
    arxiv_id = entry["arxiv_id"]
    source_slug = f"arxiv-{slug(arxiv_id)}"
    refs = ROOT / "refs"
    destination = refs / source_slug
    metadata_path = refs / f"{source_slug}.xml"
    marker_path = destination / "00README.json"

    if marker_path.exists() and not force:
        print(f"skip {arxiv_id}: {marker_path.relative_to(ROOT)} already exists")
        return

    metadata_urls = [
        f"https://export.arxiv.org/api/query?id_list={arxiv_id}",
        f"https://arxiv.org/api/query?id_list={arxiv_id}",
    ]
    source_urls = [
        f"https://arxiv.org/src/{arxiv_id}",
        f"https://arxiv.org/e-print/{arxiv_id}",
        f"https://export.arxiv.org/e-print/{arxiv_id}",
    ]
    metadata = download(metadata_urls)
    source = download(source_urls)
    metadata_path.write_bytes(metadata)
    main_tex, archive_name = extract_source(source, destination)

    marker = {
        "key": entry["key"],
        "arxiv_id": arxiv_id,
        "arxiv_version": arxiv_version(metadata),
        "role": entry["role"],
        "title": entry["title"],
        "authors": entry["authors"],
        "metadata": metadata_path.name,
        "source_archive": archive_name,
        "main_tex": str(main_tex.relative_to(refs)) if main_tex else None,
    }
    destination.mkdir(parents=True, exist_ok=True)
    marker_path.write_text(
        json.dumps(marker, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"fetched {arxiv_id}: {marker_path.relative_to(ROOT)}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help="JSON manifest (default: refs/mlc_sources.json)",
    )
    parser.add_argument(
        "--key",
        action="append",
        help="fetch only the entry with this manifest key; repeatable",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="replace existing extracted entries",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    wanted = set(args.key or [])
    entries = [
        entry for entry in manifest["sources"]
        if not wanted or entry["key"] in wanted
    ]
    if wanted and len(entries) != len(wanted):
        missing = sorted(wanted - {entry["key"] for entry in entries})
        raise SystemExit(f"unknown manifest key(s): {', '.join(missing)}")
    for entry in entries:
        fetch_entry(entry, args.force)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
