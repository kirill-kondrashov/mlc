#!/usr/bin/env python3
"""Serve the generated graph site over HTTP for local browser use."""

from __future__ import annotations

import argparse
import http.server
import socketserver
import sys
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description="Serve the generated dependency graph site.")
    parser.add_argument(
        "--directory",
        default=None,
        help="Directory to serve (default: <repo>/site)",
    )
    parser.add_argument("--host", default="127.0.0.1", help="Bind host (default: 127.0.0.1)")
    parser.add_argument("--port", type=int, default=8000, help="Bind port (default: 8000)")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    site_dir = Path(args.directory).resolve() if args.directory else (repo_root / "site").resolve()
    if not site_dir.exists() or not site_dir.is_dir():
        print(f"Site directory does not exist: {site_dir}", file=sys.stderr)
        print("Run `make graphs` first.", file=sys.stderr)
        raise SystemExit(1)

    class Handler(http.server.SimpleHTTPRequestHandler):
        def __init__(self, *h_args, **h_kwargs):
            super().__init__(*h_args, directory=str(site_dir), **h_kwargs)

    class ReusableThreadingTCPServer(socketserver.ThreadingTCPServer):
        allow_reuse_address = True

    with ReusableThreadingTCPServer((args.host, args.port), Handler) as httpd:
        print(f"Serving {site_dir}")
        print(f"Open: http://{args.host}:{args.port}/mlc_conjecture/index.html")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
