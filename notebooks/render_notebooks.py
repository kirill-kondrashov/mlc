from __future__ import annotations

import argparse
import html
import shutil
import warnings
from pathlib import Path

import nbformat
from nbconvert import HTMLExporter
from nbformat.validator import normalize
from nbformat.warnings import MissingIDFieldWarning


def build_index(output_dir: Path, html_files: list[Path]) -> None:
    items = []
    for path in sorted(html_files):
        rel = path.relative_to(output_dir).as_posix()
        label = rel.removesuffix(".html")
        items.append(f'<li><a href="{html.escape(rel)}">{html.escape(label)}</a></li>')
    index = f"""<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <title>MLC notebooks</title>
    <style>
      body {{ font-family: sans-serif; margin: 2rem; }}
      h1 {{ margin-bottom: 1rem; }}
      ul {{ line-height: 1.8; }}
    </style>
  </head>
  <body>
    <h1>MLC notebooks</h1>
    <p>Static HTML render of <code>notebooks/</code>. Refresh the page after rerendering.</p>
    <ul>
      {''.join(items)}
    </ul>
  </body>
</html>
"""
    (output_dir / "index.html").write_text(index, encoding="utf-8")


def render_notebook(exporter: HTMLExporter, source: Path, target: Path) -> None:
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", MissingIDFieldWarning)
        notebook = nbformat.read(source, as_version=4)
    _, notebook = normalize(notebook)
    body, resources = exporter.from_notebook_node(notebook)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(body, encoding="utf-8")
    for filename, data in resources.get("outputs", {}).items():
        output_path = target.parent / filename
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_bytes(data)


def main() -> None:
    parser = argparse.ArgumentParser(description="Render MLC notebooks to static HTML.")
    parser.add_argument("--input-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    input_dir = Path(args.input_dir).resolve()
    output_dir = Path(args.output_dir).resolve()

    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    exporter = HTMLExporter(template_name="classic")
    exporter.exclude_input_prompt = True
    exporter.exclude_output_prompt = True
    exporter.anchor_link_text = ""

    html_files: list[Path] = []
    for source in sorted(input_dir.rglob("*.ipynb")):
        if ".ipynb_checkpoints" in source.parts:
            continue
        rel = source.relative_to(input_dir).with_suffix(".html")
        target = output_dir / rel
        render_notebook(exporter, source, target)
        html_files.append(target)

    build_index(output_dir, html_files)
    print(f"Rendered {len(html_files)} notebook(s) to {output_dir}")


if __name__ == "__main__":
    main()
