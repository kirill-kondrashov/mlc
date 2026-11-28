#!/usr/bin/env python3
"""Checks of the typology of the Progress page: the hierarchy, the fragments, the objects and
their milestones, the census of the components and the rendering."""

from __future__ import annotations

import re
import struct
from html.parser import HTMLParser
from pathlib import Path

import numpy as np

import progress_report as report
import typology as ty
from programme import CLASSES, LEMMA, LEMMAS, STATUSES, lemma_statuses

ROOT = Path(__file__).resolve().parents[1]


def test_the_hierarchy_is_one_tree_that_covers_every_class() -> None:
    keys = [part.key for part in ty.PARTS]
    assert len(set(keys)) == len(keys)
    roots = [part for part in ty.PARTS if part.parent is None]
    assert [part.key for part in roots] == ["M"]
    for part in ty.PARTS:
        assert part.parent is None or part.parent in ty.PART
    classes = {key for key, _, _ in CLASSES}
    used = {key for part in ty.PARTS for key in part.classes}
    assert used == classes
    for part in ty.PARTS:
        if part.classes:
            assert not [p for p in ty.PARTS if p.parent == part.key], "a class is a leaf"
        assert re.fullmatch(r"(lemma|open|prog):[\w.]+", part.node) or not part.node
        if part.node.startswith("lemma:"):
            assert part.node[len("lemma:"):] in LEMMA


def test_the_fragments_sit_in_the_hierarchy() -> None:
    assert len({fragment.key for fragment in ty.FRAGMENTS}) == len(ty.FRAGMENTS)
    for fragment in ty.FRAGMENTS:
        assert fragment.part in ty.PART
        assert fragment.regime == "" or fragment.regime in ty.REGIMES
        assert fragment.half > 0


def test_the_modules_of_the_objects_exist() -> None:
    for obj in ty.OBJECTS:
        for module in obj.modules:
            if module.endswith("/"):
                assert list((ROOT / "Mlc" / module).glob("*.lean")), module
            else:
                assert (ROOT / "Mlc" / f"{module}.lean").exists(), module
    counts = ty.declaration_counts(ROOT)
    assert all(counts[key] > 0 for key in counts)


def test_the_usage_of_an_object_follows_the_dependencies() -> None:
    from types import SimpleNamespace

    files = {
        "MLC.Research.Geometry.Foo": "Mlc/Research/CaseTree.lean",
        "MLC.Research.LevelGeometry.red": "Mlc/Research/LevelGeometry.lean",
        "MLC.Research.LevelTower.cap": "Mlc/Research/LevelTower.lean",
        "MLC.Research.IsCollar": "Mlc/Research/Collar.lean",
        "MLC.Certified.tiles_0_0": "Mlc/GridTiles/G0_0.lean",
        "MLC.Certified.unresolved_volume_le_grid": "Mlc/GridCertified.lean",
        "MLC.Research.Orphan": "Mlc/Research/Collar.lean",
    }
    fq_index = {name: SimpleNamespace(file=file) for name, file in files.items()}
    edges = {
        "MLC.Research.LevelGeometry.red": {"MLC.Research.LevelTower.cap", "Lean.Nat"},
        "MLC.Research.LevelTower.cap": {"MLC.Research.IsCollar"},
        "MLC.Research.IsCollar": {"MLC.Certified.tiles_0_0"},
    }
    lemmas = [
        SimpleNamespace(key="unboundedJumpCap", lean="MLC.Research.Geometry.Foo",
                        reduction="MLC.Research.LevelGeometry.red"),
        SimpleNamespace(key="yoccoz", lean="MLC.Research.Orphan", reduction=""),
        SimpleNamespace(key="neutral", lean="MLC.Certified.unresolved_volume_le_grid",
                        reduction=""),
    ]
    usage = ty.object_usage(fq_index, edges, lemmas)
    # the cone of the statement and of its reduction, through the declarations of other
    # modules; a file of a directory entry (the tiles) and a listed file both count for the grid
    assert usage == {
        "unboundedJumpCap": {"assembly", "level", "collar", "grid"},
        "yoccoz": {"collar"},
        "neutral": {"grid"},
    }
    # on the sources of the repository every statement has an entry
    assert set(ty.object_usage({}, {})) == set(LEMMA)


def test_every_pointer_to_a_lean_declaration_exists() -> None:
    text = report.lean_research_text(ROOT) + (ROOT / "Mlc" / "Core.lean").read_text()
    pointers = [part.lean for part in ty.PARTS if part.lean]
    for pointer in pointers:
        short = pointer.rsplit(".", 1)[-1]
        assert re.search(rf"^\s*(?:theorem|lemma|def)\s+{re.escape(short)}\b", text, re.MULTILINE), pointer
    for lemma in LEMMAS:
        if lemma.reduction:
            short = lemma.reduction.rsplit(".", 1)[-1]
            assert re.search(rf"^\s*theorem\s+{re.escape(short)}\b", text, re.MULTILINE), lemma.key


def test_every_milestone_has_an_object_and_every_prefix_a_milestone() -> None:
    labels = [label for label, _, _ in report.PROGRESS_MILESTONES]
    for label in labels:
        assert ty.object_of_label(label) is not None, label
    for prefix, key in ty.MILESTONE_OBJECTS:
        assert key in ty.OBJECT
        assert any(label.startswith(prefix) for label in labels), prefix
    assert set(ty.milestone_totals(report.PROGRESS_MILESTONES).values()) != {0}


def test_the_census_counts_the_hyperbolic_components() -> None:
    rows = ty.census(10)
    assert [row["total"] for row in rows] == [1, 1, 3, 6, 15, 27, 63, 120, 252, 495]
    assert [row["satellite"] for row in rows[:6]] == [0, 1, 2, 3, 4, 7]
    assert [row["primitive"] for row in rows[:6]] == [1, 0, 1, 3, 11, 20]
    for row in rows:
        assert row["satellite"] + row["primitive"] == row["total"]
    # the centres of exact period p are the roots of f_c^p(0) that are not roots of f_c^d(0),
    # d | p, d < p; Newton steps polish the roots of the polynomial before they are classified
    def orbit_and_slope(c: complex, steps: int) -> tuple[complex, complex]:
        z, dz = 0j, 0j
        for _ in range(steps):
            z, dz = z * z + c, 2 * z * dz + 1
        return z, dz

    for period in range(1, 7):
        poly = np.polynomial.Polynomial([0.0])
        for _ in range(period):
            poly = poly**2 + np.polynomial.Polynomial([0.0, 1.0])
        roots = list(poly.roots())
        for _ in range(8):
            roots = [r - orbit_and_slope(r, period)[0] / orbit_and_slope(r, period)[1] for r in roots]
        exact = [
            r
            for r in roots
            if all(abs(orbit_and_slope(r, d)[0]) > 1e-7 for d in range(1, period) if period % d == 0)
        ]
        assert len(exact) == rows[period - 1]["total"], period
        assert len({(round(r.real, 6), round(r.imag, 6)) for r in exact}) == len(exact)


def test_the_status_of_a_lemma_follows_the_sources() -> None:
    nothing = lemma_statuses("")
    assert set(nothing.values()) <= set(STATUSES)
    for lemma in LEMMAS:
        assert nothing[lemma.key] == ("published" if lemma.kind == "published" else "open")
    reduced = {lemma.key for lemma in LEMMAS if lemma.reduction}
    # a theorem of the same name that states something else does not reduce the lemma
    wrong = "\n".join(
        f"theorem {lemma.reduction.rsplit('.', 1)[-1]} : True := trivial"
        for lemma in LEMMAS
        if lemma.reduction
    )
    assert not [key for key, value in lemma_statuses(wrong).items() if value == "reduced"]
    right = "\n".join(
        f"  theorem {lemma.reduction.rsplit('.', 1)[-1]} (h : LG.Geo) :\n"
        f"      LG.toGeometry.{lemma.lean.rsplit('.', 1)[-1]} := by\n    exact h"
        for lemma in LEMMAS
        if lemma.reduction
    )
    after = lemma_statuses(right)
    assert {key for key, value in after.items() if value == "reduced"} == reduced
    for lemma in LEMMAS:
        if lemma.kind == "published":
            assert after[lemma.key] == "published"


def test_the_statuses_of_the_tree_are_counted() -> None:
    statuses = lemma_statuses(report.lean_research_text(ROOT))
    assert len(statuses) == len(LEMMAS)
    assert statuses["unboundedDichotomy"] == "reduced"
    assert statuses["unboundedTeichmuller"] == "open"
    assert statuses["yoccoz"] == "published"


def png_size(png: bytes) -> tuple[int, int]:
    assert png[:8] == b"\x89PNG\r\n\x1a\n"
    return struct.unpack(">II", png[16:24])


def test_a_thumbnail_is_a_png_with_a_dark_interior() -> None:
    first = ty.render_fragment((0.0, 0.0), 0.2, size=33, max_iter=200)
    second = ty.render_fragment((0.0, 0.0), 0.2, size=33, max_iter=200)
    assert first == second
    assert png_size(first) == (33, 33)
    far = ty.render_fragment((3.0, 3.0), 0.2, size=9, max_iter=50)
    assert png_size(far) == (9, 9) and far != first


class Balance(HTMLParser):
    """The tags that the cards open are all closed."""

    VOID = {"img", "br", "meta", "hr", "input", "link"}

    def __init__(self) -> None:
        super().__init__()
        self.stack: list[str] = []
        self.problems: list[str] = []

    def handle_starttag(self, tag, attrs) -> None:
        if tag not in self.VOID:
            self.stack.append(tag)

    def handle_endtag(self, tag) -> None:
        if tag in self.VOID:
            return
        if not self.stack or self.stack[-1] != tag:
            self.problems.append(f"</{tag}> after {self.stack[-3:]}")
        else:
            self.stack.pop()


def test_the_cards_are_well_formed_and_complete() -> None:
    from progress_ledger import ledger_rows

    rows = ledger_rows(ROOT)
    page = report.types_html(ROOT, rows)
    balance = Balance()
    balance.feed(page)
    assert not balance.problems and not balance.stack, (balance.problems, balance.stack)
    for part in ty.PARTS:
        assert f'id="type-{part.key}"' in page
    for fragment in ty.FRAGMENTS:
        assert fragment.name in page
    for key in ty.OBJECT:
        assert ty.OBJECT[key].title in page
    for lemma in LEMMAS:
        assert f'href="#n=lemma:{lemma.key}"' in page
    assert page.count('class="tl-c') >= len(rows) * len(ty.OBJECTS)
    assert page.count("data:image/png;base64,") == len(ty.FRAGMENTS)
    # without dependency data no class is marked; with it a dot marks an object of a class
    assert 'o-cell on' not in page
    usage = {name: set() for name in LEMMA}
    usage["unboundedDichotomy"] = {"stacking"}
    marked = report.types_html(ROOT, rows, usage)
    assert marked.count("o-cell on") == 1
    balance = Balance()
    balance.feed(marked)
    assert not balance.problems and not balance.stack


def test_the_table_of_the_classes_has_a_row_per_class() -> None:
    text = ty.types_tex(report.lean_research_text(ROOT))
    assert len(text.strip().splitlines()) == len(CLASSES)
    for line in text.strip().splitlines():
        assert line.endswith(r"\\")
        assert line.count("&") == 5
    # the whole environment, with the rows inside it
    table = ty.types_table_tex(report.lean_research_text(ROOT))
    assert table.startswith(r"\begin{tabularx}") and table.rstrip().endswith(r"\end{tabularx}")
    assert text in table and table.count(r"\begin{tabularx}") == 1


if __name__ == "__main__":
    for name, function in sorted(globals().items()):
        if name.startswith("test_"):
            function()
            print(f"ok {name}")
