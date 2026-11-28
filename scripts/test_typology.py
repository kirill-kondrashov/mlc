#!/usr/bin/env python3
"""Checks of the typology of the Progress page: the hierarchy, the fragments, the objects and
their milestones, the census of the components and the rendering."""

from __future__ import annotations

import re
import struct
import zlib
from html.parser import HTMLParser
from pathlib import Path

import numpy as np

import progress_report as report
import typology as ty
from programme import CLASSES, LEMMA, LEMMAS, STATUSES, lemma_statuses, strip_lean_comments

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
    # with no dependency data every statement still has an entry, an empty one
    assert ty.object_usage({}, {}) == {key: set() for key in LEMMA}


def declared_names() -> set[str]:
    """The fully qualified names of the declarations of the library (without the grid tiles),
    as the generator of the graph reads them from the sources."""
    from generate_dependency_graph_site import parse_decls_from_file

    paths = sorted((ROOT / "Mlc").glob("*.lean")) + sorted((ROOT / "Mlc" / "Research").glob("*.lean"))
    return {decl.fq_name for path in paths for decl in parse_decls_from_file(path, ROOT)[0]}


def test_every_pointer_to_a_lean_declaration_exists() -> None:
    names = declared_names()
    pointers = [part.lean for part in ty.PARTS if part.lean]
    pointers += [lemma.lean for lemma in LEMMAS]
    pointers += [lemma.reduction for lemma in LEMMAS if lemma.reduction]
    assert pointers
    for pointer in pointers:
        assert pointer in names, pointer
    # the check separates a name from the same name in another namespace
    assert "MLC.Research.NoSuchNamespace.transfer" not in names


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
    assert reduced

    def reduced_by(template: str) -> set[str]:
        """The lemmas that are reduced when the sources hold, for each reduction, the theorem
        `template` (`{name}` is the theorem and `{target}` the definition of its lemma)."""
        text = "\n".join(
            template.format(
                name=lemma.reduction.rsplit(".", 1)[-1], target=lemma.lean.rsplit(".", 1)[-1]
            )
            for lemma in LEMMAS
            if lemma.reduction
        )
        return {key for key, value in lemma_statuses(text).items() if value == "reduced"}

    # the form of a reduction: a hypothesis, and the lemma for the dictionary of a level geometry
    for good in (
        "  theorem {name} (h : LG.Comparison) :\n      LG.toGeometry.{target} := by\n    exact h",
        "theorem {name} {{ε : ℝ}} (h : LG.Comparison) : LG.toGeometry.{target} := by exact h",
    ):
        assert reduced_by(good) == reduced, good
    # none of these reduces the lemma: another statement under the name, the lemma only among the
    # hypotheses, a conjunction, another dictionary, no hypothesis (that would prove the lemma),
    # another name, and a theorem that a comment holds
    for bad in (
        "theorem {name} : True := trivial",
        "theorem {name} (h : LG.toGeometry.{target}) : LG.Comparison := by exact h",
        "theorem {name} (h : LG.toGeometry.{target}) : LG.Other := by exact h",
        "theorem {name} (h : LG.Comparison) : LG.toGeometry.{target} ∧ True := ⟨h, trivial⟩",
        "theorem {name} (h : LG.Comparison) : Other.Space.{target} := by exact h",
        "theorem {name} (h : LG.Comparison) : {target} := by exact h",
        "theorem {name} : LG.toGeometry.{target} := by exact LG.proof",
        "theorem {name}_aux (h : LG.Comparison) : LG.toGeometry.{target} := by exact h",
        "theorem {name}' (h : LG.Comparison) : LG.toGeometry.{target} := by exact h",
        "-- theorem {name} (h : LG.Comparison) : LG.toGeometry.{target} := by exact h",
        "/-- A docstring:\ntheorem {name} (h : LG.Comparison) : LG.toGeometry.{target} := h -/",
    ):
        assert reduced_by(bad) == set(), bad
    # a published lemma stays published
    right = lemma_statuses(
        "\n".join(
            f"theorem {lemma.reduction.rsplit('.', 1)[-1]} (h : LG.Geo) :"
            f" LG.toGeometry.{lemma.lean.rsplit('.', 1)[-1]} := h"
            for lemma in LEMMAS
            if lemma.reduction
        )
    )
    for lemma in LEMMAS:
        if lemma.kind == "published":
            assert right[lemma.key] == "published"


def test_the_statuses_of_the_tree_are_counted() -> None:
    statuses = lemma_statuses(report.lean_research_text(ROOT))
    assert len(statuses) == len(LEMMAS)
    assert statuses["unboundedDichotomy"] == "reduced"
    assert statuses["unboundedTeichmuller"] == "open"
    assert statuses["yoccoz"] == "published"
    # every reduction of the catalogue is found in the sources
    assert {key for key, value in statuses.items() if value == "reduced"} == {
        lemma.key for lemma in LEMMAS if lemma.reduction
    }


def test_the_comments_of_a_lean_source_are_stripped() -> None:
    source = (
        "theorem a : True := trivial -- theorem line_comment\n"
        "/-- A docstring\ntheorem in_doc : True\n  /- nested\n  theorem deeper -/\n"
        "still a docstring --/ theorem b : True := trivial\n"
        "/-! module doc -/\n"
        "-- /- a line comment that opens no block\n"
        "theorem c : True := trivial\n"
    )
    code = strip_lean_comments(source)
    assert re.findall(r"theorem (\w+)", code) == ["a", "b", "c"]
    # the lines of the code are the lines of the source
    assert code.count("\n") == source.count("\n")
    assert code.splitlines()[-1] == "theorem c : True := trivial"
    # an unclosed block comment drops the rest
    assert strip_lean_comments("def x := 1\n/- open") == "def x := 1\n"


def test_the_declarations_of_a_source_are_counted_without_comments_and_with_attributes() -> None:
    # the lines of comments (a docstring line that starts with a keyword among them) do not count
    comments = (
        "/-\ntheorem inside_block : True := trivial\n-/\n"
        "-- theorem line_comment : True := trivial\n"
        "/-- A docstring whose line\ntheorem above), and the converse -/\n"
        "/-! module doc\ndef also_not : ℕ := 0\n-/\n"
    )
    assert ty.count_declarations(comments) == 0
    # a keyword after attributes counts, on the same line or on the next one
    attributes = (
        "@[simp] theorem b : True := trivial\n"
        "@[simp, grind] protected lemma c : True := trivial\n"
        "@[simp]\ntheorem d : True := trivial\n"
    )
    assert ty.count_declarations(attributes) == 3
    plain = (
        "/-- Doc. -/\ntheorem a : True := trivial\n"
        "noncomputable def e : ℕ := 0\n"
        "private theorem f : True := trivial\n"
        "structure S where\n  x : ℕ\n"
        "instance : Inhabited S := ⟨⟨0⟩⟩\n"
        "instance instNamed : Inhabited S := ⟨⟨0⟩⟩\n"
        "deriving instance Fintype for S\n"
    )
    # a, e, f, S and the two instances; the deriving line adds none
    assert ty.count_declarations(plain) == 6
    assert ty.count_declarations(comments + attributes + plain) == 9
    sizes = ty.declaration_counts(ROOT)
    assert set(sizes) == set(ty.OBJECT) and all(sizes[key] > 0 for key in sizes)


def png_size(png: bytes) -> tuple[int, int]:
    assert png[:8] == b"\x89PNG\r\n\x1a\n"
    return struct.unpack(">II", png[16:24])


def decode_png(png: bytes) -> np.ndarray:
    """The pixels (height, width, 3) of an 8-bit RGB PNG whose scanlines are unfiltered."""
    width, height = png_size(png)
    data, position = b"", 8
    while position < len(png):
        length, tag = struct.unpack(">I4s", png[position : position + 8])
        if tag == b"IDAT":
            data += png[position + 8 : position + 8 + length]
        position += 12 + length
    raw = zlib.decompress(data)
    stride = 1 + 3 * width
    assert len(raw) == stride * height
    rows = []
    for row in range(height):
        line = raw[row * stride : (row + 1) * stride]
        assert line[0] == 0
        rows.append(np.frombuffer(line[1:], dtype=np.uint8).reshape(width, 3))
    return np.stack(rows)


def test_a_thumbnail_is_a_png_with_a_dark_interior() -> None:
    first = ty.render_fragment((0.0, 0.0), 0.2, size=33, max_iter=200)
    assert first == ty.render_fragment((0.0, 0.0), 0.2, size=33, max_iter=200)
    assert png_size(first) == (33, 33)
    pixels = decode_png(first)
    # the middle of the window (|c| <= 0.14) lies in the main cardioid: one dark colour
    interior = pixels[16, 16]
    assert int(interior.sum()) < 60
    assert (pixels[8:25, 8:25] == interior).all()
    # a window far from M has no interior pixel
    far = decode_png(ty.render_fragment((3.0, 3.0), 0.2, size=9, max_iter=50))
    assert far.shape == (9, 9, 3)
    assert not (far == interior).all(axis=2).any()
    # a window on the boundary (the cusp at -3/4) has the interior and brighter exterior pixels
    edge = decode_png(ty.render_fragment((-0.75, 0.0), 0.2, size=33, max_iter=300))
    inside = (edge == interior).all(axis=2)
    assert inside.any() and (~inside).any()
    assert int(edge[~inside].sum(axis=1).max()) > int(interior.sum()) + 100


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
