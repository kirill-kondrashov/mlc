# MLC Scripts

Utility scripts for Lean dependency-graph generation, progress reporting, and
local serving. They use the Python standard library; the map of the Progress tab
also needs `numpy` (`pip install -r scripts/requirements.txt`).

The interactive graph is one 2D figure, the proof spine (`spine_graph.py`):

```sh
make graphs
make serve
```

`export_dependencies.lean` supplies constants from elaborated types and proofs.
Generation checks reachability, acyclicity and the axiom frontier, checks that
the milestones of the spine form a consistent order in the graph, then writes
`site/` with one HTML page (an inline SVG of about 200 elements, laid out by the
generator) and the progress files. The page has hover tracing, a side panel, a
search over the declarations, zoom, category filters, the counts of theorems,
lemmas and declarations by level of the spine, and the **Progress** tab (the
controls of the figure disappear there).

`programme.py` is the catalogue of the programme for Problems 4.3 and 4.4: the
eight classes of boundary parameters, the sixteen lemmas (the fields of
`MLC.Research.ProgrammeInput` in `Mlc/ProgrammeRoot.lean`), their sources, and
the status of each, open while it is a field and proved once its theorem exists.
The generator fails if the catalogue and the Lean structure disagree; the graph
draws the lemmas as nodes, and the progress report derives the classes component of
the Coverage-Uncertainty Profile from the catalogue.

`progress_report.py` computes the progress numbers from Git history. The
**Progress** tab shows the certified resolved share `100% − μ*(R) / 4π` of the
unresolved set `R` as a number, then the map of `M` with the list of the commits
that certified its regions (the map on the left, the list on the right), then a
table of the commits after the literature baseline (date, commit, description,
share, and what it resolved). The map marks the parameters certified by each
commit: `map_raster.py` composites the 600 000 certified rectangles of the grids,
with the exact coverage of every pixel, into one PNG (about 2500 × 2200 pixels)
that the SVG embeds, since the same rectangles as vector paths weigh 18 MB and
some browsers draw nothing for them; the axes, the disks and the numerical outline
of `∂M` stay vector. The literature
baseline is the first commit of the history whose `RootInput` has exactly the
fields `Problem43PseudoSiegelAPrioriBoundsData` and
`Problem44VirtualMoleculeData`, found by a binary search over the first-parent
history (`progress_history`); its row lists the two open problems. Every grid commit gets its own
colour: `export_grid_regions.lean pmax J fuel` reproduces the squares of its
grid, and the report uses them only when the number of unresolved cells equals
the count that the commit proved. Texts with formulas are written with
`$...$` TeX math and rendered as TeX for the report and as HTML for the page.
The same data feeds `docs/mlc_progress.tex` through `progress_commits.tex`,
`progress_routes.tex`, and `progress_map.svg`. Route probabilities are planning
priors. The share `100%` corresponds to `R = ∅` (MLC), but a nonempty `R` of
measure zero would also give it, so the share is read with the count of open
root obligations.

**Squash merges.** The table and the map are replayed from the first-parent history, and a
squash merge folds a whole branch into one commit of `main`: the table would keep one row
and the map would lose every layer of the branch. Tag the tip of the branch before it is
deleted, and push the tag:

```sh
git tag -a progress-archive/N <tip of the branch> -m "<what the branch did>"
git push origin progress-archive/N
```

`progress_history` replaces the squash commit by the first-parent commits that the branch
added, when the tree of the squash commit is the tree of a tagged tip (that holds when `main`
did not move while the branch lived). A branch that is merged without squashing (a
fast-forward, or a rebase) needs no tag, and a squash commit without a tag stays one row.
`python3 scripts/test_progress_history.py` checks these cases on temporary repositories.

The map is drawn by `map_raster.py`; `python3 scripts/test_map_raster.py` checks its pixel
coverage against a direct computation (`make test-scripts` runs both tests).

The repository hook runs `scripts/check_progress.py`. A commit that stages Lean
sources (`Mlc.lean`, `Mlc/**/*.lean`) must improve at least one of the certified
resolved share, the share of parameter classes with a Lean certificate and the
dependency-graph milestone debt (which falls when a milestone theorem is added),
and must worsen none of them, before Git accepts it; commits that stage only
documents and scripts pass unchecked. The classes and the lemmas of the programme
for Problems 4.3 and 4.4 are catalogued in `scripts/programme.py`.

`grid_hints.lean` is the search program of the certified grid, compiled natively
by `lake build gridhints`. It subdivides squares that it cannot certify and
writes a stream of natural numbers, the hints: `0` marks an unresolved finest
cell, `1` a split, and a larger number a certificate (outside `M` after `n`
steps of the first-order model, or inside `M` by a moving disk of period `p`).
`refine_grid.py` reads the tiles of the current grid, runs the search on the
unresolved finest cells of the selected blocks (`--blocks first:last`) in parallel,
one level deeper, and writes the new hint streams; `--plan N` splits the work into
N ranges of blocks with about equal kernel cost. Inside certificates are limited to
`--cap` steps, because the kernel pays one step of the model for each step of a
certificate. `generate_grid_tiles.py --hints FILE` cuts the streams into tiles of
bounded kernel cost and writes independent modules `Mlc/GridTiles/G<block>_<part>.lean`
(a block is four consecutive root squares of the upper half-plane and has one depth;
each module states its own depth, so the modules of blocks that were not refined stay
byte-identical and Lake does not rebuild them; each running module needs a few GB of
memory). It also writes `Mlc/GridCertified.lean`, which sums the weighted counts of the
modules and proves the area bound. The kernel checks every certificate, so the search
needs no proof. The progress tooling reads `gridCells` and `gridDepth` from these files
and replays the hint streams of every commit to draw the certified region on the map
in the Progress tab. The note of a grid commit in the table is the line `Area-note:`
of its commit message.
`export_grid_regions.lean` (repository root) holds a copy of the first
classifier, imports nothing from `Mlc`, and reproduces the regions of the
earlier grids.
