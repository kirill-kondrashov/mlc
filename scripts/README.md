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
search over the declarations, zoom, category filters, the counts of theorems and
declarations by level of the spine (in Lean `lemma` and `theorem` declare the same
thing, so both count as theorems), and the **Progress** tab (the controls of the
figure disappear there).

`programme.py` is the catalogue of the programme for Problems 4.3 and 4.4: the
eight classes of boundary parameters, the sixteen statements of the programme (the
fields of `MLC.Research.ProgrammeInput` in `Mlc/ProgrammeRoot.lean`, named
"Lemma T", "Lemma G", and so on as nodes of the graph), their sources, and the
status of each: open while it is a field (a hypothesis) of a proposed reading,
literature-motivated (`kind` published) while the literature suggests it and the
development takes it as a hypothesis (the dictionary is a parameter, so it is a hypothesis about
the dictionary, and the bridge from the published theorem is not formalized), reduced when a Lean
theorem of `LevelGeometry.lean` derives it from a geometric statement about the level sets of
the dictionary (the statement is itself open, and the lemma stays a field; the generator reads
the sources without their comments and checks that the theorem has a hypothesis, that its
conclusion, the type after the colon of its signature, is the definition of the lemma at the
dictionary of a level geometry (`LG.toGeometry.Target`), and that the theorem depends on it in
the graph, so a theorem that mentions the lemma among its hypotheses only, one without a
hypothesis and one that a comment holds do not count),
and proved once its theorem exists. The generator fails if the catalogue and the Lean
structure disagree; the
graph draws the statements as nodes, and the progress report derives the classes
component of the Coverage-Uncertainty Profile and the tiles "Open programme
statements" and "Classes with a Lean certificate" from the catalogue.

`typology.py` renders the cards that follow the table of the updates on the **Progress**
tab (and `progress_types.tex` for the report): the hierarchy of the types out of which `M`
and its boundary are assembled (the interior with its hyperbolic components; the boundary as a
skeleton of dimension at most 1 and a wild part of dimension 2, and as the classes of the
programme) with the status of the statements of every class; the characteristic fragments of
`M` (valleys, rabbit, airplane, ...) as numerical thumbnails placed in the hierarchy and in the
three regimes of the survey; the objects that the formalization adds, with the classes whose
statements depend on them and a timeline of their milestones; and the dimension ladder. The
statuses are computed from the Lean sources, the dependency of a class on an object from the
dependency graph of the declarations (`object_usage`, passed in by
`generate_dependency_graph_site.py`, which warns on stderr when the certified grid enters the
cone of a statement, the case in which the grounds for keeping the depth would lapse; an object
in no cone is labelled as such; a standalone run of `progress_report.py` has no graph and
marks no class), the thumbnails by an escape-time rendering with a distance estimate (an
illustration that the Lean proof does not use), and the census of the components by the
necklace formula. `scripts/test_typology.py` checks the hierarchy, the objects, the usage
computation on a small graph, that every pointer to a Lean declaration exists under its full
name, the form of a reduction (the theorems that must not count among them), the counts of
declarations of the objects (comments and attributes), that every milestone of the ledger has an
object, the census against the roots of the Gleason polynomials and the pixels of the
thumbnails.

`progress_report.py` renders the **Progress** tab and the LaTeX report from the
progress ledger (below); it reads no Git history. The tab shows the certified resolved
share `100% − μ*(R) / 4π` of the unresolved set `R` as a number, with the tiles that
measure the proof structure (open root problems, open statements of the programme,
classes with a Lean certificate), then the map of `M` with the list of the updates that
certified its regions (the map on the left, the list on the right), then the table of the
updates after the literature baseline (number, date, description, share, and what it
resolved; an update with a layer on the map also has a dot of the colour of its layer, in
the table and in the list). The share is a by-product of the kernel-checked grid: the
cells that no certificate removes form a neighbourhood of `∂M` at the resolution of the
grid, which shrinks with the depth and measures no progress on Problems 4.3 and 4.4. The
literature baseline (update 0) is the state of the literature: MLC follows from Dudko's
Problems 4.3 and 4.4, which stay open. The area `4π` only normalizes the scale of the
share, the area of the parameters that the published theorems leave open is unknown
(expected to be small, without a certificate), and the baseline row claims no unresolved
area; no reduction factor relative to the literature is shown anywhere. The map marks the
parameters certified by each update: `map_raster.py` composites the coverage masks of the
grids (2080 × 2000 pixels, from `docs/progress/layers`) into one PNG that the SVG
embeds, since the 600 000 certified rectangles of the grids as vector paths weigh 18 MB and
some browsers draw nothing for them; the axes, the disks and the numerical outline of `∂M`
stay vector. Texts with formulas are written with `$...$` TeX math and rendered as TeX for
the report and as HTML for the page. The same data feeds `docs/mlc_progress.tex` through
`progress_commits.tex`, `progress_routes.tex`, `progress_types.tex`, and `progress_map.svg`. The "Planned
residual reduction" of the routes is a relative planning prior for the set that the
published theorems leave open and has no relation to the area of the grid. The share
`100%` corresponds to `R = ∅` (MLC), but a nonempty `R` of measure zero would also give
it, so the share is read with the count of open root obligations.

**The progress ledger.** The table and the map are stored in the repository tree, so that
they survive squash merges, rebases and deleted branches, and the report needs no Git
history or tags:

```text
docs/progress/ledger.json        an array of updates, oldest first
docs/progress/layers/<id>*.png   8-bit grayscale coverage masks (2080 × 2000 pixels)
```

An entry has a stable `id`, the `timestamp` of the decision, the `subject` (the title),
an `area_note` (a sentence for the column "What it resolved"), the metrics of the tree
(`grid`, `area_exact`, `debt_percent`, `area_upper_percent`, `area_symbols`,
`open_frontier`, `open_lemmas`, `classes_share`, `milestone_weight`, `milestones`) and,
for an update that certifies grid cells, a `layer`: the colour of its dot and its masks.
The number of an update is its position (the baseline is 0), computed when the page is
rendered. The mask `<id>.png` marks the cells that the update certified inside `M`; the
latest grid update also keeps `<id>.open.png`, the cells that its grid leaves open. A
sample `v` of a mask is the coverage `v / 255` of the pixel. The three grids of the first
classifier (updates 7–9, before the Taylor models) exist only as their stored masks.
`progress_ledger.py` holds the library and the command line:

```sh
python3 scripts/progress_ledger.py add --title "Refine the grid to depth 14" --note "Depth 14 for Re c < 0."
python3 scripts/progress_ledger.py add --title "..." --staged      # metrics of the staged tree
python3 scripts/progress_ledger.py add --title "..." --date 2026-12-01   # an earlier decision date
python3 scripts/progress_ledger.py check                           # the ledger lags the tree?
python3 scripts/progress_ledger.py list
```

`add` computes the metrics of the working tree (or of the staged tree), appends an update
with the next colour of the palette when the update lowers the unresolved area of a grid,
writes the masks of that grid from the hint streams of its tiles (`Mlc/GridTiles`), and
removes the mask of the unresolved cells of the previous grid update; it needs `numpy` only
for a grid update. `check` exits with status 1 when the ledger is malformed (a missing mask,
a repeated id) or when its last update differs from the tree in the resolved share, the
milestones, the classes, the open statements or the grid; a change of `PROGRESS_MILESTONES`
or of the catalogue in `programme.py` changes the metrics of the same Lean tree and needs
an update too. The repository hook
(`check_progress.py`, see below) appends the update of a staged Lean commit by itself:
its title is `$PROGRESS_TITLE` or, without it, derived from the new milestones or the depth
of the grid; its note is `$PROGRESS_NOTE`; its date is now; the hook stages `docs/progress`.
A commit that stages only documents and scripts passes unchecked and imports no `numpy`.
`python3 scripts/check_progress.py --ledger` is the consistency check for CI. The committed
report `docs/mlc_progress.pdf` lists the updates. To include a new update in it, stage the Lean
changes, record the update (`progress_ledger.py add --staged ...`), run `make report-pdf`, stage
the PDF and commit; the hook then finds the ledger up to date. When the hook records the update
itself, the PDF stays one update behind until the next `make report-pdf`. A squash
merge brings the entries and the masks of the branch with it. When two branches both
append updates, resolve the conflict of `ledger.json` by keeping both sides in the order
of their dates.

The map is drawn by `map_raster.py`; `make test-scripts` runs `scripts/test_map_raster.py`
(the pixel coverage against a direct computation, the PNG codec),
`scripts/test_progress_ledger.py` (recording, the lag check, a squash merge, the masks, the
numbering and the hook, on temporary repositories) and `scripts/test_typology.py`.

The repository hook runs `scripts/check_progress.py`. A commit that stages Lean
sources (`Mlc.lean`, `Mlc/**/*.lean`) must improve at least one of the certified
resolved share, the share of parameter classes with a Lean certificate and the
dependency-graph milestone debt (which falls when a milestone theorem is added),
and must worsen none of them, before Git accepts it; the hook then records the update
in the ledger. Commits that stage only documents and scripts pass unchecked. The classes
and the statements of the programme for Problems 4.3 and 4.4 are catalogued in
`scripts/programme.py`.

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
needs no proof. The progress tooling reads `gridCells` and `gridDepth` from these files,
and `progress_ledger.py add` replays the hint streams of the current tiles to write the
masks of the layer of a grid update. The note of a grid update in the table is the `--note`
of the update.

## The kernel-checked grid

`Mlc/GridDefs.lean` defines fixed-point first-order models of the critical orbit: for every
parameter `c` of a square, the `n`-th iterate lies within `e` of `m + d (c - c₀)`, where `d` is
the derivative at the center `c₀`. The model follows the phases of the derivative and stays
sharp where a disk enclosure grows by large factors. A square lies outside `M` if the model
leaves the disk of radius 2 after `n` steps, and inside `M` if a moving disk centered at the
model returns into itself after `p` steps, so that every parameter of the square has a bounded
critical orbit. The kernel verifies every hint (`Sq.certify`) and counts the unresolved finest
cells (`verifyTree`); `Mlc/GridTMCertificate.lean` proves that the verified squares lie outside
`M` or inside `M`, so the unresolved cells cover `M ∖ int M` and the same count bounds the area
of every residual set (`unresolved_volume_le_grid`). The upper half-plane is covered by tiles and
the lower half follows by conjugation symmetry. The count is checked by kernel reduction
(`decide +kernel`; the library never uses `native_decide`) in the generated modules `Mlc/GridTiles/G*.lean`,
which import only `Mlc.GridDefs`.

`coarsen_grid.py` replaces the subdivision of a region by one coarser square with a long inside
certificate: near the border of a hyperbolic component a coarse square costs the kernel the same
per unit of area as a fine one. Coarsening the shells changes the modules of most blocks, so its
check is a full rebuild.

The depth-13 grid has 14,420 modules (18.5 MB of source) and about 48 CPU hours of kernel work,
about 13 seconds and 1.4–2.4 GB of memory per module; Lake runs as many modules at once as the
machine has cores, so a machine with little memory needs fewer parallel jobs. The aggregator
`Mlc/GridCertified.lean` needs a thread stack larger than the default of 8 MB (`weakLeanArgs` in
`lakefile.lean`, which stay out of the build trace). The build outputs of the modules are 8 GB
(`.olean` and `.c` files); [continuous integration](../docs/ci.md) keeps them between runs, and
`make seed` publishes the local outputs for the first run after a change of the grid.
