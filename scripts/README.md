# MLC Scripts

Utility scripts for Lean dependency-graph generation, progress reporting, and
local serving. They use only the Python standard library.

The interactive graph uses the same site generator and renderer as `main`:

```sh
make graphs
make serve
```

`export_dependencies.lean` supplies constants from elaborated types and proofs.
Generation checks reachability, acyclicity and the axiom frontier, then writes
`site/` with HTML, JavaScript, JSON, and the progress files.

`progress_report.py` computes the progress numbers from Git history. The
**Progress** tab shows the certified resolved share `100% − μ*(R) / 4π` of the
unresolved set `R` as a number, a table of the commits after the literature
baseline (date, commit, description, share, and what it resolved), and a vector
map of `M` marking the parameters certified by each commit. The literature
baseline is the first commit of the history whose `RootInput` has exactly the
fields `Problem43PseudoSiegelAPrioriBoundsData` and
`Problem44VirtualMoleculeData`, found by a binary search over the first-parent
history; its row lists the two open problems. Every grid commit gets its own
colour: `export_grid_regions.lean pmax J fuel` reproduces the squares of its
grid, and the report uses them only when the number of unresolved cells equals
the count that the commit proved. Texts with formulas are written with
`$...$` TeX math and rendered as TeX for the report and as HTML for the page.
The same data feeds `docs/mlc_progress.tex` through `progress_commits.tex`,
`progress_routes.tex`, and `progress_map.svg`. Route probabilities are planning
priors. The share `100%` corresponds to `R = ∅` (MLC), but a nonempty `R` of
measure zero would also give it, so the share is read with the count of open
root obligations.

The repository hook runs `scripts/check_progress.py`. A staged proof-progress
commit must strictly increase the certified resolved share and must not increase
the dependency-graph milestone debt before Git accepts it.

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
