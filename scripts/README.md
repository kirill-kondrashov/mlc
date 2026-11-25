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
unresolved set `R` as a number, a table of the commits after the merge base
with `origin/main` (date, commit, description, share, and what it resolved),
and a vector map of `M` marking the parameters certified by each commit. The
same data feeds `docs/mlc_progress.tex` through `progress_commits.tex`,
`progress_routes.tex`, and `progress_map.svg`. Route probabilities are planning
priors, not mathematical claims. The share `100%` corresponds to `R = ∅` (MLC),
but a nonempty `R` of measure zero would also give it, so the share is read
with the count of open root obligations.

The repository hook runs `scripts/check_progress.py`. A staged proof-progress
commit must strictly increase the certified resolved share and must not increase
the dependency-graph milestone debt before Git accepts it.

`generate_grid_tiles.py` regenerates `Mlc/GridTiles/Part*.lean` and
`Mlc/GridCertified.lean` from the parameters in `Mlc/GridParams.lean`. It asks
`grid_tile_values.lean` for the cost and unresolved-cell count of every root
square, distributes the expensive squares over independent modules (each
checked by `decide +kernel`), and writes the aggregating theorem. The progress
tooling reads `gridCells` and `gridFuel` from these files.
`export_grid_regions.lean` (repository root) lists the certified squares for
the map in the Progress tab.
