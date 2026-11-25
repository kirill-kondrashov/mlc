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
`site/` with HTML, JavaScript, JSON, and `progress.svg`.

The **Progress** tab uses the same SVG embedded by the LaTeX report. It contains
commit history for the formalization-debt proxy and a separate planning chart
for candidate proof routes. Route probabilities are explicitly planning
priors, not mathematical claims.

The repository hook runs `scripts/check_progress.py`. A staged proof-progress
commit must strictly decrease both the dependency-graph milestone debt and the
certified residual-area upper envelope before Git accepts it.
