# MLC Scripts

Utility scripts for Lean dependency-graph generation and local serving. They
use only the Python standard library.

The interactive graph uses the same site generator and renderer as `main`:

```sh
make graphs
make serve
```

`export_dependencies.lean` supplies constants from elaborated types and proofs.
Generation checks reachability, acyclicity and the axiom frontier, then writes
`site/` with HTML, JavaScript and JSON. No static graph image is generated.
