# Mandelbrot Local Connectivity (MLC) in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/) *(GitHub Pages deploys from `main`; the checked-in `site/` directory reflects the current branch state.)*

A Lean 4 formalization of the Mandelbrot local connectivity statement
`MLC.mlc_conjecture`.

## Quick Start

```bash
make build
make check
```

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.Quadratic.bottcher_package
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice, MLC.Quadratic.bottcher_package}

project_frontier(MLC.mlc_conjecture) = {MLC.Quadratic.bottcher_package}
```

## Current Status

The checked root is now routed through a **single packaged theorem-facing
Böttcher/external-ray seam**, not through the older tower / Lyubich /
Problem 4.5 detours.

1. `mlc_conjecture_of_externalRayMapData_two`
2. the packaged root wrapper `mlc_conjecture_of_external_ray_map_exists_two`
3. the single theorem-facing package axiom `MLC.Quadratic.bottcher_package`

So the earlier explicit frontier

1. para-puzzle connectedness,
2. residual virtual near-Molecule data,
3. chosen-true primitive bridge data,
4. bounded-type primitive Feigenbaum inputs,

has been pushed off the checked root. Those routes still exist in the repo, but
they are no longer part of `Axioms(MLC.mlc_conjecture)`.

## Remaining Blocker

One non-core project axiom remains:

1. `MLC.Quadratic.bottcher_package`

It lives in the theorem-facing Böttcher/external-ray surface in
`Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean` and packages:

1. the theorem-facing Böttcher coordinate interface,
2. the exterior inverse data,
3. the `c = 2` normalization fact excluding the value `1` on `K(2)`.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Elimination Target

The final reduction target is now the single packaged statement:

1. replace `MLC.Quadratic.bottcher_package` by a constructive basin-valued
   normalized Böttcher/external-ray theorem at `c = 2`

## Repository Snapshot

1. `make build`, `make check`, and `./scripts/verify_output.sh` pass.
2. `plan/` has been pruned to the single live frontier file
   `PLAN_04_lyubich_bridge.md`.
3. The current root-facing story is therefore simple: one remaining axiom, one
   remaining elimination target.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
