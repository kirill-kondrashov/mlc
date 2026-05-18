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
- MLC.Quadratic.bottcher_coordinate_data
- MLC.bottcher_map_eq_one_not_mem_K_two
- MLC.Quadratic.external_ray_map_exists_two
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.Quadratic.bottcher_coordinate_data,
   MLC.bottcher_map_eq_one_not_mem_K_two,
   MLC.Quadratic.external_ray_map_exists_two}

project_frontier(MLC.mlc_conjecture)
= {MLC.Quadratic.bottcher_coordinate_data,
   MLC.bottcher_map_eq_one_not_mem_K_two,
   MLC.Quadratic.external_ray_map_exists_two}
```

## Current Status

The checked root is now routed through the **minimal connected theorem-facing
Böttcher frontier** rather than one oversized package axiom, and still avoids
the older tower / Lyubich / Problem 4.5 detours.

1. `mlc_conjecture_of_externalRayMapData_two`
2. the packaged root wrapper `mlc_conjecture_of_external_ray_map_exists_two`
3. the coordinate-data seam `MLC.Quadratic.bottcher_coordinate_data`
4. the normalization seam `MLC.bottcher_map_eq_one_not_mem_K_two`
5. the `c = 2` external-ray seam `MLC.Quadratic.external_ray_map_exists_two`

So the earlier explicit frontier

1. para-puzzle connectedness,
2. residual virtual near-Molecule data,
3. chosen-true primitive bridge data,
4. bounded-type primitive Feigenbaum inputs,

has been pushed off the checked root. Those routes still exist in the repo, but
they are no longer part of `Axioms(MLC.mlc_conjecture)`.

## Remaining Blocker

The minimal connected Böttcher frontier currently has three non-core project
axioms:

1. `MLC.Quadratic.bottcher_coordinate_data`
2. `MLC.bottcher_map_eq_one_not_mem_K_two`
3. `MLC.Quadratic.external_ray_map_exists_two`

These are the three connected branches the checked root actually uses:

1. theorem-facing coordinate data (norm and continuity access),
2. the root-only normalization exclusion at `c = 2`,
3. the root-only exterior inverse package at `c = 2`.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Elimination Target

The final constructive target is still the basin-valued normalized
Böttcher/external-ray theorem at `c = 2`; proving it would eliminate all three
connected frontier axioms at once.

## Repository Snapshot

1. `make build`, `make check`, and `./scripts/verify_output.sh` pass.
2. `plan/` has been pruned to the single live frontier file
   `PLAN_04_lyubich_bridge.md`.
3. The current root-facing story is therefore simple: one remaining mathematical
   elimination target, exposed as three connected theorem-facing assumptions.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
