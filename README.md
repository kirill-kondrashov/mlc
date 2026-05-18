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

The checked root is now routed through the **theoremized `c = 2` external-ray
seam plus the reclaimed theorem-facing `Quadratic.bottcher_map` interface**, not
through the older tower / Lyubich / Problem 4.5 detours.

1. `mlc_conjecture_of_externalRayMapData_two`
2. the packaged root wrapper `mlc_conjecture_of_external_ray_map_exists_two`
3. the theorem-facing coordinate package axiom `MLC.Quadratic.bottcher_coordinate_data`
4. the normalization axiom `MLC.bottcher_map_eq_one_not_mem_K_two`
5. the residual external-ray package axiom `MLC.Quadratic.external_ray_map_exists_two`

So the earlier explicit frontier

1. para-puzzle connectedness,
2. residual virtual near-Molecule data,
3. chosen-true primitive bridge data,
4. bounded-type primitive Feigenbaum inputs,

has been pushed off the checked root. Those routes still exist in the repo, but
they are no longer part of `Axioms(MLC.mlc_conjecture)`.

## Remaining Blocker

Three non-core project axioms remain:

1. `MLC.Quadratic.bottcher_coordinate_data`
2. `MLC.bottcher_map_eq_one_not_mem_K_two`
3. `MLC.Quadratic.external_ray_map_exists`
   (global all-parameter version)

and the checked root currently depends on the specialized package

1. `MLC.Quadratic.bottcher_coordinate_data`
2. `MLC.bottcher_map_eq_one_not_mem_K_two`
3. `MLC.Quadratic.external_ray_map_exists_two`

These live in the theorem-facing Böttcher/external-ray surface in
`Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean` and the root normalization
wrapper in `Mlc/MainConjecture.lean`.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Elimination Target

The final reduction target is now the three-piece theorem-facing package:

1. replace `MLC.Quadratic.bottcher_coordinate_data` by a constructive
   theorem-facing Böttcher coordinate interface
2. replace `MLC.bottcher_map_eq_one_not_mem_K_two` by a theorem from that interface
3. replace `MLC.Quadratic.external_ray_map_exists_two` by a constructive
   external-ray / Böttcher inverse theorem at `c = 2`

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
