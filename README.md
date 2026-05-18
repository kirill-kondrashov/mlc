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
- MLC.Quadratic.external_ray_map_exists
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.Quadratic.external_ray_map_exists}

project_frontier(MLC.mlc_conjecture)
= {MLC.Quadratic.external_ray_map_exists}
```

## Current Status

The checked root is now routed through the **theoremized `c = 2` external-ray
seam**, not through the older tower / Lyubich / Problem 4.5 detours.

1. `mlc_conjecture_of_externalRayMapData_two`
2. the packaged root wrapper `mlc_conjecture_of_external_ray_map_exists_two`
3. the single remaining project axiom `MLC.Quadratic.external_ray_map_exists`

So the earlier explicit frontier

1. para-puzzle connectedness,
2. residual virtual near-Molecule data,
3. chosen-true primitive bridge data,
4. bounded-type primitive Feigenbaum inputs,

has been pushed off the checked root. Those routes still exist in the repo, but
they are no longer part of `Axioms(MLC.mlc_conjecture)`.

## Remaining Blocker

Only one non-core project axiom remains:

1. `MLC.Quadratic.external_ray_map_exists`

This is the exterior Böttcher inverse / external-ray map existence package from
`Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Elimination Target

The final reduction target is now singular:

1. replace `MLC.Quadratic.external_ray_map_exists` by a constructive
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
