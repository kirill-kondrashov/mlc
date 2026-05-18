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
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.Quadratic.external_ray_map_exists}

project_frontier(MLC.mlc_conjecture)
= {MLC.Quadratic.external_ray_map_exists}
```

## Current Status

The root theorem is now routed through the **theoremized `c = 2` external-ray
seam**:

1. `mlc_conjecture_of_externalRayMapData_two`
2. the packaged root wrapper `mlc_conjecture_of_external_ray_map_exists_two`
3. the single remaining project axiom `MLC.Quadratic.external_ray_map_exists`

This removes the entire explicit Problem 4.3/4.4 / chosen-true bounded-type
frontier from the checked root.

## Remaining Blocker

Only one non-core project axiom remains:

1. `MLC.Quadratic.external_ray_map_exists`

This is the exterior Böttcher inverse / external-ray map existence package.

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

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
