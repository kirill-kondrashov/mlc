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
- MLC.lyubich_conformal_bridge_bMol
- Molecule.molecule_local_fixed_seed
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.lyubich_conformal_bridge_bMol,
   Molecule.molecule_local_fixed_seed}

project_frontier(MLC.mlc_conjecture)
= {MLC.lyubich_conformal_bridge_bMol}

Problem45VirtualNearMoleculeRenormalizationData
= IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData
```

## Current Status

The root theorem is now wired through the **new true-modulus bounded-type
primitive route** instead of the old single Problem 4.5 axiom. Concretely, the
graph now passes through:

1. a chosen true conformal-modulus handle,
2. type-wise real bounds,
3. type-wise Grötzsch promotion,
4. affine normalization comparison,
5. a bridge back to the current legacy primitive eventual consumer path,
6. a Feigenbaum-faithful bounded-type constructive Problem 4.5 slice,
7. and a separate residual open seam for Problems 4.3/4.4.

So the theorem graph now exposes the latest primitive Feigenbaum findings
directly at the root, at the cost of a wider axiom frontier.

## Remaining Blocker

The unresolved mathematics is now split into two explicit external inputs:

1. `PrimitiveFeigenbaumTypewiseRealBoundsGlobalData`
2. `PrimitiveFeigenbaumTypewiseGrotzschPromotionGlobalData`

These are exactly the Step-2 / Step-3 analytic theorems needed to turn bounded
primitive combinatorics into type-wise positive constants `ε_τ`, after which the
finite-minimum step and the bounded-type constructive cutover are already
formalized.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Elimination Target

To eliminate the final repository-local frontier, the remaining root-facing
axiom to replace is:

- the BMol-level Lyubich-to-conformal bridge `MLC.lyubich_conformal_bridge_bMol`.

The root still also depends on the upstream Molecule-package axiom
`Molecule.molecule_local_fixed_seed`, because the current one-axiom route uses
the package’s zero-argument local fixed-point witness to produce a BMol
renormalization tower.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
