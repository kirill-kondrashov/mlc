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
- MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected
- MLC.chosenTrueConformalModulusData
- MLC.primitiveFeigenbaumTypewiseRealBoundsAxiom
- MLC.chosenTruePrimitiveFeigenbaumTypewiseGrotzschPromotionAxiom
- MLC.chosenTruePrimitiveFeigenbaumAffineNormalizationComparisonAxiom
- MLC.chosenTruePrimitiveEventualBridgeAxiom
- MLC.feigenbaumConstructiveBoundedTypeProblem45Axiom
- MLC.residualOpenVirtualNearMoleculeAxiom
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected,
   MLC.chosenTrueConformalModulusData,
   MLC.primitiveFeigenbaumTypewiseRealBoundsAxiom,
   MLC.chosenTruePrimitiveFeigenbaumTypewiseGrotzschPromotionAxiom,
   MLC.chosenTruePrimitiveFeigenbaumAffineNormalizationComparisonAxiom,
   MLC.chosenTruePrimitiveEventualBridgeAxiom,
   MLC.feigenbaumConstructiveBoundedTypeProblem45Axiom,
   MLC.residualOpenVirtualNearMoleculeAxiom}

project_frontier(MLC.mlc_conjecture)
= {MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected,
   MLC.chosenTrueConformalModulusData,
   MLC.primitiveFeigenbaumTypewiseRealBoundsAxiom,
   MLC.chosenTruePrimitiveFeigenbaumTypewiseGrotzschPromotionAxiom,
   MLC.chosenTruePrimitiveFeigenbaumAffineNormalizationComparisonAxiom,
   MLC.chosenTruePrimitiveEventualBridgeAxiom,
   MLC.feigenbaumConstructiveBoundedTypeProblem45Axiom,
   MLC.residualOpenVirtualNearMoleculeAxiom}

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

To shrink the current frontier again, the repository needs to replace the new
root-facing axioms by proofs of:

- the type-wise real-bounds theorem,
- the type-wise Grötzsch promotion theorem,
- the Feigenbaum constructive bounded-type Problem 4.5 slice,
- and the residual open 4.3/4.4 seam.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
