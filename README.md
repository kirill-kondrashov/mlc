# Mandelbrot Local Connectivity in Lean 4

[![Lean CI](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository contains a compact Lean 4 formalization of the Mandelbrot
local-connectivity conjecture, conditional on two explicit categorical inputs.

## Target

For $c,z\in\mathbb C$, write $f_c(z)=z^2+c$ and let $\mathcal M$ be the
Mandelbrot set. The canonical root theorem is categorical:

```lean
MLC.Categorical.categorical_mlc_conjecture :
  MLC.Categorical.MLCConjecture
```

Here `MLC.Categorical.MLCConjecture` is local connectedness of the object
`TopCat.of MLC.mandelbrotSet`. The compatibility theorem

```lean
MLC.mlc_conjecture : LocallyConnectedSpace MLC.mandelbrotSet
```

is equivalent to it by `MLC.Categorical.mlc_conjecture_iff_categorical`.

The parameter pieces used by the proof are
$A_n(c)=\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\}$ and
$T_n(c)=A_n(c)\cap\mathcal M$.

## Checked Lean state

Both root formulations are `sorry`-free and use the same project-level axioms:

1. `MLC.green_sublevel_intersection_categorical`:
   connectedness of $T_n(c)$ in the genuine straddling case
   $A_n(c)\not\subseteq\mathcal M$.
2. `MLC.residualOpenVirtualNearMoleculeAxiom`: a categorical product witness
   for the root-facing conjunction of Dudko--Lyubich Problems 4.3 and 4.4
   (pseudo-Siegel bounds and the virtual near-Molecule classification).

The categorical parameter input is equivalent to its old set-theoretic form by
`greenSublevelIntersectionCategoricalData_iff`. The residual product input is
equivalent to the original conjunction by
`categoricalResidualOpenVirtualNearMoleculeData_iff`.

The remaining reported axioms are Lean foundations:

```text
Quot.sound
propext
Classical.choice
```

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.residualOpenVirtualNearMoleculeAxiom
- MLC.green_sublevel_intersection_categorical
```

## Proved core

- $K_c$ is connected for $c\in\mathcal M$.
- The dynamical Green sublevels $\{z:G_c(z)<2^{-n}\}$ are connected.
- Translation identifies the frozen parameter pieces with those sublevels.
- The subset stratum of $T_n(c)$ is connected without an axiom.
- Yoccoz shrinking and the Molecule bridge assemble local connectivity.
- Retained glue forwards to standard Mathlib/Yoccoz APIs, including
  `locallyConnectedSpace_iff_connected_subsets`, `Set.image_iInter`,
  `integral_biUnion_finset`, `modulus`, and `groetzsch_criterion`.

`check_axioms.lean` checks both `MLC.mlc_conjecture` and
`MLC.Categorical.categorical_mlc_conjecture` and requires identical axiom
frontiers. The complete checked Lean source pass is warning-free.

## Categorical migration

The root reformulation uses `TopCat` and its over-category over the ambient
parameter plane:

- `Mlc/CategoricalTopologicalApproximation.lean` treats approximations as
  objects of `Over (TopCat.of ℂ)`, the over-category over $\mathbb C$,
  intersections as categorical pullbacks, and
  nested approximations as opposite-indexed diagrams with a universal limit.
- `Mlc/CategoricalRoot.lean` defines the categorical MLC object, root theorem,
  and equivalence with the compatibility theorem.
- `Mlc/CategoricalMandelbrot.lean` gives the boundary, interior, ordinary
  subspace presentations, a deliberately finer boundary topology, and the
  parameter-puzzle tower.
- `Mlc/CategoricalResidual.lean` presents the two residual renormalization
  inputs as a binary product in `Type`.
- `Mlc/EfimovCategoricalBridge.lean` records an honest conditional
  Efimov/Pacman interface: rigid monoidal tower levels with adjunctions,
  strong Mittag--Leffler data, a graded additive `K_n` shadow with an explicit
  limit-comparison input, compatible `TopCat` realization, and a
  space-holomorphic carving bridge whose source is the proved translated Green
  sublevel rather than an arbitrary connected set.

The categorical presentations are logically equivalent to the two existing
frontier inputs; they do not discharge either open mathematical problem. A
`K_n`-theoretic layer is represented only by the explicit graded additive
interface in `Mlc/EfimovCategoricalBridge.lean`; Mathlib does not currently
provide the stable infinity-categorical or algebraic `K`-theory machinery
needed to instantiate it.

## Validation

```bash
make build
make check
./scripts/verify_output.sh
```

## Core files

| Purpose | Path |
| --- | --- |
| Public root | [`Mlc.lean`](Mlc.lean) |
| Categorical root | [`Mlc/CategoricalRoot.lean`](Mlc/CategoricalRoot.lean) |
| Compatibility root | [`Mlc/Core.lean`](Mlc/Core.lean) |
| Parameter frontier | [`Mlc/ParaPuzzleConnectivity.lean`](Mlc/ParaPuzzleConnectivity.lean) |
| Green-sublevel proof | [`Mlc/GreenSublevelConnectedDirect.lean`](Mlc/GreenSublevelConnectedDirect.lean) |
| Molecule bridge | [`Mlc/MoleculeToParameterShrink.lean`](Mlc/MoleculeToParameterShrink.lean) |
| Categorical warm-up | [`Mlc/CategoricalMandelbrot.lean`](Mlc/CategoricalMandelbrot.lean) |
| Efimov/Pacman interface | [`Mlc/EfimovCategoricalBridge.lean`](Mlc/EfimovCategoricalBridge.lean) |
| Axiom checker | [`check_axioms.lean`](check_axioms.lean) |

## Dependencies

- [Lean 4](https://github.com/leanprover/lean4)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.28.0`.
