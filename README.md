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
- MLC.virtual_julia_strategy_data
```

## Current State

`MLC.mlc_conjecture` currently depends on exactly one non-core project axiom:

- `MLC.virtual_julia_strategy_data`

The only other axioms in the root proof are the standard Lean core ones:

- `Quot.sound`
- `propext`
- `Classical.choice`

## Root Route

The top theorem is currently routed as:

1. `virtual_julia_strategy_data : VirtualJuliaStrategyData`
2. `mlc_conjecture_of_virtualJuliaStrategyData`
3. local connectivity of `mandelbrotSet`

The package carried by the single root axiom is:

```lean
structure VirtualJuliaStrategyData : Prop where
  finiteLC : FiniteBranchLocalConnectivityData
  noTowerPrimitive : IRNoTowerImpliesPrimitiveData
  satelliteLC : VirtualJuliaSatelliteLocalConnectivityData

axiom virtual_julia_strategy_data : VirtualJuliaStrategyData
```

## What is connected to the Kahn-Lyubich virtual Julia strategy

The part directly connected to the strategy described jointly with Kahn and
Lyubich is the **satellite / infinitely renormalizable side** of
`VirtualJuliaStrategyData`, especially:

- `satelliteLC : VirtualJuliaSatelliteLocalConnectivityData`
- `noTowerPrimitive : IRNoTowerImpliesPrimitiveData`

These fields are where the repository packages the missing control behind the
quoted plan:

- partially invariant virtual Julia sets of the satellite copies `M(s)`
- control of the critical orbit only up to the relevant first returns
- virtual Molecule scales from the chain
  `M = M(0) ⊋ M(1) ⊋ ... ⊋ M(n+1)`
- the a priori bounds needed for the remaining satellite / near-degenerate
  infinitely-renormalizable cases

In other words, the current single axiom is **not** standing for an
external-ray inversion statement. It is standing for the missing a priori
virtual Julia / virtual Molecule control that should yield the satellite local
connectivity endpoint and the no-tower-implies-primitive classification needed
by the root proof.

This is the point of contact with the paper passage:

> Jointly with Kahn and Lyubich, we put forward a strategy to approach Problem
> 4.4 by considering partially invariant virtual Julia sets of `M(s)`. A
> posteriori, bounds for virtual Julia sets can be deduced by assuming uniform
> hyperbolicity of the renormalization associated with `M`; the strategy is to
> develop such control a priori.

Here, the formalization treats that missing control as the remaining
root-facing seam.

## What is *not* the Kahn-Lyubich seam

`finiteLC : FiniteBranchLocalConnectivityData` is included in the same package
only to keep the top theorem on a single project axiom. It is not the virtual
Julia / virtual Molecule part of the program.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
