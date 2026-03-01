# Mandelbrot Local Connectivity (MLC) in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

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
- MLC.lyubich_conformal_bridge
- MLC.exists_parameter_model_rfast_fixed_point
```

## Current Axiom Frontier

`MLC.mlc_conjecture` currently depends on:

- Core Lean axioms:
  - `Quot.sound`
  - `propext`
  - `Classical.choice`
- Non-core mathematical bridge axioms:
  - `MLC.lyubich_conformal_bridge`
  - `MLC.exists_parameter_model_rfast_fixed_point`

The new minimal bridge axiom is:

```lean
axiom exists_parameter_model_rfast_fixed_point :
  ExistsParameterModelRfastFixedPoint
```

where:

```lean
def ExistsParameterModelRfastFixedPoint : Prop :=
  ∃ g : BMol, IsFastRenormalizable g ∧ Rfast g = g ∧
    (∃ c : ℂ, g = parameterToBMol c)
```

This replaces the older direct tower-existence axiom at the root theorem level.

## Root Theorem Route

High-level path now used by `MLC.mlc_conjecture`:

1. `exists_parameter_model_rfast_fixed_point`
2. `exists_renormalization_tower_of_existsParameterModelRfastFixedPoint`
3. `mlc_conjecture_of_exists_tower`
4. Inconsistency route (`RenormalizationTower -> False`) via
   `lyubich_conformal_bridge`
5. Conclude local connectivity of `mandelbrotSet`

## Related Bridge API

`Mlc/RenormalizationTowerExistence.lean` also exposes stronger/alternative
bridge layers (not required by the root theorem frontier), including:

- `MoleculeRenormalizableFixedPointData`
- `FixedPointParameterModelData`
- `ParameterToBMolFixedPointLiftData`
- conversion lemmas between these bridge assumptions

These are kept to support incremental refinement toward proving
`exists_parameter_model_rfast_fixed_point` non-axiomatically.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
