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
- MLC.lyubich_conformal_bridge_bMol
- Molecule.molecule_local_fixed_seed
```

## Current Axiom Frontier

`MLC.mlc_conjecture` currently depends on:

- Core Lean axioms:
  - `Quot.sound`
  - `propext`
  - `Classical.choice`
- Non-core mathematical bridge axioms:
  - `MLC.lyubich_conformal_bridge_bMol`
  - `Molecule.molecule_local_fixed_seed`

The BMol-level Lyubich bridge axiom is:

```lean
axiom lyubich_conformal_bridge_bMol (g : BMol) (T : RenormalizationTower g) :
  LyubichConformalBridgeBMol g T
```

The Molecule-side root bridge is now imported theoremically from upstream:

```lean
theorem exists_rfast_fixed_point_of_molecule_conjecture_refined :
  ∃ g : BMol, IsFastRenormalizable g ∧ Rfast g = g
```

## Root Theorem Route

High-level path now used by `MLC.mlc_conjecture`:

1. `Molecule.molecule_local_fixed_seed` (upstream)
2. `exists_rfast_fixed_point_of_molecule_conjecture_refined`
3. `exists_renormalizationTower_of_molecule_conjecture_refined`
4. `mlc_conjecture_of_exists_tower_bMol`
5. BMol inconsistency route (`RenormalizationTower g -> False`) via
   `lyubich_conformal_bridge_bMol`
6. Conclude local connectivity of `mandelbrotSet`

## Related Bridge API

`Mlc/RenormalizationTowerExistence.lean` also exposes stronger/alternative
bridge layers (not required by the root theorem frontier), including:

- `MoleculeRenormalizableFixedPointData`
- `FixedPointParameterModelData`
- `ParameterToBMolFixedPointLiftData`
- conversion lemmas between these bridge assumptions

These are kept to support incremental refinement toward proving
the stronger parameter-model bridges non-axiomatically.

Note: the upstream zero-argument Molecule export currently relies on weakened
contract realignments; this repository integrates that API as-is and keeps the
stronger bridge interfaces for future hardening.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
