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
- MLC.finite_branch_local_connectivity
- MLC.problem43_pseudoSiegelAPrioriBounds
- MLC.problem44_virtualMolecule
- MLC.problem45_virtualNearMoleculeRenormalization
```

## Current State

`MLC.mlc_conjecture` now depends on a split non-core frontier:

- `MLC.finite_branch_local_connectivity`
- `MLC.problem43_pseudoSiegelAPrioriBounds`
- `MLC.problem44_virtualMolecule`
- `MLC.problem45_virtualNearMoleculeRenormalization`

The only other axioms in the root proof are the standard Lean core ones:

- `Quot.sound`
- `propext`
- `Classical.choice`

## Root Route

The top theorem is currently routed as:

1. `finite_branch_local_connectivity : FiniteBranchLocalConnectivityData`
2. `problem43_pseudoSiegelAPrioriBounds : Problem43PseudoSiegelAPrioriBoundsData`
3. `problem44_virtualMolecule : Problem44VirtualMoleculeData`
4. `problem45_virtualNearMoleculeRenormalization :
   Problem45VirtualNearMoleculeRenormalizationData`
5. `mlc_conjecture_of_problem43_44_45_data`
6. local connectivity of `mandelbrotSet`

The current Lean-facing split is:

```lean
def Problem43PseudoSiegelAPrioriBoundsData : Prop :=
  MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget

def Problem44VirtualMoleculeData : Prop :=
  IRNoTowerImpliesPrimitiveData

def Problem45VirtualNearMoleculeRenormalizationData : Prop :=
  Problem43PseudoSiegelAPrioriBoundsData →
    VirtualJuliaSatelliteLocalConnectivityData
```

## Connection to Problems 4.3, 4.4, and 4.5

The IR / satellite side is now expressed through separate seams:

- **Problem 4.3**:
  `problem43_pseudoSiegelAPrioriBounds`
  packages the pseudo-Siegel a priori bounds in the remaining unbounded
  satellite ql cases. At the current theorem interface, this is represented by
  the uniform conformal lower-bound Track-2 target.
- **Problem 4.4**:
  `problem44_virtualMolecule`
  packages the Virtual Molecule near-degenerate regime. At the current theorem
  interface, this is represented by `IRNoTowerImpliesPrimitiveData`.
- **Problem 4.5**:
  `problem45_virtualNearMoleculeRenormalization`
  packages the primitive-first ql / virtual near-Molecule case. At the current
  seam, it upgrades the Problem 4.3 control to the satellite local-connectivity
  endpoint.

This makes the paper-facing route explicit in Lean:

- `noTowerPrimitive_of_problem44`
- `satelliteLC_of_problem43_problem45`

The point of contact with the Kahn-Lyubich strategy is still the same:

> Jointly with Kahn and Lyubich, we put forward a strategy to approach Problem
> 4.4 by considering partially invariant virtual Julia sets of `M(s)`. A
> posteriori, bounds for virtual Julia sets can be deduced by assuming uniform
> hyperbolicity of the renormalization associated with `M`; the strategy is to
> develop such control a priori.

In this branch, that quoted program is no longer represented by one coarse
`virtual_julia_strategy_data` package. It is represented by the split
Problem 4.3 / 4.4 / 4.5 seams above.

## Finite Branch

`finite_branch_local_connectivity` is intentionally separate in this pass.
It is not part of the virtual Julia / virtual Molecule program; it remains the
finite-branch payload needed to keep the root theorem green while the
IR/satellite side is split into more specific statements.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
