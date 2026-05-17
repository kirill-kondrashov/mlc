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
- MLC.problem45_virtualNearMoleculeRenormalization
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.problem45_virtualNearMoleculeRenormalization}

project_frontier(MLC.mlc_conjecture)
= {MLC.problem45_virtualNearMoleculeRenormalization}

Problem45VirtualNearMoleculeRenormalizationData
= IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData
```

## Remaining Problem

No axiom-free theorem in the repository yields the payload needed to remove
`MLC.problem45_virtualNearMoleculeRenormalization`.

Mathematical content: **Problem 4.5** / virtual near-Molecule, i.e. the
primitive-first ql case through the canonical satellite chain
`M = M(0) ⊋ M(1) ⊋ ... ⊋ M(n+1)`.

Symbol dictionary:

- $M$: the ambient copy of the Mandelbrot set containing the primitive-first
  ql renormalization data
- $M(k)$: the $k$-th copy in the canonical satellite chain, with
  $0 \le k \le n+1$
- $M = M(0) \supsetneq M(1) \supsetneq \cdots \supsetneq M(n+1)$: strict
  nesting of satellite copies
- $n \in \mathbb{N}$: length of the virtual near-Molecule stage before the
  terminal primitive copy
- ql: quadratic-like

## Obstruction

Available reroutes reintroduce older project axioms:

1. `ir_locally_connected_seam`
2. `irLocallyConnectedData_of_tower` via `InconsistencyRoute` and
   `lyubich_conformal_bridge`
3. `exists_renormalization_tower_of_molecule_bridge_axioms` via
   `molecule_renormalizable_fixed_point_data` and
   `fixedPoint_parameter_model_data`

## Elimination Target

Required constructive theorem:

- `IRLocallyConnectedData`, or
- `IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData`

with no use of older axiom-backed routes.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
