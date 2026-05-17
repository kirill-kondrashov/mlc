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

## Current Status

The remaining project axiom is still entirely concentrated in **Problem 4.5**:
virtual near-Molecule / primitive-first ql renormalization.

The active reduction now isolates a bounded-type primitive subproblem. The code
contains:

- bounded-type sidecar interfaces in `Mlc/MainConjecture.lean`
- direct primitive routes from modulus lower bounds to shrinkage and local
  connectivity
- a literature-matched primitive Feigenbaum surface

The current minimal missing theorem is:

```lean
eventualPrimitiveModulusLowerBoundFromPrimitiveFeigenbaum :
  EventualPrimitiveModulusLowerBoundFromPrimitiveFeigenbaumData
```

This is the weakest placeholder currently needed by the downstream proof chain.
It represents eventual beau bounds in the bounded-type primitive Feigenbaum
case.

## Remaining Blocker

No theorem in this repository or in the vendored `molecule-conjecture` package
currently proves the eventual bounded primitive modulus statement above.

The downstream chain is already in place:

```text
eventual primitive Feigenbaum modulus bounds
-> primitive shrinkage
-> primitive local connectivity
-> bounded-type Problem 4.5 slice
```

So the unresolved gap is no longer shrinkage, no longer local connectivity, and
no longer an all-level modulus bound. It is specifically the missing proof of
eventual bounded primitive beau bounds.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Elimination Target

To remove `MLC.problem45_virtualNearMoleculeRenormalization`, the repository
still needs an axiom-free provider of either:

- `IRLocallyConnectedData`, or
- `IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData`

The current research route approaches this by first theoremizing the bounded
primitive Feigenbaum beau-bounds step and then shrinking the remaining Problem
4.5 residue.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
