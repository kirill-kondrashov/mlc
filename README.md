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
- MLC.problem43_pseudoSiegelAPrioriBounds
- MLC.problem44_virtualMolecule
- MLC.problem45_virtualNearMoleculeRenormalization
```

## Current Axiom Frontier

The **intended** root frontier for `MLC.mlc_conjecture` is exactly three
non-core project axioms:

- `MLC.problem43_pseudoSiegelAPrioriBounds`
- `MLC.problem44_virtualMolecule`
- `MLC.problem45_virtualNearMoleculeRenormalization`

The only other axioms in the root proof are the standard Lean core ones:

- `Quot.sound`
- `propext`
- `Classical.choice`

## Root Theorem Route

The top theorem is intended to be assembled as:

1. finite branch via the constructive provider
   `finite_lc_provider_of_motionHyp`
2. with **no additional project-level finite-branch axioms**
3. Problem 4.4 via `problem44_virtualMolecule`
4. Problems 4.3 and 4.5 via
   `problem43_pseudoSiegelAPrioriBounds` and
   `problem45_virtualNearMoleculeRenormalization`
5. `mlc_conjecture_of_problem43_44_45_data`
6. local connectivity of `mandelbrotSet`

At the Lean interface level, the remaining IR/satellite seams are:

```lean
def Problem43PseudoSiegelAPrioriBoundsData : Prop :=
  MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget

def Problem44VirtualMoleculeData : Prop :=
  IRNoTowerImpliesPrimitiveData

def Problem45VirtualNearMoleculeRenormalizationData : Prop :=
  Problem43PseudoSiegelAPrioriBoundsData →
    VirtualJuliaSatelliteLocalConnectivityData
```

## Remaining Problems in Mathematical Terms

The current frontier is meant to isolate the genuinely unresolved mathematics,
rather than hide it behind one coarse package.

| Lean axiom | Mathematical content |
| --- | --- |
| `problem43_pseudoSiegelAPrioriBounds` | **Problem 4.3**: obtain pseudo-Siegel a priori bounds in the remaining unbounded satellite ql cases. In practice this means uniform geometric control on the relevant satellite renormalizations, encoded here by a uniform conformal lower-bound target. |
| `problem44_virtualMolecule` | **Problem 4.4**: treat the virtual Molecule near-degenerate regime. Mathematically, this is the step that rules out the remaining infinitely renormalizable non-satellite behavior by forcing the no-tower case into the primitive branch. |
| `problem45_virtualNearMoleculeRenormalization` | **Problem 4.5**: handle the primitive-first ql situation through the canonical satellite chain `M = M(0) ⊋ M(1) ⊋ ... ⊋ M(n+1)`. At the current seam, this turns the bounds from Problem 4.3 into the satellite local-connectivity endpoint. |

The finite-branch blockers that still must be removed, but are **not** accepted
as part of the root frontier, are:

1. `Quadratic.para_puzzle_piece_inter_mandelbrot_connected`

## Relation to the Kahn-Lyubich Virtual Julia Strategy

The IR/satellite part of the frontier is intended to match the strategy
described jointly with Kahn and Lyubich: control partially invariant virtual
Julia sets associated with the satellite copies `M(s)` and develop that control
**a priori**, rather than deducing it afterward from an assumed hyperbolic
picture.

Concretely:

- **Problem 4.3** is the a priori bounds problem in the remaining unbounded
  satellite cases.
- **Problem 4.4** is the virtual Molecule / near-degenerate regime.
- **Problem 4.5** is the primitive-first ql case, where one passes through the
  virtual near-Molecule satellite chain before reaching the small primitive
  copy.

This is the point of contact with the quoted roadmap:

> Jointly with Kahn and Lyubich, we put forward a strategy to approach Problem
> 4.4 by considering partially invariant virtual Julia sets of `M(s)`. They are
> connected hulls of the corresponding Cantor small Julia sets within `J_f` and
> contain the critical orbit only up to an appropriate number of first returns.
> A posteriori, bounds for virtual Julia sets can be deduced by assuming a
> uniform hyperbolicity of the renormalization associated with `M`; the strategy
> towards Problem 4.4 is to develop such control a priori.

In this branch, that program is reflected by the split Problem 4.3 / 4.4 / 4.5
axioms rather than by a single `virtual_julia_strategy_data` package.

## Lean Bridge Theorems

The current split is connected to the existing proof skeleton through:

- `noTowerPrimitive_of_problem44`
- `satelliteLC_of_problem43_problem45`
- `mlc_conjecture_of_problem43_44_45_data`

These bridge the paper-facing problem statements to the theorem interfaces
already used by the main MLC proof.

## Next Possible Steps

The root finite-branch axiom has been eliminated, the basis seam is theoremized,
and the former low-level `Quadratic.filled_julia_set_connected` leak has been
removed from the checked frontier. The remaining job is to remove the last
finite-branch leak without accepting it into the frontier.

1. eliminate `Quadratic.para_puzzle_piece_inter_mandelbrot_connected` by
    redesigning the parameter-plane witness route for the translated
    `ParaPuzzlePieceAt` family
2. keep `check_axioms.lean` and the README locked to that intended frontier:

- `problem43_pseudoSiegelAPrioriBounds`
- `problem44_virtualMolecule`
- `problem45_virtualNearMoleculeRenormalization`

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
