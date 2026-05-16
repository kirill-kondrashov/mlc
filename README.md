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

## Current Axiom Frontier

The **intended** root frontier for `MLC.mlc_conjecture` is exactly one
non-core project axioms:

- `MLC.problem45_virtualNearMoleculeRenormalization`

The only other axioms in the root proof are the standard Lean core ones:

- `Quot.sound`
- `propext`
- `Classical.choice`

## Root Theorem Route

The top theorem is now assembled through the IR-only route:

1. the Gaussian proxy model makes the finite branch vacuous in
   `mlc_conjecture_of_irLocallyConnectedData`
2. Problem 4.5 now carries both IR classification and the direct satellite bridge via
   `problem45_virtualNearMoleculeRenormalization`
3. `mlc_conjecture_of_irClassifyBridgeData`
4. local connectivity of `mandelbrotSet`

At the Lean interface level, the remaining IR/satellite seams are:

```lean
def Problem43PseudoSiegelAPrioriBoundsData : Prop :=
  MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget

def Problem45VirtualNearMoleculeRenormalizationData : Prop :=
  IRClassificationData ∧ VirtualJuliaSatelliteLocalConnectivityData
```

## Remaining Problems in Mathematical Terms

The current frontier is meant to isolate the genuinely unresolved mathematics,
rather than hide it behind one coarse package.

| Lean axiom | Mathematical content |
| --- | --- |
| `problem45_virtualNearMoleculeRenormalization` | **Problem 4.5**: handle the primitive-first ql situation through the canonical satellite chain `M = M(0) ⊋ M(1) ⊋ ... ⊋ M(n+1)`. At the current seam, this now supplies both the infinitely-renormalizable classification payload and the satellite local-connectivity endpoint, so it absorbs the old Problem 4.4 root dependency as well as the old Problem 4.3 one. |

The previous finite-branch blockers

1. `Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
2. `Quadratic.filled_julia_set_connected`

are no longer on the checked root frontier.

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

In this branch, that program is reflected by the remaining strengthened Problem
4.5 axiom rather than by a single `virtual_julia_strategy_data` package.

## Lean Bridge Theorems

The current split is connected to the existing proof skeleton through:

- `irClassification_of_problem45`
- `satelliteLC_of_problem45`
- `irClassifyBridgeData_of_classify_bridge_data`
- `mlc_conjecture_of_irClassifyBridgeData`
- `mlc_conjecture_of_problem43_44_45_data`

The root theorem currently uses the IR-only assembly through
`mlc_conjecture_of_irClassifyBridgeData`; the
`mlc_conjecture_of_problem43_44_45_data` theorem remains as the explicit
finite-branch-plus-IR packaged bridge.

## Next Possible Steps

The root theorem now checks with only the remaining paper-facing axiom plus Lean
core. The finite-branch cleanup ended in two steps:

1. theoremize the basis side and remove the low-level
   `Quadratic.filled_julia_set_connected` leak
2. reroute `mlc_conjecture` through the existing IR-only assembly
   `mlc_conjecture_of_irClassifyBridgeData`, so the finite-branch seam no longer
   appears in the checked frontier

Immediate maintenance goal: keep `check_axioms.lean` and the README locked to
that intended frontier:

- `problem45_virtualNearMoleculeRenormalization`

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
