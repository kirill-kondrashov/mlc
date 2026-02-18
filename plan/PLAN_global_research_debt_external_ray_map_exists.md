# Plan: Eliminate `MLC.Quadratic.external_ray_map_exists`

Date: 2026-02-18

## Goal
- Remove `MLC.Quadratic.external_ray_map_exists` from the axiom footprint of
  `MLC.mlc_conjecture`.
- Do not add new axioms.
- Do not add new hypotheses to `MLC.mlc_conjecture`.
- Do not use contradiction-only routing (`exfalso`/`False.elim`) in the
  transitive proof path of `MLC.mlc_conjecture`.

## Verified Current State
- `make check` currently reports:
  - `Quot.sound`
  - `propext`
  - `Classical.choice`
  - `MLC.Quadratic.external_ray_map_exists`
- `scripts/verify_output.sh` passes and matches `README.md`.
- In `Mlc/MainConjecture.lean`, the current path still closes through:
  - `false_of_external_ray_data_two`
  - `ir_classification_data_of_external_ray_axioms`
  - `para_puzzle_connected_data_of_external_ray_data_two`
  - `molecule_bridge_data_of_external_ray_data_two`
  which are contradiction-backed.

## Soundness Gate (Enforced)
- No contradiction-backed branch data in the `MLC.mlc_conjecture` path.
- In particular, remove use of `false_of_external_ray_data_two` as a provider
  for finite-branch connectedness, IR classification, or molecule bridge data.

## Dependency Audit (Why Current Elimination Is Blocked)

### 1) Finite branch connectedness data
- `mlc_finitely_renormalizable_of_paraPuzzleConnectedData` requires
  `ParaPuzzlePieceInterMandelbrotConnectedData`.
- Current default constructors route through
  `Quadratic.para_puzzle_transport_exists_data_of_motion_default`, whose axiom
  footprint includes:
  - `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.
- So dropping the external-ray contradiction route immediately reintroduces the
  para-puzzle connectedness axiom unless a constructive proof of this data is
  added.
- Symbol-level confirmation (current tree):
  - `para_puzzle_transport_exists_data_of_motion_default` is built from
    `para_puzzle_transport_witness_hyp`, and
    `para_puzzle_transport_witness_hyp = para_puzzle_transport_witness_hyp_of_axiom`.
  - `para_puzzle_transport_witness_hyp_of_axiom` explicitly uses
    `para_puzzle_piece_inter_mandelbrot_connected`.
  - Boundary-motion route (`para_puzzle_transport_witness_from_boundary_motion_target`)
    is parameterized by `PuzzleBoundaryMotionHyp`; no unconditional constructor
    for `PuzzleBoundaryMotionHyp` currently exists in the active path.

### 2) IR classification data
- `IRClassificationData` requires:
  `PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c` for IR `c`.
- Existing constructive theorem
  `classify_infinitely_renormalizable` needs
  `InfinitelyRenormalizableHasTowerData` as an input.
- No unconditional theorem currently provides
  `InfinitelyRenormalizableHasTowerData`.

### 3) Molecule bridge data
- Current bridge theorems require one of:
  - `MoleculeModulusLowerBoundData`
  - `MoleculeConformalModulusLowerBoundData`
  - `MoleculeUniformConformalLowerBoundData`.
- No unconditional constructor from existing assumptions in
  `MLC.mlc_conjecture` is available.

### 4) Bottcher-side constructive replacement status
- `external_ray_map_data_of_injOn_outside_open_of_surj_exterior` is
  constructive (core axioms only), but it still requires:
  - outside-open injectivity input
  - outside-open surjectivity input.
- Current available producers of these inputs in active routes still depend on
  `external_ray_map_exists` (directly or indirectly), so the constructive route
  is not yet closed.

## Unused-Code Check (Path-Scoped)
- Current declarations in `Mlc/MainConjecture.lean` remain connected to the
  active `mlc_conjecture` path.
- No safe deletion in `Mlc/MainConjecture.lean` is possible without first
  replacing the contradiction-backed branch-data providers.

## Required Work Before External-Ray Axiom Can Be Removed
1. Constructive finite-branch replacement:
   prove `ParaPuzzlePieceInterMandelbrotConnectedData` (or a stronger data
   target that implies it) without contradiction and without new axioms.
2. Constructive IR classification replacement:
   provide `InfinitelyRenormalizableHasTowerData` constructively, then route
   through `classify_infinitely_renormalizable`.
3. Constructive molecule bridge replacement:
   provide one of the Molecule bridge data targets above without contradiction.
4. Rewire `Mlc/MainConjecture.lean` to use (1)-(3), remove contradiction-backed
   providers from the active path, then rerun:
   - `make build`
   - `make check`
   - `scripts/verify_output.sh`
5. Confirm final `make check` axiom output for `MLC.mlc_conjecture` excludes
   `MLC.Quadratic.external_ray_map_exists`.

## Status
- External-ray elimination from `MLC.mlc_conjecture` is currently blocked by
  missing constructive replacements for branch data.
- Forcing elimination now would either:
  - reintroduce removed axioms into `MLC.mlc_conjecture`, or
  - reintroduce tautological contradiction routing.
