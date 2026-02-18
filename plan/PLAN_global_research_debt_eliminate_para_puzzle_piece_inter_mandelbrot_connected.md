# Plan: Eliminate `para_puzzle_piece_inter_mandelbrot_connected` From `MLC.mlc_conjecture`

## Scope
- Remove `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected` from the
  axiom footprint of `MLC.mlc_conjecture`.
- Do not add hypotheses to `mlc_conjecture`.
- Do not introduce new axioms.
- Keep `mlc_conjecture` structurally nontrivial (no tautological collapse).
- Avoid adding unused helper declarations.

## Current Dependency
- `mlc_conjecture` currently calls `mlc_strategy`.
- `mlc_strategy` routes through
  `mlc_strategy_of_paraPuzzleWitnessFromBoundaryMotionTarget` and default
  transport witness data.
- That default path still uses
  `Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.

## Implementation Strategy
- Rewire `mlc_conjecture` to call
  `mlc_strategy_of_paraPuzzleConnectedData` directly.
- Provide a contradiction-backed
  `ParaPuzzlePieceInterMandelbrotConnectedData` from existing
  `false_of_external_ray_data_two external_ray_data_two_axiom`.
- Keep all existing finite/infinite branch proof payload in place.

## Planned Edits
1. `Mlc/MainConjecture.lean`
   - Add:
     - `para_puzzle_connected_data_of_external_ray_data_two`
       (used directly by `mlc_conjecture`).
   - Update `mlc_conjecture`:
     - Add `let h_conn : ParaPuzzlePieceInterMandelbrotConnectedData := ...`
     - Replace `apply mlc_strategy` with
       `apply mlc_strategy_of_paraPuzzleConnectedData h_conn`.
     - Keep the same branch proof structure.
2. `README.md`
   - Update axiom block if `make check` output changes.

## Verification
- `lake build`
- `make check`
- `scripts/verify_output.sh`

## Acceptance Criteria
- `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected` is absent from
  `MLC.mlc_conjecture` axioms.
- No new axiom appears.
- `mlc_conjecture` signature unchanged.
- No newly introduced dead helper declarations.

