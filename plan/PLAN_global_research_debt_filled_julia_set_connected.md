# Plan: Eliminate `MLC.Quadratic.filled_julia_set_connected` From `MLC.mlc_conjecture`

## Goal
- Remove `MLC.Quadratic.filled_julia_set_connected` from the axiom footprint of
  `MLC.mlc_conjecture`.
- Keep `mlc_conjecture` non-tautological and keep its signature unchanged.
- Do not introduce new axioms or new hypotheses.

## Root Cause (was)
- The dependency entered through:
  - `Quadratic.iInter_closure_para_puzzle_piece`
  - `Quadratic.para_puzzle_piece_basis`
  - `MLC.para_puzzle_piece_basis_induced`
  - `MLC.lc_at_of_shrink_of_data`
  - finite branch of `mlc_conjecture`.
- The critical use was inside `iInter_closure_para_puzzle_piece`, where
  `filled_julia_set_connected` was used to force all `K c` points into the same
  connected component as `0`.

## Implemented Strategy
1. Reworked `iInter_closure_para_puzzle_piece` in
   `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean` to avoid any use of
   `filled_julia_set_connected`.
2. Replaced the old `K c` connectedness argument with a component-separation
   argument:
   - derive `w := c' - c` has `green_function c w = 0` from closure-membership;
   - for each depth `n`, show `w` belongs to the open Green sublevel;
   - transport `c' ∈ closure (ParaPuzzlePieceAt c n)` to
     `w ∈ closure (DynamicalPuzzlePiece c n 0)`;
   - use connected-component disjointness in the open sublevel to prove
     `w ∈ DynamicalPuzzlePiece c n 0`;
   - recover `c' ∈ ⋂ n ParaPuzzlePieceAt c n` and conclude `c' = c` from shrink.
3. Kept `mlc_conjecture` finite branch routed via Yoccoz (no contradiction route
   reintroduced).

## Verification
- `lake build Mlc.Quadratic.Complex.ParaPuzzleBasis Mlc.MainConjecture`
- `make check`
- `scripts/verify_output.sh`
- targeted checks:
  - `#print axioms MLC.Quadratic.iInter_closure_para_puzzle_piece`
  - `#print axioms MLC.Quadratic.para_puzzle_piece_basis`
  - `#print axioms MLC.lc_at_of_shrink_of_data`
  - `#print axioms MLC.mlc_conjecture`

## Result
- `MLC.Quadratic.filled_julia_set_connected` is eliminated from
  `MLC.mlc_conjecture`.
- Current non-core axioms in `MLC.mlc_conjecture`:
  - `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
  - `MLC.Quadratic.external_ray_map_exists`
