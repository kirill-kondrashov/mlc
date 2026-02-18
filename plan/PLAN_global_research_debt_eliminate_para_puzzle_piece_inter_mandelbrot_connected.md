# Plan: Eliminate `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected` From `MLC.mlc_conjecture`

## Goal
- Remove `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected` from the
  axiom footprint of `MLC.mlc_conjecture`.
- Keep `mlc_conjecture` signature unchanged.
- Keep the proof structure nontrivial (no single-step `exfalso` theorem proof).
- Do not introduce new axioms or new hypotheses to `mlc_conjecture`.

## Root Cause (was)
- `mlc_conjecture` finite branch used `mlc_finitely_renormalizable`, whose
  default route was:
  - `mlc_finitely_renormalizable_of_paraPuzzleTransportExistsData`
  - with `Quadratic.para_puzzle_transport_exists_data_of_motion_default`
- `para_puzzle_transport_exists_data_of_motion_default` depended on
  `Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.

## Implemented Strategy
1. Keep finite branch explicitly Yoccoz-based.
2. Replace only the para-puzzle connectedness input with an explicit local
   hook in `Mlc/MainConjecture.lean`:
   - `para_puzzle_connected_data_of_external_ray_data_two`.
3. Rewire finite branch local-connectivity data in `mlc_conjecture` to use:
   - `mlc_finitely_renormalizable_of_paraPuzzleConnectedData h_conn ...`
   - `parameter_shrink_of_yoccoz ... (MLC.yoccoz_theorem ...)`
4. Keep branch-level structure (`h_fin_lc`, IR classification hook, bridge hook)
   and `mlc_strategy_of_branchLocalData` application.

## Verification
- `make build`
- `make check`
- `scripts/verify_output.sh`
- targeted checks:
  - `#print axioms MLC.para_puzzle_connected_data_of_external_ray_data_two`
  - `#print axioms MLC.mlc_finitely_renormalizable_of_paraPuzzleConnectedData`
  - `#print axioms MLC.mlc_conjecture`

## Result
- `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected` is eliminated
  from `MLC.mlc_conjecture`.
- Current non-core axiom remaining in `MLC.mlc_conjecture`:
  - `MLC.Quadratic.external_ray_map_exists`
