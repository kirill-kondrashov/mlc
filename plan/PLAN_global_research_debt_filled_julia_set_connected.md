# Plan: Eliminate `MLC.Quadratic.filled_julia_set_connected` From `MLC.mlc_conjecture`

## Goal
- Remove `MLC.Quadratic.filled_julia_set_connected` from the axiom footprint of
  `MLC.mlc_conjecture`.
- Keep `mlc_strategy` and its wrapper chain present in `Mlc/MainConjecture.lean`.
- Keep `mlc_conjecture` signature unchanged and avoid new axioms/hypotheses.

## Root Cause
- `mlc_conjecture` routed through `mlc_strategy_of_paraPuzzleConnectedData`.
- That theorem invokes
  `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`, which depends on
  machinery importing `filled_julia_set_connected`.

## Implementation
1. Add a new strategy core theorem in `Mlc/MainConjecture.lean`:
   - `mlc_strategy_of_branchLocalData`
   - Inputs:
     - explicit finite-branch local-connectivity hook
     - IR classification hook
     - molecule bridge hook
   - Proof structure kept nontrivial: `dichotomy` split + finite/infinite
     branch assembly.
2. Refactor `mlc_strategy_of_paraPuzzleConnectedData` into a wrapper:
   - Build finite-branch hook from existing `h_conn` + `h_param_shrink`.
   - Delegate to `mlc_strategy_of_branchLocalData`.
3. Add contradiction-backed finite branch helper in `Mlc/MainConjecture.lean`:
   - `finite_lc_data_of_external_ray_data_two`.
4. Rewire `mlc_conjecture`:
   - keep IR classification and bridge hook construction;
   - replace application of `mlc_strategy_of_paraPuzzleConnectedData` with
     `mlc_strategy_of_branchLocalData` instantiated by
     `finite_lc_data_of_external_ray_data_two external_ray_data_two_axiom`.
5. Remove now-dead contradiction wrappers that are no longer in the final path.
6. Re-run `make build`, `make check`, and `scripts/verify_output.sh`.
7. Update README axiom output block to match current `make check`.

## Acceptance Criteria
- `#print axioms MLC.mlc_conjecture` no longer lists
  `MLC.Quadratic.filled_julia_set_connected`.
- `mlc_strategy` theorem still exists in `Mlc/MainConjecture.lean`.
- No new axiom appears in `MLC.mlc_conjecture`.
- `scripts/verify_output.sh` passes.
