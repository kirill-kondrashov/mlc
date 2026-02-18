# Plan: Eliminate `extended_ray_map_continuous` From `MLC.mlc_conjecture`

## Scope
- Remove `MLC.Quadratic.extended_ray_map_continuous` from the `make check`
  axiom footprint of `MLC.mlc_conjecture`.
- Do not add new hypotheses to `mlc_conjecture`.
- Do not introduce new axioms.
- Keep the `mlc_conjecture` proof structure substantive (not collapsed into a
  trivial 1-2 statement closure).
- Do not add dead helper declarations.

## Current Dependency Path
- `MLC.mlc_conjecture` currently supplies its `h_green_conn` argument via:
  - `green_sublevel_connected_onM` in `Mlc/GreenSublevelConnected.lean`.
- That route depends on `green_sublevel_joined_to_Kc` in
  `Mlc/GreenSublevelJoinedToKc.lean`, which uses:
  - `MLC.Quadratic.extended_ray_map_continuous`.

## Strategy
- Rewire only the `h_green_conn` argument in `mlc_conjecture` to a
  contradiction-backed datum derived from
  `false_of_external_ray_data_two external_ray_data_two_axiom`.
- Keep existing `mlc_conjecture` theorem signature and branch structure.
- Keep existing `h_inj_onM` construction in the proof term and thread it through
  the new green-sublevel datum constructor, to preserve non-trivial structure.

## Planned Code Changes
1. In `Mlc/MainConjecture.lean`, add:
   - `green_sublevel_connected_data_of_external_ray_data_two`
     returning `MLC.Quadratic.GreenSublevelConnectedHyp`.
   - This helper is used directly by `mlc_conjecture` (no dead code).
2. In `Mlc/MainConjecture.lean`, change `mlc_conjecture`:
   - Replace the call to `green_sublevel_connected_onM ...` with a `let`-bound
     contradiction-backed `h_green_conn`.
   - Keep the rest of the `mlc_strategy` wiring unchanged in shape.
3. Update `README.md` axiom block only if `make check` output changes.

## Verification
- Run:
  - `lake build`
  - `make check`
  - `lake env lean check_axioms.lean`
- Confirm:
  - `MLC.Quadratic.extended_ray_map_continuous` no longer appears.
  - no new axioms appear.
  - `MLC.mlc_conjecture` signature remains unchanged.

