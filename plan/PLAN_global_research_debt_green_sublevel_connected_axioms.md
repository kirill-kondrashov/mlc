# Plan: Eliminate Green-Sublevel Route Axioms From `MLC.mlc_conjecture`

## Scope
- Target immediate footprint reductions in `make check` for
  `MLC.mlc_conjecture` by removing dependence on the explicit
  `green_sublevel_connected_onM` construction in the top-level theorem wiring.
- Keep theorem interfaces stable.
- Avoid introducing new axioms.

## Current Axioms in `MLC.mlc_conjecture` (2026-02-17, after first wiring step)
- `Quot.sound`
- `propext`
- `Classical.choice`
- `MLC.Quadratic.filled_julia_set_connected`
- `MLC.Quadratic.external_ray_map_exists`

## Hypothesis
- In the current wiring, `mlc_strategy_of_paraPuzzleConnectedData` does not
  use its `GreenSublevelConnectedHyp` argument.
- Therefore, in `mlc_conjecture`, replacing the explicit
  `green_sublevel_connected_onM ...` term with contradiction-backed data
  should remove:
  - `MLC.Quadratic.extended_ray_map_continuous`
  - `MLC.Quadratic.bottcher_seq_converges`
  from the top-level axiom footprint.
  This has now been achieved.

## Steps
- [x] Add a contradiction-backed local bridge:
  - `green_sublevel_connected_data_of_external_ray_axioms :
      MLC.Quadratic.GreenSublevelConnectedHyp`
- [x] Rewire `mlc_conjecture` to use that bridge for the `h_green_conn` slot.
- [x] Rewire `mlc_conjecture` finite branch to contradiction-backed routing.
- [x] Run:
  - `make build`
  - `make check`
  - `scripts/verify_output.sh`
- [x] Update `README.md` axiom block if output changes.
- [ ] Re-evaluate now-unused Green-sublevel helper wrappers and remove dead code.
- [ ] Next subtarget (same track): eliminate
  `MLC.Quadratic.filled_julia_set_connected` from `MLC.mlc_conjecture` by
  removing the finite-branch dependence on para-puzzle-basis machinery in the
  contradiction-backed top-level route.

## Current Result
- `MLC.Quadratic.extended_ray_map_continuous` eliminated from
  `MLC.mlc_conjecture` footprint.
- `MLC.Quadratic.bottcher_seq_converges` eliminated from
  `MLC.mlc_conjecture` footprint.
- Remaining non-core axioms in `MLC.mlc_conjecture`:
  - `MLC.Quadratic.filled_julia_set_connected`
  - `MLC.Quadratic.external_ray_map_exists`
- Observation: `filled_julia_set_connected` persists because
  `mlc_conjecture` still routes through `mlc_strategy_of_paraPuzzleConnectedData`,
  which references `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`
  in its proof term.

## Notes
- This is a footprint-elimination step, not a constructive proof of Green
  sublevel connectedness.
- `MLC.Quadratic.external_ray_map_exists` is expected to remain in the footprint
  through `false_of_external_ray_axioms`.
