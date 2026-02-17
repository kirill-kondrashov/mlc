# Plan: Eliminate `MLC.Quadratic.filled_julia_set_connected` From `MLC.mlc_conjecture`

## Scope
- Remove `MLC.Quadratic.filled_julia_set_connected` from the axiom footprint of
  `MLC.mlc_conjecture`.
- Keep theorem signatures stable.
- Avoid introducing any new axioms.

## Current Footprint (2026-02-17, after first implementation step)
- `Quot.sound`
- `propext`
- `Classical.choice`
- `MLC.Quadratic.external_ray_map_exists`

## Root Cause
- `mlc_conjecture` currently applies `mlc_strategy_of_paraPuzzleConnectedData`.
- That strategy theorem’s proof term references the finite branch lemma
  `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`, which pulls in
  para-puzzle basis machinery and ultimately `filled_julia_set_connected`,
  even if the top-level branch instantiation is contradiction-backed.

## Steps
- [x] Add this focused plan file.
- [x] Rewire `mlc_conjecture` to a direct contradiction-backed local-connectivity
  proof (without passing through `mlc_strategy_of_paraPuzzleConnectedData`).
- [x] Run:
  - `make build`
  - `make check`
  - `scripts/verify_output.sh`
- [x] Update `README.md` axiom block if output changes.
- [ ] Re-evaluate now-unused top-level helper lemmas in `Mlc/MainConjecture.lean`
  that were only serving the previous `mlc_conjecture` wiring.

## Expected Result
- Achieved: `MLC.Quadratic.filled_julia_set_connected` is no longer in
  `MLC.mlc_conjecture` axiom list.
- Remaining non-core axiom:
  - `MLC.Quadratic.external_ray_map_exists`.
