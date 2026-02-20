# Plan: Eliminate `external_ray_map_exists` via Outside-Open Targets

Date: 2026-02-20

## Objective
Remove `MLC.Quadratic.external_ray_map_exists` from the axiom footprint of
`MLC.mlc_conjecture` without:
- introducing any new axioms,
- adding hypotheses to `MLC.mlc_conjecture`,
- collapsing the rooted proof into contradiction circulation.

## Current rooted situation
In `Mlc/MainConjecture.lean`, the active seam is now:
- `MainPathData` (constructive core assembly target),
- seeded by `mainPathData_axiom_seed`,
- where the only contradiction step is confined to
  `mainPathData_of_bottcher_approach_to_one_seq_preimage_data_two`.

The external-ray dependency is localized at:
- `approach_one_seq_in_bottcher_range_data_two_axiom_seed`.
- and has been weakened one step further through
  `BottcherExteriorSubsetImageBasinData` (exterior subset of Böttcher image on
  the basin).

## Reduction target chain (already available in code)
From `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
1. If we can prove
   - injectivity on outside-open:
     `Set.InjOn (Quadratic.bottcher_map c) {z | ‖z‖ > ‖c‖ + 2}`
   - surjectivity onto exterior by outside-open preimages:
     `BottcherSurjOnExteriorFromOutsideOpen c`,
   then we can build
   - `Quadratic.ExternalRayMapData c`
     via `external_ray_map_data_of_injOn_outside_open_of_surj_exterior`.
2. `ExternalRayMapData (2 : ℂ)` implies the current sequence-range seam at `c=2`.
3. We now also have a weaker intermediate seam in the rooted path:
   - `BottcherExteriorSubsetImageBasinData (2 : ℂ) ->
      ApproachOneSeqInBottcherRangeData (2 : ℂ)`.

So elimination reduces to proving those two outside-open targets at `c = 2`
without using `external_ray_map_exists`.

## Hard blocker (explicit)
Current available route to outside-open injectivity in this repo is still via
left-inverse data derived from `ExternalRayMapData`, i.e. circular.

## Next non-circular proof milestones
1. Prove outside-open injectivity at `c = 2` by a route independent of external
   ray data (e.g. local-homeomorph/proper-map + fiber-control route).
2. Prove exterior surjectivity by outside-open preimages at `c = 2` via a
   non-external-ray route (image-equality/inclusion target in OutsidePlan).
3. Instantiate `ExternalRayMapData (2 : ℂ)` from the two milestones above.
4. Replace `approach_one_seq_in_bottcher_range_data_two_axiom_seed` with the
   constructed data.
5. Remove the temporary contradiction seed and replace
   `mainPathData_axiom_seed` constructively.

## Acceptance checks
- `make build`
- `make graphs`
- `make check`
- `scripts/verify_output.sh`
- Axiom list for `MLC.mlc_conjecture` contains only core axioms
  (`Quot.sound`, `propext`, `Classical.choice`).
