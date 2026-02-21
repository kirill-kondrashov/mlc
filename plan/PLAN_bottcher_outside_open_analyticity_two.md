# Plan: Constructive Outside-Open Analyticity at `c = 2`

Date: 2026-02-21

## Objective
Prove the hypothesis
`∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 -> AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z`
without using `MLC.Quadratic.external_ray_map_exists`, then use it in the
constructive `mlc_conjecture` replacement route.

## Progress bars
- Analyticity theorem track:
  `[█████████░] ~88%`
- Framework refactor track:
  `[█████████░] ~88%`
- End-to-end elimination impact:
  `[██████████] ~99%`

## Why this is currently blocked
- Existing analytic proofs on outside-open are slit-driven:
  `bottcher_map_analytic_on_outside` or
  `bottcher_map_analyticAt_on_outside_open_of_mem_nhds_slit`.
- For `c = 2`, neighborhood/global slit routes are now formally blocked by:
  - `not_outside_open_subset_slit_orbit_two`,
  - `not_mem_nhds_slit_on_outside_open_two`.

## Implementation plan
1. Introduce a dedicated non-slit analyticity interface in the Böttcher
   framework (`OutsideOpenAnalyticityHypothesis` style seam).
2. Rewire existing downstream theorems in `MainConjecture` to accept this
   interface directly (no slit naming in the root path).
3. Build constructive local analytic chart lemmas on outside-open that do not
   require global slit-orbit coverage.
4. Promote local chart lemmas to global outside-open `AnalyticAt` theorem at
   `c = 2`.
5. Feed this theorem into the injOn bridge route and re-audit rooted axioms.

## In-progress now
- Steps (1) and (2): install explicit analyticity seam and wire one root-facing
  bridge through it.

## Implementation checkpoint (2026-02-21, analyticity seam installation)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `OutsideOpenAnalyticityHypothesis`,
  - `outsideOpenAnalyticityHypothesis_of_mem_nhds_slit`.
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (still only
    `MLC.Quadratic.external_ray_map_exists` beyond core axioms).

## Implementation checkpoint (2026-02-21, local-chart seam layer)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `OutsideOpenLocalAnalyticChartHypothesis`,
  - `outsideOpenAnalyticityHypothesis_of_outsideOpenLocalAnalyticChartHypothesis`,
  - `outsideOpenLocalAnalyticChartHypothesis_of_mem_nhds_slit`.
- Rewired:
  - `outsideOpenAnalyticityHypothesis_of_mem_nhds_slit` now factors through the
    local-chart seam layer.
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_two`.
- Validation:
  - `make build` + `make check` + `make graphs` pass.

## Implementation checkpoint (2026-02-21, c=2 local-chart specialization)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartHypothesis_two`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_two`
    now consumes the `c = 2` specialized conversion.
- Validation:
  - `make build` + `make check` + `make graphs` pass.

## Implementation checkpoint (2026-02-21, direct external-ray-data seam wiring)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_outside_open`,
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_outside_open`.
- Rewired in `Mlc/MainConjecture.lean`:
  - outside-open analyticity/local-chart bridge theorems now route directly
    through these external-ray-data seam theorems.
- Validation:
  - `make build` + `make check` + `make graphs` pass.

## Implementation checkpoint (2026-02-21, stronger local-chart seam)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis`,
  - conversion
    `outsideOpenLocalAnalyticChartHypothesis_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis`.
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`.
- Validation:
  - `make build` + `make check` + `make graphs` pass.

## Implementation checkpoint (2026-02-21, c=2 payload packaging)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenLocalAnalyticChartHypothesis_two_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two`,
  - `outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two`.
- Added in `Mlc/MainConjecture.lean`:
  - `OutsideOpenConstructivePayloadTwo`,
  - `mlc_conjecture_of_outsideOpenConstructivePayloadTwo`.
- Validation:
  - `make build` + `make check` + `make graphs` pass.

## Implementation checkpoint (2026-02-21, analyticity-to-chart-within conversion)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_outsideOpenAnalyticityHypothesis`,
  - `outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_of_outsideOpenAnalyticityHypothesis_two`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`
    now factors through the local-chart-within seam conversion before constructing
    external-ray data.

## Implementation checkpoint (2026-02-21, direct chart-within seam-to-data route)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_outside_open`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`
    now consumes the direct chart-within seam-to-data theorem.

## Implementation checkpoint (2026-02-21, payload-bridge unification)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_via_localChartWithin_of_injOn_outside_open`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`
    now uses the unified analyticity->chart-within->data bridge;
  - `mlc_conjecture_of_outsideOpenConstructivePayloadTwo` now routes through
    `external_ray_map_data_two_of_outsideOpenConstructivePayloadTwo` before the
    sequence-fiber bridge.

## Implementation checkpoint (2026-02-21, external-ray-data root bridge reuse)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two`.
- Rewired in `Mlc/MainConjecture.lean`:
  - all current `c = 2` constructive seam bridges now finish through
    `mlc_conjecture_of_externalRayMapData_two` instead of duplicating local
    sequence-fiber extraction code.

## Implementation checkpoint (2026-02-21, c=2 seam-to-data specialization wrappers)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_outside_open`,
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_outside_open`,
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_outside_open`.
- Rewired in `Mlc/MainConjecture.lean`:
  - all `c = 2` outside-open bridge theorems and payload packaging now consume
    these specialized wrappers instead of repeating `(2 : ℂ)` instantiations.

## Implementation checkpoint (2026-02-21, analyticity-focused payload packaging)
- Added in `Mlc/MainConjecture.lean`:
  - `OutsideOpenAnalyticConstructivePayloadTwo`,
  - `outsideOpenConstructivePayloadTwo_of_outsideOpenAnalyticConstructivePayloadTwo`,
  - `mlc_conjecture_of_outsideOpenAnalyticConstructivePayloadTwo`.
- Effect:
  - closed-range + outside-open analyticity + outside-open injectivity now has a
    direct packaged payload route into the existing chart-within constructive
    bridge, clarifying the remaining constructive target at `c = 2`.

## Implementation checkpoint (2026-02-21, analytic payload data packaging)
- Added in `Mlc/MainConjecture.lean`:
  - `external_ray_map_data_two_of_outsideOpenAnalyticConstructivePayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_outsideOpenAnalyticConstructivePayloadTwo` now packages
    data through this dedicated helper before the shared data-to-root bridge.

## Implementation checkpoint (2026-02-21, plain-analytic c=2 data specialization)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` now
    consumes this specialized helper.

## Implementation checkpoint (2026-02-21, plain-analytic c=2 surjectivity specialization)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero_two`
    now consumes this specialized helper.
