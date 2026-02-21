# Plan: Constructive Outside-Open Analyticity at `c = 2`

Date: 2026-02-21

## Objective
Prove the hypothesis
`∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 -> AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z`
without using `MLC.Quadratic.external_ray_map_exists`, then use it in the
constructive `mlc_conjecture` replacement route.

## Progress bars
- Analyticity theorem track:
  `[███████░░░] ~70%`
- Framework refactor track:
  `[███████░░░] ~70%`
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
