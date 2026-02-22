# Plan: Constructive Outside-Open Analyticity at `c = 2`

Date: 2026-02-21

## Objective
Prove the hypothesis
`∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 -> AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z`
without using `MLC.Quadratic.external_ray_map_exists`, then use it in the
constructive `mlc_conjecture` replacement route.

## Progress bars
- Analyticity theorem track:
  `[█████████░] ~92%`
- Framework refactor track:
  `[██████████] ~100%`
- End-to-end elimination impact:
  `[█████████░] ~99.6%`

## Implementation checkpoint (2026-02-22, internet-backed theorem chain + surjectivity bridge)
- External references reviewed for the remaining proof shape:
  - Douady–Hubbard (`Étude dynamique des polynômes complexes`),
  - Milnor (`Dynamics in One Complex Variable`),
  - DeMarco–Pilgrim (`Polynomial Basins of Infinity`).
- Lean-targeted chain fixed as:
  - outside-open analyticity
  -> quotient analyticity
  -> quotient constancy
  -> real-scalar witness
  -> outside-open surjectivity
  -> rooted `mlc_conjecture`.
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesisTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`
    now consumes the new direct surjectivity bridge;
  - `mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo` now reuses that
    theorem directly.
- Validation:
  - `make build && make check && make graphs` passed;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

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

## Implementation checkpoint (2026-02-21, plain-analytic payload packaging)
- Added in `Mlc/MainConjecture.lean`:
  - `AnalyticConstructivePayloadTwo`,
  - `external_ray_map_data_two_of_analyticConstructivePayloadTwo`,
  - `mlc_conjecture_of_analyticConstructivePayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` now
    routes through the packaged plain-analytic payload bridge.

## Implementation checkpoint (2026-02-21, plain-analytic/derivative payload packaging)
- Added in `Mlc/MainConjecture.lean`:
  - `AnalyticDerivConstructivePayloadTwo`,
  - `mlc_conjecture_of_analyticDerivConstructivePayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero_two`
    now routes through this packaged plain-analytic/derivative payload bridge.

## Implementation checkpoint (2026-02-21, outside-open/analytic payload convergence)
- Added in `Mlc/MainConjecture.lean`:
  - `analyticConstructivePayloadTwo_of_outsideOpenAnalyticConstructivePayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`
    now routes through `AnalyticConstructivePayloadTwo`;
  - `external_ray_map_data_two_of_outsideOpenAnalyticConstructivePayloadTwo` and
    `mlc_conjecture_of_outsideOpenAnalyticConstructivePayloadTwo` now factor via
    the shared analytic payload bridge.

## Implementation checkpoint (2026-02-21, bidirectional outside-open payload convergence)
- Added in `Mlc/MainConjecture.lean`:
  - `outsideOpenAnalyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `external_ray_map_data_two_of_outsideOpenConstructivePayloadTwo` now factors
    through the outside-open-analytic payload helper, so both outside-open
    payload variants flow through one analytic packaging route.

## Implementation checkpoint (2026-02-21, plain-analytic convergence endpoint)
- Added in `Mlc/MainConjecture.lean`:
  - `analyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `external_ray_map_data_two_of_outsideOpenConstructivePayloadTwo` now factors
    through this direct conversion;
  - `mlc_conjecture_of_outsideOpenConstructivePayloadTwo` now routes through
    `mlc_conjecture_of_analyticConstructivePayloadTwo`.

## Implementation checkpoint (2026-02-21, local-chart bridge convergence)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_two`
    now routes through the outside-open-analyticity bridge;
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`
    now routes through `OutsideOpenConstructivePayloadTwo`.

## Implementation checkpoint (2026-02-21, chart-within direct analyticity bridge)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`
    now routes directly through the outside-open-analyticity bridge
    (`outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two`)
    instead of passing through the intermediate local-chart wrapper theorem.

## Implementation checkpoint (2026-02-21, dead payload-conversion pruning)
- Removed in `Mlc/MainConjecture.lean`:
  - `outsideOpenConstructivePayloadTwo_of_outsideOpenAnalyticConstructivePayloadTwo`
    (unused conversion wrapper after convergence on analytic payload routing).

## Implementation checkpoint (2026-02-21, analytic-payload alias pruning)
- Removed in `Mlc/MainConjecture.lean`:
  - `OutsideOpenAnalyticConstructivePayloadTwo`;
  - `outsideOpenAnalyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo`;
  - `analyticConstructivePayloadTwo_of_outsideOpenAnalyticConstructivePayloadTwo`;
  - `external_ray_map_data_two_of_outsideOpenAnalyticConstructivePayloadTwo`;
  - `mlc_conjecture_of_outsideOpenAnalyticConstructivePayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `analyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo` now
    maps chart-within payload directly to the plain-analytic payload.

## Implementation checkpoint (2026-02-21, local-chart root-wrapper pruning)
- Removed in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_two`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`.
- Rationale:
  both wrappers were dead after convergence onto
  `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`.

## Implementation checkpoint (2026-02-21, outside-open payload wrapper pruning)
- Removed in `Mlc/MainConjecture.lean`:
  - `OutsideOpenConstructivePayloadTwo`;
  - `analyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo`;
  - `external_ray_map_data_two_of_outsideOpenConstructivePayloadTwo`;
  - `mlc_conjecture_of_outsideOpenConstructivePayloadTwo`.
- Rationale:
  all four declarations were dead wrappers after the root path converged on the
  direct outside-open-analyticity bridge theorem.

## Implementation checkpoint (2026-02-21, direct analyticAt bridge flattening)
- Removed in `Mlc/MainConjecture.lean`:
  - `AnalyticConstructivePayloadTwo`;
  - `external_ray_map_data_two_of_analyticConstructivePayloadTwo`;
  - `mlc_conjecture_of_analyticConstructivePayloadTwo`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` now
    constructs `ExternalRayMapData` directly and bridges to
    `mlc_conjecture_of_externalRayMapData_two`.

## Implementation checkpoint (2026-02-21, external-ray-data root-wrapper pruning)
- Removed in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` now
    finishes directly through
    `mlc_conjecture_of_bottcherApproachOneSeqFiberData_two`;
  - `mlc_conjecture` now uses the same direct finish route.

## Implementation checkpoint (2026-02-21, rotated-slit no-go extension)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outside_open_subset_slit_orbit_rot_of_mem_nhds_slit`;
  - `not_outside_open_subset_slit_orbit_rot`;
  - `not_mem_nhds_slit_rot_on_outside_open_two`.
- Impact:
  ruled out not only principal-slit but also any fixed-angle rotated-slit
  neighborhood payload as a global outside-open analyticity strategy at `c = 2`.

## Implementation checkpoint (2026-02-22, real-scale quotient seam)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `bottcher_map_div_eq_real_scale_of_ne_zero`;
  - `bottcher_map_div_eq_real_scale_of_outside_open`.
- Refined:
  - `bottcher_map_div_mem_slitPlaneRight_of_ne_zero` now reuses the new
    real-scale quotient lemma.
- Impact:
  establishes an explicit non-slit algebraic form for
  `Quadratic.bottcher_map c z / z` on outside-open, preparing a direct
  analyticity no-go/constraint route independent of slit-neighborhood payloads.

## Implementation checkpoint (2026-02-22, non-slit analytic+injective seam wiring)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `OutsideOpenAnalyticInjPayload`;
  - `OutsideOpenAnalyticInjNonSlitPayloadTwo`;
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload`;
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Added in `Mlc/MainConjecture.lean`:
  - `NonSlitAnalyticInjConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo`.
- Impact:
  the root path now has an explicit combined non-slit payload slot, so the only
  remaining work is discharging that payload constructively at `c = 2`.

## Implementation checkpoint (2026-02-22, quotient rigidity payload extraction)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `OutsideOpenQuotientAnalyticityHypothesis`;
  - `OutsideOpenQuotientRealScaleHypothesis`;
  - `OutsideOpenQuotientAnalyticRealScalePayload` (+ `Two` specialization).
- Added derived bridges:
  - `outsideOpenQuotientAnalyticityHypothesis_of_outsideOpenAnalyticityHypothesis`;
  - `outsideOpenQuotientRealScaleHypothesis_of_bottcher_map_div`;
  - `outsideOpenQuotientAnalyticRealScalePayload_of_outsideOpenAnalyticInjPayload`
    (+ `outsideOpenQuotientAnalyticRealScalePayloadTwo_of_nonSlitPayload`).
- Impact:
  reduced the remaining non-slit proof to a cleaner rigidity target on the
  quotient map `z ↦ bottcher_map c z / z` over outside-open.

## Implementation checkpoint (2026-02-22, direct non-slit surjectivity bridge)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Refined:
  - `mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo` now routes
    directly via surjectivity (no local `ExternalRayMapData` reconstruction).

## Implementation checkpoint (2026-02-22, quotient-const witness bridge)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `OutsideOpenQuotientConstRealWitness` (+ `Two` specialization);
  - `outsideOpenAnalyticityHypothesis_of_outsideOpenQuotientConstRealWitness`;
  - `injOn_outside_open_of_outsideOpenQuotientConstRealWitness`;
  - `outsideOpenAnalyticInjPayload_of_outsideOpenQuotientConstRealWitness`
    (+ `Two` specialization).
- Added in `Mlc/MainConjecture.lean`:
  - `NonSlitQuotientConstRealConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitQuotientConstRealConstructivePayloadTwo`.
- Impact:
  final blocker is now isolated to proving the single rigidity witness
  `OutsideOpenQuotientConstRealWitnessTwo`.

## Implementation checkpoint (2026-02-22, quotient-constancy reduction)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `OutsideOpenQuotientConstHypothesis` (+ `Two` specialization);
  - `outsideOpenQuotientConstRealWitness_of_outsideOpenQuotientConstHypothesis`
    (+ `Two` specialization).
- Added in `Mlc/MainConjecture.lean`:
  - `NonSlitQuotientConstConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitQuotientConstConstructivePayloadTwo`.
- Impact:
  the remaining proof now reduces to establishing only
  `OutsideOpenQuotientConstHypothesisTwo` (constancy of
  `z ↦ Quadratic.bottcher_map (2:ℂ) z / z` on outside-open).

## Implementation checkpoint (2026-02-22, quotient-constancy proof repair)
- Repaired in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `isPreconnected_outside_open` image proof details (connected-image invocation,
    real-norm/div simplifications, scalar-division witness);
  - open-mapping contradiction branch in
    `outsideOpenQuotientConstHypothesis_of_outsideOpenQuotientAnalyticRealScalePayload`
    (inline outside-open witness, metric-ball imaginary-part contradiction).
- Result:
  - the quotient analyticity+real-scale -> quotient constancy bridge now compiles;
  - derived analyticity -> quotient constancy wrappers compile.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged
    (still includes `MLC.Quadratic.external_ray_map_exists`).

## Implementation checkpoint (2026-02-22, quotient-analytic payload root bridge)
- Added in `Mlc/MainConjecture.lean`:
  - `NonSlitQuotientAnalyticConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitQuotientAnalyticConstructivePayloadTwo`.
- Impact:
  root-facing non-slit payload route now accepts quotient analyticity directly
  and derives quotient constancy through the repaired bridge.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analyticity-route quotient rewiring)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientAnalyticityHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo`;
  - `outsideOpenQuotientConstHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`
    now routes through quotient constancy payload;
  - `mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo` now routes through
    the quotient-analytic payload bridge.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, direct quotient-analytic ingress seam)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis_two`.
- Rewired:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`
    now factors through the direct quotient-analytic ingress theorem.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, direct quotient-const ingress seam)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis_two`.
- Rewired:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis_two`
    now factors through the direct quotient-const ingress theorem.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, c=2 quotient-specialization cleanup)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientConstHypothesisTwo_of_outsideOpenQuotientAnalyticityHypothesisTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - quotient-analytic and quotient-const ingress bridges now use `Two`-specialized
    quotient constancy lemmas and payload types directly.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analytic ingress direct-to-const specialization)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`
    now uses
    `outsideOpenQuotientConstHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo`
    directly (bypassing quotient-analytic intermediary);
  - `mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo` now maps directly
    to quotient-const payload.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, quotient-analytic `Two` alias cleanup)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `OutsideOpenQuotientAnalyticityHypothesisTwo`.
- Rewired:
  - `outsideOpenQuotientConstHypothesisTwo_of_outsideOpenQuotientAnalyticityHypothesisTwo`
    and
    `outsideOpenQuotientAnalyticityHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo`
    now use the `Two` alias directly;
  - `NonSlitQuotientAnalyticConstructivePayloadTwo` and
    `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis_two`
    now consume the alias type.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analytic-inj route normalized to analytic core)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`
    now projects analyticity and routes through quotient-const payload bridges
    (no direct surjectivity construction on this route);
  - `mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo` now factors via
    `mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo`.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analytic-inj to quotient-const specialization)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientConstHypothesis_of_outsideOpenAnalyticInjPayload`;
  - `outsideOpenQuotientConstHypothesisTwo_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`
    now uses the specialized analytic-inj -> quotient-const bridge;
  - `mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo` now maps
    directly to quotient-const payload.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, plain analytic ingress normalization)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` now
    factors through `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`;
  - kept derivative-based bridge unchanged (ordering-safe).
- Impact:
  plain analytic ingress now converges with the same quotient-const reduction
  path used by outside-open analytic and analytic-inj seams.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analyticity route via quotient-real witness)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenAnalyticityHypothesisTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`
    now routes through `NonSlitQuotientConstRealConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo` now routes through
    the same quotient-real witness payload.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, direct witness-to-surjectivity bridge)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitness`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_nonSlitQuotientConstRealConstructivePayloadTwo` now uses
    the direct witness-to-surjectivity specialization.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analytic-inj direct witness specialization)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - analytic-inj ingress and non-slit analytic-inj payload root bridges now map
    directly to `NonSlitQuotientConstRealConstructivePayloadTwo`.
- Validation:
  - `make build && make check` pass; rooted axiom frontier unchanged.
