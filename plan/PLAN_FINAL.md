# PLAN_FINAL: Constructive elimination of `Quadratic.external_ray_map_exists` at `c = 2`

## Objective
Constructively prove:

`Quadratic.ExternalRayMapData (2 : ℂ)`

and replace the final axiom ingress in `MLC.mlc_conjecture`.

## Current status
- Root wiring is normalized.
- The final blocker is isolated at `externalRayMapData_two_axiom_seed`.
- Validation pipeline is stable (`make build`, `make check`, `make graphs`, `scripts/verify_output.sh`).

## Checkpoint progress (non-percent)
- `[x]` CP0: Route/spec documented
- `[x]` CP1: Constructive target seam theorem under explicit hypotheses added
- `[~]` CP2: Constructive `OutsideOpenAnalyticityHypothesis (2 : ℂ)` (revised formal target exported: `RevisedCP2TargetTwo`; original CP2 target certified impossible in current model; assumption-gated bridge exists but remains vacuous)
- `[~]` CP3: Constructive outside-open injectivity payload at `c = 2` (revised formal target exported: `RevisedCP3TargetTwo`; original payload certified impossible in current model)
- `[~]` CP4: Constructive closed-range/properness payload at `c = 2` (revised formal target exported: `RevisedCP4TargetTwo`; original analytic-derivative payload certified impossible in current model)
- `[~]` CP5: Build `external_ray_map_exists_two_constructive` (revised formal target exported: `RevisedCP5TargetTwo`; currently blocked legacy ingress families are aggregated as `KnownCP5IngressCandidateTwo` and certified inconsistent via `not_knownCP5IngressCandidateTwo`; open candidate lane `InjSurjExteriorConstructivePayloadTwo` is wired; a non-iterate-left-inverse injection route from outside-open left-inverse data is now exported, alongside iterate-left-inverse constructors; surjectivity seams still include closed-range + local-homeomorph / local-homeomorph-on assumptions and outside-disk-refinement/landing variants; at `c = 2` landing/refinement are equivalent (`outsideDiskRefinement_two_iff_externalRayLandsOutsideOpen`); preimage-control is inconsistent (`not_preimageExteriorSubsetOutsideOpenTwo`), and iterate-left-inverse landing/refinement payload packages are inconsistent (`not_iterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo`, `not_iterLeftInverseOutsideDiskRefinementConstructivePayloadTwo`); known local-homeomorph-on source families remain inconsistent via `not_knownLocalHomeomorphOnSourceCandidateTwo`; endpoint body still axiom-seeded)
- `[ ]` CP6: Replace axiom usage and verify zero dependency

## Latest implementation checkpoint
- Added in `Mlc/MainConjecture.lean`:
  - `externalRayMapData_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn`;
  - `externalRayMapData_two_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload`;
  - `external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis`;
  - `external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis`;
  - `external_ray_map_exists_two_constructive_of_analyticAt_of_preimageCompact`;
  - `external_ray_map_exists_two_constructive_of_analyticAt_of_preimageClosed`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesisTwo`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt_of_injOn`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis`;
  - `outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_constructive_of_outsideOpenQuotientAnalyticityHypothesis`;
  - `outsideOpenQuotientAnalyticityHypothesisTwo_constructive_of_outsideOpenAnalyticityHypothesis`;
  - `outsideOpenQuotientAnalyticityHypothesisTwo_constructive`;
  - `outsideOpenAnalyticityHypothesisTwo_constructive_of_outsideOpenQuotientAnalyticityHypothesis`;
  - `outsideOpenAnalyticityHypothesisTwo_constructive_of_outsideOpenQuotientConstRealWitnessTwo`;
  - `outsideOpenQuotientAnalyticityHypothesisTwo_constructive_of_outsideOpenQuotientConstRealWitnessTwo`;
  - `outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_constructive_of_outsideOpenQuotientConstRealWitnessTwo`;
  - `outside_open_subset_slit_orbit_of_eventualSlitImpliesSlitOrbit`;
  - `mem_nhds_slit_on_outside_open_of_eventualSlitImpliesSlitOrbit`;
  - `outsideOpenAnalyticityHypothesisTwo_constructive_of_eventualSlitImpliesSlitOrbit`;
  - `outsideOpenQuotientConstRealWitnessTwo_constructive_of_eventualSlitImpliesSlitOrbit`;
  - `not_outsideOpenQuotientConstHypothesisTwo`;
  - `not_outsideOpenAnalyticityHypothesisTwo`;
  - `RevisedCP2TargetTwo`;
  - `revisedCP2TargetTwo_constructive`;
  - `not_outsideOpenQuotientAnalyticityHypothesisTwo`;
  - `not_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesisTwo`;
  - `not_outsideOpenQuotientConstRealWitnessTwo`;
  - `not_eventualSlitImpliesSlitOrbit_two`;
  - `not_nonSlitAnalyticConstructivePayloadTwo`;
  - `not_nonSlitEventualSlitConstructivePayloadTwo`;
  - `not_nonSlitQuotientConstConstructivePayloadTwo`;
  - `not_nonSlitQuotientAnalyticConstructivePayloadTwo`;
  - `not_nonSlitQuotientConstRealConstructivePayloadTwo`;
  - `OutsideOpenAnalyticityScopeAssumptionTwo`;
  - `outsideOpenAnalyticityHypothesisTwo_assumptionGated`;
  - `outsideOpenQuotientAnalyticityHypothesisTwo_assumptionGated`;
  - `outsideOpenQuotientConstRealWitnessTwo_assumptionGated`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenAnalyticityScopeAssumptionTwo`;
  - `NonSlitAnalyticScopeAssumptionConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitAnalyticScopeAssumptionConstructivePayloadTwo`;
  - `not_nonSlitAnalyticScopeAssumptionConstructivePayloadTwo`;
  - `KnownCP5IngressCandidateTwo`;
  - `not_knownCP5IngressCandidateTwo`;
  - `NonSlitBoundaryExclusionConstructivePayloadTwo`;
  - `NonSlitMemNhdsSlitInjConstructivePayloadTwo`;
  - `NonSlitMemNhdsSlitIterLeftInverseConstructivePayloadTwo`;
  - `not_nonSlitBoundaryExclusionConstructivePayloadTwo`;
  - `not_nonSlitMemNhdsSlitInjConstructivePayloadTwo`;
  - `not_nonSlitMemNhdsSlitIterLeftInverseConstructivePayloadTwo`;
  - `cp2_revised_target_two`;
  - `not_outsideOpenAnalyticInjNonSlitPayloadTwo`;
  - `not_nonSlitAnalyticInjConstructivePayloadTwo`;
  - `not_analyticDerivConstructivePayloadTwo`;
  - `RevisedCP3TargetTwo`;
  - `revisedCP3TargetTwo_constructive`;
  - `RevisedCP4TargetTwo`;
  - `revisedCP4TargetTwo_constructive`;
  - `RevisedCP5TargetTwo`;
  - `revisedCP5TargetTwo_constructive`;
  - `external_ray_map_exists_two_constructive_of_injOn_outside_open_of_surj_exterior`;
  - `InjSurjExteriorConstructivePayloadTwo`;
  - `injSurjExteriorConstructivePayloadTwo_of_leftInverseOutsideOpen_of_surjExterior`;
  - `injSurjExteriorConstructivePayloadTwo_of_leftInverseOutsideOpen_of_localHomeomorph`;
  - `injSurjExteriorConstructivePayloadTwo_of_leftInverseOutsideOpen_of_localHomeomorphOn`;
  - `injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_surjExterior`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphConstructivePayload`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_localHomeomorphOnConstructivePayload`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_outsideDiskRefinement`;
  - `outsideDiskRefinement_two_of_externalRayLandsOutsideOpen`;
  - `externalRayLandsOutsideOpen_two_of_outsideDiskRefinement`;
  - `outsideDiskRefinement_two_iff_externalRayLandsOutsideOpen`;
  - `externalRayLandsOutsideOpen_two_of_preimageExteriorSubsetOutsideOpen`;
  - `bottcher_left_inverse_on_outside_open_data_of_injOn_outside_open`;
  - `bottcher_left_inverse_on_outside_open_data_iff_injOn_outside_open`;
  - `leftInverseOutsideOpen_two_iff_injOn_outside_open`;
  - `injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_localHomeomorph`;
  - `injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_localHomeomorphOn`;
  - `localHomeomorphOnOutsideOpen_two_of_analyticDerivConstructivePayloadTwo`;
  - `KnownSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `KnownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `KnownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_open_or_blocked`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_knownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `ReducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reduced`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `not_knownBlockedSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `knownOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `reducedOpenSurjOnExteriorFromOutsideOpenSourceCandidateTwo_of_knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo`;
  - `knownSurjOnExteriorFromOutsideOpenSourceCandidateTwo_iff_reducedOpen`;
  - `localHomeomorphSurjSource_two_of_reducedOpen_of_not_externalRayLandsOutsideOpen`;
  - `externalRayLandsOutsideOpen_two_of_reducedOpen_of_not_localHomeomorphSurjSource`;
  - `injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_analyticDerivConstructivePayloadTwo`;
  - `injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_outsideDiskRefinement`;
  - `injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_externalRayLandsOutsideOpen`;
  - `injSurjExteriorConstructivePayloadTwo_of_iterLeftInverse_of_preimageExteriorSubsetOutsideOpen`;
  - `IterLeftInverseAnalyticDerivConstructivePayloadTwo`;
  - `external_ray_map_exists_two_constructive_of_iterLeftInverse_of_surjExterior`;
  - `external_ray_map_exists_two_constructive_of_leftInverseOutsideOpen_of_surjExterior`;
  - `external_ray_map_exists_two_constructive_of_iterLeftInverse_of_outsideDiskRefinement`;
  - `external_ray_map_exists_two_constructive_of_iterLeftInverse_of_externalRayLandsOutsideOpen`;
  - `external_ray_map_exists_two_constructive_of_iterLeftInverse_of_preimageExteriorSubsetOutsideOpen`;
  - `mlc_conjecture_of_injSurjExteriorConstructivePayloadTwo`;
  - `mlc_conjecture_of_iterLeftInverse_of_surjExterior_two`;
  - `mlc_conjecture_of_leftInverseOutsideOpen_of_surjExterior_two`;
  - `mlc_conjecture_of_leftInverseOutsideOpen_of_localHomeomorph_two`;
  - `mlc_conjecture_of_leftInverseOutsideOpen_of_localHomeomorphOn_two`;
  - `mlc_conjecture_of_iterLeftInverse_of_localHomeomorph_two`;
  - `mlc_conjecture_of_iterLeftInverse_of_localHomeomorphOn_two`;
  - `mlc_conjecture_of_iterLeftInverse_of_outsideDiskRefinement_two`;
  - `mlc_conjecture_of_iterLeftInverse_of_externalRayLandsOutsideOpen_two`;
  - `mlc_conjecture_of_iterLeftInverse_of_preimageExteriorSubsetOutsideOpen_two`;
  - `IterLeftInverseOutsideDiskRefinementConstructivePayloadTwo`;
  - `mlc_conjecture_of_iterLeftInverseOutsideDiskRefinementConstructivePayloadTwo`;
  - `IterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo`;
  - `IterLeftInversePreimageExteriorSubsetOutsideOpenConstructivePayloadTwo`;
  - `mlc_conjecture_of_iterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo`;
  - `mlc_conjecture_of_iterLeftInversePreimageExteriorSubsetOutsideOpenConstructivePayloadTwo`;
  - `not_preimageExteriorSubsetOutsideOpenTwo`;
  - `not_iterLeftInversePreimageExteriorSubsetOutsideOpenConstructivePayloadTwo`;
  - `not_externalRayLandsOutsideOpen_two_of_iterLeftInverse`;
  - `not_iterLeftInverseExternalRayLandsOutsideOpenConstructivePayloadTwo`;
  - `not_iterLeftInverseOutsideDiskRefinementConstructivePayloadTwo`;
  - `mlc_conjecture_of_iterLeftInverseAnalyticDerivConstructivePayloadTwo`;
  - `not_iterLeftInverseAnalyticDerivConstructivePayloadTwo`;
  - `SlitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo`;
  - `localHomeomorphOnOutsideOpen_two_of_slitInjOutsideDisk`;
  - `not_slitInjOutsideDiskLocalHomeomorphOnConstructivePayloadTwo`;
  - `KnownLocalHomeomorphOnSourceCandidateTwo`;
  - `not_knownLocalHomeomorphOnSourceCandidateTwo`;
  - `KnownInjOnOutsideOpenSourceCandidateTwo`;
  - `injOn_outside_open_two_of_outsideOpenAnalyticityHypothesis`;
  - `injOn_outside_open_two_of_knownInjOnOutsideOpenSourceCandidateTwo`;
  - `not_knownInjOnOutsideOpenSourceCandidateTwo`;
  - `nonIterInjOnOutsideOpenSourceExhaustionTwo`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo_via_localChartWithin`;
  - `external_ray_map_exists_two_constructive_of_isClosedRange_restrict_of_eventualSlitImpliesSlitOrbit`;
  - `mlc_conjecture_of_nonSlitEventualSlitConstructivePayloadTwo`;
  - `external_ray_map_exists_two_constructive` (current placeholder endpoint, body still axiom-seeded).
- This extends CP2/CP3/CP4 scaffolding and wires a single CP5 replacement point for
  the final constructive payload body, including quotient and analytic/non-slit CP4 lanes.

## Final route
1. **Constructive outside-open analyticity at `c = 2`**
   - Prove `OutsideOpenAnalyticityHypothesis (2 : ℂ)` without `external_ray_map_exists`.
   - Preferred route: local analytic charts on outside-open and existing conversion lemmas.

2. **Constructive outside-open injectivity at `c = 2`**
   - Prove `Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}`.
   - Package with analyticity into `OutsideOpenAnalyticInjPayload (2 : ℂ)` or the existing `Two` specialization.

3. **Closed-range/properness bridge at `c = 2`**
   - Prove either:
     - `IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ)))`, or
     - `IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ))` and derive closed range.
   - Use existing bridge lemmas already present in `BottcherOutsidePlan.lean`.

4. **Derive external-ray map data constructively**
   - Apply:
     - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload`, or
     - equivalent `Two`-specialized seam.
   - Produce theorem:
     - `external_ray_map_exists_two_constructive : Quadratic.ExternalRayMapData (2 : ℂ)`.

5. **Replace final axiom ingress**
   - Rewire:
     - `externalRayMapData_two_axiom_seed := external_ray_map_exists_two_constructive`.
   - Remove remaining reference to `Quadratic.external_ray_map_exists (2 : ℂ)`.

6. **Final verification**
   - Run:
     - `make build`
     - `make check`
     - `make graphs`
     - `bash scripts/verify_output.sh`
   - Confirm `check_axioms.lean` no longer lists `MLC.Quadratic.external_ray_map_exists`.

## Exit condition
`MLC.mlc_conjecture` compiles with no dependency on `MLC.Quadratic.external_ray_map_exists`.
