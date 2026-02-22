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
- `[~]` CP2: Constructive `OutsideOpenAnalyticityHypothesis (2 : ℂ)` (target seam in place; proof missing)
- `[~]` CP3: Constructive outside-open injectivity payload at `c = 2` (CP2→payload bridge wired; standalone proof still missing)
- `[~]` CP4: Constructive closed-range/properness payload at `c = 2` (preimage-compact/closed→properness→CP5 bridges wired; proof missing)
- `[~]` CP5: Build `external_ray_map_exists_two_constructive` (named endpoint wired; constructive body still pending)
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
  - `external_ray_map_exists_two_constructive` (current placeholder endpoint, body still axiom-seeded).
- This extends CP2/CP3/CP4 scaffolding and wires a single CP5 replacement point for
  the final constructive payload body, including quotient-const/analytic CP4 lanes.

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
