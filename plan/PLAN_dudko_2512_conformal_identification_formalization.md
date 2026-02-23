# PLAN: Dudko 2512.24171 conformal-identification formalization (CP5 ingress)

## Scope
Formalize the input suggested by arXiv:2512.24171 (lines ~189-193): at `c = 2`, the restricted dynamical Böttcher map gives an outside-open/exterior conformal identification, and wire it into the existing CP5 residual closure chain.

## New Lean ingress (started)
- Added `DynamicalBottcherConformalIdentificationTwo : Prop` in `Mlc/MainConjecture.lean`:
  - `∃ e : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} ≃ₜ {w : ℂ // 1 < ‖w‖}, (fun z => e z) = bottcher_map_outside_open_to_exterior (2 : ℂ)`.

## Wiring added (started)
- `isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_dynamicalBottcherConformalIdentificationTwo`
  derives the CP5 left-branch pair from a homeomorphic identification input.
- `cp5ResidualTwo_of_dynamicalBottcherConformalIdentificationTwo`
  converts that pair to `CP5ResidualTwo`.
- `external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo`
  converts `CP5ResidualTwo` to the constructive CP5 endpoint data theorem.
- Added concrete ingress realizations from local Böttcher development:
  - `dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload`
  - `dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis`
  These discharge the abstract `∃ e : ... ≃ₜ ...` assumption from existing properness + outside-open payload lemmas.
- Added source-family Dudko bridges:
  - `dynamicalBottcherConformalIdentificationTwo_of_properLocalFromAnalyticPreimageClosedCandidateTwo`
  - `dynamicalBottcherConformalIdentificationTwo_of_properLocalFromAnalyticBoundaryExclusionCandidateTwo`
  - `dynamicalBottcherConformalIdentificationTwo_of_knownProperLocalSourceCandidateTwo`
  - `external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_via_dudko`
  This wires all currently catalogued proper+local source families through the Dudko route.
- Added direct Dudko-route endpoint wrappers from previously used assumptions:
  - `external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis_via_dudko`
  - `external_ray_map_exists_two_constructive_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload_via_dudko`
  This gives parity between legacy CP5 seams and the Dudko ingress route.
- Added explicit CP5 closure-criterion packaging:
  - `DirectProperLocalWitnessTwo`
  - `external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo`
  - `mlc_conjecture_of_directProperLocalWitnessTwo`
  This makes the final remaining implementation target explicit in Lean.
- Added a new non-analytic bridge toward the direct witness target:
  - `isProperMap_bottcher_map_outside_open_to_exterior_two_of_isLocalHomeomorph_restrict_of_preimage_closed`
  - `directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_preimage_closed`
  - `external_ray_map_exists_two_constructive_of_isLocalHomeomorph_restrict_of_preimage_closed`
  This opens a route where restricted properness is derived from local-homeomorph continuity plus ambient preimage-closed compact-target data, without requiring the blocked outside-open analyticity hypothesis.

## Remaining work
1. Strengthen the new concrete realization so that restricted properness is itself derived from non-axiomatic local inputs for `c = 2`.
2. Keep searching for a direct constructive witness of
   `IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧ IsLocalHomeomorph (...)`
   that avoids the blocked source families.
3. After a concrete witness is available, rewire the placeholder theorem
   `external_ray_map_exists_two_constructive` to remove `Quadratic.external_ray_map_exists`.

## Validation target
- `make build`
- `make check`
- `make graphs`
- `bash scripts/verify_output.sh`
