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
- Added boundary-exclusion specialization of that non-analytic route:
  - `directProperLocalWitnessTwo_of_isLocalHomeomorph_restrict_of_boundary_exclusion`
  - `external_ray_map_exists_two_constructive_of_isLocalHomeomorph_restrict_of_boundary_exclusion`
  This factors boundary exclusion into the direct-witness pipeline through `isClosed_outside_open_preimage_image_compact_of_boundary_exclusion`.
- Added local-homeomorph-on outside-open lifts for the non-analytic direct-witness route:
  - `directProperLocalWitnessTwo_of_isLocalHomeomorphOn_outside_open_of_preimage_closed`
  - `directProperLocalWitnessTwo_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion`
  - `external_ray_map_exists_two_constructive_of_isLocalHomeomorphOn_outside_open_of_preimage_closed`
  - `external_ray_map_exists_two_constructive_of_isLocalHomeomorphOn_outside_open_of_boundary_exclusion`
  This shifts the remaining assumptions further toward local Böttcher payload shapes.
- Added Dudko ingress from direct proper+local witness shapes:
  - `dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict`
  - `dynamicalBottcherConformalIdentificationTwo_of_directProperLocalWitnessTwo`
  - `external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo_via_dudko`
  This connects the direct CP5 closure criterion to the Dudko conformal-identification route.
- Added Dudko/direct-witness equivalence and assumption-lifted Dudko wrappers:
  - `directProperLocalWitnessTwo_of_dynamicalBottcherConformalIdentificationTwo`
  - `dynamicalBottcherConformalIdentificationTwo_iff_directProperLocalWitnessTwo`
  - Dudko ingress and endpoint wrappers from
    local-homeomorph (`...of_isLocalHomeomorph_restrict_of_preimage_closed`, `...of_boundary_exclusion`)
    and local-homeomorph-on (`...of_isLocalHomeomorphOn_outside_open_of_preimage_closed`, `...of_boundary_exclusion`)
    assumptions.
  This aligns all current non-analytic closure lanes with the Dudko ingress API.
- Added source-exhaustion normalization into direct-witness/Dudko forms:
  - `properLocalSourceExhaustionTwo_directProperLocalWitness`
  - `properLocalSourceExhaustionTwo_dynamicalBottcherConformalIdentification`
  - `external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_dudko`
  - `mlc_conjecture_of_knownProperLocalSourceCandidateTwo_or_dudko`
  This makes the remaining non-blocked CP5 ingress branch explicit at both endpoint and root levels.
- Added cross-normalization and direct-disjunction wrappers:
  - `properLocalSourceExhaustionTwo_knownSourceOrDudko_iff_directProperLocalWitness`
  - `external_ray_map_exists_two_constructive_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo`
  - `mlc_conjecture_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo`
  This aligns the exhausted disjunction APIs on both Dudko and direct-witness sides.
- Added aggregate non-axiomatic ingress normalization:
  - `RemainingConstructiveIngressTwo`
  - `remainingConstructiveIngressTwo_of_directProperLocalWitnessTwo`
  - `remainingConstructiveIngressTwo_of_dynamicalBottcherConformalIdentificationTwo`
  - `remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo`
  - `remainingConstructiveIngressTwo_of_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo`
  - `remainingConstructiveIngressTwo_iff_knownProperLocalSourceCandidateTwo_or_directProperLocalWitnessTwo`
  - `remainingConstructiveIngressTwo_iff_knownProperLocalSourceCandidateTwo_or_dynamicalBottcherConformalIdentificationTwo`
  - `remainingConstructiveIngressTwo_iff_dynamicalBottcherConformalIdentificationTwo_or_directProperLocalWitnessTwo`
  - `remainingConstructiveIngressTwo_iff_directProperLocalWitness`
  - `directProperLocalWitnessTwo_of_remainingConstructiveIngressTwo`
  - `dynamicalBottcherConformalIdentificationTwo_of_remainingConstructiveIngressTwo`
  - `remainingConstructiveIngressTwo_iff_dynamicalBottcherConformalIdentificationTwo`
  - `external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo`
  - `external_ray_map_exists_two_constructive_of_remainingConstructiveIngressTwo_via_dudko`
  - `external_ray_map_exists_two_constructive_of_directProperLocalWitnessTwo_via_remainingConstructiveIngressTwo`
  - `external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo_via_remainingConstructiveIngressTwo`
  - `mlc_conjecture_of_directProperLocalWitnessTwo_via_remainingConstructiveIngressTwo`
  - `mlc_conjecture_of_dynamicalBottcherConformalIdentificationTwo_via_remainingConstructiveIngressTwo`
  - `mlc_conjecture_of_remainingConstructiveIngressTwo`
  This consolidates all currently exposed non-axiomatic ingress branches into one predicate that normalizes to the direct witness target.

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
