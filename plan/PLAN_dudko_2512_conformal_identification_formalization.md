# PLAN: Dudko 2512.24171 Conformal-Identification Formalization (CP5 Ingress)

## Goal
- [ ] Provide a constructive conformal-identification ingress at `c = 2` that can
  feed the CP5 closure chain without reintroducing blocked axioms.
- [ ] Rewire final placeholder root paths once a concrete witness is available.

## Parallel Placement
- [x] Assigned to **Track C (Alternative Ingress Backstops)** in
  `PLAN_axiom_elimination_status.md`.
- [x] Coordinated with CP5 seam plan:
  `PLAN_cp5_residual_inj_seam_unconditional.md`.

## Scope
- [x] Formalized ingress proposition:
  `DynamicalBottcherConformalIdentificationTwo : Prop`.
- [x] Wired to CP5 residual and constructive endpoint wrappers.
- [x] Wired to root-level wrappers (`mlc_conjecture`-facing) through existing
  direct-witness/ingress normalization APIs.

## Implemented Bridges (Completed)
- [x] `isProperMap_and_isLocalHomeomorph_bottcher_map_outside_open_to_exterior_two_of_dynamicalBottcherConformalIdentificationTwo`
- [x] `cp5ResidualTwo_of_dynamicalBottcherConformalIdentificationTwo`
- [x] `external_ray_map_exists_two_constructive_of_dynamicalBottcherConformalIdentificationTwo`
- [x] Concrete ingress realizations from existing payloads:
  `dynamicalBottcherConformalIdentificationTwo_of_isProperMap_restrict_of_outsideOpenAnalyticInjPayload`,
  `..._of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis`.
- [x] Source-family wrappers and normalization with direct-witness / remaining-ingress APIs.

## Remaining Work
- [ ] Strengthen concrete realization so restricted properness is derived from
  non-axiomatic local inputs for `c = 2`.
- [ ] Produce a direct constructive witness of
  `IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧ IsLocalHomeomorph (...)`
  that avoids blocked source families.
- [ ] Rewire `external_ray_map_exists_two_constructive` off placeholders when
  the witness is available.

## Current Sprint
- [x] Re-validated compatibility with current selector/root wrapper stack
  (via successful `lake build Mlc.MainConjecture`).
- [x] Add one new witness-producing lemma or one new theorem-level reduction
  step toward the direct proper/local target.
  Status: added
  `directProperLocalWitnessTwo_and_cp5ResidualTwo_of_dynamicalBottcherConformalIdentificationTwo`
  in `Mlc/MainConjecture.lean`.
