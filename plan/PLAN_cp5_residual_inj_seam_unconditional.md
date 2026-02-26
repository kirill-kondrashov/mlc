# PLAN: CP5 Residual Injectivity Seam (Unconditional)

## Goal
- [x] Prove `CP5ResidualInjOnOutsideOpenSeamTwo`.
- [x] Instantiate `external_ray_map_exists_two_constructive_of_cp5ResidualTwo`.
- [x] Obtain `CP5ResidualTwo → Quadratic.ExternalRayMapData (2 : ℂ)` without widening the axiom frontier.

## Parallel Placement
- [x] Assigned to **Track C (Alternative Ingress Backstops)** in
  `PLAN_axiom_elimination_status.md`.
- [x] Interface-coupled with Dudko ingress wrappers in
  `PLAN_dudko_2512_conformal_identification_formalization.md`.

## Branch Decomposition
- [x] Branch 1: `CP5ResidualLocalHomeomorphInjSeamTwo`
  - [x] Input/target split identified:
    `IsClosed(range) ∧ IsLocalHomeomorph(restrict-map)` -> outside-open `InjOn`.
  - [x] Constructive route selected:
    proper/local-homeomorph + degree-one-fiber route.
  - [x] Supporting file added:
    `Mlc/Quadratic/Complex/Bottcher/DegreeOneInj.lean`.
  - [x] Close final constructive proof for this branch.
- [ ] Branch 2: `CP5ResidualLandingInjSeamTwo`
  - [x] Input/target split identified:
    `ExternalRayLandsOutsideOpen (2 : ℂ)` -> outside-open `InjOn`.
  - [ ] Add refinement-to-injectivity bridge required by this branch.
  - [ ] Close final constructive proof for this branch.

## Implemented Wiring
- [x] Added branch seam definitions in `Mlc/MainConjecture.lean`:
  `CP5ResidualLocalHomeomorphInjSeamTwo`,
  `CP5ResidualLandingInjSeamTwo`.
- [x] Added branch combiner:
  `cp5ResidualInjOnOutsideOpenSeamTwo_of_branchSeams`.
- [x] Added equivalence/consumer wrappers:
  `cp5ResidualInjOnOutsideOpenSeamTwo_iff_branchSeams`,
  `external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_branchSeams`.
- [x] Added explicit axiom-seeded fallback witnesses for isolation only:
  `injOn_outside_open_two_axiom_seed`,
  `cp5ResidualInjOnOutsideOpenSeamTwo_axiom_seed`,
  `cp5ResidualLocalHomeomorphInjSeamTwo_axiom_seed`,
  `cp5ResidualLandingInjSeamTwo_axiom_seed`,
  `cp5ResidualInjOnOutsideOpenSeamTwo_axiom_seed_of_branchSeams`,
  `external_ray_map_exists_two_constructive_of_cp5ResidualTwo_axiom_seam`.
- [x] Re-routed strict-mono CP5 endpoint aliases through seam-parameterized
  uniqueness constructors (instead of direct seam shortcut calls):
  `external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen_strictMono_fn`,
  `external_ray_map_exists_two_constructive_of_cp5ResidualTwo_strictMono_unconditional_fn`.
- [x] Re-routed late strict-mono CP5 seam aliases through uniqueness-seam
  constructors:
  `cp5ResidualLocalHomeomorphInjSeamTwo_strictMono`,
  `cp5ResidualInjOnOutsideOpenSeamTwo_strictMono_of_not_externalRayLandsOutsideOpen`.
- [x] Added centralized strict-mono-seeded uniqueness witness alias and routed
  strict-mono CP5 wrappers through it:
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed`.
- [x] Routed strict-mono-seeded root injectivity witness through the same
  uniqueness-seam bridge:
  `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded`.
- [x] Repointed root-seeded strict-mono uniqueness alias
  (`greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_rootSafeOutsideOpenInjWitnessTwo`)
  to the centralized green-function-seeded alias path.
- [x] Bulk-repointed downstream strict-mono CP5/direct/local wrapper call sites
  to the centralized green-function-seeded uniqueness alias path, keeping the
  root-safe alias as compatibility only.

## Current Sprint
- [x] Re-verified Track C wrapper interfaces compile with current root-selector
  API (`lake build Mlc.MainConjecture`).
- [x] Add one constructive (non-axiom) branch-closing lemma to either Branch 1
  or Branch 2.
  Status: added
  `cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo` and
  `cp5ResidualInjOnOutsideOpenSeamTwo_of_directProperLocalWitnessTwo_of_not_externalRayLandsOutsideOpen`
  in `Mlc/MainConjecture.lean`.
