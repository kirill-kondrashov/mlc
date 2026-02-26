# Plan: Eliminate `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`

## Goal
- [ ] Remove `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam` from the axiom footprint of `MLC.mlc_conjecture`.

## Locked Model Constraints
- [x] `not_outsideOpenAnalyticityHypothesisTwo` blocks outside-open analyticity replacement.
- [x] `not_greenFunctionDegreeOneIngressTwo` blocks degree-one strict-mono-free replacement.
- [x] `not_knownInjOnOutsideOpenSourceCandidateTwo` blocks known injectivity-source replacement.
- [x] Strict-mono-free alternatives are treated as closed for root elimination.
- [x] Remaining constructive target is direct proof of monotonicity.

## Parallel Placement
- [x] Assigned to **Track A (Strict-Mono Elimination)** in
  `PLAN_axiom_elimination_status.md`.
- [x] Coordinated with:
  `PLAN_prove_green_function_radial_monotonicity.md` and
  `PLAN_basin_monotonicity_practical_way_forward.md`.

## Hard Constraints
- [x] Do not reintroduce `MLC.Quadratic.external_ray_map_exists` into the root path.
  Status: current `#print axioms MLC.mlc_conjecture` does not include
  `MLC.Quadratic.external_ray_map_exists`.
- [x] Keep `MLC.greenRayLogGtAnchorTwo_axiom_seed` unchanged for this plan (strict-mono elimination only).
  Status: retained as-is; no statement changes.

## Current State (Verified)
- [x] Legacy theorem still uses strict monotonicity:
  `GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function`.
- [x] Injectivity-routed variant is strict-mono free:
  `GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function_of_injOn_outside_open`.
- [x] Root selector is routed through the strict-mono-free seed constructor in
  `Mlc/MainConjecture.lean`; remaining strict-mono dependence is in the current
  witness source feeding that constructor.

## Phase 1: Cut Strict-Mono at MainConjecture Root Call Site
- [x] Replace body of `external_ray_map_exists_two_constructive` to use
  `external_ray_map_exists_two_constructive_of_green_function_of_injOn_outside_open`
  (instead of legacy `..._via_green_function`).
  Status: now routed through outside-open injectivity from the strict-mono
  Green-ray injectivity route; this localizes remaining strict-mono dependence
  to the legacy witness source.
- [x] Provide root-safe witness for outside-open injectivity at `c = 2` from an ingress that does **not** use `external_ray_map_exists`.
  Status: `rootSafeOutsideOpenInjWitnessTwo_of_external_ray_map_exists_two_constructive_legacy_strictMono`
  is now the active root witness source; axiom scan confirms it does not depend
  on `MLC.Quadratic.external_ray_map_exists`.
- [x] Re-run axiom check for:
  `MLC.external_ray_map_exists_two_constructive`,
  `MLC.mlc_conjecture`.
  Status: both still include
  `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`.
- [x] Added a strict-mono-free assumption-layer external-ray-data theorem:
  `external_ray_map_exists_two_constructive_of_green_function_degreeOneIngressTwo`
  (keeps root unchanged while validating the bridge path).
- [x] Isolated the exact remaining root target as a named witness:
  `RootSafeOutsideOpenInjWitnessTwo`,
  with strict-mono-free candidate wrappers:
  `external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo`,
  `mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo`.
- [x] Added canonical constructor from degree-one hypotheses to the root target:
  `rootSafeOutsideOpenInjWitnessTwo_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness`
  and routed
  `external_ray_map_exists_two_constructive_of_green_function_degreeOneIngressTwo`
  through this target.
- [x] Added package-level bridge from degree-one ingress to root target:
  `rootSafeOutsideOpenInjWitnessTwo_of_green_function_degreeOneIngressTwo`.
- [x] Added a root-seed selector split in `MainConjecture`:
  `externalRayMapData_two_legacy_seed`,
  `externalRayMapData_two_strictMonoFree_candidate_seed`,
  `externalRayMapData_two_root_seed`.
  Selector is now routed through the strict-mono-free constructor; remaining
  strict-mono dependence is in the witness source currently feeding that
  constructor.
- [x] Routed `mlc_conjecture` through a centralized root-seed theorem:
  `mlc_conjecture_of_externalRayMapData_two_root_seed` to keep final swap
  localized.
- [x] Rewired `externalRayMapData_two_root_seed` to the strict-mono-free seed
  constructor, fed by
  `rootSafeOutsideOpenInjWitnessTwo_of_external_ray_map_exists_two_constructive_legacy_strictMono`
  (so root no longer aliases a legacy root-seed wrapper directly).
- [x] Isolated the currently unresolved root witness source explicitly to the
  legacy strict-mono endpoint via
  `rootSafeOutsideOpenInjWitnessTwo_of_external_ray_map_exists_two_constructive_legacy_strictMono`.

## Phase 2: Keep the Frontier Safe While Supplying Injectivity
- [x] Route injectivity through the degree-one ingress package already implemented:
  `properLocalDegreeOneFiberWitnessTwo_of_isProperMap_of_injOn_outside_open`,
  `injOn_outside_open_two_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness`,
  and wrappers.
  Status:
  `external_ray_map_exists_two_constructive_of_green_function_degreeOneIngressTwo`
  is now available and strict-mono free.
- [x] Complete one non-`external_ray_map_exists` source of required hypotheses
  (outside-open `InjOn` route), via:
  `rootSafeOutsideOpenInjWitnessTwo_of_knownInjOnOutsideOpenSourceCandidateTwo`,
  `rootSafeOutsideOpenInjWitnessTwo_of_outsideOpenAnalyticityHypothesis`,
  and strict-mono-free root-candidate wrappers.
  Note: in the current model, these sources are still blocked globally by
  `not_knownInjOnOutsideOpenSourceCandidateTwo` and
  `not_outsideOpenAnalyticityHypothesisTwo`.
- [x] Added temporary assumption-layer root-seed theorems (non-root default):
  `externalRayMapData_two_root_seed_strictMonoFree_of_rootSafeOutsideOpenInjWitnessTwo`,
  `externalRayMapData_two_root_seed_strictMonoFree_of_green_function_degreeOneIngressTwo`,
  and corresponding `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_*`
  wrappers; axiom scans confirm strict-mono is absent on these paths.
- [x] Extended selector-layer strict-mono-free coverage to the two existing
  frontier-safe source families:
  `..._of_knownInjOnOutsideOpenSourceCandidateTwo` and
  `..._of_outsideOpenAnalyticityHypothesis` (both seed and rooted variants).
- [x] Added direct strict-mono-free rooted wrappers for those same families:
  `mlc_conjecture_of_green_function_of_knownInjOnOutsideOpenSourceCandidateTwo`
  and `mlc_conjecture_of_green_function_of_outsideOpenAnalyticityHypothesis`
  (axiom scan: no strict-mono seam).
- [x] Re-routed the direct-proper witness branch to the strict-mono Green-ray
  injectivity seam:
  `injOn_outside_open_two_of_directProperLocalWitnessTwo_constructive`,
  `external_ray_map_exists_two_constructive_of_green_function_of_directProperLocalWitnessTwo`,
  and `mlc_conjecture_of_green_function_of_directProperLocalWitnessTwo` no
  longer depend on `MLC.Quadratic.external_ray_map_exists`.
- [x] Split the direct-proper injectivity route into a seam-parameterized bridge
  and a strict-mono specialization:
  `injOn_outside_open_two_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`,
  `rootSafeOutsideOpenInjWitnessTwo_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`,
  and `injOn_outside_open_two_of_directProperLocalWitnessTwo_constructive`.
  Status: the generic bridge is axiom-minimal (`Quot.sound`, `propext`,
  `Classical.choice`) and keeps strict-mono dependence isolated to the
  specialization.
- [x] Added direct-proper strict-mono-free candidate wrappers parameterized by
  the same local-homeomorph seam witness:
  `external_ray_map_exists_two_constructive_strictMono_free_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`
  and
  `mlc_conjecture_strictMonoFree_candidate_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`.
  Status: axiom scan shows no `green_function_strictMono_along_ray_basin_seam`
  and no `MLC.Quadratic.external_ray_map_exists` on this candidate path.
- [x] Added CP5 local-homeomorph-branch strict-mono-free candidate wrappers
  that avoid `CP5ResidualTwo` in their theorem types:
  `external_ray_map_exists_two_constructive_strictMono_free_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`
  and
  `mlc_conjecture_strictMonoFree_candidate_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`.
  Status: axiom scan shows this surrogate branch uses only
  `Quot.sound`, `propext`, `Classical.choice`, and
  `greenRayLogGtAnchorTwo_axiom_seed` (no
  `green_function_strictMono_along_ray_basin_seam`, no
  `MLC.Quadratic.external_ray_map_exists`).
- [x] Added strict-mono-free wrappers for the explicit restricted-map
  proper/local-homeomorph source family:
  `external_ray_map_exists_two_constructive_strictMono_free_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo`
  and
  `mlc_conjecture_strictMonoFree_candidate_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo`.
  Status: axiom scan matches the same frontier-safe profile
  (`Quot.sound`, `propext`, `Classical.choice`,
  `greenRayLogGtAnchorTwo_axiom_seed`).
- [x] Added root-target and root-seed strict-mono-free specializations for the
  CP5 local-homeomorph surrogate sources:
  `rootSafeOutsideOpenInjWitnessTwo_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`,
  `externalRayMapData_two_root_seed_strictMonoFree_of_localHomeomorphSurjSourceTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`,
  `externalRayMapData_two_root_seed_strictMonoFree_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_of_cp5ResidualLocalHomeomorphInjSeamTwo`,
  and rooted wrappers
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_*`.
  Status: these selector-level routes remain frontier-safe
  (no `green_function_strictMono_along_ray_basin_seam`,
  no `MLC.Quadratic.external_ray_map_exists`).
- [x] Extended selector/root-candidate API coverage for the CP5 local-homeomorph
  surrogate family with direct-witness specializations:
  `externalRayMapData_two_root_seed_strictMonoFree_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_directProperLocalWitnessTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`,
  and root-candidate wrappers
  `mlc_conjecture_root_candidate_of_*_of_cp5ResidualLocalHomeomorphInjSeamTwo`.
  Status: these wrappers keep the same frontier-safe axiom profile
  (`Quot.sound`, `propext`, `Classical.choice`,
  `greenRayLogGtAnchorTwo_axiom_seed`).
- [x] Added strict-mono-seeded (no seam-argument) specializations for the
  explicit restricted-map proper/local source family:
  `rootSafeOutsideOpenInjWitnessTwo_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_strictMono`,
  `externalRayMapData_two_root_seed_strictMonoFree_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_strictMono`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_strictMono`,
  and `mlc_conjecture_root_candidate_of_isProperMap_restrict_of_isLocalHomeomorph_restrict_strictMono`.
  Status: these wrappers remain free of `MLC.Quadratic.external_ray_map_exists`
  while explicitly carrying the strict-mono seam dependency
  (`MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`), as
  expected for the seeded specialization.
- [x] Added strict-mono-seeded selector/root wrappers for the CP5 local
  surrogate family’s direct/local variants:
  `externalRayMapData_two_root_seed_strictMonoFree_of_directProperLocalWitnessTwo_strictMono`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_localHomeomorphSurjSourceTwo_strictMono`,
  and
  `mlc_conjecture_root_candidate_of_directProperLocalWitnessTwo_strictMono`
  (plus local/source siblings).
  Status: these wrappers keep the expected seeded profile
  (`green_function_strictMono_along_ray_basin_seam` present, still no
  `MLC.Quadratic.external_ray_map_exists`).
- [x] Added strict-mono-seeded convenience wrappers at the constructive endpoint
  layer (`external_ray_map_exists_two_constructive_strictMono_seeded_of_*`) and
  rooted layer (`mlc_conjecture_strictMono_seeded_of_*`) for direct/local and
  explicit restricted-map ingress families.
  Status: `#print axioms` confirms the expected seeded profile
  (`MLC.greenRayLogGtAnchorTwo_axiom_seed`,
  `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`) and still no
  `MLC.Quadratic.external_ray_map_exists`.
- [x] Filled the missing direct-proper seam-parameterized tier for the same
  strict-mono-seeded convenience family:
  `external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo`
  and
  `mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo`,
  and rewired the existing direct-proper seeded aliases to these seam forms.
  Status: generalized wrappers are strict-mono free except for
  `MLC.greenRayLogGtAnchorTwo_axiom_seed`; seeded aliases keep the expected
  strict-mono profile, with no `MLC.Quadratic.external_ray_map_exists`.
- [x] Factored Green-ray outside-open injectivity through an explicit
  uniqueness seam at `c = 2`:
  `GreenRayUniquePreimageTwoAnchorSeam`,
  `injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`,
  plus strict-mono specialization
  `greenRayUniquePreimageTwoAnchorSeam_strictMono`.
  Status: axiom scan shows the generalized bridge is seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice` only); strict-mono now enters
  only through the specialization witness used by current root defaults.
- [x] Extended the same seam-parameterized factoring to CP5/local and endpoint
  wrappers:
  `cp5ResidualLocalHomeomorphInjSeamTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`,
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`,
  and `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`
  (with strict-mono defaults as specializations).
  Status: endpoint/root wrappers are seam-minimal (`Quot.sound`, `propext`,
  `Classical.choice` only). The no-landing CP5 seam wrapper remains
  `MLC.Quadratic.external_ray_map_exists`-contaminated through the proposition
  type `ExternalRayLandsOutsideOpen`, as expected.
- [x] Re-routed strict-mono CP5 endpoint aliases
  (`..._of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen_strictMono_fn`,
  `..._of_cp5ResidualTwo_strictMono_unconditional_fn`)
  through the seam-parameterized uniqueness constructor family to centralize
  strict-mono entry behind the uniqueness seam witness.
- [x] Re-routed late strict-mono CP5 seam aliases
  (`cp5ResidualLocalHomeomorphInjSeamTwo_strictMono`,
  `cp5ResidualInjOnOutsideOpenSeamTwo_strictMono_of_not_externalRayLandsOutsideOpen`)
  through the same uniqueness-seam constructor family.
- [x] Added centralized strict-mono-seeded uniqueness witness alias
  (`greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed`)
  and re-routed strict-mono CP5 wrappers to use it, reducing repeated strict-mono
  witness expressions and tightening dependency hygiene.
- [x] Re-routed `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded` through the
  uniqueness-seam bridge, so strict-mono seeded root witness construction now
  follows the same centralized uniqueness-seam path as CP5 endpoint wrappers.
- [x] Repointed
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_rootSafeOutsideOpenInjWitnessTwo`
  to the centralized alias
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed`,
  reducing duplicate strict-mono seed routes.
- [x] Bulk-replaced downstream wrapper call sites to use
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed`
  as the default strict-mono-seeded uniqueness witness (kept the
  root-safe alias as a compatibility wrapper).
- [x] Re-routed `injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam` to the
  centralized strict-mono-seeded uniqueness alias path.
- [x] Repointed compatibility theorem
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_injOn_outside_open`
  to the centralized green-function-seeded uniqueness alias.
- [x] Reduced strict-mono root-seed alias depth:
  `rootSeedPayloadTwo_strictMono_seeded` now consumes
  `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded` directly (instead of
  the extra `rootSafeOutsideOpenInjWitnessTwo_seed` indirection).
- [x] Reduced strict-mono root-seam-bundle alias depth:
  `rootSeedPairTwo_strictMono_seeded` now consumes
  `rootSeedPayloadTwo_strictMono_seeded` directly and `rootSeedPairTwo_seed`
  is an alias of `rootSeedPairTwo_strictMono_seeded`.
- [x] Reduced strict-mono root selector/root theorem alias depth by routing:
  `externalRayMapData_two_root_seed_strictMono_seeded`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMono_seeded`,
  and `mlc_conjecture` through `rootSeedPayloadTwo_strictMono_seeded`.
- [x] Removed dead strict-mono compatibility aliases from `MainConjecture.lean`:
  `rootSafeOutsideOpenInjWitnessTwo_seed`,
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_rootSafeOutsideOpenInjWitnessTwo`,
  `rootSeedPayloadTwo_seed`,
  `rootSeedPairTwo_seed`.
- [x] Added a seam-parameterized root-witness bridge and rewired the centralized
  root seed to use its strict-mono-seeded specialization:
  `rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`,
  `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded`,
  and `externalRayMapData_two_root_seed`.
  Status: generalized root-witness bridge is seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice` only); root footprint is
  unchanged and continues to carry strict-mono only via the seeded witness.
- [x] Generalized the injectivity-based Green inversion endpoint wrappers to
  accept an explicit anchor-gap seam parameter:
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open`
  and
  `external_ray_map_exists_two_constructive_strictMono_free_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam`,
  with existing `..._of_green_function_...` names retained as seeded
  specializations.
  Status: axiom scan shows the new parameterized wrappers are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`), and seeded aliases keep the
  expected `greenRayLogGtAnchorTwo_axiom_seed` profile.
- [x] Extended seam-parameterization at the root-seed/root-candidate layer:
  `externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam`,
  `mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam`,
  plus centralized default alias
  `external_ray_map_exists_two_constructive_strictMono_seeded`.
  Status: the new parameterized root wrappers are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`); seeded aliases preserve the
  expected `greenRayLogGtAnchorTwo_axiom_seed` profile.
- [x] Generalized the centralized root seed and rooted selector theorem through
  explicit Green-ray seams:
  `externalRayMapData_two_root_seed_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`,
  with strict-mono-seeded defaults
  `externalRayMapData_two_root_seed_strictMono_seeded` and
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMono_seeded`.
  Status: generalized root-seed/rooted selectors are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`), while root defaults keep the
  expected strict-mono-seeded profile.
- [x] Lifted the same anchor-seam parameterization through the packaged
  degree-one ingress family:
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo`,
  `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo`,
  and
  `externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_green_function_degreeOneIngressTwo`,
  with existing `...of_green_function_degreeOneIngressTwo` names retained as
  seeded specializations.
  Status: parameterized wrappers are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`); seeded specializations keep
  the expected `greenRayLogGtAnchorTwo_axiom_seed` profile.
- [x] Lifted anchor-seam parameterization through the known-injectivity and
  outside-open-analyticity source families at endpoint, seed, root-candidate,
  and rooted-theorem layers:
  `external_ray_map_exists_two_constructive_strictMono_free_of_greenRayLogGtAnchorTwoSeam_of_*`,
  `externalRayMapData_two_strictMonoFree_candidate_seed_of_greenRayLogGtAnchorTwoSeam_of_*`,
  `mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_*`,
  and `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_*`.
  Status: parameterized wrappers are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`), and existing non-parameterized
  wrappers remain seeded specializations with expected
  `greenRayLogGtAnchorTwo_axiom_seed`.
- [x] Added a second seam-parameterization tier for the
  `externalRayMapData_two_root_seed_strictMonoFree_of_*` family and matching
  rooted theorem wrappers:
  `externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_*`
  and
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_*`,
  with existing non-parameterized names kept as seeded specializations.
  Status: parameterized wrappers are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`); seeded wrappers carry only the
  expected `greenRayLogGtAnchorTwo_axiom_seed` among frontier axioms.
- [x] Added direct-proper branch seam-parameterized wrappers through both
  Green-ray seams:
  `injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo`,
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo`,
  and
  `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo`,
  with existing `...of_green_function_of_directProperLocalWitnessTwo` names
  retained as strict-mono-seeded specializations.
  Status: generalized direct-proper wrappers are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`); seeded wrappers keep the
  expected strict-mono profile.
- [x] Added local-homeomorph-source seam-parameterized strict-mono-seeded
  wrapper tier (plus explicit restricted-map sibling) through both Green-ray
  seams:
  `rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_*`,
  `external_ray_map_exists_two_constructive_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_*`,
  and `mlc_conjecture_strictMono_seeded_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_*`,
  with existing `..._strictMono` names retained as seeded specializations.
  Status: root-witness wrappers are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`), while seeded endpoint/rooted
  wrappers carry only the expected `greenRayLogGtAnchorTwo_axiom_seed` among
  frontier axioms.
- [x] Added CP5 no-landing/unconditional seam-parameterized wrappers through
  both Green-ray seams for both endpoint and rooted layers:
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen`,
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional`,
  `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen`,
  and `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional`,
  with existing `...of_green_function...` names retained as strict-mono-seeded
  specializations.
  Status: strict-mono dependence is removed from these generalized wrappers, but
  `MLC.Quadratic.external_ray_map_exists` contamination remains due
  `CP5ResidualTwo`/`ExternalRayLandsOutsideOpen` proposition-level branches, and
  the unconditional variants additionally carry
  `MLC.Quadratic.extended_ray_map_continuous`.
- [x] Added iterate-left-inverse branch anchor-seam parameterized wrappers at
  endpoint and rooted layers:
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_iter_left_inverse`
  and `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_iter_left_inverse_two`,
  with existing `...of_green_function_of_iter_left_inverse...` names kept as
  seeded specializations.
  Status: strict-mono dependence is removed from the generalized wrappers, but
  this branch remains frontier-unsafe due
  `MLC.Quadratic.external_ray_map_exists` and
  `MLC.Quadratic.bottcher_seq_converges` carried by the iterate-left-inverse
  route in the current development.
- [x] Lifted anchor-seam parameterization through the direct global
  proper/local wrappers (degree-one and outside-open-injective forms), plus
  rooted counterparts:
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_*`
  and
  `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_isProperMap_isLocalHomeomorph_of_*`,
  together with
  `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open_two`.
  Existing `...of_green_function...` names remain seeded specializations.
  Status: generalized wrappers are seam-minimal
  (`Quot.sound`, `propext`, `Classical.choice`); seeded aliases keep the
  expected `greenRayLogGtAnchorTwo_axiom_seed` profile.
- [x] Added function-level CP5 residual endpoint seam wrappers (and strict-mono
  seeded aliases) for no-landing and unconditional routes:
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen_fn`,
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_cp5ResidualTwo_unconditional_fn`,
  and strict-mono counterparts
  `..._of_not_externalRayLandsOutsideOpen_strictMono_fn`,
  `..._of_cp5ResidualTwo_strictMono_unconditional_fn`.
  Status: strict-mono dependence is removed from generalized function wrappers,
  but this function-level CP5 route remains frontier-unsafe due
  `MLC.Quadratic.external_ray_map_exists` and
  `MLC.Quadratic.bottcher_seq_converges`; unconditional variants also include
  `MLC.Quadratic.extended_ray_map_continuous`.
- [x] Added late strict-mono CP5 seam replacements:
  `cp5ResidualLocalHomeomorphInjSeamTwo_strictMono` and
  `cp5ResidualInjOnOutsideOpenSeamTwo_strictMono_of_not_externalRayLandsOutsideOpen`,
  and rewired
  `external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen`
  to this replacement seam.
  Status: this improves local factoring but does **not** yet remove
  `MLC.Quadratic.external_ray_map_exists` from that CP5 route because
  `ExternalRayLandsOutsideOpen` appears in the seam hypothesis type.
- [x] Added explicit end-state candidate root theorem aliases:
  `mlc_conjecture_strictMonoFree_candidate_of_rootSafeOutsideOpenInjWitnessTwo`
  and `..._of_green_function_degreeOneIngressTwo`, plus
  `external_ray_map_exists_two_constructive_eq_legacy_strictMono` as a boundary
  marker for the remaining strict-mono ingress.
- [x] Added Green-ray seam-parameterized root-seed wrappers for the direct/local
  CP5 family:
  `externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo`,
  `..._of_localHomeomorphSurjSourceTwo`, and
  `..._of_isProperMap_restrict_of_isLocalHomeomorph_restrict`.
  Rewired strict-mono convenience wrappers in this family to these seam forms.
  Status: strict-mono dependence is now concentrated in the explicit seeded
  specializations (via `greenRayUniquePreimageTwoAnchorSeam_strictMono`).
- [x] Added the same Green-ray seam-parameterized lift at the root-candidate
  theorem layer for the direct/local CP5 family:
  `mlc_conjecture_root_candidate_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo`,
  `..._of_localHomeomorphSurjSourceTwo`, and
  `..._of_isProperMap_restrict_of_isLocalHomeomorph_restrict`, with strict-mono
  aliases rewired to these new wrappers.
  Status: generalized wrappers are strict-mono free; seeded aliases keep the
  expected strict-mono profile.
- [x] Added the same Green-ray seam-parameterized lift at the
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree` theorem
  layer for the direct/local CP5 family:
  `..._of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam_of_directProperLocalWitnessTwo`,
  `..._of_localHomeomorphSurjSourceTwo`, and
  `..._of_isProperMap_restrict_of_isLocalHomeomorph_restrict`; rewired the
  corresponding `..._strictMono` aliases to these seam wrappers.
  Status: generalized wrappers are seam-minimal (`Quot.sound`, `propext`,
  `Classical.choice`), while seeded aliases keep the expected strict-mono
  profile.
- [x] Introduced a centralized strict-mono uniqueness-seam seed alias
  `greenRayUniquePreimageTwoAnchorSeam_seed` and rewired root-entry strict-mono
  constructors (`cp5ResidualLocalHomeomorphInjSeamTwo_strictMono`,
  `cp5ResidualInjOnOutsideOpenSeamTwo_strictMono_of_not_externalRayLandsOutsideOpen`,
  `external_ray_map_exists_two_constructive_legacy_strictMono`,
  `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded`,
  `externalRayMapData_two_root_seed_strictMono_seeded`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMono_seeded`) to
  this alias.
  Status: no axiom-profile change, but strict-mono root ingress is now anchored
  at a single named swap point.
- [x] Completed seed-centralization follow-through: replaced remaining uses of
  `greenRayUniquePreimageTwoAnchorSeam_strictMono` across `MainConjecture`
  wrappers with `greenRayUniquePreimageTwoAnchorSeam_seed` (keeping the
  original strict-mono theorem as the seed definition source).
  Status: behavior/axiom profile unchanged; subsequent strict-mono elimination
  now requires replacing only `greenRayUniquePreimageTwoAnchorSeam_seed`.
- [x] Added the reverse bridge from outside-open injectivity back to the
  anchored uniqueness seam:
  `greenRayUniquePreimageTwoAnchorSeam_of_greenRayLogGtAnchorTwoSeam_of_injOn_outside_open`.
  Status: axiom scan shows this bridge is seam-minimal (`Quot.sound`,
  `propext`, `Classical.choice`) and does not use
  `green_function_strictMono_along_ray_basin_seam`; strict-mono remains only in
  the current seed `greenRayUniquePreimageTwoAnchorSeam_seed`.
- [x] Rewired strict-mono-seeded root uniqueness packaging through the new
  reverse bridge: `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded` is now
  proved directly via Green inversion + outside-open left-inverse extraction,
  and `rootSeedPairTwo_seed` now uses
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_rootSafeOutsideOpenInjWitnessTwo`.
  Status: frontier unchanged (`greenRayLogGtAnchorTwo_axiom_seed` +
  `green_function_strictMono_along_ray_basin_seam`), but seed wiring no longer
  depends on the old direct uniqueness strict-mono specialization.
- [x] Added centralized root-seam-bundle constructor from
  `(GreenRayLogGtAnchorTwoSeam × RootSafeOutsideOpenInjWitnessTwo)`:
  `rootSeedPairTwo_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo`,
  plus seeded alias `rootSeedPairTwo_strictMono_seeded`; rewired
  `rootSeedPairTwo_seed` and strict-mono-seeded root theorem wrappers through
  this constructor.
  Status: no frontier change, but the seeded root path is now factored through
  the exact target witness (`RootSafeOutsideOpenInjWitnessTwo`) with a single
  root-seam bundle constructor.
- [x] Rewired strict-mono-free root theorem wrappers to flow through the same
  root-seam bundle constructor path:
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo`,
  plus specialized wrappers for `green_function_degreeOneIngressTwo`,
  `DirectProperLocalWitnessTwo`, and local-homeomorph source pairs.
  Status: the core wrapper path is seam-minimal (`Quot.sound`, `propext`,
  `Classical.choice`); frontier remains unchanged because seeded specializations
  still supply the remaining root axioms.
- [x] Rewired root-candidate wrappers to the same canonical root-seam-bundle
  path:
  `mlc_conjecture_root_candidate_of_rootSafeOutsideOpenInjWitnessTwo_of_greenRayLogGtAnchorTwoSeam`
  and `mlc_conjecture_root_candidate_of_green_function_degreeOneIngressTwo`
  no longer call the external-ray endpoint constructors directly.
  Status: wrapper layering is now consistent (single root assembly path), with
  unchanged frontier axioms.
- [x] Normalized late strict-mono-seeded seam specializations to use the
  root-safe-derived uniqueness seed
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_rootSafeOutsideOpenInjWitnessTwo`
  (instead of direct `greenRayUniquePreimageTwoAnchorSeam_seed`) across
  post-root-witness wrappers.
  Status: no frontier change, but strict-mono seed usage is now concentrated in
  earlier legacy ingress and root-safe seed bridge points.
- [x] Rewired `external_ray_map_exists_two_constructive_strictMono_seeded` to
  the injectivity-based Green inversion constructor
  (`..._via_green_function_of_injOn_outside_open`) instead of aliasing
  `external_ray_map_exists_two_constructive_legacy_strictMono`.
  Status: axiom footprint is unchanged, but seeded endpoint layering no longer
  depends directly on the legacy endpoint theorem body.
- [x] Added an independent strict-mono-seeded outside-open injectivity witness
  (`injOn_outside_open_two_strictMono_seeded`) and rewired early strict-mono
  seam wrappers to derive uniqueness through
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_injOn_outside_open`.
  Status: direct uses of `greenRayUniquePreimageTwoAnchorSeam_seed` in
  `MainConjecture` are reduced to the seed definition itself and the explicit
  legacy boundary endpoint theorem; the rest of strict-mono wrappers now route
  through the injectivity-derived uniqueness seed.
- [x] Rewired the explicit legacy boundary endpoint
  `external_ray_map_exists_two_constructive_legacy_strictMono` to the
  injectivity-derived strict-mono uniqueness seed
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_injOn_outside_open`.
  Status: `MainConjecture` now has a single direct occurrence of
  `greenRayUniquePreimageTwoAnchorSeam_seed` (its own definition line).
- [x] Canonicalized seeded strict-mono outside-open injectivity witnesses:
  `injOn_outside_open_two_of_external_ray_map_exists_two_constructive_legacy_strictMono`,
  `rootSafeOutsideOpenInjWitnessTwo_of_external_ray_map_exists_two_constructive_legacy_strictMono`,
  and `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded` now all route to the
  single theorem `injOn_outside_open_two_strictMono_seeded`.
  Status: no frontier change; strict-mono seeded injectivity ingress now has one
  canonical source theorem in `MainConjecture`.
- [x] Removed dead legacy-named injectivity wrapper declarations after
  canonicalization:
  `injOn_outside_open_two_of_external_ray_map_exists_two_constructive_legacy_strictMono`
  and
  `rootSafeOutsideOpenInjWitnessTwo_of_external_ray_map_exists_two_constructive_legacy_strictMono`.
  Status: no behavior/axiom change; reduces legacy ingress surface area and
  keeps only canonical seeded injectivity aliases.
- [x] Converted the legacy boundary endpoint theorem to a pure alias:
  `external_ray_map_exists_two_constructive_legacy_strictMono` now aliases
  `external_ray_map_exists_two_constructive_strictMono_seeded` instead of
  carrying an independent strict-mono proof body.
  Status: no frontier change; removes duplicate seeded strict-mono endpoint
  implementation while preserving boundary naming for tracking.
- [x] Re-pointed `external_ray_map_exists_two_constructive_strictMono_seeded`
  to the direct strict-mono Green inversion constructor
  (`external_ray_map_exists_two_via_green_function`) rather than the
  injectivity-based variant.
  Status: axiom profile unchanged; seeded endpoint ingress is now explicitly
  anchored at the direct strict-mono constructor, while injectivity-derived
  strict-mono bridges remain available for seam factoring.
- [x] Re-routed CP5 strict-mono seam wrappers
  (`cp5ResidualLocalHomeomorphInjSeamTwo_strictMono`,
  `cp5ResidualInjOnOutsideOpenSeamTwo_strictMono_of_not_externalRayLandsOutsideOpen`,
  and `external_ray_map_exists_two_constructive_of_cp5ResidualTwo_*_strictMono_fn`)
  through the canonical constructive seam chain.
  Status: `mlc_conjecture` frontier is unchanged; these CP5 wrappers remain
  frontier-unsafe (still carrying `MLC.Quadratic.external_ray_map_exists` on
  the residual/no-landing branch), which matches the existing blocker model.
- [x] Removed obsolete direct strict-mono uniqueness-seed declarations from
  `MainConjecture`:
  `greenRayUniquePreimageTwoAnchorSeam_strictMono` and
  `greenRayUniquePreimageTwoAnchorSeam_seed`.
  Status: all strict-mono uniqueness routing now goes through the
  injectivity-derived seed bridge
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_injOn_outside_open`;
  no behavior or frontier change.
- [x] Removed the now-redundant legacy endpoint alias theorem
  `external_ray_map_exists_two_constructive_legacy_strictMono` and replaced the
  boundary marker with
  `external_ray_map_exists_two_constructive_eq_strictMono_seeded`.
  Status: boundary tracking is preserved while removing one more duplicate
  strict-mono endpoint symbol; no frontier change.
- [x] Added a centralized anchor-gap seed alias
  `greenRayLogGtAnchorTwo_seed` and rewired post-definition uses of
  `greenRayLogGtAnchorTwo_axiom_seed` to this alias throughout
  `MainConjecture` wrappers.
  Status: behavior/axiom profile unchanged; anchor-gap axiom ingress is now
  concentrated at one named swap point for future elimination.
- [x] Added centralized root-seam bundle packaging:
  `RootSeedPairTwo`, `rootSeedPairTwo_seed`,
  `externalRayMapData_two_root_seed_of_rootSeedPairTwo`, and
  `mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPairTwo`;
  rewired strict-mono-seeded root selectors to this bundle.
  Status: `rootSeedPairTwo_seed` now captures both remaining root axioms in one
  place, while bundle-parameterized root wrappers are seam-minimal.
- [x] Re-routed the final exported theorem through the root-seam bundle:
  added `mlc_conjecture_of_rootSeedPairTwo` and changed `mlc_conjecture` to
  call it with `rootSeedPairTwo_seed`.
  Status: no frontier change, but root elimination now has a single explicit
  entry point theorem + single bundled seed value.
- [x] Extended the aggregated strict-mono-free ingress bundle to the
  centralized root-seed route:
  `rootSeedPairTwo_of_greenRayLogGtAnchorTwoSeam_of_strictMonoFreeIngressTwo`,
  `externalRayMapData_two_root_seed_strictMonoFree_of_strictMonoFreeIngressTwo`,
  and
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMonoFree_of_strictMonoFreeIngressTwo`.
  Status: this now expresses the strict-mono-free candidate directly on the
  exact final root-seed path; `#print axioms` confirms only
  `greenRayLogGtAnchorTwo_axiom_seed` remains among frontier axioms on that
  candidate route.
- [x] Added a centralized seeded root injectivity alias
  `rootSafeOutsideOpenInjWitnessTwo_seed` and rewired seeded root selectors to
  use it (`rootSeedPairTwo_strictMono_seeded`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMono_seeded`).
  Status: strict-mono dependence is now isolated behind one named root witness
  seed swap point on the final route; axiom profile unchanged.
- [x] Added a centralized root-seed payload layer and routed seeded selectors
  through it:
  `RootSeedPayloadTwo`,
  `rootSeedPayloadTwo_seed`,
  `externalRayMapData_two_root_seed_of_rootSeedPayloadTwo`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_of_rootSeedPayloadTwo`.
  Status: the final root route now factors as payload -> seam-pair -> endpoint;
  strict-mono elimination swap points are localized at payload seed
  construction, while strict-mono-free ingress wrappers still carry only
  `greenRayLogGtAnchorTwo_axiom_seed`.
- [x] Added payload-level root theorem entrypoints and routed the final theorem
  through payload seed directly:
  `mlc_conjecture_of_rootSeedPayloadTwo`,
  `mlc_conjecture_of_greenRayLogGtAnchorTwoSeam_of_rootSafeOutsideOpenInjWitnessTwo_via_rootSeedPayloadTwo`,
  and final `mlc_conjecture := mlc_conjecture_of_rootSeedPayloadTwo rootSeedPayloadTwo_seed`.
  Status: final route is now explicitly payload-first; pair-based wrappers are
  compatibility aliases. Axiom frontier is unchanged.

## Phase 3: Retire Strict-Mono Dependency
- [x] Remove remaining call paths to
  `GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function`.
  Status: `MainConjecture` now routes through the injectivity-based constructor
  (`..._via_green_function_of_injOn_outside_open`) with
  `injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam`; only a docstring
  mention of `..._via_green_function` remains.
- [x] Delete or deprecate strict-mono seam uses in `MainConjecture` wrappers.
  Status: removed now-unused `externalRayMapData_two_legacy_seed` wrapper and
  kept legacy strict-mono dependence isolated to
  `external_ray_map_exists_two_constructive_legacy_strictMono` plus its
  dedicated root-witness extractor.
- [ ] Remove `green_function_strictMono_along_ray_basin_seam` from
  `Mlc/Quadratic/Complex/Axioms.lean` when no theorem depends on it.
- [x] Isolated current strict-mono root dependence explicitly through
  `external_ray_map_exists_two_constructive_legacy_strictMono` and its
  dedicated root-witness extractor.

## Validation Checklist
- [x] `lake build Mlc.MainConjecture`
- [x] `make check`
  Status: executed; currently fails exactly on expected frontier axioms
  (`MLC.greenRayLogGtAnchorTwo_axiom_seed`,
  `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`).
- [ ] `#print axioms MLC.mlc_conjecture` no longer lists
  `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`.
- [x] Confirm no new unexpected axioms were introduced.
  Status: root-path axiom scans remain stable
  (`greenRayLogGtAnchorTwo_axiom_seed` + `green_function_strictMono_along_ray_basin_seam`).

## Risks / Blockers
- [x] Root strict-mono elimination is blocked until a strict-mono-free root
  injectivity witness is available.
  Status: reconfirmed by axiom scans:
  `mlc_conjecture` still contains
  `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`, while
  `mlc_conjecture_strictMonoFree_candidate_of_rootSafeOutsideOpenInjWitnessTwo`
  does not; therefore the remaining dependency is exactly the current root
  witness seed path.
- [x] Added explicit no-go theorem for the global-degree ingress alternative:
  `not_greenFunctionDegreeOneIngressTwo`.
  Status: this theorem is axiom-light (`Quot.sound`, `propext`,
  `Classical.choice`) and confirms the current model cannot discharge the
  strict-mono-free root via `GreenFunctionDegreeOneIngressTwo`.
- [x] Added a bundled strict-mono-free ingress interface and blocker theorem:
  `RootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo`,
  `rootSafeOutsideOpenInjWitnessTwo_of_strictMonoFreeIngressTwo`,
  `not_rootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo`.
  Status: bundle-to-root witness bridge is axiom-minimal
  (`Quot.sound`, `propext`, `Classical.choice`), and the bundled
  strict-mono-free candidate root theorem
  `mlc_conjecture_strictMonoFree_candidate_of_strictMonoFreeIngressTwo`
  carries only `greenRayLogGtAnchorTwo_axiom_seed` among frontier axioms.
- [x] Added payload-level strict-mono-free ingress blocker/entry layer:
  `RootSeedPayloadTwoStrictMonoFreeIngressTwo`,
  `rootSeedPayloadTwo_of_rootSeedPayloadTwoStrictMonoFreeIngressTwo`,
  `not_rootSeedPayloadTwoStrictMonoFreeIngressTwo`, plus payload-root candidate
  wrappers (`mlc_conjecture_strictMonoFree_candidate_of_rootSeedPayloadTwoStrictMonoFreeIngressTwo`,
  `mlc_conjecture_root_candidate_of_rootSeedPayloadTwo`).
  Status: strict-mono-free no-go is now expressed at the same payload layer as
  the final root theorem route; candidate payload-root wrappers remain
  seam-minimal (`Quot.sound`, `propext`, `Classical.choice`).
- [x] The direct-proper witness Green-function branch no longer depends on
  `MLC.Quadratic.external_ray_map_exists` after rerouting through
  `injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam`.
- [x] The earlier CP5 local-homeomorph constructive seam
  (`cp5ResidualLocalHomeomorphInjSeamTwo_constructive`) no longer uses the
  `Mlc.Bottcher.DegreeOne` route.
  Status: rerouted through
  `GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function`
  and outside-open left-inverse extraction; this removes the DegreeOne bridge
  but the theorem remains frontier-unsafe because that ingress still carries
  `MLC.Quadratic.external_ray_map_exists`.
- [x] Even with late strict-mono CP5 replacement seams, the
  `...of_not_externalRayLandsOutsideOpen` CP5 route still inherits
  `MLC.Quadratic.external_ray_map_exists` through the proposition-level
  `ExternalRayLandsOutsideOpen` branch in the seam type.
  Status: reconfirmed by axiom scans of
  `external_ray_map_exists_two_constructive_of_cp5ResidualTwo_of_cp5ResidualInjOnOutsideOpenSeamTwo`
  and `cp5ResidualInjOnOutsideOpenSeamTwo_strictMono_of_not_externalRayLandsOutsideOpen`;
  contamination persists even when a seam is passed explicitly, because
  `CP5ResidualTwo` itself contains the `ExternalRayLandsOutsideOpen` branch.
- [x] Checked and rejected the iterate-left-inverse route as a root witness source:
  current `bottcher_map_inj_on_outside_open_of_iter_left_inverse` path carries
  `MLC.Quadratic.external_ray_map_exists` in this development, so it is
  frontier-unsafe and must not be used for the root seed swap.
