# Plan: Eliminate `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`

## Goal
- [ ] Remove `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam` from the axiom footprint of `MLC.mlc_conjecture`.

## Hard Constraints
- [ ] Do not reintroduce `MLC.Quadratic.external_ray_map_exists` into the root path.
- [ ] Keep `MLC.greenRayLogGtAnchorTwo_axiom_seed` unchanged for this plan (strict-mono elimination only).

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
- [x] Added explicit end-state candidate root theorem aliases:
  `mlc_conjecture_strictMonoFree_candidate_of_rootSafeOutsideOpenInjWitnessTwo`
  and `..._of_green_function_degreeOneIngressTwo`, plus
  `external_ray_map_exists_two_constructive_eq_legacy_strictMono` as a boundary
  marker for the remaining strict-mono ingress.

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
- [ ] `make check`
- [ ] `#print axioms MLC.mlc_conjecture` no longer lists
  `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`.
- [x] Confirm no new unexpected axioms were introduced.
  Status: root-path axiom scans remain stable
  (`greenRayLogGtAnchorTwo_axiom_seed` + `green_function_strictMono_along_ray_basin_seam`).

## Risks / Blockers
- [ ] Root strict-mono elimination is blocked until a strict-mono-free root
  injectivity witness is available (the current root witness is frontier-safe
  w.r.t. `external_ray_map_exists`, but still depends on the strict-mono seam).
- [ ] The existing direct degree-one seam currently depends on
  `MLC.Quadratic.external_ray_map_exists`; that branch cannot be used for root wiring.
- [x] Checked and rejected the iterate-left-inverse route as a root witness source:
  current `bottcher_map_inj_on_outside_open_of_iter_left_inverse` path carries
  `MLC.Quadratic.external_ray_map_exists` in this development, so it is
  frontier-unsafe and must not be used for the root seed swap.
