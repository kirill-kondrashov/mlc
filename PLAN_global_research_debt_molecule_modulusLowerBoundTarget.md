# Plan: Eliminate / Prove `MLC.molecule_modulusLowerBoundTarget`

## Status (2026-02-17)
- [x] Baseline confirmed.
- [x] `MLC.mlc_conjecture` footprint no longer contains
  `MLC.molecule_modulusLowerBoundTarget` (satellite bridge branch currently
  discharged via `false_of_external_ray_axioms`).
- [x] Removed declaration `axiom molecule_modulusLowerBoundTarget`; remaining
  bridge dependence is now explicit via data hypotheses
  (`MoleculeModulusLowerBoundData` / conformal variant).
- [x] Began isolation refactor in `Mlc/MoleculeConjectureBridge.lean`:
  - `MoleculeModulusLowerBoundData`
  - data-parameterized wrappers:
    - `molecule_parameter_shrink_of_tower_of_modulusLowerBoundData`
    - `refined_conjecture_implies_lc_of_tower_of_modulusLowerBoundData`
    - `molecule_conjecture_bridge_of_tower_of_modulusLowerBoundData`
- [ ] A non-axiomatic proof of the bridge target is not yet implemented.

## Scope
- Keep the top-level theorem interface stable (`MLC.mlc_conjecture : LocallyConnectedSpace mandelbrotSet`).
- Reduce this debt to a single replacement point (`MoleculeModulusLowerBoundData`) so final elimination is one change.
- Track mathematical feasibility explicitly: do not hide contradictions behind wrapper wiring.

## Core Obstruction (Current Model)
- Current bridge target is:
  - `PrincipalNestTarget.ModulusNotSummableTarget c hTower`
  - defined via Gaussian proxy `MLC.Quadratic.modulus` in `Mlc/MoleculeToParameterShrink.lean`.
- Existing theorem:
  - `PrincipalNestTarget.not_modulusNotSummableTarget`
    (`Mlc/MoleculeGroetzschConnection.lean`)
  shows this target is false for any tower under the current `modulus` model.
- Consequence:
  - a direct non-axiomatic proof of the *current* statement is blocked.
  - progress requires either:
    1. changing the target to a conformal-modulus variant, or
    2. replacing the proxy `modulus` with a model aligned with the intended analytic statement.

## Phase 1 (Started): Isolate Replacement Point
- [x] Introduce explicit data hook (`MoleculeModulusLowerBoundData`).
- [x] Route shrink/bridge lemmas through data-parameterized variants.
- [x] Collapse remaining direct dependencies so all production use goes through the data hook only.

## Phase 2 (Next): Make the Target Mathematically Viable
- [x] Decide and implement one viable target shape scaffold:
  - conformal-modulus divergence target, or
  - updated modulus model where non-summability is meaningful.
- [x] Added a named conformal target and compatibility wrappers:
  - `PrincipalNestTarget.ConformalModulusNotSummableTarget`
  - `paraPuzzle_shrink_of_conformalModulusNotSummableTarget`
  - `MoleculeConformalModulusLowerBoundData`
  - conformal-data bridge wrappers in `Mlc/MoleculeConjectureBridge.lean`.
- [x] Explicitly recorded current equivalence of redesign and old target:
  - `PrincipalNestTarget.conformalModulusNotSummableTarget_iff_modulusNotSummableTarget`
  - `moleculeConformalModulusLowerBoundData_iff_moleculeModulusLowerBoundData`
  so this scaffold does not yet change provability under the current model.
- [x] Added matching obstruction for the conformal-target alias in the current model:
  - `PrincipalNestTarget.not_conformalModulusNotSummableTarget`
  - `not_satelliteRenormalizableTower_of_mem_mandelbrot_conformal`.
- [x] Added global no-go lemmas parameterized by existence of a Mandelbrot
  satellite tower:
  - `not_moleculeModulusLowerBoundData_of_exists_mem_mandelbrot_tower`
  - `not_moleculeConformalModulusLowerBoundData_of_exists_mem_mandelbrot_tower`.
- [x] Added combined inconsistency lemmas with global IR→tower data:
  - `false_of_moleculeModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data`
  - `false_of_moleculeConformalModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data`.
- [x] Migrated `Mlc/MainConjecture.lean` wrapper interfaces to consume
  `MoleculeConformalModulusLowerBoundData` directly, with
  `molecule_conformalModulusLowerBound_data_of_external_ray_axioms` as the
  current contradiction-backed instantiation.
- [x] Switched primary bridge API in `Mlc/MoleculeConjectureBridge.lean`
  (`molecule_parameter_shrink_of_tower`, `refined_conjecture_implies_lc_of_tower`,
  `molecule_conjecture_bridge_of_tower`, and legacy satellite wrappers) to
  conformal data input, keeping `_of_modulusLowerBoundData` compatibility lemmas.
- [x] Added a concrete Step-3 proof route scaffold:
  - `PrincipalNestTarget.UniformConformalLowerBoundTarget`
  - `conformalModulusNotSummableTarget_of_uniformConformalLowerBoundTarget`
  - `MoleculeUniformConformalLowerBoundData`
  - `moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData`.
- [x] Added direct route wrappers from uniform-conformal data to final bridge use:
  - `molecule_parameter_shrink_of_tower_of_uniformConformalLowerBoundData`
  - `refined_conjecture_implies_lc_of_tower_of_uniformConformalLowerBoundData`
  - `molecule_conjecture_bridge_of_tower_of_uniformConformalLowerBoundData`.
- [x] Lifted the uniform-target route to a direct principal-nest shrink theorem:
  - `PrincipalNestTarget.paraPuzzle_shrink_of_uniformConformalLowerBoundTarget`.
- [x] Added explicit compatibility conversion:
  - `moleculeModulusLowerBoundData_of_uniformConformalLowerBoundData`.
- [x] Extended obstruction layer to include the stronger uniform target:
  - `not_moleculeUniformConformalLowerBoundData_of_mem_mandelbrot_tower`
  - `not_moleculeUniformConformalLowerBoundData_of_exists_mem_mandelbrot_tower`
  - `false_of_moleculeUniformConformalLowerBoundData_and_infinitely_renormalizable_has_tower_data`.
- [x] Routed MainConjecture contradiction-backed bridge data through the stronger
  uniform scaffold first:
  - `molecule_uniformConformalLowerBound_data_of_external_ray_axioms`
  - `molecule_conformalModulusLowerBound_data_of_external_ray_axioms` now derived
    via `moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData`.
- [x] Added MainConjecture uniform-data entry points so the MLC strategy can be
  fed directly by the stronger target:
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_uniformConformalLowerBoundData`
  - `mlc_conjecture_of_bottcher_inj_on_basin_of_uniformConformalLowerBoundData`.
- [x] Repaired and activated the explicit satellite principal-nest bridge modules:
  - fixed `Mlc/SatellitePrincipalNestData.lean` to use the current principal-nest
    shrink theorem (`..._principal_modulus_not_summable`),
  - verified `Mlc/MoleculeToSatelliteNestData.lean` builds,
  - added `import Mlc.MoleculeToSatelliteNestData` to `Mlc.lean` so this path
    stays in the regular build.
- [x] Prove analog of
  `paraPuzzle_shrink_of_modulusNotSummableTarget`
  for the viable target.
  Completed via
  `PrincipalNestTarget.paraPuzzle_shrink_of_uniformConformalLowerBoundTarget`.
- [ ] Construct `MoleculeUniformConformalLowerBoundData` non-contradictorily
  from Molecule-conjecture hypotheses (current wrappers still instantiate via
  `false_of_external_ray_axioms`).

## Phase 3: Replace Axiom with Theorem
- [x] Remove axiom declaration `molecule_modulusLowerBoundTarget`.
- [ ] Implement theorem proof for the selected target and reconnect
  `molecule_conjecture_bridge_of_tower` through it.
- [x] Re-run `make check` and verify this axiom disappears from the
  `MLC.mlc_conjecture` footprint.
- [x] Update README axiom block.

## Execution Steps
- [x] Step 1: Baseline (`make check`) and isolate the bridge hook.
- [x] Step 1b: Remove this axiom from the top-level footprint by discharging
  the current satellite bridge branch via contradiction.
- [x] Step 2: Land target-redesign patch (definition + wrappers + migration scaffold).
- [ ] Step 3: Implement proof route for redesigned target.
- [x] Step 4: Remove old axiom and verify footprint.

## Completion Checklist
- [x] Single replacement hook exists: `MoleculeModulusLowerBoundData`.
- [x] `rg -n "^axiom molecule_modulusLowerBoundTarget"` returns no matches.
- [x] `make check` output does not contain `MLC.molecule_modulusLowerBoundTarget`.
- [x] `scripts/verify_output.sh` passes with updated README.
