# Plan: Cleanup Code Not Directly Contributing to `MLC.mlc_conjecture`

## Status (Completed)
- [x] Split non-direct declarations out of `Mlc/MainConjecture.lean`.
- [x] Kept `Mlc/MainConjecture.lean` focused on direct `mlc_conjecture` path.
- [x] Pruned non-essential root exports in `Mlc.lean`.
- [x] Verified with `make check`, `lake build`, and `lake env lean check_axioms.lean`.
- [x] Deleted legacy file `Mlc/MainConjectureLegacyRoutes.lean`.

## Scope and Decision Rule
Direct contribution is defined as declarations reachable from `MLC.mlc_conjecture`
inside `Mlc/MainConjecture.lean` by declaration-reference traversal, plus external
lemmas/constants called by that reachable set.

I ran a local reachability pass over top-level declarations in
`Mlc/MainConjecture.lean`:
- reachable from `mlc_conjecture`: 35 declarations
- not reachable from `mlc_conjecture`: 62 declarations

## Direct Core Slice (Keep in Main Path)
Core declarations on the `mlc_conjecture` route in `Mlc/MainConjecture.lean`:
- `multibrotSet`, `mandelbrotSet`, `mandelbrotSet_eq_MandelbrotSet`
- `dichotomy`
- `mlc_strategy_of_paraPuzzleConnectedData`
- `mlc_strategy_of_paraPuzzleWitnessFromBoundaryMotionTarget_of_motion`
- `mlc_strategy_of_paraPuzzleWitnessFromBoundaryMotionTarget`
- `mlc_strategy`
- `IRClassificationData`
- `BottcherMapInjOnBasinOnMData`
- `bottcher_map_inj_on_basin_of_mem_mandelbrot`
- `bottcher_map_inj_on_basin_onM_via_basin_dynamics`
- `bottcher_map_inj_on_basin_onM_target`
- `ir_classification_data_of_external_ray_data_two`
- `ir_classification_data_of_external_ray_axioms`
- `molecule_uniformConformalLowerBound_data_of_external_ray_data_two`
- `molecule_uniformConformalLowerBound_data_of_external_ray_axioms`
- `false_of_external_ray_data_two` and its helper chain used in its proof
- `mlc_conjecture`

External/internal files used directly by this path:
- `Mlc/AxiomsMainConjecture.lean` (`parameter_shrink_of_yoccoz`)
- `Mlc/GreenSublevelConnected.lean` (`green_sublevel_connected_onM`)
- `Mlc/MoleculeConjectureBridge.lean`
  (`molecule_conjecture_bridge_of_tower_of_uniformConformalLowerBoundData`)
- `Mlc/Quadratic/Complex/Bottcher/BottcherOnM.lean` (`bottcher_onM_hyp`)

## Non-Direct Cleanup Candidates
These are currently not on the direct `mlc_conjecture` route.

### 1) Alternate Strategy Entrypoints (not used by `mlc_strategy` route)
- `Mlc/MainConjecture.lean:69` `paraPuzzleConnectedData_of_paraPuzzleTransportData`
- `Mlc/MainConjecture.lean:76` `paraPuzzleConnectedData_of_paraPuzzleTransportExistsData`
- `Mlc/MainConjecture.lean:82` `paraPuzzleTransportExistsData_ofWitness`
- `Mlc/MainConjecture.lean:91` `paraPuzzleTransportExistsData_ofMotionWitnessHyp`
- `Mlc/MainConjecture.lean:120` `mlc_strategy_of_paraPuzzleMandelbrotSubsetData`
- `Mlc/MainConjecture.lean:141` `mlc_strategy_of_paraPuzzleTransportData`
- `Mlc/MainConjecture.lean:161` `mlc_strategy_of_paraPuzzleTransportExistsData`
- `Mlc/MainConjecture.lean:181` `mlc_strategy_of_paraPuzzleMotionWitnessHyp`
- `Mlc/MainConjecture.lean:246` `mlc_strategy_of_paraPuzzleMandelbrotSubsetData_via_motionWitnessHyp`

### 2) Legacy Step-2b Data Families and Bridges
- `Mlc/MainConjecture.lean:290`..`Mlc/MainConjecture.lean:420`
  (`BottcherProperLocalHomeomorph*`, `BottcherContinuousDeriv*`,
  `BottcherIsLocalHomeomorphOnMData`, and related bridge/negation lemmas)

### 3) Unused Contradiction Wrappers
- `Mlc/MainConjecture.lean:469` `false_of_bottcher_map_inj_on_K_axiom`
- `Mlc/MainConjecture.lean:988` `false_of_external_ray_axioms`
- `Mlc/MainConjecture.lean:1023` `green_sublevel_connected_data_of_external_ray_data_two`
- `Mlc/MainConjecture.lean:1033` `green_sublevel_connected_data_of_external_ray_axioms`
- `Mlc/MainConjecture.lean:1040` `molecule_conformalModulusLowerBound_data_of_external_ray_data_two`

### 4) Eventual-Slit / Basin Left-Inverse Redesign Layer (currently bypassed)
- `Mlc/MainConjecture.lean:1047`..`Mlc/MainConjecture.lean:1300`
  (`EventualSlit*`, `BasinBottcherPointwiseLeftInverse*`,
  equivalence/bridge lemmas, and inconsistency theorems)

### 5) Misc Non-Direct Leftovers
- `Mlc/MainConjecture.lean:371` `zero_mem_mandelbrotSet`
- `Mlc/MainConjecture.lean:501` `fixed_point_two_ne_zero`
- `Mlc/MainConjecture.lean:821` `bottcher_map_fixed_point_two_ne_one`

### 6) Root Export Imports Not Needed for the `mlc_conjecture` Proof Path
`Mlc.lean` currently exports many extra modules that are not directly needed by
`MLC.mlc_conjecture`:
- `Mlc.Quadratic.Complex.Bottcher.BottcherRayMap`
- `Mlc.Quadratic.Complex.Bottcher.BottcherOnMOutline`
- `Mlc.Quadratic.Complex.Bottcher.BottcherOutsideOutline`
- `Mlc.Quadratic.Complex.InverseBranch`
- `Mlc.Quadratic.Complex.InverseBranchQuadratic`
- `Mlc.Quadratic.Complex.Bottcher.InverseBranchSlit`

## Execution Steps
Completed as listed in the status section above.

## Safety Notes
- This list is intentionally conservative and based on direct-route reachability,
  not on historical/research value.
- Before deleting any candidate, confirm it is not an intentional staging hook for
  ongoing debt-elimination plans in `plan/`.
