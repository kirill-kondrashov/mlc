# Plan: Eliminate `MLC.Quadratic.external_ray_map_exists` (Critical Revision)

Date: 2026-02-19

## Hard Constraints
- Remove `MLC.Quadratic.external_ray_map_exists` from the axiom footprint of
  `MLC.mlc_conjecture`.
- Do not introduce new axioms.
- Do not add new hypotheses to `MLC.mlc_conjecture`.
- Keep the proof non-tautological:
  no contradiction-only routing (`exfalso`, `False.elim`) in the transitive
  dependency path of `MLC.mlc_conjecture`.
- Keep the current high-level structure: finite branch via Yoccoz,
  infinite branch via `mlc_strategy_of_branchLocalData`.

## Re-Audited Current State
- `make check` still reports:
  - `Quot.sound`
  - `propext`
  - `Classical.choice`
  - `MLC.Quadratic.external_ray_map_exists`
- `MLC.mlc_conjecture` still instantiates all three branch-data slots from
  contradiction-backed providers routed from explicit `c = 2` exterior data:
  - `mlc_conjecture_of_bottcher_map_surj_two`
  - `mlc_conjecture_of_bottcher_approach_one_point_surj_data_two`
  - `main_branch_data_of_false`
  - `false_of_bottcher_approach_one_point_surj_data_two`
  - `false_of_bottcher_approach_one_lift_data_two`
- Direct contradiction-backed providers currently on-path in
  `Mlc/MainConjecture.lean`:
  - `main_branch_bottcherMotion_hyp_of_false`
  - `main_branch_classify_data_of_false`
  - `main_branch_uniformConformalLowerBoundData_of_false`
  - `main_branch_data_of_false`

## Critical Issues in Previous Plan

### 1) Fake-progress risk via placeholder/stub routes
- There are non-axiom but placeholder pathways that can make elimination appear
  complete without mathematical substance:
  - `MLC.bottcher_onM_hyp` is a trivial stub (`B := 0`, `in_M := trivial`).
  - `homeomorphism_maps_component_hyp` and
    `parameter_dynamics_stability_hyp` are `True`.
- These must not be accepted as constructive replacements for active
  `mlc_conjecture` wiring.

### 2) Consistency risk in current global bridge targets
- `Mlc/FastTowerExistenceObstruction.lean` contains:
  - `not_infinitely_renormalizable_has_tower_data`
  - `false_of_moleculeModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data`
- So a plan that globally assumes both:
  - IR-to-tower data (`InfinitelyRenormalizableHasTowerData`), and
  - molecule modulus-lower-bound bridge data,
  can be inconsistent in the current formal model.
- Previous plan under-emphasized this and treated both as independently
  constructible without redesign.

### 3) Finite-branch default still axiom-backed
- Default transport witness route still goes through:
  `para_puzzle_transport_witness_hyp_of_axiom`, which uses
  `para_puzzle_piece_inter_mandelbrot_connected`.
- Replacing external-ray contradiction with this default just reintroduces
  removed axiom debt under a new name.

## Revised Plan

### Phase 0: Enforced Soundness Gates (must hold at every PR)
1. `MLC.mlc_conjecture` must not depend on any declaration whose proof body
   uses contradiction as the sole provider of branch data.
2. No active dependency from `MLC.mlc_conjecture` may use:
   - `false_of_bottcher_approach_one_point_surj_data_two`
   - `false_of_bottcher_approach_one_lift_data_two`
   - `Quadratic.bottcher_map_surj`
3. No active dependency may use placeholder stubs as constructive witnesses:
   - `bottcher_onM_hyp`
   - `homeomorphism_maps_component_hyp`
   - `parameter_dynamics_stability_hyp`
4. Keep Yoccoz finite branch explicit in `MLC.mlc_conjecture`.

### Phase 1: Resolve Model-Level Consistency Blocker First
1. Decide and implement one consistent bridge architecture before rewiring
   `MainConjecture`:
   - either construct IR classification without global tower data that clashes
     with current molecule lower-bound targets,
   - or redesign molecule/IR bridge targets so required data are jointly
     consistent in the formal model.
2. Add a dedicated consistency checkpoint theorem documenting that the chosen
   IR + molecule bridge assumptions can coexist without deriving `False`.
3. Do not proceed to final rewiring until this checkpoint is in place.

### Phase 2: Constructive Finite-Branch Provider
1. Produce `ParaPuzzlePieceInterMandelbrotConnectedData` constructively from a
   non-axiom, non-placeholder route.
2. Explicitly avoid:
   - `para_puzzle_transport_witness_hyp_of_axiom`
   - contradiction-based fallback lemmas.
3. Keep path integrated with `parameter_shrink_of_yoccoz`.

### Phase 3: Constructive IR Classification Provider
1. Provide `IRClassificationData` through constructive classification,
   with no contradiction fallback.
2. Ensure this provider does not pull in
   `MLC.Quadratic.external_ray_map_exists`.
3. Ensure it is compatible with Phase 1 consistency checkpoint.

### Phase 4: Constructive Molecule Bridge Provider
1. Provide the `h_bridge` argument for
   `mlc_strategy_of_branchLocalData` via constructive data only.
2. No `exfalso`-based provider on the active path.
3. No reliance on placeholder `True`-packaged structures.

### Phase 5: Rewire `Mlc/MainConjecture.lean`
1. Replace the three contradiction-backed local bindings in `mlc_conjecture`
   with Phase 2–4 constructive providers.
2. Remove now-dead contradiction wrappers from active path.
3. Keep theorem statement unchanged:
   `MLC.mlc_conjecture : LocallyConnectedSpace mandelbrotSet`.

### Phase 6: Verification and Exit Checks
1. Run:
   - `make build`
   - `make check`
   - `scripts/verify_output.sh`
2. Confirm `make check` output for `MLC.mlc_conjecture` excludes
   `MLC.Quadratic.external_ray_map_exists`.
3. Confirm dependency graph rooted at `MLC.mlc_conjecture` has no path through:
   - `false_of_bottcher_approach_one_point_surj_data_two`
   - `false_of_bottcher_approach_one_lift_data_two`
   - `Quadratic.bottcher_map_surj`.
4. Confirm Yoccoz linkage remains in the finite branch path.

## Exit Criteria
- `MLC.Quadratic.external_ray_map_exists` is absent from
  `#print axioms MLC.mlc_conjecture` / `make check`.
- No contradiction-only branch-data providers in the transitive
  `MLC.mlc_conjecture` path.
- No placeholder-stub witnesses in the transitive `MLC.mlc_conjecture` path.
- No new axioms added and no new hypotheses added to `MLC.mlc_conjecture`.

## Status
- Progress (2026-02-19):
  - Added theorem-level seams
    `mlc_conjecture_of_bottcher_approach_one_point_surj_data_two` and
    `mlc_conjecture_of_bottcher_map_surj_two` and routed
    `MLC.mlc_conjecture` through it, so the active external dependency surface
    is explicit at the theorem boundary.
  - Reduced the external seam used by the contradiction core from full
    `Quadratic.ExternalRayMapData (2 : ℂ)` to
    `BottcherApproachOnePointSurjData (2 : ℂ)`.
    The contradiction core remains
    `false_of_bottcher_approach_one_lift_data_two`, but active wiring now
    reaches it through
    `bottcher_approach_one_lift_data_of_bottcher_approach_one_point_surj_data`.
  - Replaced direct `Quadratic.external_ray_map_data` routing in
    `MLC.mlc_conjecture` with `Quadratic.bottcher_map_surj` routing at `c = 2`
    via
    `bottcher_approach_one_point_surj_data_of_bottcher_map_surj`.
  - Extracted a dedicated assembly theorem
    `mlc_conjecture_of_branchData` in `Mlc/MainConjecture.lean`.
  - `MLC.mlc_conjecture` now routes through that theorem with the current
    external-ray-backed branch-data providers.
  - This isolates the exact replacement interface for Phases 2–4 without
    changing theorem signatures or introducing new axioms.
  - Reworked the branch-data assembly surface to accept explicit
    `IRClassificationData` directly (instead of requiring global
    `InfinitelyRenormalizableHasTowerData`). This removes active reliance on
    the known inconsistent tower-data interface from `Mlc/MainConjecture.lean`
    while preserving the same high-level strategy shape
    (`h_conn`, `h_classify_ir`, `h_bridge`).
  - Attempted routing via
    `molecule_conjecture_bridge_of_tower_of_uniformConformalLowerBoundData`
    was reverted because it reintroduced
    `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected` into
    `MLC.mlc_conjecture`'s axiom footprint.
  - Current state keeps `h_bridge` contradiction-backed to preserve the
    one-axiom target while replacement work continues.
  - Finite-branch slot now routes through `PuzzleBoundaryMotionHyp` and
    `main_branch_transport_exists_data_of_puzzleBoundaryMotion`, then into
    connectedness data via
    `para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data`.
  - Added explicit branch-data assembler
    `main_branch_data_of_puzzleBoundaryMotion_of_classifyData_of_conformalModulusLowerBoundData`
    (with a transport-exists assembler retained as a lower-level wrapper).
    Active external-ray wiring now uses the stronger uniform variant
    `main_branch_data_of_puzzleBoundaryMotion_of_classifyData_of_uniformConformalLowerBoundData`,
    with conformal data derived via
    `moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData`.
    Current external-ray route instantiates this theorem via a single
    contradiction-seed builder `main_branch_data_of_false`.
  - Current branch-data assembly is centralized at
    `main_branch_data_of_false`, with contradiction seeded by
    `false_of_bottcher_approach_one_point_surj_data_two` at `c = 2`.
  - Rebased the finite-branch slot onto the boundary-motion interface with the
    conversion theorem
    `main_branch_transport_exists_data_of_puzzleBoundaryMotion`. This exposes
    an axiom-clean finite-branch replacement target (`PuzzleBoundaryMotionHyp`)
    directly in `Mlc/MainConjecture.lean`, with current routing through
    `main_branch_data_of_false`.
  - Lifted that finite-branch replacement surface one layer higher to
    Böttcher-motion packaging via
    `main_branch_puzzleBoundaryMotion_hyp_of_bottcherMotion`, with current
    temporary input routed through
    `main_branch_bottcherMotion_hyp_of_false` (inside `main_branch_data_of_false`).
    Axiom audit confirms:
    - `main_branch_puzzleBoundaryMotion_hyp_of_bottcherMotion` is axiom-clean
      (only `Quot.sound`/`propext`/`Classical.choice`)
    - external-ray dependence for the current path is routed through the
      single explicit seed `Quadratic.ExternalRayMapData (2 : ℂ)`.
  - Rebuilt the satellite bridge through explicit finite-branch connectedness:
    `main_branch_bridge_data_of_connectedData_of_conformalModulusLowerBoundData`
    (using `lc_at_of_shrink_of_data` and
    `molecule_parameter_shrink_of_tower_of_conformalModulusLowerBoundData`),
    and now source its conformal bridge input from the stronger uniform slot via
    `moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData`.
    This avoids routing bridge construction through `lc_at_of_shrink`, which is
    where `para_puzzle_piece_inter_mandelbrot_connected` previously leaked into
    candidate replacement paths.
  - Simplified IR-classification placeholder routing to a direct contradiction
    wrapper:
    - `main_branch_classify_data_of_false`
    and removed the intermediate tower-data hop from the active
    `MLC.mlc_conjecture` path in `Mlc/MainConjecture.lean`.
  - Kept the *active* branch-data assembly surface at
    `(PuzzleBoundaryMotionHyp, IRClassificationData, MoleculeConformalModulusLowerBoundData)`
    to avoid exposing the known-inconsistent pair
    `(InfinitelyRenormalizableHasTowerData, MoleculeConformalModulusLowerBoundData)`
    as top-level inputs.
  - Axiom-audited candidate direct replacements:
    - `Quadratic.para_puzzle_transport_exists_data_of_motion_default`
    - `molecule_conjecture_bridge_of_tower` (and conformal/uniform variants)
    each depends on
    `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`, so these
    routes are currently excluded if we keep the one-axiom target focused on
    `MLC.Quadratic.external_ray_map_exists`.
  - Axiom audit on `BottcherOutsidePlan` replacement pieces confirms:
    - `external_ray_map_data_of_injOn_outside_open_of_image_eq_exterior` is
      axiom-clean (modulo `Quot.sound`/`propext`/`Classical.choice`) and is a
      viable long-term constructor target.
    - current available injectivity route
      `bottcher_map_inj_on_outside_open` is circular through
      `MLC.Quadratic.external_ray_map_exists`.
    - analytic local-homeomorph route on outside-open currently pulls
      `MLC.Quadratic.bottcher_seq_converges`, which would violate the
      no-new-axiom constraint if activated in `MLC.mlc_conjecture`.
- Blocked pending a consistent constructive replacement architecture for
  finite-branch data + IR classification + molecule bridge data.
- Any attempt to remove `external_ray_map_exists` before Phase 1 is complete
  is likely to either:
  - reintroduce old axioms indirectly, or
  - recreate tautological/contradiction routing.
