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
  - `mlc_conjecture_of_external_ray_map_data_two`
  - `false_of_bottcher_approach_one_point_surj_data_two`
- Direct contradiction-backed providers currently on-path in
  `Mlc/MainConjecture.lean`:
  - field-level `False.elim` instantiations inside
    `mlc_conjecture_of_external_ray_map_data_two`

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
   - theorem-local contradiction wrappers fed by
     `Quadratic.external_ray_map_data (2 : ℂ)`
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
2. Add a dedicated consistency checkpoint theorem documenting the chosen
   architecture constraint (active conformal-bridge route excludes global
   IR→tower data in the current model).
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
   - theorem-local contradiction wrappers fed by
     `Quadratic.external_ray_map_data (2 : ℂ)`.
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
    `mlc_conjecture_of_external_ray_map_data_two` and routed
    `MLC.mlc_conjecture` through it, so the active external dependency surface
    is explicit at the theorem boundary.
  - Reduced the external seam used by the contradiction core from full
    `Quadratic.ExternalRayMapData (2 : ℂ)` to
    `BottcherApproachOnePointSurjData (2 : ℂ)`.
    The contradiction core is now directly
    `false_of_bottcher_approach_one_point_surj_data_two`.
  - Replaced `Quadratic.bottcher_map_surj` routing in `MLC.mlc_conjecture` with
    direct `Quadratic.external_ray_map_data` routing at `c = 2` via
    an inline point-surjectivity construction over `approach_one_seq`.
  - Axiom audit confirms:
    - `false_of_bottcher_approach_one_point_surj_data_two` is axiom-clean.
    - remaining non-core axiom dependence is localized to
      `mlc_conjecture_of_external_ray_map_data_two`,
      i.e. through `Quadratic.external_ray_map_data` / `external_ray_map_exists`.
  - `MLC.mlc_conjecture` now consumes that localized seam directly:
    `mlc_conjecture` is routed through
    `mlc_conjecture_of_external_ray_map_data_two
      (Quadratic.external_ray_map_data (2 : ℂ))`.
  - Axiom audit after seam refactor confirms:
    - `mlc_conjecture_of_external_ray_map_data_two` is axiom-clean
      (only `Quot.sound`/`propext`/`Classical.choice`).
    - `MLC.mlc_conjecture` remains the only declaration in this local chain that
      pulls `MLC.Quadratic.external_ray_map_exists`, via
      `Quadratic.external_ray_map_data (2 : ℂ)`.
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
    `Quadratic.para_puzzle_transport_exists_data_of_boundary_motion_target`, then into
    connectedness data via
    `para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data`.
  - Inlined branch-data assembly in
    `mlc_conjecture_of_external_ray_map_data_two` using
    boundary-motion transport conversion plus explicit connectedness/bridge construction.
    Active external-ray wiring now instantiates this conformal-target route via a single
    contradiction-seed builder
    `mlc_conjecture_of_external_ray_map_data_two`.
  - Current branch-data assembly is centralized at
    `mlc_conjecture_of_external_ray_map_data_two`,
    with contradiction seeded by
    `false_of_bottcher_approach_one_point_surj_data_two` at `c = 2`.
  - Rebased the finite-branch slot onto the boundary-motion interface with the
    conversion theorem
    `Quadratic.para_puzzle_transport_exists_data_of_boundary_motion_target`. This exposes
    an axiom-clean finite-branch replacement target (`PuzzleBoundaryMotionHyp`)
    directly in `Mlc/MainConjecture.lean`, with current routing through
    `mlc_conjecture_of_external_ray_map_data_two`.
  - Removed the unused Böttcher-motion wrapper from `Mlc/MainConjecture.lean`
    to keep only declarations that contribute to the active MLC path.
  - External-ray dependence for the current path is routed through the
    single explicit seed `Quadratic.ExternalRayMapData (2 : ℂ)`.
  - Rebuilt the satellite bridge through explicit finite-branch connectedness:
    the inline bridge lambda in
    `mlc_conjecture_of_external_ray_map_data_two`
    (using `lc_at_of_shrink_of_data` and
    `molecule_parameter_shrink_of_tower_of_conformalModulusLowerBoundData`).
    This avoids routing bridge construction through `lc_at_of_shrink`, which is
    where `para_puzzle_piece_inter_mandelbrot_connected` previously leaked into
    candidate replacement paths.
  - IR-classification slot is now routed through
    `classify_infinitely_renormalizable` with a localized seam
    `h_tower_data : InfinitelyRenormalizableHasTowerData` inside
    `mlc_conjecture_of_external_ray_map_data_two`.
  - Current instantiation of `h_tower_data` remains contradiction-backed
    (`False.elim hFalse`), but the classification path is now explicit and
    replacement-ready.
  - Finite-branch connectedness wiring inside
    `mlc_conjecture_of_external_ray_map_data_two` now uses the direct bridge
    `Quadratic.para_puzzle_connected_data_of_boundary_motion_target`
    (instead of an intermediate transport-data local), keeping the active
    replacement seam centered on `PuzzleBoundaryMotionHyp`.
  - Extracted a dedicated assembly theorem
    `mlc_conjecture_of_motionClassificationConformalData` taking exactly:
    - `PuzzleBoundaryMotionHyp`
    - `IRClassificationData`
    - `MoleculeConformalModulusLowerBoundData`
    and routing to `mlc_conjecture_of_branchData`.
    This keeps the strategy structure explicit while reducing the
    external-ray seam to provider instantiation only.
  - Axiom audit confirms the extracted three-input assembly layer is core-only:
    - `mlc_conjecture_of_motionClassificationConformalData`
    - `classify_infinitely_renormalizable`
    - `Quadratic.para_puzzle_connected_data_of_boundary_motion_target`
    do not add non-core axioms.
  - Current blocker remains data provisioning, not the assembly surface:
    e.g. `molecule_conjecture_bridge_of_tower_of_conformalModulusLowerBoundData`
    still pulls `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.
  - Classification-provider audit confirms:
    `classify_infinitely_renormalizable` is axiom-clean, but its only active
    route still requires `InfinitelyRenormalizableHasTowerData`. There is no
    in-repo constructive `InfinitelyRenormalizable → SatelliteRenormalizableTower`
    theorem independent of that seam at present.
  - Added Phase-1 consistency checkpoint theorem in
    `Mlc/FastTowerExistenceObstruction.lean`:
    `consistency_checkpoint_conformal_bridge_excludes_global_ir_tower`.
    This records the chosen architecture gate explicitly: with
    `MoleculeConformalModulusLowerBoundData`, global
    `InfinitelyRenormalizableHasTowerData` must be excluded on the active path.
  - Added a single named contradiction seed
    `false_of_external_ray_map_data_two` in `Mlc/MainConjecture.lean`.
    All current fallback providers in
    `mlc_conjecture_of_external_ray_map_data_two` now route through this one
    lemma, making replacement scope explicit and auditable.
  - Extracted named current provider lemmas from the external seam:
    - `connected_provider_of_external_ray_map_data_two`
    - `tower_data_provider_of_external_ray_map_data_two`
    - `classify_provider_of_external_ray_map_data_two`
    - `conformal_modulus_provider_of_external_ray_map_data_two`
    `mlc_conjecture_of_external_ray_map_data_two` now composes these into
    `mlc_conjecture_of_connectedClassificationConformalData`.
  - Removed several single-use wrappers from `Mlc/MainConjecture.lean` and
    inlined their bodies into the active route:
    - `main_branch_data_of_transportExists_of_classifyData_of_bridgeData`
    - `main_branch_data_of_puzzleBoundaryMotion_of_classifyData_of_conformalModulusLowerBoundData`
    - `main_branch_bridge_data_of_connectedData_of_conformalModulusLowerBoundData`
    - `main_branch_data_of_false`
    - `mlc_conjecture_of_bottcher_approach_one_point_surj_data_two`
    - `bottcher_approach_one_point_surj_data_of_external_ray_map_data`
  - Narrowed imports in `Mlc/MainConjecture.lean` by replacing the broad
    `BottcherMotion` import with `PuzzleBoundaryMotion`, keeping only interfaces
    used by the active theorem path.
  - Kept the *active* branch-data assembly surface at
    `(ParaPuzzlePieceInterMandelbrotConnectedData, IRClassificationData,
    MoleculeConformalModulusLowerBoundData)` to avoid exposing the known-inconsistent pair
    `(InfinitelyRenormalizableHasTowerData, MoleculeConformalModulusLowerBoundData)`
    as top-level inputs.
  - Added a Step-2 partial-elimination theorem:
    `mlc_conjecture_of_connected_data_of_external_ray_map_data_two`.
    This isolates finite-branch replacement explicitly: once
    `ParaPuzzlePieceInterMandelbrotConnectedData` is constructed without the
    external seam, only classification/bridge providers remain on that seam.
  - Axiom audit for Step-2 seams:
    - `mlc_conjecture_of_connectedClassificationConformalData`
    - `connected_provider_of_external_ray_map_data_two`
    - `mlc_conjecture_of_connected_data_of_external_ray_map_data_two`
    - `mlc_conjecture_of_external_ray_map_data_two`
    are all core-only (`Quot.sound`, `propext`, `Classical.choice`).
    `MLC.Quadratic.external_ray_map_exists` now appears only at the final
    `mlc_conjecture` instantiation boundary.
  - Re-audited finite-branch constructor candidates:
    - `Quadratic.para_puzzle_connected_data_of_boundary_motion_target` and
      `Quadratic.para_puzzle_transport_witness_from_boundary_motion_target`
      are core-only.
    - but available boundary-motion constructors
      `Quadratic.puzzle_boundary_motion_hyp_of_onM` and
      `Quadratic.puzzle_boundary_motion_hyp_of_onM_connected`
      still depend on
      `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.
    So Step 2 remains blocked on a non-axiom constructor for
    `ParaPuzzlePieceInterMandelbrotConnectedData` (or equivalent upstream
    boundary-motion data) that does not reintroduce removed axiom debt.
  - Extracted a dedicated finite-branch seam in `Mlc/MainConjecture.lean`:
    - `mlc_conjecture_of_finiteClassificationBridgeData`
    - `finite_lc_provider_of_connected_data`
    and rewired `mlc_conjecture_of_branchData` through them. This keeps
    Yoccoz finite-branch routing explicit and makes finite-branch replacement
    independently auditable from classification/bridge assembly.
  - Axiom audit confirms the new seam declarations are core-only:
    `mlc_conjecture_of_finiteClassificationBridgeData` and
    `finite_lc_provider_of_connected_data` depend only on
    `Quot.sound`, `propext`, `Classical.choice`.
  - Further seam reduction in `Mlc/MainConjecture.lean`:
    `mlc_conjecture_of_external_ray_map_data_two` now routes directly through
    `mlc_conjecture_of_finiteClassificationBridgeData` with explicit providers:
    - `finite_lc_provider_of_external_ray_map_data_two`
    - `classify_provider_of_external_ray_map_data_two`
    - `bridge_provider_of_external_ray_map_data_two`
    The older conformal wrapper route
    (`mlc_conjecture_of_connectedClassificationConformalData`,
    `mlc_conjecture_of_connected_data_of_external_ray_map_data_two`,
    `conformal_modulus_provider_of_external_ray_map_data_two`) was removed from
    the active path.
  - Axiom audit confirms the new external providers are core-only:
    `finite_lc_provider_of_external_ray_map_data_two` and
    `bridge_provider_of_external_ray_map_data_two` depend only on
    `Quot.sound`, `propext`, `Classical.choice`.
  - Removed the extra connectedness fallback wrapper
    `connected_provider_of_external_ray_map_data_two` from the active path and
    inlined its role inside
    `finite_lc_provider_of_external_ray_map_data_two`, while keeping the
    Yoccoz finite-branch route on-path through
    `finite_lc_provider_of_connected_data`.
  - Added a tighter Step-2 seam theorem:
    `mlc_conjecture_of_finite_lc_of_external_ray_map_data_two`.
    This isolates finite-branch replacement directly at the
    `h_fin_lc` interface: once that provider is constructive, only
    classification/bridge providers remain seam-backed.
  - Refined Step-2 finite target from global connectedness data to pointwise
    finite-branch data:
    - `FiniteBranchConnectedAtData`
    - `finite_lc_provider_of_connectedAtData`
    with supporting pointwise route in `Mlc/LcAtOfShrink.lean`:
    - `para_puzzle_piece_induced_connected_of_at`
    - `lc_at_of_shrink_of_connected_at`
    Active fallback in `mlc_conjecture_of_external_ray_map_data_two` now routes
    through this pointwise target, keeping Yoccoz finite-branch reasoning
    explicit while lowering the constructive replacement burden for Phase 2.
  - Axiom audit confirms the pointwise finite seam is core-only:
    `finite_lc_provider_of_connectedAtData` and
    `mlc_conjecture_of_finite_lc_of_external_ray_map_data_two` depend only on
    `Quot.sound`, `propext`, `Classical.choice`.
  - Removed single-use wrapper `tower_data_provider_of_external_ray_map_data_two`
    and inlined tower fallback construction inside
    `classify_provider_of_external_ray_map_data_two`, while preserving the
    explicit call to `classify_infinitely_renormalizable`.
  - Promoted the Step-2 seam to the explicit pointwise finite target theorem:
    `mlc_conjecture_of_finite_connectedAt_data_of_external_ray_map_data_two`.
    `mlc_conjecture_of_external_ray_map_data_two` now instantiates
    `FiniteBranchConnectedAtData` at the seam and routes through this theorem.
    The intermediate fallback wrapper
    `finite_lc_provider_of_external_ray_map_data_two` was removed.
  - Current Phase-2 minimal remaining target is now explicit:
    construct `FiniteBranchConnectedAtData` non-axiomatically (or redesign the
    finite branch so this target is no longer required), without introducing
    new axioms/hypotheses and without collapsing to contradiction-only routing.
  - Added a Phase-3 seam-reduction theorem:
    `mlc_conjecture_of_finite_connectedAt_classify_of_external_ray_map_data_two`.
    With `FiniteBranchConnectedAtData` and `IRClassificationData` supplied,
    only the bridge provider remains seam-backed.
  - Removed newly off-path intermediate seam theorem
    `mlc_conjecture_of_finite_lc_of_external_ray_map_data_two` to keep
    `Mlc/MainConjecture.lean` rooted-closure clean.
  - Added finite-branch motion seam target:
    - `FiniteBranchMotionAtData`
    - `finite_connectedAtData_of_motionAtData`
    - `mlc_conjecture_of_finite_motionAt_data_of_external_ray_map_data_two`
    and routed `mlc_conjecture_of_external_ray_map_data_two` through this new
    seam by instantiating `FiniteBranchMotionAtData` at `c = 2`.
  - This makes the finite replacement interface closer to the intended
    boundary-motion strategy (Phase 2), while keeping all new declarations
    on-path and core-only.
  - Tightened classification seam routing by replacing
    `classify_provider_of_external_ray_map_data_two` with tower-data routing:
    - `tower_provider_of_external_ray_map_data_two`
    - `mlc_conjecture_of_finite_connectedAt_tower_bridge_data`
    so classification now flows explicitly through
    `classify_infinitely_renormalizable` from `InfinitelyRenormalizableHasTowerData`.
  - Routed the active finite seam through global motion hypothesis instantiation:
    - `motion_hyp_provider_of_external_ray_map_data_two`
    - `finite_motionAtData_of_puzzleBoundaryMotionHyp`
    - `mlc_conjecture_of_finite_motionAt_data_of_external_ray_map_data_two`
    This keeps the finite branch aligned with boundary-motion semantics while
    preserving the same axiom footprint.
  - Removed now-unused assembly wrappers from the active rooted file:
    `MainBranchData`, `mlc_conjecture_of_branchData`, and the prior conformal
    wrapper route. Rooted graph audit confirms remaining `Mlc/MainConjecture.lean`
    declarations are all in the `MLC.mlc_conjecture` dependency closure.
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
  - Axiom audit on the eventual-slit bridge route confirms it is currently
    incompatible with constraints for on-path use:
    - `quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_bridge` depends on
      `MLC.bottcher_outside_axiom` and
      `MLC.Quadratic.bottcher_seq_converges`.
    - `bottcher_map_inj_on_outside_of_slit(_of_iter_left_inverse)` still pulls
      `MLC.Quadratic.external_ray_map_exists` and
      `MLC.Quadratic.bottcher_seq_converges`.
    Therefore this route is excluded until those dependencies are eliminated.
  - Axiom audit on boundary-motion constructors from `BottcherMotion` confirms:
    - `puzzle_boundary_motion_hyp_of_onM`
    - `puzzle_boundary_motion_hyp_of_onM_connected`
    both depend on `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.
    So they are currently excluded from the active one-axiom path.
  - Axiom audit on `BottcherOnMTheory` / Green-sublevel candidates confirms:
    - `bottcher_theorem_outside`, `bottcher_theorem_outside_of_basin`,
      `bottcher_map_inj_on_basin_of_outside_left_inv`, and
      `bottcher_map_inj_theorem` all still pull
      `MLC.Quadratic.external_ray_map_exists`.
    - `green_sublevel_connected_onM` additionally pulls
      `MLC.Quadratic.extended_ray_map_continuous` and
      `MLC.Quadratic.filled_julia_set_connected`.
    Therefore these routes are excluded for the current elimination target.
  - Narrowed direct import debt in `Mlc/MainConjecture.lean` by replacing
    `Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan` with the smaller
    `Mlc.Quadratic.Complex.Bottcher.BottcherAxioms` import (while retaining
    `BottcherOnMTheory` for `iterate_quadratic_map_tendsto_infty`).
  - Re-audited rooted declaration usage for `Mlc/MainConjecture.lean` against
    `site/mlc_conjecture/graph.json`: no declarations in that file are outside
    the `MLC.mlc_conjecture` dependency closure.
  - Consolidated external seam routing through:
    `mlc_conjecture_of_motionHyp_tower_bridge_data`, with explicit inputs
    `(PuzzleBoundaryMotionHyp, InfinitelyRenormalizableHasTowerData, h_bridge)`.
    `mlc_conjecture_of_external_ray_map_data_two` now instantiates exactly
    those three providers from external-seam fallback.
  - Removed newly off-path external wrappers:
    - `mlc_conjecture_of_finite_connectedAt_data_of_external_ray_map_data_two`
    - `mlc_conjecture_of_finite_motionAt_data_of_external_ray_map_data_two`
    keeping the active rooted declaration set minimal.
  - Removed single-use external fallback wrappers for motion/tower/bridge data.
    `mlc_conjecture_of_external_ray_map_data_two` now creates one
    contradiction seed `hFalse` and instantiates the three seam inputs via
    `False.elim hFalse` directly at the final external seam boundary.
  - Rebased the active seam away from tower-specific classification routing:
    `mlc_conjecture_of_motionHyp_classify_bridge_data` is now the primary
    assembly surface, with inputs:
    - `PuzzleBoundaryMotionHyp`
    - `IRClassificationData`
    - satellite bridge `h_bridge`
    and finite branch routed via
    `finite_motionAtData_of_puzzleBoundaryMotionHyp →
     finite_connectedAtData_of_motionAtData →
     finite_lc_provider_of_connectedAtData`.
  - Removed now-off-path tower-specific seam wrapper
    `mlc_conjecture_of_finite_connectedAt_tower_bridge_data`.
  - Replaced abstract bridge-input routing on the active external path with a
    conformal-modulus bridge constructor:
    - `bridge_provider_of_motionHyp_conformalModulus_data`
    - `mlc_conjecture_of_motionHyp_classify_conformalModulus_data`
    `mlc_conjecture_of_external_ray_map_data_two` now routes through this
    conformal-modulus seam, still with core-only axioms.
  - Reduced finite-branch seam indirection in `Mlc/MainConjecture.lean` by
    replacing global connected-data conversion with pointwise boundary-motion
    extraction:
    - added `finite_connectedAt_provider_of_motionHyp`
    - added `finite_lc_provider_of_motionHyp`
    - rewired `mlc_conjecture_of_motionHyp_classify_bridge_data` to consume
      `finite_lc_provider_of_motionHyp` directly.
    This keeps the Yoccoz finite branch explicit while removing one
    intermediate wrapper layer from the active path.
  - Rewired `bridge_provider_of_motionHyp_conformalModulus_data` to use
    `lc_at_of_shrink_of_connected_at` with
    `finite_connectedAt_provider_of_motionHyp` directly, eliminating another
    intermediate connected-data bridge in the active route.
  - Verification after this refactor:
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes.
  - Aligned IR classification seam with the Mandelbrot-domain strategy:
    - updated `mlc_infinitely_renormalizable` to classify with explicit
      `hc : c ∈ MandelbrotSet`
    - updated `mlc_strategy_of_branchLocalData` and `IRClassificationData`
      accordingly in `Mlc/MainConjecture.lean`.
    This keeps theorem statements unchanged while removing off-domain
    classification obligations from the active replacement interface.
  - Re-audit of classification constructors shows only one in-repo route to
    `IRClassificationData`:
    `classify_infinitely_renormalizable`, which requires
    `InfinitelyRenormalizableHasTowerData`.
    Combined with active conformal-modulus bridge assumptions, this remains
    blocked by
    `consistency_checkpoint_conformal_bridge_excludes_global_ir_tower`.
  - Additional type-level blocker:
    `InfinitelyRenormalizable` is currently defined without Mandelbrot-set
    membership in `Mlc/RenormalizationTypes.lean`, so conformal-modulus
    obstructions that require `c ∈ MandelbrotSet` cannot by themselves force a
    contradiction against all `IRClassificationData`.
- Blocked pending a consistent constructive replacement architecture for
  finite-branch data + IR classification + molecule bridge data.
- Any attempt to remove `external_ray_map_exists` before Phase 1 is complete
  is likely to either:
  - reintroduce old axioms indirectly, or
  - recreate tautological/contradiction routing.
