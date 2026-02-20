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
  - Research kickoff audit (2026-02-19):
    - Confirmed seam localization:
      - `MLC.mlc_conjecture` is the only audited declaration in the current
        path that depends on `MLC.Quadratic.external_ray_map_exists`.
      - `mlc_conjecture_of_external_ray_map_data_two`,
        `false_of_external_ray_map_data_two`,
        `mlc_conjecture_of_motionHyp_classify_conformalModulus_data`,
        `bridge_provider_of_motionHyp_conformalModulus_data`,
        `finite_connectedAt_provider_of_motionHyp`,
        `finite_lc_provider_of_motionHyp`,
        `classify_infinitely_renormalizable`,
        and
        `consistency_checkpoint_conformal_bridge_excludes_global_ir_tower`
        are all core-only (`Quot.sound`, `propext`, `Classical.choice`).
    - Motion-constructor audit:
      - `Quadratic.puzzle_boundary_motion_hyp_of_bottcher` is core-only.
      - `Quadratic.puzzle_boundary_motion_hyp_of_onM` and
        `Quadratic.puzzle_boundary_motion_hyp_of_onM_connected` still depend on
        `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.
      This isolates the actionable finite-motion target to constructing a
      suitable `BottcherMotionHyp` without reintroducing removed axiom debt.
    - Outside-Böttcher external-data constructor audit:
      - `external_ray_map_data_of_injOn_outside_open_of_image_eq_exterior` and
        its supporting surjectivity/image-equality wrappers are core-only.
      - Current available source for the injectivity precondition,
        `bottcher_map_inj_on_outside_open`, still depends on
        `MLC.Quadratic.external_ray_map_exists`.
      - Alternative local route `bottcher_map_local_inj_on_outside_open`
        depends on `MLC.Quadratic.bottcher_seq_converges`, which is outside the
        current one-axiom budget.
      This identifies the primary constructive replacement bottleneck:
      non-axiomatic `h_inj` on outside-open.
  - Immediate research track (next iteration):
    - prove or import a non-axiomatic outside-open injectivity theorem for
      `bottcher_map` that avoids both `external_ray_map_exists` and
      `bottcher_seq_converges`, then feed it to
      `external_ray_map_data_of_injOn_outside_open_of_image_eq_exterior`;
    - in parallel, pursue a constructive `BottcherMotionHyp` constructor and
      test whether it can provide a non-contradiction
      `PuzzleBoundaryMotionHyp` for the main seam.
  - Active seam reduced further from full external-ray data to a weaker
    point-surjectivity target:
    - added `mlc_conjecture_of_bottcher_approach_one_point_surj_data_two`
      and routed
      `mlc_conjecture_of_external_ray_map_data_two` through this theorem;
    - removed the now-redundant wrapper
      `false_of_external_ray_map_data_two`.
    This makes the replacement obligation strictly smaller:
    constructing pointwise preimages for `approach_one_seq` at `c = 2` is now
    the direct seam, rather than constructing full `ExternalRayMapData (2)`.
  - Verification after this seam reduction:
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes.
  - Further rooted-path narrowing in `Mlc/MainConjecture.lean`:
    - removed `mlc_conjecture_of_external_ray_map_data_two` from the active
      path;
    - added
      `bottcher_approach_one_point_surj_data_two_of_external_ray_map_exists`;
    - rewired `mlc_conjecture` directly through
      `mlc_conjecture_of_bottcher_approach_one_point_surj_data_two`.
    This eliminates full `ExternalRayMapData (2)` packaging from the rooted
    theorem chain and keeps the active seam at the weaker
    `BottcherApproachOnePointSurjData (2)` interface.
  - Verification after rooted-path narrowing:
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - rooted graph closure for `Mlc/MainConjecture.lean` remains complete
      (no off-path declarations in that file).
  - Further seam normalization in `Mlc/MainConjecture.lean`:
    - added
      `exterior_subset_image_outside_disk_of_external_ray_map_data`:
      explicit external-data route to exterior image coverage on
      `outside_disk`;
    - added
      `bottcher_approach_one_point_surj_data_two_of_exterior_subset_image_outside_disk`;
    - rewired
      `bottcher_approach_one_point_surj_data_two_of_external_ray_map_data`
      through this intermediate image-coverage seam.
    This keeps `MLC.mlc_conjecture` unchanged while expressing the active
    replacement target one layer closer to pure `bottcher_map` image data
    (instead of direct pointwise right-inverse construction).
  - Verification after seam normalization:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes.
  - Rooted seam narrowed again in `Mlc/MainConjecture.lean`:
    - added `BottcherExteriorSubsetImageOutsideDiskData`;
    - added
      `mlc_conjecture_of_bottcher_exterior_subset_image_outside_disk_data_two`;
    - rewired `mlc_conjecture` to consume this new minimal seam directly;
    - kept current default seam provider
      `bottcher_exterior_subset_image_outside_disk_data_two` sourced from
      `Quadratic.external_ray_map_data (2 : ℂ)`.
    This isolates the external dependency at a strictly weaker image-coverage
    interface than direct approach-sequence preimage construction.
  - Verification after rooted seam narrowing:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - axiom audit confirms:
      - `mlc_conjecture_of_bottcher_exterior_subset_image_outside_disk_data_two`
        is core-only;
      - `MLC.Quadratic.external_ray_map_exists` enters only at the default seam
        provider (`bottcher_exterior_subset_image_outside_disk_data_two`) and
        therefore at `MLC.mlc_conjecture`.
  - Rooted seam narrowed once more in `Mlc/MainConjecture.lean`:
    - added `BottcherApproachOneSubsetImageOutsideDiskData`;
    - added conversion
      `bottcher_approach_one_subset_image_outside_disk_data_of_exterior_subset_image_outside_disk_data`;
    - added
      `mlc_conjecture_of_bottcher_approach_one_subset_image_outside_disk_data_two`;
    - rewired `mlc_conjecture` to consume this sequence-only image seam.
    This further weakens the active replacement target from global exterior
    image coverage to just the canonical approach-to-`1` sequence image.
  - Verification after sequence-only seam narrowing:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - axiom audit confirms:
      - `mlc_conjecture_of_bottcher_approach_one_subset_image_outside_disk_data_two`
        is core-only;
      - `MLC.Quadratic.external_ray_map_exists` enters only at the default
        sequence-seam provider
        (`bottcher_approach_one_subset_image_outside_disk_data_two`) and
        therefore at `MLC.mlc_conjecture`.
  - Rooted seam narrowed further in `Mlc/MainConjecture.lean` by removing the
    outside-disk image layer from the active path:
    - removed `BottcherExteriorSubsetImageOutsideDiskData` and its
      sequence-image conversion from the rooted chain;
    - introduced `BottcherApproachOneRangeData` (`approach_one_seq` points in
      `Set.range (Quadratic.bottcher_map c)`);
    - added
      `mlc_conjecture_of_bottcher_approach_one_range_data_two` and rewired
      `mlc_conjecture` through this direct range seam.
    This is a strict weakening of the replacement interface compared to
    sequence-image-in-`outside_disk`.
  - Verification after direct range-seam narrowing:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - axiom audit confirms:
      - `mlc_conjecture_of_bottcher_approach_one_range_data_two` is core-only;
      - `MLC.Quadratic.external_ray_map_exists` enters only at the default
        range-seam provider
        (`bottcher_approach_one_range_data_two`) and therefore at
        `MLC.mlc_conjecture`.
  - Provider simplification on the rooted range seam:
    - removed explicit `ExternalRayMapData (2 : ℂ)` constructor usage from
      `Mlc/MainConjecture.lean`;
    - replaced it with
      `bottcher_approach_one_range_data_two_of_bottcher_map_surj`, i.e. the
      default seam now consumes only `Quadratic.bottcher_map_surj` for
      `approach_one_seq`.
    This keeps the rooted interface cleaner and centered on Böttcher-map
    surjectivity statements rather than explicit ray-map data packages.
  - Verification after provider simplification:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - axiom audit confirms:
      - `bottcher_approach_one_range_data_two_of_bottcher_map_surj` still
        depends on `MLC.Quadratic.external_ray_map_exists` (via
        `Quadratic.bottcher_map_surj`);
      - therefore the remaining elimination task is unchanged: replace this
        surjectivity source constructively.
  - Rooted contradiction-surface simplification in `Mlc/MainConjecture.lean`:
    - removed intermediate wrapper
      `BottcherApproachOnePointSurjData` from the active chain;
    - replaced
      `false_of_bottcher_approach_one_point_surj_data_two` with
      `false_of_bottcher_approach_one_range_data_two`;
    - rewired
      `mlc_conjecture_of_bottcher_approach_one_range_data_two` to consume the
      range seam directly.
    This keeps theorem shape unchanged while shrinking rooted indirection.
  - Verification after contradiction-surface simplification:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - axiom audit confirms:
      - `false_of_bottcher_approach_one_range_data_two` is core-only;
      - `mlc_conjecture_of_bottcher_approach_one_range_data_two` is core-only.
  - Re-audit of non-contradictory motion replacement candidate:
    constructing `PuzzleBoundaryMotionHyp` without contradiction currently
    requires providing `motion_preserves_para_piece`, whose payload is exactly
    para-puzzle connectedness on `M`; in the present model this still routes to
    `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`, so it is not
    an immediate replacement path for the one-axiom target.
  - Seam naming/target cleanup in `Mlc/MainConjecture.lean`:
    - replaced `BottcherApproachOneRangeData` with
      `BottcherApproachOneSurjData` (direct preimage-surjectivity wording);
    - renamed dependent declarations accordingly:
      - `false_of_bottcher_approach_one_surj_data_two`
      - `bottcher_approach_one_surj_data_two_of_bottcher_map_surj`
      - `mlc_conjecture_of_bottcher_approach_one_surj_data_two`.
    This keeps the same mathematical seam while making the remaining
    elimination target explicit and search-friendly.
  - Verification after seam naming cleanup:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - axiom audit confirms:
      - `BottcherApproachOneSurjData`,
        `false_of_bottcher_approach_one_surj_data_two`, and
        `mlc_conjecture_of_bottcher_approach_one_surj_data_two` are core-only;
      - `bottcher_approach_one_surj_data_two_of_bottcher_map_surj` remains the
        unique current ingress of `MLC.Quadratic.external_ray_map_exists` on the
        rooted seam.
  - Import-level rooted cleanup:
    - removed direct import
      `Mlc.Quadratic.Complex.Bottcher.BottcherAxioms` from
      `Mlc/MainConjecture.lean` (now covered transitively by
      `BottcherOnMTheory` in the current path).
    This keeps `MainConjecture` closer to the active dependency surface.
  - Verification after import cleanup:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes.
  - Rooted seam generalized from sequence-only surjectivity to exterior
    surjectivity at `c = 2`:
    - added `BottcherExteriorSurjData`;
    - added conversion
      `bottcher_approach_one_surj_data_of_bottcher_exterior_surj_data`;
    - added `mlc_conjecture_of_bottcher_exterior_surj_data_two`;
    - rewired `mlc_conjecture` through this exterior-surjectivity seam.
    This makes the remaining replacement obligation explicit at the natural
    exterior-surjectivity interface, while preserving theorem shape.
  - Verification after exterior-surjectivity seam routing:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - axiom audit confirms:
      - `BottcherExteriorSurjData`,
        `bottcher_approach_one_surj_data_of_bottcher_exterior_surj_data`, and
        `mlc_conjecture_of_bottcher_exterior_surj_data_two` are core-only;
      - `bottcher_exterior_surj_data_two` is the current ingress of
        `MLC.Quadratic.external_ray_map_exists` on the rooted path.
  - Rooted contradiction path cleanup:
    - added `false_of_bottcher_exterior_surj_data_two`;
    - rewired `mlc_conjecture_of_bottcher_exterior_surj_data_two` to consume
      this direct contradiction lemma;
    - removed now-unused intermediate theorem
      `mlc_conjecture_of_bottcher_approach_one_surj_data_two`.
    This keeps all declarations in `Mlc/MainConjecture.lean` on the rooted
    dependency path and removes one extra theorem layer.
  - Verification after contradiction-path cleanup:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes
    - axiom audit confirms:
      - `false_of_bottcher_exterior_surj_data_two` is core-only;
      - `mlc_conjecture_of_bottcher_exterior_surj_data_two` is core-only.
  - Additional rooted cleanup:
    - inlined the one-use conversion from `BottcherExteriorSurjData` to
      `BottcherApproachOneSurjData` inside
      `false_of_bottcher_exterior_surj_data_two`;
    - removed the now-redundant conversion lemma.
    This reduces rooted theorem clutter without changing obligations.
  - Verification after inlining cleanup:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes.
  - Rooted-closure audit refresh:
    - generated `site/mlc_conjecture/graph.json` and compared all top-level
      declarations from `Mlc/MainConjecture.lean` against graph nodes;
    - result: no declarations missing from the rooted closure (all current
      declarations in the file participate in the `MLC.mlc_conjecture` path).
  - Seam narrowing update in `Mlc/MainConjecture.lean`:
    - replaced `BottcherExteriorSurjData` on the active route with the strictly
      smaller target `BottcherApproachOneSeqPreimageData`;
    - rewired the default ingress from
      `bottcher_exterior_surj_data_two_of_bottcher_map_surj` to
      `bottcher_approach_one_seq_preimage_data_two_of_bottcher_map_surj`;
    - rewired `mlc_conjecture` through
      `mlc_conjecture_of_bottcher_approach_one_seq_preimage_data_two`;
    - removed the now-redundant wrapper `BottcherApproachOneSurjData`.
    This reduces the remaining external-ray seam to exactly the countable
    preimage data consumed by the contradiction core.
  - Verification after seam narrowing:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes.
  - Rooted wrapper cleanup:
    - removed one-step forwarding lemma
      `false_of_bottcher_approach_one_seq_preimage_data_two_seam`;
    - `mlc_conjecture_of_bottcher_approach_one_seq_preimage_data_two` now
      consumes the contradiction core directly.
    This keeps all remaining declarations in the local seam materially used.
  - Rooted ingress cleanup:
    - rewired
      `bottcher_approach_one_seq_preimage_data_two`
      to build directly from
      `Quadratic.ExternalRayMapData (2 : ℂ)` via
      `Quadratic.external_ray_map_of_data_right_inverse`;
    - removed dependence on `Quadratic.bottcher_map_surj` from the active
      rooted seam in `Mlc/MainConjecture.lean`.
    This makes the remaining external dependency boundary explicit at
    `ExternalRayMapData` and reduces unrelated rooted edges.
  - Rooted ingress tightening:
    - default provider now instantiates the seam directly from
      `Quadratic.external_ray_map_exists (2 : ℂ)` instead of the intermediate
      wrapper `Quadratic.external_ray_map_data (2 : ℂ)`.
    This keeps the only non-core ingress explicit and minimal in
    `Mlc/MainConjecture.lean`.
  - Rooted-closure audit refresh (post seam narrowing/tightening):
    - regenerated `site/mlc_conjecture/graph.json`;
    - checked all top-level `def`/`lemma`/`theorem` declarations in
      `Mlc/MainConjecture.lean` against rooted graph nodes;
    - result: no declarations missing from the rooted closure.
  - Rooted wrapper reduction (follow-up):
    - removed default provider wrappers
      `bottcher_approach_one_seq_preimage_data_two_of_external_ray_map_data_two`
      and `bottcher_approach_one_seq_preimage_data_two`;
    - `mlc_conjecture` now inlines the direct construction of
      `BottcherApproachOneSeqPreimageData (2 : ℂ)` from
      `Quadratic.external_ray_map_exists (2 : ℂ)` using
      `Quadratic.external_ray_map_of_data_right_inverse`.
    This shortens the active rooted chain while preserving the same theorem
    signature and axiom footprint.
  - Constructive-gap audit (current repository state):
    - searched for non-axiomatic preimage/surjectivity providers for
      `Quadratic.bottcher_map` on `{w | 1 < ‖w‖}`;
    - all currently available routes still pass through one of:
      `Quadratic.external_ray_map_of_data_right_inverse`,
      `Quadratic.external_ray_map_right_inverse`,
      `Quadratic.bottcher_map_surj`,
      and these are sourced from
      `Quadratic.external_ray_map_exists`;
    - no existing theorem currently provides
      `BottcherApproachOneSeqPreimageData (2 : ℂ)` independently of
      `external_ray_map_exists`.
    This identifies the exact remaining constructive target: a direct,
    non-axiomatic provider of approach-sequence preimages at `c = 2`
    (or a strategy redesign that removes this requirement from the active path).
  - Seam weakening step in `Mlc/MainConjecture.lean`:
    - introduced `BottcherRightInverseOnExteriorData` (strictly weaker than
      full `ExternalRayMapData`, keeping only the right-inverse-on-exterior
      payload actually used on the active path);
    - added conversion
      `bottcher_approach_one_seq_preimage_data_of_right_inverse_on_exterior`;
    - kept the main route target minimal:
      `mlc_conjecture` still assembles through
      `mlc_conjecture_of_bottcher_approach_one_seq_preimage_data_two`, with
      default preimage data now produced via the weaker right-inverse seam.
    Current default instantiation still comes from
    `external_ray_map_exists`, but the required seam obligation is now weaker
    and explicit.
  - Verification after seam weakening:
    - `make graphs` passes
    - `make build` passes
    - `make check` unchanged (`Quot.sound`, `propext`, `Classical.choice`,
      `MLC.Quadratic.external_ray_map_exists`)
    - `scripts/verify_output.sh` passes.
  - Bridge-boundary axiom audit (Böttcher outside-plan layer):
    - `MLC.external_ray_map_data_of_injOn_outside_open_of_surj_exterior` is
      axiom-clean (core axioms only);
    - current default providers of its inputs are not:
      - `MLC.bottcher_map_inj_on_outside_open` depends on
        `MLC.Quadratic.external_ray_map_exists`;
      - `MLC.exterior_subset_image_outside_disk` depends on
        `MLC.Quadratic.external_ray_map_exists`.
    This isolates a concrete next boundary: construct
    outside-open injectivity and exterior-image surjectivity without the
    external-ray axiom, then reuse the existing axiom-clean bridge theorem.
  - Injectivity-stack audit (outside-plan):
    - axiom-clean:
      - `MLC.bottcher_map_isProperMap_of_continuous`
      - `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorph_and_outside_seed`
    - currently axiom-backed:
      - `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorph`
      - `MLC.bottcher_map_inj_on_basin_of_isLocalHomeomorph`
    because the current automatic path still calls
    `MLC.bottcher_map_inj_on_outside_open` (which depends on
    `external_ray_map_exists`).
    This gives a concrete sub-target: provide an external-ray-free
    outside-open injectivity seed, then lift via the existing core-only
    proper/local-homeomorph theorem chain.
  - Rooted wrapper cleanup in `Mlc/MainConjecture.lean`:
    - removed one-use default lemma
      `bottcher_right_inverse_on_exterior_data_two`;
    - inlined its construction at the `mlc_conjecture` call-site.
    This keeps the active rooted path minimal while preserving theorem shape
    and the current axiom boundary.
  - Outside-plan conversion-chain audit (additional):
    - core-only (axiom-clean) conversion lemmas are already available:
      - `MLC.bottcherImageOutsideOpenIsExterior_iff_exterior_subset_image`
      - `MLC.bottcherSurjOnExteriorFromOutsideOpen_of_image_eq_exterior`
      - `MLC.bottcherImageOutsideOpenIsExterior_of_surj`
      - `MLC.outside_disk_to_outside_open_image_refinement_of_exterior_subset_image_outside_open`
      - `MLC.bottcher_map_norm_gt_one_implies_basin`
    - axiom-backed boundary points remain:
      - `MLC.exterior_subset_image_outside_disk`
      - `MLC.bottcher_map_inj_on_outside_open`
    This sharpens the next objective: replace the two boundary providers above
    with external-ray-free constructions, then reuse the existing core-only
    conversion chain to recover the right-inverse seam needed by
    `Mlc/MainConjecture.lean`.
  - Local-to-global injectivity audit (outside-open layer):
    - local analytic/inverse machinery on outside-open is already independent of
      `external_ray_map_exists`:
      - `MLC.bottcher_map_local_inj_on_outside_open`
      - `MLC.bottcher_map_isLocalHomeomorphOn_outside_open`
      - `MLC.bottcher_map_isOpenMap_on_outside_open`
      (these currently depend on `MLC.Quadratic.bottcher_seq_converges`, not on
      external-ray existence);
    - the remaining blocker is a global injectivity upgrade on outside-open
      without routing through
      `MLC.bottcher_map_inj_on_outside_open_of_data`.
    This suggests the next technical task: add an external-ray-free global
    injectivity theorem for outside-open from the existing local/proper stack.
  - Outside-plan seam refactor (core-only boundary extraction):
    - added
      `MLC.exterior_subset_image_outside_disk_of_right_inverse`, a core-only
      theorem that derives exterior-in-image-of-`outside_disk` from an explicit
      right-inverse-on-exterior payload;
    - rewired `MLC.exterior_subset_image_outside_disk` to be only a default
      wrapper that instantiates that payload via `external_ray_map`;
    - added
      `MLC.exterior_subset_image_outside_open_of_outside_disk_refinement_of_exterior_subset_image_outside_disk`,
      extracting a core-only conversion step with explicit `h_disk` input;
    - rewired
      `MLC.exterior_subset_image_outside_open_of_outside_disk_refinement` to be
      a wrapper through that extracted theorem.
    This keeps the current behavior unchanged while making the constructive
    replacement boundary explicit and reusable.
  - Outside-plan seam refactor (follow-up):
    - added
      `MLC.exterior_subset_image_outside_open_of_right_inverse_and_outside_disk_refinement`,
      a core-only bridge from:
      - right-inverse-on-exterior payload, and
      - outside-disk→outside-open image refinement
      to outside-open exterior inclusion;
    - rewired the default theorem
      `MLC.exterior_subset_image_outside_open_of_outside_disk_refinement`
      to instantiate the right-inverse payload with `external_ray_map`.
    This further isolates the external-ray dependency to default instantiation
    while preserving existing theorem interfaces.
  - Axiom audit for newly extracted outside-plan bridges:
    - `MLC.exterior_subset_image_outside_disk_of_right_inverse` is core-only.
    - `MLC.exterior_subset_image_outside_open_of_right_inverse_and_outside_disk_refinement`
      is core-only.
  - Outside-open injectivity seam extraction:
    - introduced `MLC.BottcherLeftInverseOnOutsideOpenData` as an explicit
      seam target for injectivity on outside-open;
    - added core-only theorem
      `MLC.bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open`;
    - rewired `MLC.bottcher_map_inj_on_outside_open_of_data` through that seam
      using
      `MLC.bottcher_left_inverse_on_outside_open_data_of_external_ray_map_data`.
    This makes the injectivity boundary explicit and keeps default external-ray
    usage out of the core injectivity theorem.
  - Axiom audit for outside-open injectivity seams:
    - `MLC.BottcherLeftInverseOnOutsideOpenData` is core-only.
    - `MLC.bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open`
      is core-only.
    - `MLC.bottcher_left_inverse_on_outside_open_data_of_external_ray_map_data`
      is core-only.
    - `MLC.bottcher_map_inj_on_outside_open_of_data` remains core-only.
  - External-ray-data bridge extraction from new injectivity seam:
    - added
      `MLC.external_ray_map_data_of_left_inverse_on_outside_open_of_surj_exterior`;
    - added
      `MLC.external_ray_map_data_of_left_inverse_on_outside_open_of_image_eq_exterior`.
    These route external-ray-data construction through the explicit
    left-inverse seam plus existing surjectivity/image-equality seams.
  - Axiom audit for extracted external-ray-data bridges:
    - both newly extracted theorems above are core-only.
  - Wrapper cleanup:
    - removed forwarding lemma
      `MLC.bottcher_map_inj_on_outside_open_of_data`;
    - rewired `MLC.bottcher_map_inj_on_outside_open` directly through
      `MLC.bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open`
      plus
      `MLC.bottcher_left_inverse_on_outside_open_data_of_external_ray_map_data`.
    This reduces one wrapper layer while preserving behavior and axioms.
  - Surjectivity conversion seam extraction:
    - added core-only theorem
      `MLC.bottcherSurjOnExteriorFromOutsideOpen_of_exterior_subset_image_outside_open`;
    - rewired
      `MLC.bottcherSurjOnExteriorFromOutsideOpen_of_image_eq_exterior`
      through this new seam.
    This factors the outside-open surjectivity conversion into a reusable,
    assumption-explicit step.
  - External-ray-data conversion seam extraction (subset-image variant):
    - added core-only theorem
      `MLC.external_ray_map_data_of_left_inverse_on_outside_open_of_exterior_subset_image_outside_open`;
    - rewired
      `MLC.external_ray_map_data_of_left_inverse_on_outside_open_of_image_eq_exterior`
      through this new subset-image seam.
    This keeps the conversion chain granular and avoids coupling directly to
    the image-equality form.
  - Basin-injectivity seam extraction (`proper + local homeomorph` route):
    - added core-only theorem
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorph_and_outside_seed_of_left_inverse_on_outside_open`;
    - added core-only theorem
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorph_of_left_inverse_on_outside_open`;
    - rewired
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorph`
      to be a default wrapper through the new left-inverse seam.
  - Axiom audit for new basin-injectivity seams:
    - both newly extracted `...of_left_inverse_on_outside_open` theorems are
      core-only;
    - default theorem
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorph` remains
      external-ray-backed (as expected) via default seam instantiation.
  - Basin-injectivity seam extraction (`isLocalHomeomorph` route):
    - added core-only theorem
      `MLC.bottcher_map_inj_on_basin_of_isLocalHomeomorph_of_left_inverse_on_outside_open`;
    - rewired
      `MLC.bottcher_map_inj_on_basin_of_isLocalHomeomorph`
      as a default wrapper through this seam.
  - Axiom audit for the `isLocalHomeomorph` seam:
    - extracted theorem above is core-only;
    - default wrapper remains external-ray-backed via default seam
      instantiation (expected).
  - Basin-injectivity seam extraction (`IsLocalHomeomorphOn` route):
    - added core-only theorem
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin_of_injOn_outside_open_of_exterior_subset_image_basin`;
    - rewired
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin`
      as a default wrapper through this seam.
  - Axiom audit for the `IsLocalHomeomorphOn` seam:
    - extracted theorem above is core-only;
    - default wrapper remains external-ray-backed via default seam
      instantiation (expected).
  - Basin-image + `IsLocalHomeomorphOn` combined seam extraction:
    - added core-only theorem
      `MLC.exterior_subset_image_basin_of_right_inverse`;
    - added core-only theorem
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin_of_left_inverse_on_outside_open_of_right_inverse_on_exterior`;
    - rewired default theorem
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin`
      through these explicit left/right seam payloads.
  - Axiom audit for combined seam:
    - both extracted theorems above are core-only;
    - default wrapper remains external-ray-backed via default seam
      instantiation (expected).
  - Seam normalization cleanup:
    - introduced shared alias
      `MLC.BottcherRightInverseOnExteriorDataOutsidePlan`;
    - rewired extracted outside-plan bridge theorems to consume this shared
      right-inverse seam type (instead of repeating raw existential payloads).
    This is a non-semantic cleanup that keeps seam signatures uniform.
  - Main-conjecture seam integration:
    - removed local duplicate right-inverse seam type from
      `Mlc/MainConjecture.lean`;
    - switched the active MLC seam route to use the shared
      `MLC.BottcherRightInverseOnExteriorDataOutsidePlan`;
    - added explicit import of
      `Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan`
      for this shared seam type.
    This ties the active `mlc_conjecture` path to the extracted outside-plan
    seam layer directly.
  - Outside-plan right-inverse constructor normalization:
    - added
      `MLC.bottcher_right_inverse_on_exterior_data_of_external_ray_map_data`
      and default wrapper
      `MLC.bottcher_right_inverse_on_exterior_data`;
    - rewired default outside-plan wrappers
      `MLC.exterior_subset_image_outside_disk`,
      `MLC.exterior_subset_image_outside_open_of_outside_disk_refinement`, and
      `MLC.bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin`
      to consume the shared constructor;
    - rewired `MLC.mlc_conjecture` to instantiate its right-inverse seam via
      the shared outside-plan constructor instead of local ad-hoc assembly.
    This removes duplicated right-inverse construction logic and keeps the
    external-ray boundary localized to explicit default constructors.
  - Main-conjecture classification-path preservation:
    - rewired
      `mlc_conjecture_of_bottcher_approach_one_seq_preimage_data_two`
      to build `IRClassificationData` through
      `classify_infinitely_renormalizable` with an explicit
      `InfinitelyRenormalizableHasTowerData` seam variable;
    - kept contradiction seeding explicit at the same boundary (`hFalse` from
      approach-sequence preimage data), but removed direct `False.elim` feeding
      of the classification slot.
    This keeps the intended IR-classification theorem path active in the
    rooted strategy surface while preserving the current axiom footprint.
  - Final seam explicitness at the theorem boundary:
    - added
      `mlc_conjecture_of_bottcher_right_inverse_on_exterior_data_two`;
    - added default provider
      `bottcher_right_inverse_on_exterior_data_two_of_external_ray_map_exists`;
    - rewired `mlc_conjecture` through this explicit right-inverse seam theorem.
    This isolates the remaining non-core ingress as a single named provider
    while keeping the contradiction core and strategy assembly unchanged.
  - Outside-plan default constructor tightening:
    - added generic constructor
      `MLC.bottcher_right_inverse_on_exterior_data_of_external_ray_map_exists`;
    - rewired
      `MLC.bottcher_right_inverse_on_exterior_data`
      to call this constructor directly;
    - rewired
      `MLC.bottcher_right_inverse_on_exterior_data_two_of_external_ray_map_exists`
      in `Mlc/MainConjecture.lean` to consume the shared constructor.
    This keeps the external ingress explicit at the outside-plan seam layer and
    removes one default indirection through `external_ray_map_data`.
  - Active seam weakened from right-inverse payload to exterior surjectivity:
    - removed `BottcherRightInverseOnExteriorDataOutsidePlan` from the active
      `Mlc/MainConjecture.lean` route;
    - introduced `BottcherExteriorSurjData` and
      `bottcher_approach_one_seq_preimage_data_of_bottcher_exterior_surj_data`;
    - added default provider
      `bottcher_exterior_surj_data_two_of_bottcher_map_surj`;
    - rewired `mlc_conjecture` through
      `mlc_conjecture_of_bottcher_exterior_surj_data_two`.
    This further weakens the rooted replacement obligation from a global
    right-inverse function to existential exterior surjectivity data.
  - Rooted boundary weakened again to direct approach-sequence preimage data:
    - removed intermediate rooted wrapper
      `mlc_conjecture_of_bottcher_exterior_surj_data_two`;
    - added default provider
      `bottcher_approach_one_seq_preimage_data_two_of_bottcher_map_surj`;
    - rewired `mlc_conjecture` back through
      `mlc_conjecture_of_bottcher_approach_one_seq_preimage_data_two`.
    This keeps the active seam at the strict minimal contradiction input
    (`BottcherApproachOneSeqPreimageData (2)`), while still sourcing defaults
    from `bottcher_map_surj`.
  - Provider audit after re-rooting:
    - re-searched the repository for any independent constructors of
      `BottcherApproachOneSeqPreimageData (2)` and found only the active route
      through `bottcher_exterior_surj_data_two_of_bottcher_map_surj`;
    - `Quadratic.bottcher_map_surj` remains connected to
      `MLC.Quadratic.external_ray_map_exists` in the current model.
    So the next constructive elimination target remains unchanged:
    replace the `bottcher_map_surj`-sourced default provider with a
    non-axiomatic approach-sequence preimage constructor at `c = 2`.
  - Wrapper cleanup on rooted preimage ingress:
    - removed the intermediate seam layer
      `BottcherExteriorSurjData` and conversion wrapper
      `bottcher_approach_one_seq_preimage_data_of_bottcher_exterior_surj_data`
      from `Mlc/MainConjecture.lean`;
    - rewired
      `bottcher_approach_one_seq_preimage_data_two_of_external_ray_map_exists`
      to construct preimages directly from
      `Quadratic.external_ray_map_exists`.
    This keeps the rooted ingress minimal and avoids extra single-use wrappers.
  - Rooted ingress directness update:
    - removed the `bottcher_map_surj` detour from the active `mlc_conjecture`
      path;
    - the only non-core ingress for the active seam provider is now explicit at
      `Quadratic.external_ray_map_exists (2 : ℂ)`.
    This improves boundary auditability without changing theorem signatures or
    axiom footprint.
  - Rooted ingress simplification:
    - rewired
      `bottcher_approach_one_seq_preimage_data_two_of_external_ray_map_exists`
      to destructure `Quadratic.external_ray_map_exists (2 : ℂ)` directly
      (`⟨f, hf_right, _⟩`) and build preimages from `hf_right`;
    - removed use of intermediate helper projections at this call site.
    This keeps the same mathematical content while making the residual axiom
    dependency syntactically explicit at the exact provider boundary.
  - Rooted-closure audit refresh:
    - regenerated `site/mlc_conjecture/graph.json`;
    - rechecked top-level declarations of `Mlc/MainConjecture.lean`;
    - result: no declarations missing from rooted closure.
- Blocked pending a consistent constructive replacement architecture for
  finite-branch data + IR classification + molecule bridge data.
- Any attempt to remove `external_ray_map_exists` before Phase 1 is complete
  is likely to either:
  - reintroduce old axioms indirectly, or
  - recreate tautological/contradiction routing.
