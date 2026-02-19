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
  contradiction wrappers around:
  - `external_ray_data_two_axiom`
  - `false_of_external_ray_data_two`
- Direct contradiction-backed providers currently on-path in
  `Mlc/MainConjecture.lean`:
  - `ir_classification_data_of_external_ray_data_two`
  - `para_puzzle_connected_data_of_external_ray_data_two`
  - `molecule_bridge_data_of_external_ray_data_two`

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
   - `false_of_external_ray_data_two`
   - `external_ray_data_two_axiom`
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
   - `false_of_external_ray_data_two`
   - `external_ray_data_two_axiom`.
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
  - Extracted a dedicated assembly theorem
    `mlc_conjecture_of_branchData` in `Mlc/MainConjecture.lean`.
  - `MLC.mlc_conjecture` now routes through that theorem with the current
    external-ray-backed branch-data providers.
  - This isolates the exact replacement interface for Phases 2–4 without
    changing theorem signatures or introducing new axioms.
- Blocked pending a consistent constructive replacement architecture for
  finite-branch data + IR classification + molecule bridge data.
- Any attempt to remove `external_ray_map_exists` before Phase 1 is complete
  is likely to either:
  - reintroduce old axioms indirectly, or
  - recreate tautological/contradiction routing.
