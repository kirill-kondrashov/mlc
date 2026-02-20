# Plan: Unblock `external_ray_map_exists` Elimination via Track 1 + Track 2

Date: 2026-02-20

## Goal
Eliminate `MLC.Quadratic.external_ray_map_exists` from the axiom footprint of
`MLC.mlc_conjecture` without:
- introducing new axioms,
- adding hypotheses to `MLC.mlc_conjecture`,
- collapsing the proof into tautological contradiction routing.

## Why previous path was blocked
Current model contains an explicit incompatibility:
- `MoleculeConformalModulusLowerBoundData -> ¬ InfinitelyRenormalizableHasTowerData`
  (`Mlc/FastTowerExistenceObstruction.lean`).
So any architecture that tries to constructively assume both global
`InfinitelyRenormalizableHasTowerData` and conformal bridge data is blocked.

## Track 1 (IR Classification, constructive)
Target: produce
`IRClassificationData :=
  ∀ c hc hIR, PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c`
without using global `InfinitelyRenormalizableHasTowerData`.

### Scope
- Build a local, per-parameter classification route for IR parameters.
- Keep finite branch via Yoccoz path unchanged.
- Do not use contradiction as the provider in final active path.

### Deliverables
1. New constructive provider theorem for `IRClassificationData` (or an equivalent
   theorem consumed directly by `mlc_strategy_of_branchLocalData`).
2. No dependence of that provider on
   `InfinitelyRenormalizableHasTowerData`.
3. `make check` still reports only core axioms plus remaining external-ray seam
   until Track 2 is complete.

## Track 2 (Satellite bridge, constructive)
Target: provide constructive
`h_bridge : MoleculeConjectureRefined -> ... -> LocallyConnectedAt ...`
without contradiction providers in `Mlc/MainConjecture.lean`.

### Scope
- Prefer direct bridge construction into `mlc_conjecture_of_motionHyp_classify_bridge_data`.
- Avoid reintroducing removed axioms through hidden wrappers.
- Keep all introduced declarations on the rooted `mlc_conjecture` path.

### Deliverables
1. Constructive bridge provider theorem with explicit dependencies.
2. Active `mlc_conjecture` path no longer obtains bridge data from `False.elim`.
3. Rooted dependency audit clean: no unused declarations in
   `Mlc/MainConjecture.lean`.

## Baseline Refactor Completed (this commit series)
To avoid spinning around the inconsistent pair interface, the active fallback
in `Mlc/MainConjecture.lean` is now routed directly through:
- `mlc_conjecture_of_motionHyp_classify_bridge_data`,
and no longer through a bundled `(tower + conformal)` wrapper theorem.

This keeps the remaining replacement targets explicit:
1. constructive `IRClassificationData`,
2. constructive `h_bridge`.

## Progress (2026-02-20)
- [x] Track-1 interface extraction in `Mlc/MainConjecture.lean`:
  - added `IRNoTowerImpliesPrimitiveData`;
  - added
    `irClassificationData_of_noTowerImpliesPrimitiveData :
      IRNoTowerImpliesPrimitiveData -> IRClassificationData`;
  - added
    `mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeBridgeTarget`
    and rewired the active fallback to consume this Track-1 target directly.
  This removes dependence on opaque pre-packed `IRClassificationData` at the
  fallback boundary and makes the remaining constructive classification
  obligation explicit.
- [x] Centralized Track-1 classification theorem in
  `Mlc/InfinitelyRenormalizable.lean`:
  - added `classify_infinitely_renormalizable_of_noTowerImpliesPrimitive`;
  - rewired `Mlc/MainConjecture.lean` to derive `IRClassificationData`
    through that theorem.
  This keeps Track-1 logic in the IR module rather than duplicating the
  by-cases proof in `MainConjecture`.
- [x] Combined Track-1 + Track-2 seam packaging in `Mlc/MainConjecture.lean`:
  - added
    `IRNoTowerPrimitiveAndMoleculeBridgeTargetData :=
      IRNoTowerImpliesPrimitiveData ∧
      MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData`;
  - added `mlc_conjecture_of_motionHyp_track12_data`;
  - rewired the active fallback to consume this single combined seam datum.
  This reduces replacement surface area and makes remaining obligations explicit
  as one packaged target.
- [x] Began Track-2 proof content in `Mlc/MoleculeToSatelliteNestData.lean`:
  - proved
    `moleculeBridgeTarget_of_moleculeUniformBridgeTarget :
      MoleculeImpliesUniformConformalLowerBoundTarget ->
      MoleculeImpliesSatellitePrincipalNestData`;
  - rewired `Mlc/MainConjecture.lean` to consume the uniform Track-2 target in
    the combined seam datum and derive the strong target by theorem.
  This is a completed theorem-level reduction step (proof, not just interface
  refactor) and narrows Track-2 obligations to the uniform target.
- [x] Began Track-1/Track-2 interaction proof in `Mlc/MainConjecture.lean`:
  - proved
    `irClassificationData_of_noTowerImpliesPrimitiveData_of_moleculeUniformBridgeTarget`,
    using
    `classify_infinitely_renormalizable_of_noTowerImpliesPrimitive` plus
    `not_satelliteRenormalizableTower_of_mem_mandelbrot_conformal`;
  - rewired
    `mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeUniformBridgeTarget`
    to consume that derived classification directly.
  This starts replacing purely interface-level Track-1 usage with theorem-level
  interaction between Track-1 and Track-2 assumptions.
- [x] Added an explicit Track-2 assembly theorem in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_motionHyp_classify_moleculeBridgeTarget`
  consuming `MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData`.
- [x] Fixed a regression where direct use of
  `MoleculeBridgeTarget.bridge_of_moleculeBridgeTarget` reintroduced
  `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.
  The active bridge now uses `lc_at_of_shrink_of_connected_at` with
  `finite_connectedAt_provider_of_motionHyp`, preserving the current
  one-axiom frontier.
- [x] `make build`, `make graphs`, `make check`, and
  `scripts/verify_output.sh` pass after rewiring.
- [x] Removed contradiction-routing in the Track-1/Track-2 IR-classification seam:
  - added
    `not_satelliteRenormalizableTower_of_mem_mandelbrot_uniform` in
    `Mlc/FastTowerExistenceObstruction.lean`;
  - added
    `classify_infinitely_renormalizable_of_noTowerImpliesPrimitive_of_noTowerOnM`
    in `Mlc/InfinitelyRenormalizable.lean`;
  - rewired
    `irClassificationData_of_noTowerImpliesPrimitiveData_of_moleculeUniformBridgeTarget`
    in `Mlc/MainConjecture.lean` to use these direct theorems instead of the
    `False.elim` satellite branch.
- [x] Reduced the remaining external-ray default seam at `c = 2` from direct
  use of `bottcher_map_surj` to explicit outside-plan right-inverse payload:
  - added
    `approach_one_seq_in_bottcher_range_data_two_of_right_inverse_on_exterior`;
  - rewired the default instantiation through
    `approach_one_seq_in_bottcher_range_data_two_of_bottcher_right_inverse_on_exterior`.
  This makes the final replacement target more explicit as
  `BottcherRightInverseOnExteriorDataOutsidePlan (2 : ℂ)`.
- [x] Further reduced the same seam to a weaker existential-range target in
  `Mlc/MainConjecture.lean`:
  - added `BottcherExteriorRangeData`;
  - added
    `bottcherExteriorRangeData_of_right_inverse_on_exterior`;
  - routed `approach_one_seq_in_bottcher_range_data_two_of_right_inverse_on_exterior`
    through
    `approach_one_seq_in_bottcher_range_data_two_of_bottcherExteriorRangeData`.
  This isolates the minimal active need for the `c = 2` seed to
  `BottcherExteriorRangeData (2 : ℂ)`.
- [x] Isolated the current default `c = 2` exterior-range seed to a single
  named seam lemma:
  - added
    `bottcherExteriorRangeData_two_of_bottcher_right_inverse_on_exterior`;
  - rewired
    `approach_one_seq_in_bottcher_range_data_two_of_bottcher_right_inverse_on_exterior`
    through this seam.
- [x] Weakened the default `c = 2` exterior-range seam further from
  right-inverse payload to outside-disk image inclusion:
  - added
    `bottcherExteriorRangeData_of_exterior_subset_image_outside_disk`;
  - added
    `bottcherExteriorRangeData_two_of_exterior_subset_image_outside_disk`;
  - rewired
    `approach_one_seq_in_bottcher_range_data_two_of_bottcher_right_inverse_on_exterior`
    to use the outside-disk inclusion seam.
- [x] Isolated the active `mlc_conjecture` endpoint to the single theorem-level
  seam `BottcherExteriorRangeData (2 : ℂ)`:
  - added `mlc_conjecture_of_bottcherExteriorRangeData_two`;
  - rewired `mlc_conjecture` to instantiate only this seam (currently by
    `bottcherExteriorRangeData_two_of_exterior_subset_image_outside_disk`).
- [x] Removed unused intermediate right-inverse seam lemmas from
  `Mlc/MainConjecture.lean` to keep only declarations on the active rooted
  path.
- [x] Added theorem-level seam equivalence:
  `BottcherExteriorRangeData c` ↔
  `{w | 1 < ‖w‖} ⊆ Quadratic.bottcher_map c '' outside_disk c`.
  This makes the remaining constructive obligation explicit in image-inclusion
  form and avoids further wrapper churn.
- [x] Rewired the default `c = 2` seam source from outside-plan right-inverse
  chain to direct `Quadratic.bottcher_map_surj`:
  - added `bottcherExteriorRangeData_of_bottcher_map_surj`;
  - default seed is now
    `bottcherExteriorRangeData_two_of_bottcher_map_surj`.
  The active seam is unchanged (`BottcherExteriorRangeData (2 : ℂ)`), but the
  default provider is now a simpler direct surjectivity route.
- [x] Localized seam provenance further to explicit data-package form:
  - replaced surjectivity-route default with
    `bottcherExteriorRangeData_of_externalRayMapData`;
  - default seed is now
    `bottcherExteriorRangeData_two_of_externalRayMapData`.
  This keeps the active seam unchanged while making the missing dependency
  source explicit as `Quadratic.ExternalRayMapData (2 : ℂ)`.
- [x] Simplified the active endpoint seam back to the weaker sequence-range form
  at `c = 2` and removed unused stronger exterior-range wrappers:
  - added
    `approach_one_seq_in_bottcher_range_data_two_of_externalRayMapData`;
  - rewired `mlc_conjecture` to instantiate
    `mlc_conjecture_of_approach_one_seq_in_bottcher_range_data_two` directly;
  - deleted now-unused `BottcherExteriorRangeData` wrapper chain from
    `Mlc/MainConjecture.lean`.
  Active missing-dependency source remains explicit as
  `Quadratic.ExternalRayMapData (2 : ℂ)`.
- [x] Isolated the constructive core assembly seam in
  `Mlc/MainConjecture.lean`:
  - added
    `MainPathData := PuzzleBoundaryMotionHyp ∧ IRNoTowerPrimitiveAndMoleculeBridgeTargetData`;
  - added `mlc_conjecture_of_mainPathData` as the explicit non-contradiction
    core route;
  - confined contradiction fallback to a single temporary seed lemma
    `mainPathData_of_bottcher_approach_to_one_seq_preimage_data_two`.
  This reduces circular flow in the rooted path and makes the remaining
  constructive replacement target explicit.
- [x] Rewired the root theorem endpoint to consume the constructive seam
  directly:
  - added `mainPathData_axiom_seed`;
  - rewired `mlc_conjecture` to
    `mlc_conjecture_of_mainPathData mainPathData_axiom_seed`.
  The active frontier is now explicitly the constructive `MainPathData` seed,
  with external-ray and contradiction fallback contained below it.
- [x] Removed now-unused wrapper assembly theorems from
  `Mlc/MainConjecture.lean` to keep only rooted declarations:
  - removed
    `mlc_conjecture_of_bottcher_approach_to_one_seq_preimage_data_two`;
  - removed
    `mlc_conjecture_of_approach_one_seq_in_bottcher_range_data_two`;
  - kept the direct rooted seed route
    `mainPathData_axiom_seed -> mlc_conjecture_of_mainPathData`.
- [x] Weakened the active external-ray sequence seam from explicit right-inverse
  data to basin-image inclusion:
  - added `BottcherExteriorSubsetImageBasinData`;
  - routed
    `approach_one_seq_in_bottcher_range_data_two_of_externalRayMapData`
    through
    `approach_one_seq_in_bottcher_range_data_of_exterior_subset_image_basin`;
  - added
    `bottcherExteriorSubsetImageBasinData_of_externalRayMapData`.
  This isolates the remaining constructive obligation to exterior image
  inclusion on the basin, which is weaker than explicit external-ray inverse
  data.
- [x] Isolated the default `c = 2` basin-image seed into a single named seam
  lemma:
  - added
    `bottcherRightInverseOnExteriorData_two_axiom_seed`;
  - added
    `bottcherExteriorSubsetImageBasinData_two_of_exterior_subset_image_outside_disk`;
  - added
    `bottcherExteriorSubsetImageBasinData_two_axiom_seed`;
  - rewired
    `approach_one_seq_in_bottcher_range_data_two_of_basinImageSeed`
    through this seam.
  This keeps the rooted endpoint stable and exposes one explicit replacement
  target at `c = 2`.
- [x] Removed now-unused
  `approach_one_seq_in_bottcher_range_data_two_of_externalRayMapData` from
  `Mlc/MainConjecture.lean` after rerouting the default seam.

## Execution Order
1. Implement Track 1 provider interface and prove as much non-axiomatically as
   possible.
2. Implement Track 2 provider interface and wire it into the same assembly
   theorem.
3. Rewire `mlc_conjecture` path to consume constructive Track 1 + Track 2
   providers.
4. Remove contradiction fallbacks from rooted path.
5. Verify with:
   - `make build`
   - `make graphs`
   - `make check`
   - `scripts/verify_output.sh`

## Immediate Theorem Targets
1. Track 1:
   prove `IRNoTowerImpliesPrimitiveData` constructively in
   `Mlc/InfinitelyRenormalizable.lean` (without
   `InfinitelyRenormalizableHasTowerData`).
2. Track 2:
   prove `MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData`
   constructively (or via a proved stronger target with a theorem-level
   reduction), then wire it into `mlc_conjecture_of_motionHyp_track12_data`
   without `False.elim`.

## Current Hard Blockers (after first proof steps)
1. Track 1 core:
   no in-repo theorem currently derives
   `InfinitelyRenormalizable c ∧ ¬ SatelliteRenormalizableTower c ->
    PrimitiveRenormalizable c`.
   Existing primitive theorem (`primitive_tower_implies_primitive`) requires an
   explicit renormalization tower and infinitely many primitive steps.
2. Track 2 core:
   no in-repo constructive producer yet for
   `MoleculeImpliesUniformConformalLowerBoundTarget` from
   `MoleculeConjectureRefined`.
   The current proof progress only reduces:
   `uniform target -> strong principal-nest target`.
3. Motion-seed fallback route check:
   constructing `PuzzleBoundaryMotionHyp` from `bottcher_onM_hyp` via
   `puzzle_boundary_motion_hyp_of_onM` compiles, but its axiom footprint
   includes `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
   (probe run on 2026-02-20 with `#print axioms`). This route is therefore
   excluded by the "no new axioms" requirement.
4. Current external-ray dependency bottleneck is fully localized to one
   outside-plan constructor:
   `bottcher_right_inverse_on_exterior_data_of_external_ray_map_exists`.
   All rooted dependencies now flow through this single node via the explicit
   seam chain in `PLAN_external_ray_map_exists_outside_open_targets.md`.

## Exit Criteria
- `MLC.Quadratic.external_ray_map_exists` removed from `MLC.mlc_conjecture`
  axiom footprint.
- No contradiction-only provider in transitive dependencies of
  `MLC.mlc_conjecture`.
- No new axioms, no new hypotheses on `MLC.mlc_conjecture`.
