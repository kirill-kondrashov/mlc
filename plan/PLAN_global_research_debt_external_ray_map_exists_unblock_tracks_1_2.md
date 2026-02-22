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
- [x] Rebased the outside-plan default right-inverse seam from direct
  `external_ray_map_exists` usage to `Quadratic.bottcher_map_surj`:
  - added
    `bottcher_right_inverse_on_exterior_data_of_bottcher_map_surj` in
    `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`;
  - rewired
    `bottcher_right_inverse_on_exterior_data` to use this theorem.
  This shifts the active bottleneck from external-ray existence directly to the
  explicit exterior-surjectivity seam.
- [x] Shortened the rooted `mlc_conjecture` chain by removing the local
  right-inverse seed from `Mlc/MainConjecture.lean`:
  - deleted `bottcherRightInverseOnExteriorData_two_axiom_seed`;
  - rewired
    `bottcherExteriorSubsetImageBasinData_two_of_exterior_subset_image_outside_disk`
    to use `exterior_subset_image_outside_disk (2 : ℂ)` directly.
  The active rooted path now reaches
  `Quadratic.bottcher_map_surj` without intermediate right-inverse wrappers.
- [x] Removed one more wrapper node below `Quadratic.bottcher_map_surj`:
  - rewrote `Quadratic.bottcher_map_surj` to use
    `external_ray_map_of_data_right_inverse` with
    `h_data := external_ray_map_exists c` directly.
  The rooted chain now hits `external_ray_map_exists` from
  `Quadratic.bottcher_map_surj` with no intermediate `external_ray_map` node.
- [x] Pruned the rooted `MainConjecture` seam to the direct sequence-range
  constructor:
  - removed the intermediate
  `BottcherExteriorSubsetImageBasinData` wrapper chain from the active root
    path;
  - rewired `approach_one_seq_in_bottcher_range_data_two_axiom_seed` to
    `approach_one_seq_in_bottcher_range_data_of_bottcher_map_surj`.
  Active rooted bottleneck is now explicitly
  `approach_one_seq_in_bottcher_range_data_of_bottcher_map_surj ->
   Quadratic.bottcher_map_surj -> external_ray_map_exists`.
- [x] Removed redundant `c = 2` sequence-range wrapper seed from rooted path:
  - deleted `approach_one_seq_in_bottcher_range_data_two_axiom_seed`;
  - rewired `mainPathData_axiom_seed` to consume
  `approach_one_seq_in_bottcher_range_data_of_bottcher_map_surj (2 : ℂ)`
    directly.
  Rooted chain is now:
  `mlc_conjecture -> mainPathData_axiom_seed ->
   approach_one_seq_in_bottcher_range_data_of_bottcher_map_surj ->
   Quadratic.bottcher_map_surj -> external_ray_map_exists`.
- [x] Removed the intermediate sequence-range data layer entirely from the
  rooted path:
  - deleted `ApproachOneSeqInBottcherRangeData` and
    `approach_one_seq_in_bottcher_range_data_of_bottcher_map_surj` from
    `Mlc/MainConjecture.lean`;
  - replaced them with direct seam constructor
    `bottcher_approach_to_one_seq_preimage_data_of_bottcher_map_surj`;
  - rewired `mainPathData_axiom_seed` to use this direct constructor.
  Rooted chain is now:
  `mlc_conjecture -> mainPathData_axiom_seed ->
   bottcher_approach_to_one_seq_preimage_data_of_bottcher_map_surj ->
   Quadratic.bottcher_map_surj -> external_ray_map_exists`.
- [x] Removed one more rooted wrapper node by inlining the preimage-sequence
  constructor into `mainPathData_axiom_seed`:
  - deleted
    `bottcher_approach_to_one_seq_preimage_data_of_bottcher_map_surj`;
  - kept the same witness construction directly in `mainPathData_axiom_seed`.
  Rooted chain is now minimal on this seam:
  `mlc_conjecture -> mainPathData_axiom_seed ->
   Quadratic.bottcher_map_surj -> external_ray_map_exists`.
- [x] Removed `Quadratic.bottcher_map_surj` from the rooted path by switching
  `mainPathData_axiom_seed` to direct `ExternalRayMapData` witness extraction:
  - rewired witness sequence to
    `Quadratic.external_ray_map_of_data h_ray (approach_one_seq n)` with
    `h_ray := Quadratic.external_ray_map_exists (2 : ℂ)`;
  - used `Quadratic.external_ray_map_of_data_right_inverse` directly.
  Rooted chain is now:
  `mlc_conjecture -> mainPathData_axiom_seed -> external_ray_map_exists`.
- [x] Factored the final seam into a named theorem in `Mlc/MainConjecture.lean`:
  - added `mainPathData_of_externalRayMapData_two`;
  - rewired `mainPathData_axiom_seed` to consume that theorem.
  This makes the last replacement target explicit as a constructive provider of
  `ExternalRayMapData (2 : ℂ)` without changing the rooted axiom footprint.
- [x] Exposed the last rooted axiom seam as a single named seed:
  - added `ExternalRayMapDataTwo`;
  - added `externalRayMapData_two_axiom_seed`;
  - rewired `mainPathData_axiom_seed` through that seed.
  Rooted chain is now:
  `mlc_conjecture -> mainPathData_axiom_seed ->
   externalRayMapData_two_axiom_seed -> external_ray_map_exists`.
- [x] Added a theorem-level clopen exterior-surjectivity bridge in
  `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - added
    `bottcher_map_outside_open_to_exterior`;
  - added
    `bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_of_isLocalHomeomorph_restrict`;
  - added
    `external_ray_map_data_of_injOn_outside_open_of_isProperMap_of_isLocalHomeomorph_restrict`.
  This advances the non-circular outside-open route by replacing the previous
  “planned method” with a proved theorem-level bridge under explicit geometric
  assumptions on the restricted map `outside_open → exterior`, and removes the
  previously over-strong `preimage exterior ⊆ outside_open` assumption.
- [x] Reduced the restricted-map clopen assumptions one step further:
  - added
    `isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_slit_of_injOn`;
  - added
    `bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_restrict_of_slit_of_injOn`;
  - added
    `external_ray_map_data_of_isProperMap_restrict_of_slit_of_injOn_outside_open`.
  This removes the standalone obligation to prove
  `IsLocalHomeomorph (bottcher_map_outside_open_to_exterior c)` by deriving it
  from slit analyticity + outside-open injectivity.
- [x] Weakened the clopen surjectivity input from `IsProperMap` to closed-range
  on the restricted map:
  - added
    `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_of_isLocalHomeomorph_restrict`;
  - retained
    `bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_of_isLocalHomeomorph_restrict`
    as a specialization.
  This reduces the remaining geometric burden to proving range closedness (or
  any stronger criterion implying it), rather than full properness.
- [x] Added a closed-range-only derived bridge on top of slit+injectivity:
  - added
    `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_slit_of_injOn`;
  - added
    `external_ray_map_data_of_isClosedRange_restrict_of_slit_of_injOn_outside_open`.
  This removes the last dependency on explicit proper-map hypotheses from the
  derived external-ray construction path.
- [x] Weakened the rooted `c = 2` seam in `Mlc/MainConjecture.lean` from full
  external-ray data to exterior surjectivity + exact preimages of
  `approach_one_seq`:
  - rewired `mainPathData_axiom_seed` through an exterior-surjectivity seam
    witness.
  Rooted chain is now:
  `mlc_conjecture -> mainPathData_axiom_seed ->
   external_ray_map_exists`.
- [x] Removed one more rooted seam wrapper:
  - deleted `bottcherSurjOnExteriorTwo_axiom_seed`;
  - inlined its witness into `mainPathData_axiom_seed`.
- [x] Removed non-essential wrapper seams from `Mlc/MainConjecture.lean`:
  - deleted `BottcherApproachToOneSeqExactPreimageData`,
    `bottcher_approach_to_one_seq_preimage_data_of_exact_preimage_data`,
    and `bottcher_approach_to_one_seq_exact_preimage_data_of_surj_on_exterior`;
  - kept the same mathematical path by inlining those steps into
    `mainPathData_axiom_seed`.
- [x] Removed one more single-use rooted wrapper:
  - deleted `mainPathData_of_bottcherSurjOnExteriorTwo`;
  - inlined its witness construction directly into `mainPathData_axiom_seed`.
- [x] Removed the remaining local exterior-surjectivity scaffold in
  `mainPathData_axiom_seed`:
  - deleted local `h_surj` construction through `Classical.choose`;
  - switched to direct sequence witness
    `Quadratic.external_ray_map_of_data h_ray (approach_one_seq n)`.
- [x] Inlined the remaining local sequence wrapper in
  `mainPathData_axiom_seed`:
  - deleted local `h_data` binding;
  - passed the preimage-sequence witness inline to
  `mainPathData_of_bottcher_approach_to_one_seq_preimage_data_two`.
- [x] Added a non-global-slit theorem route in
  `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - analytic core over outside-open:
    `...of_isClosedRange_restrict_of_analyticAt_of_injOn`;
  - local-slit wrappers:
    `...of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn`.
  This keeps Step 4 aligned with the no-go checkpoint against global
  outside-open slit inclusion and avoids reintroducing that impossible target.
- [x] Added iterate-left-inverse bridge wrappers in
  `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `bottcher_map_inj_on_outside_open_of_iter_left_inverse`,
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse`,
  - `external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse`.
  This prepares a non-external-ray candidate route for the remaining Step-3
  outside-open injectivity payload, directly compatible with the restricted-map
  closed-range framework.
- [x] Re-extracted the rooted seed in `Mlc/MainConjecture.lean` through an
  explicit exterior-surjectivity seam:
  - added `BottcherSurjOnExteriorData`,
    `bottcherApproachToOneSeqPreimageData_of_bottcherSurjOnExteriorData`,
    `bottcherSurjOnExteriorData_two_axiom_seed`;
  - rewired `mainPathData_axiom_seed` through this seam.
  This keeps the rooted endpoint aligned with the outside-open-surjectivity
  elimination route instead of hard-coding direct ray witness construction.

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
4. Current external-ray dependency bottleneck is localized directly at
   `Quadratic.external_ray_map_exists (2 : ℂ)` through
   `mainPathData_axiom_seed`.
   The immediate replacement target is therefore a constructive
   `c = 2` exterior-surjectivity provider (preferably via outside-open
   injectivity + restricted-map clopen surjectivity), sufficient to build exact
   preimages of `approach_one_seq` without `external_ray_map_exists`.
   No-go checkpoint: the global slit payload shape
   `{z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c` should be treated as impossible in
   this model (large negative real exterior points fail slit membership at
   iterate `n = 0`), so the remaining path must use a local/eventual-slit
   condition instead. This no-go is now formalized in
   `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean` as:
   - `not_outside_open_subset_slit_orbit`,
   - `not_outside_open_subset_slit_orbit_two`.
   All rooted dependencies are tracked in
   `PLAN_external_ray_map_exists_outside_open_targets.md`.

## Exit Criteria
- `MLC.Quadratic.external_ray_map_exists` removed from `MLC.mlc_conjecture`
  axiom footprint.
- No contradiction-only provider in transitive dependencies of
  `MLC.mlc_conjecture`.
- No new axioms, no new hypotheses on `MLC.mlc_conjecture`.
